"""Export pinned replacement allocations for SlackAllocation's finite inputs.

Requires python-flint. Replays the pinned exact regional allocation checker,
NOT the predecessor matrix/PSD checks or the entire strengthened-bound chain.
The JSON packet and optional fixed Lean data modules are not proofs of the
numerical checks or a physical-bound claim. Original Gram matrices and source
columns retain their pinned source/metadata hashes and original (cell, block)
indices. --lean-dump compares Lean-decoded values against the original data.
"""
import argparse
from fractions import Fraction as F
import gzip
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess

from bind_slack import REV, need

ALLOCATION = "c92d741884064a671643081415ad701c2cb6c2f0f6ecdf5f7bac4f1bf6e84b73"
BASE = "3e2fbd42d779da00e1800ee2c5ae62e51c240f7b245c67139b12864576ba18bb"
DIRECTORY = "sdp/verification_results/slack-campaign-2935"


def check_projection_layout(rec, meta):
    """Exact source-row and reduced-polynomial checks; deliberately no PSD claim."""
    need(rec["localizer"] == meta["localizer"], "projection localizer")
    anti, holo = rec["anti"], rec["holo"]
    need(len(anti) == len(holo) == 5 and
         all(type(e) is int and e >= 0 for e in anti+holo), "projection exponents")
    need(rec["population_exponents"] == [anti[i]+holo[i] for i in range(1, 5)],
         "population exponents")
    need(rec["phase"] in ("one", "i"), "nonunit source phase")
    entries = rec["entries"]
    need(entries and len({e[0] for e in entries}) == len(entries), "projection rows")
    for row, power, coefficient in entries:
        need(type(row) is int and 0 <= row < meta["gram_side"], "source row")
        tr = meta["transform_rows"][row]
        need(len(tr) == 1 and tr[0]["coefficient"] == coefficient, "facial column")
        index = tr[0]["basis_index"]
        monomial = meta["basis"][index]["monomial"]
        need(monomial == {"anti": anti, "holo": holo, "cost_power": power} and
             meta["basis_phases"][index] == rec["phase"], "source monomial/phase")
    matrix = [[F(x) for x in row] for row in rec["reduced_matrix"]]
    n = len(entries)
    need(len(matrix) == n and all(len(row) == n for row in matrix), "projection matrix size")
    need(all(matrix[i][j] == matrix[j][i] for i in range(n) for j in range(n)),
         "projection matrix symmetry")
    power = [F(0)] * (2*max(e[1] for e in entries)+1)
    for i, (_, k, c) in enumerate(entries):
        for j, (_, l, d) in enumerate(entries):
            power[k+l] += c*d*matrix[i][j]
    loc = {"one": [1], "xi": [0, 1], "one_minus_xi": [1, -1],
           "xi_one_minus_xi": [0, 1, -1]}[rec["localizer"]]
    beta = [F(0)] * (len(power)+len(loc)-1)
    for k, c in enumerate(power):
        for l, d in enumerate(loc):
            beta[k+l] += c*d
    need(beta == list(map(F, rec["polynomial"])), "projected polynomial identity")


def load_checker(root):
    need(subprocess.check_output(
        ["git", "-C", str(root), "rev-parse", "HEAD"], text=True).strip() == REV,
        "publication revision")
    # The checker imports adaptive-slack/verify.py as well. Check the whole
    # tracked verification tree against the pinned revision before execution.
    subprocess.run(["git", "-C", str(root), "diff", "--quiet", "HEAD", "--",
                    "sdp/verification_results"], check=True)
    path = root / DIRECTORY / "verify.py"
    spec = importlib.util.spec_from_file_location("pinned_allocation", path)
    checker = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(checker)
    return checker


def packet(root):
    checker = load_checker(root)
    v, base, occ, final, _ = checker.inputs(root / "sdp")
    raw = gzip.decompress((root / DIRECTORY / "allocation.json.gz").read_bytes())
    need(hashlib.sha256(raw).hexdigest() == ALLOCATION, "allocation hash")
    cert = json.loads(raw)
    # This verifies region coverage, allowed IDs, cell ownership, positive
    # weights, PER-ORIGINAL-BLOCK budgets, and all tensor residual signs.
    gain, result = checker.allocation(v, base, occ, final, cert)
    result = {**result, "additional_occupation_slack": str(gain)}
    from flint import fmpq as Q

    maps = {(x, y): v.popmap(7, x, y, 8) for x in range(8) for y in range(8)}
    records = base["projection_records"]
    allowed = {i for b in base["integration_bins"] for i, _, _ in b["allocations"]}
    regions, used, cache = [], set(), {}
    for entry in cert["replacements"]:
        index = entry["interval_index"]
        item = base["integration_bins"][index]
        a, b = F(item["a"]), F(item["b"])
        transform = v.affine(14, a, b)
        delta = list(map(Q, entry["bernstein"]))
        for region in entry["regions"]:
            x, y = region["x"], region["y"]
            groups, _, ids = v.region_weights(region, records, allowed, item["cell"])
            used.update(ids)
            pop, cost = maps[x, y]
            values = transform * v.tensor(groups, cache) * pop
            residual = [str(values[k, i] - delta[k] * cost[i])
                        for k in range(15) for i in range(64)]
            need(all(Q(c) >= 0 for c in residual), "exported residual sign")
            # Preserve original block ownership explicitly, including multiple
            # projection IDs from the same block. Never sum their budgets twice.
            blocks = {}
            for rid, weight in region["weights"]:
                blocks.setdefault(records[rid]["block"], []).append([rid, weight])
            regions.append({
                "interval_index": index, "cell": item["cell"],
                "lo": [str(a), str(F(x, 8)), str(F(y, 8))],
                "hi": [str(b), str(F(x+1, 8)), str(F(y+1, 8))],
                "delta": entry["bernstein"],
                "allocations_by_original_block": blocks,
                "residual_14_7_7_exposure_major": residual,
            })
    raw_meta = gzip.decompress((root / "sdp/verification_results/population-refinement/certified/trajectory-metadata.json.gz").read_bytes())
    need(hashlib.sha256(raw_meta).hexdigest() == base["metadata_sha256"], "metadata hash")
    cells = {r["cell"] for r in regions}
    metadata = [m for m in json.loads(raw_meta) if m["owner"]["measure"] == "occupation_cell"
                and m["owner"]["cell_index"] in cells]
    lookup = {(m["owner"]["cell_index"], m["owner_block_index"]): m for m in metadata}
    for rid in sorted(used):
        rec = records[rid]
        check_projection_layout(rec, lookup[rec["cell"], rec["block"]])
    return {
        "schema": "LowerBoundCZ.AllocationRegion-v1",
        "revision": REV, "allocation_sha256": ALLOCATION,
        "base_decompressed_sha256": BASE,
        "source_sha256": base["source_certificate_sha256"],
        "metadata_sha256": base["metadata_sha256"],
        "source_block_layouts": [{k: m[k] for k in (
            "owner", "owner_block_index", "gram_side", "basis", "basis_phases",
            "transform_rows", "localizer")} for m in metadata],
        "projections": {i: records[i] for i in sorted(used)},
        "regions": regions,
        "regional_check_result": result,
        "undischarged": [
            "Decode all original cell blocks, including unallocated blocks, from pinned source/metadata",
            "Original PSD and embedded projection matrix domination (predecessor replay)",
            "Source drift and allocated tensor polynomial identities in Lean's normalization ideal",
            "Full predecessor, interface, reachability, and replacement-integral assembly",
        ],
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("checkout", type=Path)
    parser.add_argument("--output", type=Path, required=True, help="gzip JSON decoding packet")
    parser.add_argument("--lean-dir", type=Path, help="generate fixed Lean data modules here")
    parser.add_argument("--lean-dump", type=Path, help="compare AllocationDataAudit output against the pinned archive")
    args = parser.parse_args()
    data = packet(args.checkout.resolve())
    raw = json.dumps(data, separators=(",", ":"), sort_keys=True).encode()
    args.output.write_bytes(gzip.compress(raw, mtime=0))
    if args.lean_dir:
        emit_lean(args.checkout.resolve(), data, args.lean_dir)
    if args.lean_dump:
        verify_lean_dump(args.checkout.resolve(), data, args.lean_dump)
    print(json.dumps({"regions": len(data["regions"]),
                      "projections": len(data["projections"]),
                      "residual_coefficients": sum(len(r["residual_14_7_7_exposure_major"])
                                                   for r in data["regions"]),
                      "packet_sha256": hashlib.sha256(raw).hexdigest(),
                      "physical_bound_proved": False}, indent=2))


def emit_lean(root, data, destination):
    """Fixed literals, shared projections/groups, and every original cell-2 Gram.

    The large tensor is defined by exact arithmetic in PinnedAllocations,
    rather than duplicated as a million unwieldy rational literals.
    """
    from bind_certificates import LOWER, RAW, scalar
    from functools import lru_cache

    raw = gzip.decompress(b"".join((root / LOWER / f"certificate.json.gz.part-{i:02}").read_bytes()
                                  for i in range(2)))
    need(hashlib.sha256(raw).hexdigest() == RAW, "original Gram archive hash")
    source = json.loads(raw)["occupation_grams_by_cell"][2]
    del raw
    metadata = sorted(data["source_block_layouts"], key=lambda m: m["owner_block_index"])
    need(len(metadata) == len(source) == 736, "all original cell-2 blocks")
    need(all(m["owner"] == {"measure": "occupation_cell", "cell_index": 2} and
             m["owner_block_index"] == i for i, m in enumerate(metadata)), "source block order")
    destination.mkdir(parents=True, exist_ok=True)
    pieces = destination / "AllocationData"
    pieces.mkdir(exist_ok=True)
    header = "-- Generated by bind_allocations.py; do not edit.\n"
    namespace = ("namespace LowerBoundCZ.AllocationData\nopen AllocationCodec\n"
                 "set_option maxRecDepth 10000\nset_option maxHeartbeats 0\n")

    @lru_cache(maxsize=65536)
    def exact(s):
        return (F(s), F(0)) if "sqrt" not in s else scalar(s)

    def encoded_scalar(s):
        a, b = exact(s)
        return str(a) if not b else f"{a},{b}"

    def array(values):
        return "#[" + ", ".join(values) + "]"

    manifest = []
    for shard in range(8):
        lines = [header, "import LowerBoundCZ.AllocationCodec\n", namespace]
        for bi in range(shard*92, (shard+1)*92):
            m, Q = metadata[bi], source[bi]
            n = m["gram_side"]
            need(len(Q) == n and all(len(row) == n for row in Q), "source matrix shape")
            need(all(Q[i][j] == Q[j][i] or exact(Q[i][j]) == exact(Q[j][i])
                     for i in range(n) for j in range(i, n)), "source symmetry")
            codes = []
            for b, phase in zip(m["basis"], m["basis_phases"]):
                mono = b["monomial"]
                powers = [mono["cost_power"]] + [v for pair in zip(mono["holo"], mono["anti"]) for v in pair]
                need(len(powers) == 11 and all(type(e) is int and 0 <= e < 16 for e in powers), "power encoding")
                need(phase in ("one", "i"), "source phase encoding")
                codes.append(str(2*sum(e*16**i for i, e in enumerate(powers)) + (phase == "i")))
            need(len(m["basis"]) == len(m["basis_phases"]) and len(m["transform_rows"]) == n, "source columns")
            rows = []
            for row in m["transform_rows"]:
                need(all(0 <= e["basis_index"] < len(codes) and type(e["coefficient"]) is int for e in row), "sparse source row")
                rows.append(" ".join(f'{e["basis_index"]}:{e["coefficient"]}' for e in row))
            loc = {"one": 0, "xi": 1, "one_minus_xi": 2, "xi_one_minus_xi": 3}[m["localizer"]]
            upper = " ".join(encoded_scalar(Q[i][j]) for i in range(n) for j in range(i, n))
            lines.append(f"def source{bi} : EncodedSource :=\n  ⟨{n}, {loc}, {json.dumps(' '.join(codes))},\n"
                         f"    {json.dumps('|'.join(rows))},\n    {json.dumps(upper)}⟩\n")
        lines.append("end LowerBoundCZ.AllocationData\n")
        path = pieces / f"Source{shard}.lean"
        path.write_text("\n".join(lines))
        manifest.append((path.name, hashlib.sha256(path.read_bytes()).hexdigest()))
    del source
    ids = sorted(map(int, data["projections"]))
    need(len(ids) == 1078, "projection count")
    index = {rid: i for i, rid in enumerate(ids)}
    lines = [header] + [f"import LowerBoundCZ.AllocationData.Source{i}\n" for i in range(8)] + [namespace]
    lines.append("def sources : Array EncodedSource := " + array([f"source{i}" for i in range(736)]))
    for i, rid in enumerate(ids):
        r = data["projections"][rid] if rid in data["projections"] else data["projections"][str(rid)]
        need(r["cell"] == 2, "projection cell")
        for name, values, decoder in (("rows", [e[0] for e in r["entries"]], "naturals"),
                                       ("matrix", [F(x) for row in r["reduced_matrix"] for x in row], "rationals"),
                                       ("polynomial", map(F, r["polynomial"]), "rationals"),
                                       ("population", r["population_exponents"], "naturals")):
            lines.append(f"private def projection{i}_{name} : String := {json.dumps(' '.join(map(str, values)))}")
        lines.append(f"def projection{i} : EncodedProjection := ⟨{rid}, {r['block']}, projection{i}_rows, "
                     f"projection{i}_matrix, projection{i}_polynomial, projection{i}_population⟩")
    lines.append("def projections : Array EncodedProjection := " + array([f"projection{i}" for i in range(1078)]))
    regions = sorted(data["regions"], key=lambda r: (r["interval_index"], F(r["lo"][1]), F(r["lo"][2])))
    groups = {(): 0}
    group_values = ['""']
    maps = []
    for i, r in enumerate(regions):
        need(r["cell"] == 2 and r["interval_index"] == 176+i//64, "region order")
        need(list(map(F, r["lo"])) == [F(48+i//64, 64), F(i%64//8, 8), F(i%8, 8)] and
             list(map(F, r["hi"])) == [F(49+i//64, 64), F(i%64//8+1, 8), F(i%8+1, 8)], "box coordinates")
        row = []
        for bi in range(736):
            original = r["allocations_by_original_block"].get(bi, r["allocations_by_original_block"].get(str(bi), []))
            key = tuple((index[rid], str(F(w))) for rid, w in original)
            if key not in groups:
                groups[key] = len(groups)
                group_values.append(json.dumps(" ".join(f"{rid}:{w}" for rid, w in key)))
            row.append(groups[key])
        maps.append(json.dumps(" ".join(map(str, row))))
        if i % 64 == 0:
            lines.append(f"private def delta{i//64} : String := " + json.dumps(" ".join(str(F(x)) for x in r["delta"])))
        else:
            need(r["delta"] == regions[i-i%64]["delta"], "shared profile")
    for i, g in enumerate(group_values):
        lines.append(f"private def group{i} := {g}")
    lines.append("def groups := " + array([f"group{i}" for i in range(len(group_values))]))
    for i, row in enumerate(maps):
        lines.append(f"private def region{i} := {row}")
    lines.append("def regionGroups := " + array([f"region{i}" for i in range(1024)]))
    lines.append("def profiles := " + array([f"delta{i}" for i in range(16)]))
    lines.append("end LowerBoundCZ.AllocationData\n")
    path = destination / "AllocationData.lean"
    path.write_text("\n".join(lines))
    manifest.append((path.name, hashlib.sha256(path.read_bytes()).hexdigest()))
    (destination / "AllocationData" / "bindings.json").write_text(json.dumps({
        "revision": REV, "source_sha256": RAW, "allocation_sha256": ALLOCATION,
        "metadata_sha256": data["metadata_sha256"], "files": dict(manifest),
        "sources": 736, "projections": 1078, "regions": 1024, "groups": len(groups),
    }, indent=2)+"\n")
    print("Fixed Lean source matrices, columns, projections, profiles and allocations exported.")


def verify_lean_dump(root, data, path):
    """Compare decoded values, not just hashes or dimensions. No sampling of
    matrices, source columns, allocations or profiles; only tensor evaluation
    is sampled here (the regional checker checks every tensor coefficient).
    """
    from bind_certificates import LOWER, RAW, scalar
    from functools import lru_cache
    raw = gzip.decompress(b"".join((root / LOWER / f"certificate.json.gz.part-{i:02}").read_bytes()
                                  for i in range(2)))
    need(hashlib.sha256(raw).hexdigest() == RAW, "source hash in data comparison")
    matrices = json.loads(raw)["occupation_grams_by_cell"][2]
    del raw
    metadata = sorted(data["source_block_layouts"], key=lambda m: m["owner_block_index"])
    records = {int(k): v for k, v in data["projections"].items()}
    ids = sorted(records)
    regions = sorted(data["regions"], key=lambda r: (r["interval_index"], F(r["lo"][1]), F(r["lo"][2])))
    @lru_cache(maxsize=65536)
    def exact(s):
        return (F(s), F(0)) if "sqrt" not in s else scalar(s)
    matrix_count, weight_count = 0, 0
    with path.open() as dump:
        def read(tag, *indices):
            fields = dump.readline().split()
            prefix = [tag, *map(str, indices)]
            need(fields[:len(prefix)] == prefix, f"decoded line order: {prefix}")
            return fields[len(prefix):]
        for b, (m, Q) in enumerate(zip(metadata, matrices)):
            loc = {"one": 0, "xi": 1, "one_minus_xi": 2, "xi_one_minus_xi": 3}[m["localizer"]]
            need(list(map(int, read("S", b))) == [m["gram_side"], loc], f"source shape {b}")
            codes = list(map(int, read("B", b)))
            need(len(codes) == len(m["basis"]), f"basis size {b}")
            for code, basis, phase in zip(codes, m["basis"], m["basis_phases"]):
                mono = basis["monomial"]
                powers = [mono["cost_power"]] + [v for pair in zip(mono["holo"], mono["anti"]) for v in pair]
                need(code//2//16**11 == 0 and [(code//2//16**k)%16 for k in range(11)] == powers
                     and code%2 == int(phase == "i"), f"decoded powers/phase {b}")
            for i, row in enumerate(m["transform_rows"]):
                values = [tuple(map(int, token.split(":"))) for token in read("C", b, i)]
                need(values == [(e["basis_index"], e["coefficient"]) for e in row], f"decoded facial row {b}:{i}")
            values = [tuple(map(F, token.split(","))) for token in read("Q", b)]
            expected = [exact(s) for row in Q for s in row]
            need(values == expected, f"decoded full matrix (including lower triangle) {b}")
            matrix_count += len(values)
        for i, rid in enumerate(ids):
            r = records[rid]
            need(list(map(int, read("P", i))) == [rid, r["block"]], f"projection identity {i}")
            need(list(map(int, read("R", i))) == [e[0] for e in r["entries"]], f"projection rows {i}")
            need(list(map(F, read("M", i))) == [F(c) for row in r["reduced_matrix"] for c in row], f"projection matrix {i}")
            need(list(map(int, read("E", i))) == r["population_exponents"], f"population exponents {i}")
            need(list(map(F, read("F", i))) == list(map(F, r["polynomial"])), f"projection polynomial {i}")
        groups = []
        for g in range(1180):
            pairs = [token.split(":") for token in read("G", g)]
            groups.append([(ids[int(i)], F(w)) for i, w in pairs])
        for i, region in enumerate(regions):
            gids = list(map(int, read("A", i)))
            need(len(gids) == 736, f"region block shape {i}")
            for b, g in enumerate(gids):
                expected = region["allocations_by_original_block"].get(b,
                    region["allocations_by_original_block"].get(str(b), []))
                need(groups[g] == [(rid, F(w)) for rid, w in expected], f"decoded allocation {i}:{b}")
                weight_count += len(expected)
        for i in range(16):
            need(list(map(F, read("D", i))) == list(map(F, regions[64*i]["delta"])), f"decoded profile {i}")
        for r in (0, 31, 1000):
            for a, b, c in ((0,0,7), (5,2,6), (14,7,0)):
                need(list(map(F, read("T", r, a, b, c))) ==
                     [F(regions[r]["residual_14_7_7_exposure_major"][a*64+b*8+c])],
                     f"Lean tensor computation {r}:{a}:{b}:{c}")
        need(not dump.read().strip(), "extra decoded data")
    print(f"PASS: {matrix_count} full Gram entries, all source columns and projections, "
          f"{weight_count} allocated weights, all profiles, 9 Lean tensor coefficients match pinned inputs.")


if __name__ == "__main__":
    main()
