"""Bind all remaining retained occupation regions and replay local tensor checks.

The optional domination replay checks every used regional projection against
the original Gram, after comparing the Lean-decoded data. Source PSD is reused
from the recorded base audit; normalization-ideal identities remain separate.
"""
import argparse
from fractions import Fraction as F
import gzip
import hashlib
import importlib.util
import json
import copy
import sys
from pathlib import Path
from functools import lru_cache

from bind_allocations import load_checker, check_projection_layout
from bind_certificates import LOWER, RAW, scalar
from bind_profiles import collect
from bind_slack import need


def module(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def collect_regions(root):
    packet = collect(root)
    checker = load_checker(root)
    v, base, occ, _, _ = checker.inputs(root / "sdp")
    directory = root / "sdp/verification_results"
    regional = json.loads(gzip.decompress((directory / "adaptive-slack/certified/certificate.json.gz").read_bytes()))
    dark_profiles = {e["interval_index"]: e for e in
                     json.loads((directory / "slack-campaign-2935/dark/profiles.json").read_text())["profiles"]}
    reach = module(directory / "reachability-slack/verify.py", "regional_reach")
    dark = module(directory / "slack-campaign-2935/dark/verify.py", "regional_dark")
    records = base["projection_records"]
    allowed = {a[0] for b in base["integration_bins"] for a in b["allocations"]}
    barrier, _ = reach.barrier_coefficients()
    from flint import fmpq as Q
    cache, maps, used, group_ids, groups, region_ids, region_maps = {}, {}, set(), {(): 0}, [""], {}, []
    regions, excluded, checks = [], [], 0
    for i, p in enumerate(packet["profiles"]):
        if p["owner"] == "allocation":
            continue  # Already bound in PinnedAllocations; never credit it twice.
        cell, n = p["cell"], p["grid"]
        a, b = F(p["local_left"]), F(p["local_right"])
        prior = regional["intervals"][p["source_index"]]
        if prior["mode"] == "regional":
            choices = {(r["x"], r["y"]): r for r in prior["regions"]}
            need(len(choices) == len(prior["regions"]) == 16, "coarse coverage")
        else:
            need(i == 1 and p["owner"] == "inherited", "unexpected inherited allocation")
            choices = {(x, y): {"weights": [[rid, w] for rid, w, _ in base["integration_bins"][i]["allocations"]]}
                       for x in range(4) for y in range(4)}
        tensors, assignments = {}, {}
        radius = min(F(p["right"]), F(733, 250)-F(p["left"]))
        dropped = 0
        for x in range(n):
            for y in range(n):
                skip = ((p["owner"] == "reachable" and reach.excluded(x, y, n, radius, barrier)) or
                        (p["owner"] == "dark" and dark.excluded(x, y, n, radius)))
                if skip:
                    excluded.append([i, x, y, n, p["owner"]]); dropped += 1
                    continue
                key = (x*4//n, y*4//n)
                if key not in tensors:
                    r = choices[key]
                    tensor_groups, _, ids = v.region_weights(r, records, allowed, cell)
                    used.update(ids)
                    tensors[key] = v.affine(14, a, b)*v.tensor(tensor_groups, cache)
                    blocks = [[] for _ in range(736)]
                    for rid, w in r["weights"]:
                        blocks[records[rid]["block"]].append((rid, str(F(w))))
                    row = []
                    for block in blocks:
                        g = tuple(block)
                        if g not in group_ids:
                            group_ids[g] = len(groups)
                            groups.append(" ".join(f"{rid}:{w}" for rid, w in g))
                        row.append(group_ids[g])
                    vector = tuple(row)
                    if vector not in region_ids:
                        region_ids[vector] = len(region_maps); region_maps.append(row)
                    assignments[key] = region_ids[vector]
                if (x, y, n) not in maps:
                    maps[x, y, n] = v.popmap(7, x, y, n)
                pop, costs = maps[x, y, n]
                values = tensors[key]*pop
                for k, delta in enumerate(p["bernstein"]):
                    for z, cost in enumerate(costs):
                        need(values[k, z] >= Q(delta)*cost, f"tensor sign {i}/{x}/{y}/{k}/{z}")
                        checks += 1
                regions.append([i, assignments[key], x, y, n])
        if p["owner"] == "reachable":
            need(dropped == occ["intervals"][i]["discarded_boxes"], "W8 box count")
        if p["owner"] == "dark":
            need(dropped == dark_profiles[i]["discarded_boxes"] and
                 n*n-dropped == dark_profiles[i]["retained_boxes"], "dark box counts")
        if i % 16 == 0:
            print(f"CHECKED profile {i}, retained {len(regions)}, coefficients {checks}", flush=True)
    need({r[0] for r in regions} == set(range(321))-set(range(176,192)), "remaining profile coverage")
    need(len({(r[0],r[2],r[3],r[4]) for r in regions}) == len(regions), "duplicate retained box")
    raw_meta = gzip.decompress((directory / "population-refinement/certified/trajectory-metadata.json.gz").read_bytes())
    need(hashlib.sha256(raw_meta).hexdigest() == base["metadata_sha256"], "metadata hash")
    metadata = {(m["owner"]["cell_index"], m["owner_block_index"]): m
                for m in json.loads(raw_meta) if m["owner"]["measure"] == "occupation_cell"}
    need(len(metadata) == 3680, "all five source cells")
    for rid in used:
        r = records[rid]; check_projection_layout(r, metadata[r["cell"], r["block"]])
    return packet, metadata, records, sorted(used), groups, region_maps, regions, excluded, checks


def export(root, destination):
    packet, metadata, records, ids, groups, maps, regions, excluded, checks = collect_regions(root)
    raw = gzip.decompress(b"".join((root / LOWER / f"certificate.json.gz.part-{i:02}").read_bytes() for i in range(2)))
    need(hashlib.sha256(raw).hexdigest() == RAW, "source Gram hash")
    source = json.loads(raw)["occupation_grams_by_cell"]
    del raw
    need(len(source) == 5 and all(len(cell) == 736 for cell in source), "source layout")
    pieces = destination / "RegionalData"; pieces.mkdir(parents=True, exist_ok=True)
    header = "-- Generated by bind_regions.py; do not edit.\n"
    ns = "namespace LowerBoundCZ.RegionalData\nopen AllocationCodec\nset_option maxRecDepth 10000\n"
    imports = []

    def write(name, lines, dependencies):
        path = pieces / f"{name}.lean"
        path.write_text(header + "".join(f"import {d}\n" for d in dependencies) + ns +
                        "\n".join(lines) + "\nend LowerBoundCZ.RegionalData\n")
        imports.append(f"LowerBoundCZ.RegionalData.{name}")

    def array(xs):
        return "#[" + ", ".join(xs) + "]"

    @lru_cache(maxsize=65536)
    def exact(s):
        return (F(s), F(0)) if "sqrt" not in s else scalar(s)

    for cell in range(5):
        for shard in range(8):
            lines = []
            for bi in range(92*shard, 92*(shard+1)):
                m, reference, mat = metadata[cell, bi], metadata[2, bi], source[cell][bi]
                for key in ("gram_side", "basis", "basis_phases", "transform_rows", "localizer"):
                    need(m[key] == reference[key], "shared source columns")
                n = m["gram_side"]
                need(len(mat) == n and all(len(row) == n for row in mat), "matrix dimensions")
                need(all(exact(mat[i][j]) == exact(mat[j][i]) for i in range(n) for j in range(i, n)), "matrix symmetry")
                if cell == 2:
                    lines.append(f"def source{cell}_{bi} := AllocationData.source{bi}")
                else:
                    upper = []
                    for i in range(n):
                        for j in range(i, n):
                            a, b = exact(mat[i][j]); upper.append(str(a) if not b else f"{a},{b}")
                    lines.append(f"def source{cell}_{bi} : EncodedSource := {{ AllocationData.source{bi} with upper := " +
                                 json.dumps(" ".join(upper)) + " }")
            lines.append(f"def sources{cell}_{shard} := " + array([f"source{cell}_{b}" for b in range(92*shard,92*(shard+1))]))
            write(f"Source{cell}_{shard}", lines, [f"LowerBoundCZ.AllocationData.Source{shard}"])
    remap = {rid: i for i, rid in enumerate(ids)}
    projections = []
    for rid in ids:
        r = records[rid]
        fields = [" ".join(str(e[0]) for e in r["entries"]),
                  " ".join(str(F(x)) for row in r["reduced_matrix"] for x in row),
                  " ".join(str(F(x)) for x in r["polynomial"]),
                  " ".join(map(str, r["population_exponents"]))]
        projections.append(f"⟨{rid}, {r['block']}, " + ", ".join(map(json.dumps, fields)) + "⟩")
    groups = [" ".join(f"{remap[int(a.split(':')[0])]}:{a.split(':')[1]}" for a in g.split()) for g in groups]
    tables = dict(projections=("EncodedProjection", projections), groups=("String", list(map(json.dumps, groups))),
                  maps=("String", [json.dumps(" ".join(map(str, m))) for m in maps]),
                  regions=("Nat × Nat × Nat × Nat × Nat", ["("+", ".join(map(str,r))+")" for r in regions]))
    lengths = {}
    for name, (typ, values) in tables.items():
        lengths[name] = len(values)
        for shard, start in enumerate(range(0,len(values),512)):
            write(f"{name}{shard}", [f"def {name}{shard} : Array ({typ}) := " + array(values[start:start+512])],
                  ["LowerBoundCZ.AllocationCodec"])
    lines = [header] + [f"import {x}\n" for x in imports] + [ns]
    lines.append("def sources := " + " ++ ".join(f"sources{c}_{s}" for c in range(5) for s in range(8)))
    for name, length in lengths.items():
        lines.append(f"def {name} := " + " ++ ".join(f"{name}{s}" for s in range((length+511)//512)))
    lines.append("def profiles : Array (Nat × String × String × String) := " + array([
        f"({p['cell']}, {json.dumps(p['local_left'])}, {json.dumps(p['local_right'])}, " +
        json.dumps(" ".join(p["bernstein"])) + ")" for p in packet["profiles"]]))
    lines.append("end LowerBoundCZ.RegionalData\n")
    (destination / "RegionalData.lean").write_text("\n".join(lines))
    report = dict(sources=3680, **lengths, excluded=excluded, tensor_checks=checks,
                  hashes=packet["hashes"], source_hash=RAW,
                  scope="retained local regions only; original PSD/domination and ideal identities remain external")
    (pieces / "bindings.json").write_text(json.dumps(report, indent=2)+"\n")
    print(json.dumps({k: v for k,v in report.items() if k not in ("excluded", "hashes")}), flush=True)


def verify_dump(root, path):
    packet, metadata, records, ids, groups, maps, regions, _, _ = collect_regions(root)
    raw = gzip.decompress(b"".join((root / LOWER / f"certificate.json.gz.part-{i:02}").read_bytes() for i in range(2)))
    need(hashlib.sha256(raw).hexdigest() == RAW, "source Gram hash")
    source = json.loads(raw)["occupation_grams_by_cell"]
    del raw
    remap = {rid: i for i, rid in enumerate(ids)}
    with path.open() as stream:
        line_number = 0

        def line():
            nonlocal line_number
            line_number += 1
            result = stream.readline()
            need(result != "", f"truncated decoder output at line {line_number}")
            return result.rstrip("\n")

        def same(expected):
            need(line() == expected, f"decoded mismatch at line {line_number}")

        @lru_cache(maxsize=65536)
        def exact(s):
            return (F(s), F(0)) if "sqrt" not in s else scalar(s)

        for c in range(5):
            for b in range(736):
                m, mat = metadata[c, b], source[c][b]
                n = m["gram_side"]
                loc = {"one": 0, "xi": 1, "one_minus_xi": 2, "xi_one_minus_xi": 3}[m["localizer"]]
                same(f"S {c*736+b} {n} {loc}")
                codes = []
                for basis, phase in zip(m["basis"], m["basis_phases"]):
                    mono = basis["monomial"]
                    ex = [mono["cost_power"]]+[v for pair in zip(mono["holo"],mono["anti"]) for v in pair]
                    codes.append(2*sum(e*16**k for k,e in enumerate(ex))+(phase == "i"))
                need(list(map(int, line().split())) == codes, "decoded source basis")
                same("|".join(" ".join(f'{e["basis_index"]}:{e["coefficient"]}' for e in row)
                              for row in m["transform_rows"]))
                values = [tuple(map(F, x.split(","))) for x in line().split()]
                need(values == [exact(mat[i][j]) for i in range(n) for j in range(i,n)], "decoded source matrix")
        for i,rid in enumerate(ids):
            p = records[rid]
            same(f"P {i} {rid} {p['block']}")
            need(list(map(int,line().split())) == [e[0] for e in p["entries"]], "projection rows")
            need(list(map(F,line().split())) == [F(x) for row in p["reduced_matrix"] for x in row], "projection matrix")
            need(list(map(F,line().split())) == list(map(F,p["polynomial"])), "projection polynomial")
            need(list(map(int,line().split())) == p["population_exponents"], "projection exponents")
        for i,g in enumerate(groups):
            same(f"G {i}")
            actual = [(int(x.split(":")[0]),F(x.split(":")[1])) for x in line().split()]
            expected = [(remap[int(x.split(":")[0])],F(x.split(":")[1])) for x in g.split()]
            need(actual == expected, "allocation weights/ownership")
        for i,m in enumerate(maps):
            same(f"M {i}"); need(list(map(int,line().split())) == m, "allocation map")
        for i,r in enumerate(regions):
            same("R " + " ".join(map(str,[i]+r)))
        for i,p in enumerate(packet["profiles"]):
            q = line().split()
            need(q[:3] == ["D",str(i),str(p["cell"])] and
                 list(map(F,q[3:])) == [F(p["local_left"]),F(p["local_right"])], "profile endpoints")
            need(list(map(F,line().split())) == list(map(F,p["bernstein"])), "profile coefficients")
        v = module(root / "sdp/verification_results/adaptive-slack/verify.py", "sample_tensor")
        from flint import fmpq as Q
        for slot in (0, 1, 237, 320):
            ri = next(i for i,r in enumerate(regions) if r[0] == slot)
            _, mi, x, y, n = regions[ri]
            p = packet["profiles"][slot]
            weights = [[int(t.split(":")[0]),t.split(":")[1]]
                       for gid in maps[mi] for t in groups[gid].split()]
            ts, _, _ = v.region_weights({"weights": weights}, records, set(ids), p["cell"])
            pop, cost = v.popmap(7,x,y,n)
            tensor = v.affine(14,F(p["local_left"]),F(p["local_right"]))*v.tensor(ts,{})*pop
            expected = F(str(tensor[3,22]-Q(p["bernstein"][3])*cost[22]))
            tag, actual_region, actual = line().split()
            need(tag == "T" and int(actual_region) == ri and F(actual) == expected, "tensor sample")
        need(stream.read() == "", "unexpected decoder output")
    print("PASS: exhaustive decoded source matrices/columns, projections, weights, maps, retained boxes and profiles")
    return metadata, records, ids


def audit_domination(root, dump, destination):
    """Certify Q-E R E^T >= 0 on all used pairs, not just sampled matrices.

    On the active face, the base PSD audit and the validated inverse imply
    Q>0. R>0 and R^-1-E^T Q^-1 E>0 imply domination by the Schur complement.
    All omitted rows of Q are exactly zero and all selected rows are active.
    Consequently the full matrix is PSD, even when its zero face is singular.
    """
    from flint import ctx
    import flint
    ctx.prec = 384
    metadata, records, ids = verify_dump(root, dump)
    binding_path = Path(__file__).parent / "certificate-bindings.json"
    binding = json.loads(binding_path.read_bytes())
    need(binding["lower_raw_sha256"] == RAW and
         binding["lower_audit"]["all_gram_matrices_exactly_positive_semidefinite"] is True and
         binding["lower_audit"]["nonzero_exact_residual_count"] == 0, "completed source PSD audit")
    raw = gzip.decompress(b"".join((root / LOWER / f"certificate.json.gz.part-{i:02}").read_bytes()
                                  for i in range(2)))
    need(hashlib.sha256(raw).hexdigest() == RAW, "source Gram hash")
    source = json.loads(raw)
    del raw
    directory = root / "sdp/verification_results/population-refinement"
    sys.path.insert(0, str(directory))
    verifier = module(directory / "verify_population_slack.py", "regional_matrix_verifier")
    controls = domination_controls(verifier)
    cache, previous, blocks, results = {}, None, set(), []
    lean_indices = {rid: i for i, rid in enumerate(ids)}
    for rid in sorted(ids, key=lambda rid: (records[rid]["cell"], records[rid]["block"], rid)):
        rec = records[rid]
        key = (rec["cell"], rec["block"])
        if key != previous:
            cache.clear()  # One validated inverse per block, without retaining every dense inverse.
            previous = key
        verifier.check_projection(rec, metadata, source, cache)
        blocks.add(key)
        results.append(dict(lean_projection=lean_indices[rid], source_projection=rid,
                            cell=key[0], block=key[1], selected_rows=[e[0] for e in rec["entries"]],
                            active_size=len(rec["active_indices"]),
                            record_sha256=hashlib.sha256(json.dumps(rec, sort_keys=True).encode()).hexdigest()))
        if len(results) % 100 == 0:
            print(f"DOMINATION {len(results)}/{len(ids)}; source blocks {len(blocks)}", flush=True)
    need(len(results) == len(ids) == 6190, "complete regional projection coverage")
    report = dict(status="PASS", scope="PinnedRegion.NumericalChecks.blocks domination; source PSD reused",
                  projections=len(results), source_blocks=len(blocks), precision_bits=ctx.prec,
                  method="validated active-face inverse and positive LDL pivots of R and R^-1-E^T Q^-1 E",
                  source_sha256=RAW, decoded_sha256=hashlib.sha256(dump.read_bytes()).hexdigest(),
                  binding_sha256=hashlib.sha256(binding_path.read_bytes()).hexdigest(),
                  checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  upstream_checkers={p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in
                    [directory / "verify_population_slack.py", directory / "verify_projected_slack.py"]},
                  python_flint=flint.__version__, negative_controls=controls,
                  source_psd_replayed=False, ideal_identities_checked=False,
                  results=sorted(results, key=lambda r: r["lean_projection"]))
    destination.write_text(json.dumps(report, indent=2)+"\n")
    print(f"PASS: all {len(results)} regional projections on {len(blocks)} source blocks; Arb {ctx.prec} bits")


def domination_controls(verifier):
    """An asymmetric matrix distinguishes the correct Schur threshold 5/2.
    Also exercise full-space zero-face embedding and input rejection.
    """
    anti, holo = [0,0,1,0,0], [0]*5
    meta = {(0,0): dict(localizer="one", transform_rows=[[dict(basis_index=0, coefficient=1)]],
                        basis=[dict(monomial=dict(anti=anti, holo=holo, cost_power=0))], basis_phases=["1"])}
    source = dict(occupation_grams_by_cell=[[[["3","1","0"],["1","2","0"],["0","0","0"]]]])
    rec = dict(cell=0, block=0, anti=anti, holo=holo, population_exponents=[0,1,0,0],
               localizer="one", entries=[[0,0,1]], active_indices=[0,1], phase="1",
               reduced_matrix=[["2"]], polynomial=["2"])
    verifier.check_projection(rec, meta, source, {})
    def inflated(r):
        r.update(reduced_matrix=[["3"]], polynomial=["3"])
    def wrong_face(r):
        r["active_indices"] = [0]
    def duplicate(r):
        r["entries"].append(r["entries"][0])
    rejected = []
    for name, mutate in [("inflated projection", inflated), ("omitted nonzero row", wrong_face),
                         ("duplicate selected row", duplicate)]:
        bad = copy.deepcopy(rec); mutate(bad)
        try:
            verifier.check_projection(bad, meta, source, {})
        except ValueError:
            rejected.append(name)
        else:
            raise ValueError("accepted negative control: " + name)
    return rejected


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("checkout", type=Path)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--lean-dump", type=Path)
    parser.add_argument("--domination-report", type=Path)
    args = parser.parse_args()
    need(args.output is not None or args.lean_dump is not None, "choose output or lean-dump")
    need(args.domination_report is None or args.lean_dump is not None, "domination requires Lean-decoded data")
    if args.output:
        export(args.checkout, args.output)
    if args.domination_report:
        audit_domination(args.checkout, args.lean_dump, args.domination_report)
    elif args.lean_dump:
        verify_dump(args.checkout, args.lean_dump)
