"""Bind the pinned publication archives to Lean data; not a PSD verifier.

Run with python-flint==0.9.0. Input is a checkout of Lowerbound_pub at REV.
No output is written until hashes, layout, objective and upper checks pass.
"""
import argparse
import ast
from collections import OrderedDict
from fractions import Fraction as F
from functools import lru_cache
import gzip
import hashlib
import importlib.util
import json
from math import comb
from pathlib import Path
import subprocess
import sys
import tempfile

REV = "139dfc0aeb39fbc09d9352a3cbfcd603cb6612e2"
LOWER = "sdp/verification_results/five-cell-ceiling/certification/o7-shoulder-36-t29305-axis"
UPPER = "certificates/cz-upper-bound-2.935875225844105-v1/verification"
RAW = "1f715c99684ed7dbbf1036f168eadac54043e0a235e0f9f273451f875db4bf52"
GZIP = "53731503c1be0bc7c9645b4cc98c7208b6bddbdfc7d5b407340e33ca27b6ce16"
VERIFIER = "7144feb6dd8a1b79c331004a8f4ff9c12308e11fc7b66bb164a542f0d86f2bac"
WITNESS = "fbd9f18240972d437468f63ef0b704bc1af94917690c15736a5777ab3ce4d676"


def need(ok, message):
    if not ok:
        raise ValueError(message)


def digest(b):
    return hashlib.sha256(b).hexdigest()


def packed(x):
    return json.dumps(x, separators=(",", ":"), sort_keys=True).encode()


def scalar(text):
    """Parse exact Q(sqrt(2)) syntax without eval or binary floating point."""
    def parse(n):
        if isinstance(n, ast.Constant) and type(n.value) is int:
            return F(n.value), F(0)
        if isinstance(n, ast.UnaryOp) and isinstance(n.op, (ast.USub, ast.UAdd)):
            a, b = parse(n.operand)
            return (-a, -b) if isinstance(n.op, ast.USub) else (a, b)
        if (isinstance(n, ast.Call) and isinstance(n.func, ast.Name)
                and n.func.id == "sqrt" and len(n.args) == 1 and not n.keywords
                and isinstance(n.args[0], ast.Constant) and n.args[0].value == 2):
            return F(0), F(1)
        if isinstance(n, ast.BinOp):
            a, b = parse(n.left)
            c, d = parse(n.right)
            if isinstance(n.op, ast.Add):
                return a+c, b+d
            if isinstance(n.op, ast.Sub):
                return a-c, b-d
            if isinstance(n.op, ast.Mult):
                return a*c+2*b*d, a*d+b*c
            if isinstance(n.op, ast.Div):
                den = c*c-2*d*d
                return (a*c-2*b*d)/den, (b*c-a*d)/den
        raise ValueError(f"unsupported exact scalar: {text}")
    return parse(ast.parse(text, mode="eval").body)


@lru_cache(None)
def monomials(n, degree):
    def compositions(total, slots):
        if slots == 1:
            yield (total,)
        else:
            for k in range(total+1):
                for rest in compositions(total-k, slots-1):
                    yield (k,)+rest
    return tuple(v for d in range(degree+1) for v in compositions(d, n))


def normal(a, h):
    return all(not (a[i] and h[i]) for i in ((0, 1, 3) if len(a) == 5 else (0, 2)))


def charge(v):
    weights = ((1, 0), (0, 1), (-1, 1), (0, 2), (-1, 2))
    if len(v) == 4:
        weights = weights[1:]
    return tuple(sum(x*w[j] for x, w in zip(v, weights)) for j in (0, 1))


def basis(n, degree, invariant=False):
    blocks = OrderedDict()
    for xi in range(degree+1):
        for a in monomials(n, degree-xi):
            ac = charge(a)
            for h in monomials(n, degree-xi-sum(a)):
                if not normal(a, h):
                    continue
                hc = charge(h)
                q = (hc[0]-ac[0], hc[1]-ac[1])
                if invariant:
                    if q == (0, 0) and a <= h:
                        blocks.setdefault(q, []).append((xi, a, h))
                elif q <= (-q[0], -q[1]):
                    blocks.setdefault(q, []).append((xi, a, h))
    return blocks


def face_columns(b):
    cols, groups = [], OrderedDict()
    for i, (xi, a, h) in enumerate(b):
        if a[2] or h[2] or a[4] or h[4]:
            cols.append([(i, 1)])
        else:
            key = (xi, h[0]-a[0], h[1]-a[1], h[3]-a[3])
            groups.setdefault(key, []).append(i)
    for indices in groups.values():
        for k in range(1, len(indices)):
            cols.append([(i, 1) for i in indices[:k]]+[(indices[k], -k)])
    return cols


def lean_gram_layout(block, family):
    """RawBlock layout: prune unused columns, retain source order and signs.

    The Lean decoder takes source powers, then conjugates into its positive
    charge basis. Its transport matrix, not the archived Gram, gets parity signs.
    """
    basis_rows = block["basis"]
    weights = block.get("columns", [[(i, 1)] for i in range(len(basis_rows))])
    used = sorted({i for col in weights for i, coefficient in col if coefficient})
    need(bool(used), "empty source block")
    positions = {i: j for j, i in enumerate(used)}
    powers, partners, signs = [], [], []
    charge_weights = ((0, 0), (1, 0), (-1, 0), (0, 1), (0, -1),
                      (-1, 1), (1, -1), (0, 2), (0, -2), (-1, 2), (1, -2))
    q = tuple(block["charge"])
    target_q = tuple(-v for v in q)
    need(target_q[0] > 0 or target_q[0] == 0 and target_q[1] >= 0, "Lean kept charge")
    for i in used:
        xi, anti, holo = basis_rows[i]
        if len(anti) == 4:
            anti, holo = (0,)+tuple(anti), (0,)+tuple(holo)
        p = [xi]+[v for pair in zip(holo, anti) for v in pair]
        partner = [xi]+[v for pair in zip(anti, holo) for v in pair]
        need(tuple(sum(v*w[j] for v, w in zip(p, charge_weights)) for j in (0, 1)) == q,
             "source coordinate/charge correspondence")
        need(all(not (partner[j] and partner[j+1]) for j in (1, 3, 7)), "normal target column")
        need(sum(partner) <= (6 if family == "interval" else 7), "target degree")
        if family == "moment":
            need(any(partner[j] for j in (5, 6, 9, 10)), "target zero-cost face")
        if family == "interface":
            need(partner[:3] == [0, 0, 0], "interface contains control or exposure")
        powers.append(p)
        partners.append(partner)
        signs.append(-1 if (p[1]+p[2]) % 2 else 1)
    sparse = [[(positions[i], c) for i, c in col if c] for col in weights]
    return dict(source_charge=q, target_charge=target_q, source_powers=powers,
                target_powers=partners, parity_signs=signs, source_basis_indices=used,
                weights=sparse, family=family,
                theorem="LowerBoundCZ.Certification.GramBridge.RawBlock.cone")


def qlean(q):
    return f"({q.numerator} / {q.denominator} : ℚ)"


def diagonal_signature(m):
    xi, a, h = m
    powers = [x+y for x, y in zip(a, h)]
    # Normal form of |m|²: |u|²=1, |g_k|²=1-|r_k|².
    terms = {}
    for j in range(powers[1]+1):
        for k in range(powers[3]+1):
            e = (0, 0, powers[2]+j, 0, powers[4]+k)
            weight = (-1)**(j+k)*comb(powers[1], j)*comb(powers[3], k)
            for shift, sign in ((1, 1), (2, -1)):
                key = (2*xi+shift, e, e)
                terms[key] = terms.get(key, 0)+sign*weight
    return tuple(sorted((key, value) for key, value in terms.items() if value))


def array(name, typ, entries):
    # Small chunks avoid Lean's parser/recursion depth limits.
    lines, chunks = [], []
    for i in range(0, len(entries), 64):
        chunk = f"{name}_{i//64}"
        chunks.append(chunk)
        lines.append(f"private def {chunk} : Array ({typ}) := #[\n  "+",\n  ".join(entries[i:i+64])+"\n]\n")
    lines.append(f"def {name} : Array ({typ}) := "+" ++ ".join(chunks)+"\n")
    return "\n".join(lines)


def main():
    need(not sys.flags.optimize, "Python optimization disables upstream certificate assertions")
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("publication", type=Path)
    ap.add_argument("--output", type=Path, required=True)
    ap.add_argument("--audit-lower", action="store_true",
                    help="rebuild and run the pinned core-only exact Rust auditor (requires Cargo)")
    args = ap.parse_args()
    root = args.publication.resolve()
    need(subprocess.check_output(["git", "-C", str(root), "rev-parse", "HEAD"], text=True).strip() == REV,
         "publication revision mismatch")
    compressed = b"".join((root/LOWER/f"certificate.json.gz.part-{i:02}").read_bytes() for i in range(2))
    need(digest(compressed) == GZIP, "lower gzip hash mismatch")
    raw = gzip.decompress(compressed)
    need(digest(raw) == RAW, "lower raw hash mismatch")
    lower_audit = None
    if args.audit_lower:
        subprocess.run(["git", "-C", str(root), "diff", "--quiet", "HEAD", "--",
                        "sdp/Cargo.toml", "sdp/Cargo.lock", "sdp/crates"], check=True)
        with tempfile.TemporaryDirectory(prefix="cz-lower-") as directory:
            source = Path(directory)/"certificate.json"
            source.write_bytes(raw)
            lower_audit = json.loads(subprocess.check_output(
                ["cargo", "run", "--locked", "--release", "-p", "minexposure-core",
                 "--example", "audit_terminal_bootstrap_source", "--", str(source)],
                cwd=root/"sdp", text=True))
        need(lower_audit["coefficient_count"] == 18739
             and lower_audit["nonzero_exact_residual_count"] == 0
             and lower_audit["all_gram_matrices_exactly_positive_semidefinite"] is True
             and lower_audit["certified_bound"] == "5861/2000", "lower exact audit")
    cert = json.loads(raw)
    del raw, compressed
    need(cert["order"] == 7 and cert["knots"] == ["0", "1/36", "1/3", "2/3", "35/36", "1"], "order/grid")
    need(cert["exposure_upper"] == "2935887/1000000" and cert["bound_target"] == "5861/2000", "endpoints")
    need(cert["schema"] == "jan22-cost-lifted-split-exact-dual-q-v1", "schema")
    need(cert["equality_order"] == "cell_major_liouville_v1", "coefficient order")
    need(cert["gram_order"] == "occupation_by_cell_then_interface_by_knot_then_terminal_pair_by_cell_v1", "Gram order")
    tests = basis(4, 13, True)[(0, 0)]
    need(len(tests) == 776, "potential basis count")
    coeffs = cert["liouville_multipliers_by_cell"]
    need(len(coeffs) == 5 and all(len(v) == 776 for v in coeffs), "potential shape")
    offset = scalar(cert["normalization"])
    parsed = [[scalar(s) for s in row] for row in coeffs]
    initial = [i for i, (xi, a, h) in enumerate(tests) if xi == 0 and not (a[1] or a[3] or h[1] or h[3])]
    objective = tuple(-offset[j]+sum(parsed[0][i][j] for i in initial) for j in (0, 1))
    need(objective == (F(5861, 2000), F(0)), "exact objective/sign mismatch")
    dims = {}
    for field, count, per_cell in [("occupation_grams_by_cell", 5, 736),
                                  ("interface_grams_by_knot", 4, 134), ("terminal_grams_by_cell", 5, 2)]:
        groups = cert[field]
        need(len(groups) == count and all(len(g) == per_cell for g in groups), field)
        for g in groups:
            need(all(all(len(r) == len(m) for r in m) for m in g), "non-square Gram")
        dims[field] = [[len(m) for m in g] for g in groups]
    need(all(d == [8, 7] for d in dims["terminal_grams_by_cell"]), "terminal sides")
    # Export the full ordered main/support bases and sparse face transforms.
    layout = []
    for family, degree in [("moment", 7), ("interval", 6)]:
        for q, b in basis(5, degree).items():
            face = face_columns(b) if family == "moment" else [[(i, 1)] for i in range(len(b))]
            if face:
                layout.append(dict(family=family, charge=q, basis=b, columns=face,
                                   rephase_i=[bool((a[0]+h[0]) % 2) for _, a, h in b]))
    regular_count = len(layout)
    seen = set()
    for charge_key, b in basis(5, 6).items():
        for m in b:
            signature = diagonal_signature(m)
            if signature not in seen:
                seen.add(signature)
                layout.append(dict(family="interval_diagonal", charge=charge_key,
                                   basis=[m], columns=[[(0, 1)]],
                                   rephase_i=[bool((m[1][0]+m[2][0]) % 2)]))
    regular_sides = [len(b["columns"]) for b in layout]
    for sides in dims["occupation_grams_by_cell"]:
        need(sides == regular_sides, "occupation basis/face/diagonal ordering")
    interfaces = [dict(charge=q, basis=[m for m in b if m[0] == 0]) for q, b in basis(4, 7).items()]
    interfaces = [b for b in interfaces if b["basis"]]
    need(all(s == [len(b["basis"]) for b in interfaces] for s in dims["interface_grams_by_knot"]), "interface basis ordering")
    bridge_layout = dict(
        occupation=[lean_gram_layout(b, "moment" if b["family"] == "moment" else "interval")
                    for b in layout],
        interface=[lean_gram_layout(b, "interface") for b in interfaces],
        matrix_sha256={field: [[digest(packed(matrix)) for matrix in cell] for cell in cert[field]]
                       for field in dims},
        matrix_encoding="exact Q(sqrt(2)) strings; row-major, full symmetric matrices",
        coordinate_order=["xi", "u", "conj(u)", "g1", "conj(g1)", "r1", "conj(r1)",
                          "g2", "conj(g2)", "r2", "conj(r2)"],
        matrix_entries=sum(sum(side*side for side in cell) for cells in dims.values() for cell in cells),
        lean_matrix_values_embedded=False)
    verifier_path = root/UPPER/"jan22_cz_exposure_interval_upper.py"
    witness_path = root/UPPER/"reference_data/jan22_cz_exposure_candidate_12672.json"
    need(digest(verifier_path.read_bytes()) == VERIFIER, "upper verifier hash")
    need(digest(witness_path.read_bytes()) == WITNESS, "upper witness hash")
    import flint
    need(flint.__version__ == "0.9.0", "python-flint version")
    spec = importlib.util.spec_from_file_location("pinned_upper", verifier_path)
    v = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(v)
    witness = json.loads(witness_path.read_text(), parse_float=str)
    phases = witness["phases"]
    need(len(phases) == 12672 and v.VARIABLE_PHASE_INDICES == (731, 6676, 8661, 11922), "upper parameter order")
    # Replay the authoritative assertions before exporting anything.
    v.main()
    boxes = [v.arb(f"{c} +/- {v.BOX_RADIUS}") for c in v.CENTERS]
    terminal, exposure, branch = v.evaluate([v.variable(b, i) for i, b in enumerate(boxes)], phases)
    bounds = lambda x: (F(str(x.lower().fmpq())), F(str(x.upper().fmpq())))
    jacobian = [[bounds(t.derivatives[j]) for j in range(5)] for t in terminal]
    centers, radius = list(map(F, v.CENTERS)), F(v.BOX_RADIUS)
    inv = [[F(s) for s in row] for row in v.APPROXIMATE_INVERSE]
    need(centers[0] > radius > 0, "positive duration")
    # Recheck inclusion for the EXACT rational box, not the rounded Arb box.
    arbq = lambda q: v.arb(flint.fmpq(q.numerator, q.denominator))
    jboxes = [[v.arb(arbq((lo+hi)/2), arbq((hi-lo)/2)) for lo, hi in row] for row in jacobian]
    eye = [[v.arb(int(i == j)) for j in range(5)] for i in range(5)]
    defect = [[eye[i][j]-sum((arbq(inv[i][k])*jboxes[k][j] for k in range(5)), v.arb(0)) for j in range(5)] for i in range(5)]
    point, _, _ = v.evaluate([v.variable(arbq(c), i) for i, c in enumerate(centers)], phases)
    correction = [sum((arbq(inv[i][j])*point[j].value for j in range(5)), v.arb(0)) for i in range(5)]
    row_bounds = [sum((bounds(x.abs_upper())[1] for x in row), F(0)) for row in defect]
    q = max(row_bounds)
    need(q < 1, "contraction")
    need(all(bounds(c.abs_upper())[1]+r*radius < radius for c, r in zip(correction, row_bounds)), "exact-box inclusion")
    need(bounds(branch.value)[1] < 0 and bounds(exposure.value)[1] < F(v.CERTIFIED_UPPER_BOUND), "branch/exposure")
    entries = []
    for xi, a, h in tests:
        entries.append(f"({xi}, #[{', '.join(map(str,a))}], #[{', '.join(map(str,h))}])")
    text = "-- Generated by bind_certificates.py; do not edit.\nimport Mathlib.Data.Rat.Defs\nnamespace LowerBoundCZ.CertificateData\n\n"
    text += array("basis", "Nat × Array Nat × Array Nat", entries)
    text += array("multipliers", "ℚ × ℚ", [f"({qlean(a)}, {qlean(b)})" for row in parsed for a, b in row])
    text += f"def offset : ℚ × ℚ := ({qlean(offset[0])}, {qlean(offset[1])})\n"
    for name, data in [("phases", list(map(F, phases))), ("center", centers),
                       ("inverse", [x for row in inv for x in row]),
                       ("jacobianLower", [x[0] for row in jacobian for x in row]),
                       ("jacobianUpper", [x[1] for row in jacobian for x in row])]:
        text += array(name, "ℚ", list(map(qlean, data)))
    text += f"def radius : ℚ := {qlean(radius)}\ndef contraction : ℚ := {qlean(q)}\nend LowerBoundCZ.CertificateData\n"
    report = dict(revision=REV, lower_raw_sha256=RAW, lower_gzip_sha256=GZIP,
                  upper_verifier_sha256=VERIFIER, upper_witness_sha256=WITNESS,
                  grid=cert["knots"], formulation_hash=cert["formulation_hash"],
                  split_grid_hash=cert["split_grid_hash"], objective=list(map(str, objective)),
                  gram_dimensions=dims, occupation_layout=layout, interface_layout=interfaces,
                  lean_gram_bridge=bridge_layout,
                  diagonal_interval_blocks_per_cell=736-regular_count,
                  potential_basis_sha256=digest(packed(tests)), generated_lean_sha256=digest(text.encode()),
                  upper_exact_box_inclusion=True, upper_contraction=str(q),
                  upper_branch=list(map(str, bounds(branch.value))), upper_exposure=list(map(str, bounds(exposure.value))),
                  lower_psd_replayed=lower_audit is not None, lower_audit=lower_audit)
    args.output.mkdir(parents=True, exist_ok=True)
    (args.output/"CertificateData.lean").write_text(text)
    (args.output/"bindings.json").write_text(json.dumps(report, indent=2)+"\n")
    print("Certificate bindings exported; lower PSD replay: " +
          ("PASS" if lower_audit is not None else "NOT RUN"))


if __name__ == "__main__":
    main()
