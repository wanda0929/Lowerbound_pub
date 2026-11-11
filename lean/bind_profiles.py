"""Bind final occupation profiles without claiming their physical applicability.

Exact rational conversion and replacement accounting only. This does not replay
Gram checks, prove mandatory prefixes, or turn a checker PASS into a theorem.
"""
import argparse
from fractions import Fraction as F
import gzip
import hashlib
import json
from math import comb
from pathlib import Path

from bind_allocations import ALLOCATION, load_checker
from bind_slack import HASHES, need


def power_coefficients(beta):
    n = len(beta) - 1
    return [sum((beta[k] * comb(n, k) * comb(n-k, m-k) * (-1)**(m-k)
                 for k in range(m+1)), F(0)) for m in range(n+1)]


def collect(root):
    checker = load_checker(root)
    v, base, occ, _, _ = checker.inputs(root / "sdp")
    directory = root / "sdp/verification_results"
    hashes = {}

    def read(name, expected=None):
        raw = (directory / name).read_bytes()
        if name.endswith(".gz"):
            raw = gzip.decompress(raw)
        digest = hashlib.sha256(raw).hexdigest()
        if expected is not None:
            need(digest == expected, "hash: " + name)
        hashes[name] = digest
        return json.loads(raw)

    regional = read("adaptive-slack/certified/certificate.json.gz",
                    occ["regional_certificate_sha256"])
    tail = read("adaptive-slack/certified/tail-certificate.json",
                occ["previous_certificate_sha256"])
    alloc = read("slack-campaign-2935/allocation.json.gz", ALLOCATION)
    dark = read("slack-campaign-2935/dark/profiles.json", HASHES["dark/profiles.json"])
    hashes["population-refinement/certified/population-certificate.json.gz"] = checker.BASE
    hashes["reachability-slack/certified/occupation-certificate.json"] = checker.OCC
    replacements = {e["interval_index"]: e for e in alloc["replacements"]}
    darks = {e["interval_index"]: e for e in dark["profiles"]}
    need(len(replacements) == len(alloc["replacements"]) == 16, "allocation uniqueness")
    need(set(replacements) == set(range(176, 192)), "allocation ownership")
    need(len(darks) == len(dark["profiles"]) == 32, "dark uniqueness")
    need(not set(replacements) & set(darks), "overlapping replacements")
    need(len(base["integration_bins"]) == len(occ["intervals"]) ==
         len(regional["intervals"]) == 320, "prefix coverage")
    profiles = []
    old_total = F(0)
    gains = {"allocation": F(0), "dark": F(0)}

    def append(cell, a, b, beta, owner, grid, source_index):
        need(len(beta) == 15 and 0 <= a < b <= 1, "profile shape/local interval")
        width = v.U * (v.KNOTS[cell+1] - v.KNOTS[cell])
        left, right = v.U*v.KNOTS[cell] + width*a, v.U*v.KNOTS[cell] + width*b
        power = power_coefficients(beta)
        mean = sum(beta, F(0)) / 15
        need(sum((x/F(k+1) for k, x in enumerate(power)), F(0)) == mean,
             "primitive/mean identity")
        # Check conversion at nontrivial asymmetric points, independently of
        # the signed-power coefficient loop above.
        for t in (F(0), F(2, 7), F(5, 8), F(1)):
            need(sum(x*t**k for k, x in enumerate(power)) ==
                 sum(x*comb(14, k)*t**k*(1-t)**(14-k) for k, x in enumerate(beta)),
                 "Bernstein/power evaluation")
        profiles.append(dict(cell=cell, local_left=str(a), local_right=str(b),
                             left=str(left), right=str(right), owner=owner, grid=grid,
                             source_index=source_index, bernstein=list(map(str, beta)),
                             power=list(map(str, power)), credit=str((right-left)*mean)))

    for i, (item, old, reg) in enumerate(zip(base["integration_bins"], occ["intervals"],
                                           regional["intervals"])):
        need(old["interval_index"] == reg["interval_index"] == i, "profile ordering")
        cell, a, b = item["cell"], F(item["a"]), F(item["b"])
        need(cell == i//64, "cell ownership")
        beta = list(map(F, old["bernstein"]))
        width = v.U*(v.KNOTS[cell+1]-v.KNOTS[cell])*(b-a)
        old_total += width*sum(beta, F(0))/15
        owner, grid = old["mode"], occ["grid"] if old["mode"] == "reachable" else regional["grid"]
        if i in replacements:
            new = list(map(F, replacements[i]["bernstein"]))
            owner, grid = "allocation", alloc["grid"]
        elif i in darks:
            e = darks[i]
            need(list(map(F, e["old_profile"])) == beta, "dark baseline")
            new = list(map(F, e["new_profile"]))
            owner, grid = "dark", e["grid"]
        else:
            new = beta
        if owner in gains:
            gain = width*(sum(new, F(0))-sum(beta, F(0)))/15
            gains[owner] += gain
            if owner == "dark":
                need(gain == F(darks[i]["integrated_gain"]), "dark interval gain")
        append(cell, a, b, new, owner, grid, i)
    need(old_total == F(occ["new_prefix_slack"]), "reachability prefix sum")
    need(gains["allocation"] == F(alloc["additional_occupation_slack"]), "allocation gain")
    need(gains["dark"] == F(dark["exact_integrated_gain"]), "dark gain")
    need(F(profiles[-1]["right"]) == F(tail["prefix_from"]) == F(base["previous_bound"]),
         "prefix/tail join")
    append(4, F(tail["local_from"]), F(tail["local_to"]),
           list(map(F, tail["tail_bernstein"])), "tail", tail["grid"], 319)
    need(F(profiles[-1]["right"]) == F(tail["prefix_to"]), "tail endpoint")
    need(F(profiles[-1]["credit"]) == F(tail["additional_occupation_slack"]), "tail gain")
    need(F(profiles[0]["left"]) == 0 and all(
        p["right"] == q["left"] for p, q in zip(profiles, profiles[1:])), "contiguous prefix")
    total = sum((F(p["credit"]) for p in profiles), F(0))
    need(total == old_total + sum(gains.values()) + F(tail["additional_occupation_slack"]),
         "replacement accounting")
    return dict(hashes=hashes, profiles=profiles, total_credit=str(total),
                prefix_end=tail["prefix_from"], tail_end=tail["prefix_to"],
                reachability_credit=str(old_total), gains={k: str(x) for k, x in gains.items()})


def export(packet, path):
    lines = ["-- Generated by bind_profiles.py; do not edit.",
             "import LowerBoundCZ.AllocationCodec", "namespace LowerBoundCZ.ProfileData",
             "structure EncodedProfile where", "  cell : Nat", "  left : String",
             "  right : String", "  power : String", "  deriving Inhabited",
             "def profiles : Array EncodedProfile := #["]
    for p in packet["profiles"]:
        lines.append('  ⟨%d, "%s", "%s", "%s"⟩,' %
                     (p["cell"], p["left"], p["right"], " ".join(p["power"])))
    lines += ["]", "end LowerBoundCZ.ProfileData", ""]
    path.write_text("\n".join(lines))
    path.with_suffix(".json").write_text(json.dumps(packet, indent=2) + "\n")


def compare(packet, path):
    rows = path.read_text().splitlines()
    need(len(rows) == 321, "decoded profile count")
    for i, (row, p) in enumerate(zip(rows, packet["profiles"])):
        fields = row.split("\t")
        need(len(fields) == 20 and list(map(int, fields[:2])) == [i, p["cell"]], "decoded ID/cell")
        need(list(map(F, fields[2:])) == list(map(F, [p["left"], p["right"],
             *p["power"], p["credit"]])), "decoded profile: " + str(i))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("checkout", type=Path)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--lean-dump", type=Path)
    args = parser.parse_args()
    packet = collect(args.checkout)
    if args.output:
        export(packet, args.output)
    if args.lean_dump:
        compare(packet, args.lean_dump)
    print("PASS: 321 profiles; 16 allocation and 32 disjoint dark replacements; exact total/mean identities.")
    print("Mandatory prefix and local Gram/profile validity are separate proof obligations.")


if __name__ == "__main__":
    main()
