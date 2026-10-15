# Reachability lower bound: 2.931287603326

The new all-duration ideal-blockade stationary-torus certificate gives

```
1465643801663/500000000000 = 2.931287603326 <= C* < 2.935875225844105.
```

This computation started from the newer repository endpoint 2.931286076089,
not the older conversational endpoint 2.931272845583. The increase made here
is exactly 0.000001527237. It is a small, certified improvement, not a proof of
2.932 or 2.935. The upper witness is unchanged.

## What changed

`PROOF.md` derives a duration-free, forward-and-backward population barrier
from the exact sector equations. It is built from a finite positive series,
and its derivative bound is certified by an exact polynomial identity.
Unreachable population rectangles can then be excluded from slack minimization
for the hypothetical low-exposure trajectories being ruled out. All remaining
rectangles receive complete Bernstein coefficient checks.

`CROSSINGS.md` applies the same barrier to the four mandatory cost crossings,
combines the disjoint occupation/interface gains, and gives the final proof.
The two middle crossing gains come from finer subdivision rather than exclusion.

No new SDP or optimizer is used in these new stages. All acceptance arithmetic
is rational. The old source and projected Gram inequalities remain unchanged;
their exact/rigorous original checks are explicit dependencies, not replaced
by hashes or a solver status.

## Reproduction

From this repository's research branch:

```bash
python3 -m pip install python-flint==0.8.0
bash verification_results/reachability-slack/reproduce.sh "$PWD"
```

This replays the full predecessor extension chain, the new occupation checker,
and the crossing/combined-endpoint checker. To also rerun the original large
native global audit:

```bash
bash verification_results/reachability-slack/reproduce.sh "$PWD" --full-source-audit
```

The downloadable supplemental proof bundle preserves the sibling directory
layout. From its root use `bash reproduce.sh /path/to/min-exposure-sdp`.
The repository path supplies the original large certificate chunks. The
optional original native audit additionally requires the Rust toolchain and
the audit example on the research branch.

The original global source audit is inherited in this round. All predecessor
extensions were rerun successfully in workflow 34024241552. New occupation
acceptance passed in 34024199691 and again in 34024435352; the latter also
accepted the stronger crossing and final endpoint certificates.

## Files

- `certified/occupation-certificate.json`: the first new endpoint, 2.931287271171.
- `certified/occupation-independent.json`: exact independently reconstructed report.
- `certified/certificate.json`: the final crossing-composed endpoint, 2.931287603326.
- `certified/independent.json`: final acceptance report and corruption tests.
- `produce.py`: factorwise producer, not used by the independent checker.
- `verify.py`: signed-power occupation reconstruction and exact reachability tests.
- `crossings.py`: factorwise crossing producer and separately reconstructed acceptance.
- `RESULT.json`: result arithmetic and provenance.
- `predecessor-replay.log`: completed predecessor extension replay.

The original source certificate SHA256 is
`1f715c99684ed7dbbf1036f168eadac54043e0a235e0f9f273451f875db4bf52`.
The final new certificate SHA256 is
`5f5edbf79a66e4ee060ae0d069eeaabe772e30f2a6df64f29d626d2c956c0784`.

Main, the original certificate payload, and its `bound_target` are unchanged.
