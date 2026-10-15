# Split O7 certification above 2.915

This directory records the first certified order-7 result in the three-cell
cumulative-cost split lane, continuing
`verification_results/split-o6-above-291/`. The final exact closure, native
audit, and independent audit ran from commit
`59fd23f67d10abc370f5413c270a9088718aaaff`; the knots are
`0,1/32,31/32,1`, and the exact payload schema remains
`jan22-cost-lifted-split-exact-dual-q-v1`.

## Result

The target `117/40` passed both the exactifier's native audit and a separately
executed 8-job `audit-exact-split` process:

```text
C* >= 117/40 = 2.925.
```

Together with the imported Arb/Krawczyk upper witness
(`C* < 2.935875225844105`, refined 12,672-segment pulse), the rigorous bracket
is now `2.925 <= C* < 2.935875225844105`.

The seed is a fresh fixed-target interior solve against an order-7 reference
regenerated with `--dump-solution` (objective `2.930279100780325`; the
committed O7 reference lacks dumped duals). The active-set classification used
entry-norm threshold `1e-8` and reference minimum-eigenvalue threshold `1e-6`,
giving 928 active and 1,554 inactive Grams. Exactification used the established
PSD-constrained native-bar recipe with `--cone-facial-zero-threshold 1e-7`;
four cone passes newly zeroed 1,103, 125, 33, then 0 facial rows.

The stronger `366/125` (2.928) seed had positive margin
`1.4831230797767266e-4`, but the `1e-7` cone face did not stabilize in eight
passes. The sanctioned `1e-6` retry stabilized after seven passes but failed
the unchanged reconstructed-cone gate at `-7.991929876368819e-7`. A higher
`2929/1000` seed had margin `6.116271464444463e-4`; both the `1e-7` and `1e-6`
faces remained unstable after eight passes. The 2.93 seed margin was negative
(`-7.85767333036208e-6`), so it was screened out. None of these failed or
screened targets is a bound.

## Validation table

Tiny negative reconstructed floating eigenvalues are diagnostics, not the
rigor gate. Every Gram is accepted either as an exact zero block, by the
rigorous exact residual certificate (exact dyadic factor, exact integer
residual, and Gershgorin), or by exact LDL fallback.

| order | target | facial threshold | seed margin | exactification outcome | native audit | independent audit | min reconstructed eig / min certified eigenvalue lower bound | wall time | peak RSS |
|---:|---:|---:|---:|---|---|---|---|---|---|
| 7 | `117/40` (2.925) | `1e-7` | `2.9031613634593893e-3` | PASS; 11,139 identities closed, 0 nonzero residuals | PASS; 1,976 strictly PD, 289 zero, 2,187 residual-certified, 6 exact-LDL | PASS; exit 0, 8 jobs | `-3.463025804339165e-15` / `23636797414344388196264014285892770203663966697/18731823325732748675289309114169343981754777600000000000` | seed 7:00.33; cone stages 27:52.86; final exact-closure/native-audit resume 3:07.30; independent 1:34.96 | seed 10,740,244 KiB; original retained-task exactifier 29,085,432 KiB observed; fresh final resume 1,341,088 KiB; independent 746,732 KiB |

Certificate provenance records 186.164808037 s for the successful final resume
pipeline: 113.638700182 s total exact repair (including 50.939236416 s
pre-cone exact repair retained from the checkpoint), 6.925289975 s for the
reconstructed-eigenvalue screen, and 55.208327676 s for the native exact audit.
The separately timed independent audit took 94.96 s. The original retained-task
process reached the complete cone/audit checkpoint but was stopped after
2:16:51 because the old rational fallback had not finished; the merged
fraction-free fallback completed the fresh native resume in 3:07.30 outer wall.

## Retained evidence

- `split-o7-target-2925-seed.json`: fresh fixed-target floating seed.
- `split-o7-target-2925-exact-certificate.json`: exact split-v1 payload with
  `exactification_status = passed_native_exact_audit`.
- `split-o7-target-2925-facezero1e-7-native-audit.json`: native exact-audit
  report emitted by the exactifier.
- `split-o7-target-2925-independent-audit.json`: report from the separately
  executed optimizer-independent audit process.
- `*.resources.txt`: GNU `time -v` command, wall-time, peak-RSS, and exit
  records for the retained seed, final exactification resume, and independent
  audit.
- `results.json`: compact machine-readable campaign summary.
- `SHA256SUMS`: hashes for every retained file except the manifest itself.

The exact certificate is 279,977,609 bytes, above this campaign's 95 MB Git
retention ceiling. It is present and byte-verified in the campaign worktree but
is intentionally not committed. Its SHA-256 is
`ef1f4f5a193b64100edabddd943386d070af9403c0bdbead09babf4a1c12b9ef`;
`results.json` and `SHA256SUMS` pin the same size and hash. The 87,982,464-byte
seed remains below the ceiling and is committed. This certificate is not
claimed to be byte-identical to the independently generated order-7 artifact
from the exactifier-scaling campaign.

## Independent audit command

```bash
target/release/minexposure audit-exact-split \
  verification_results/split-o7-above-2915/split-o7-target-2925-exact-certificate.json \
  --audit-jobs 8
```

This independent command exited zero in 1:34.96. Both reports certify exact
bound `117/40`, 11,139 zero coefficient residuals, 1,976 strictly
positive-definite Grams, 289 exact-zero Grams, 2,187 residual-certified Grams,
and 6 exact-LDL fallbacks. No schema, auditor acceptance gate, golden file,
residual policy, or upper-bound artifact was modified. All work ran on the Amp
orb; cloud spend was 0 CNY.
