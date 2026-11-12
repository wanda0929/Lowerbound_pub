# Source provenance

## Lean proof and acceptance snapshot added 2026-11-11

- Source repository: https://github.com/wanda0929/LowerBoundCZ
- Source commit: `7f9d30aa63e55d3b68f65a6e67b5ef64e2b0e6fb`.
- All 469 tracked files under `lean/` are copied byte for byte, including
  dependency locks, generated data, exact-input bindings, 63 additional Lean
  audit logs, numerical replay records and the snapshot hash manifest.
- Accepted conclusions and retained hypotheses: `LEAN_VERIFICATION.md`.
- The numerical inputs remain pinned to this repository's existing commit
  `139dfc0aeb39fbc09d9352a3cbfcd603cb6612e2`; reproduction uses a detached
  worktree of that revision, not a weakened revision check.
- `lean/UnifiedAcceptance.md` is the historical pre-commit acceptance report;
  its statements about then-uncommitted delivery and development manuscript
  hashes describe that run, not the current Git publication status.
- No private thread or development-repository access is needed to run the
  published verification. Original provenance identifiers are retained.
- The root manuscript and all existing numerical inputs remain unchanged.
  `validation/lean-publication-check.json` records the transfer checks.

## Original numerical/manuscript packaging

Packaging date: 2026-10-15. Source files are copied without scientific rewrites.
The root manifest records their packaged bytes. No source repository history,
agent instructions, credentials, virtual environments or compiled binaries are
part of the publication snapshot.

## Manuscript, illustrative pulse, and existing proof packages

- Repository: https://github.com/wanda0929/LowerBoundCZ
- Revision: `fb03dd152c69bdf112262945fb176b93d0e20f6b`
- Retained paths: the three included figures;
  selected `proof/data` and the transitive script dependencies; `certificates/`.
- The originally packaged `main.tex` and `main.pdf` have been removed.
  Read the paper at https://arxiv.org/abs/2611.07388; historical manuscript
  hashes in acceptance records are preserved.
- Original package manifests and provenance remain unchanged.

## Final lower-bound extension and historical auditors

- Repository: https://ampcode.com/@wz-s-space/min-exposure-sdp
- Revision: `b85a98afb440629162db28381fb3f32d079f62d4`
- Final extension: `sdp/verification_results/slack-campaign-2935/`.
- Exact O7 source chunks and their retained audit evidence:
  `sdp/verification_results/five-cell-ceiling/certification/o7-shoulder-36-t29305-axis/`.
- Raw source certificate SHA-256:
  `1f715c99684ed7dbbf1036f168eadac54043e0a235e0f9f273451f875db4bf52`.
- Unsplit exact O8 certificate and audit records are also from this revision.
- `historical-source/campaign-auditor-b85a98a.tar.gz` preserves its workspace.
- `historical-source/order6-auditor-45d45bf.tar.gz` preserves the auditor
  workspace at manuscript-pinned revision
  `45d45bf11abbacd0be693bf0068f78de77d91997`.

## Complete predecessor chain and optimizer-free Rust source audit

- Repository: https://github.com/exAClior/min-exposure-sdp
- Revision: `66b7b154d632fe389daee235c75d45586a26b355`
- `sdp/Cargo.toml`, `Cargo.lock`, `rust-toolchain.toml`, and `crates/`.
- Six retained sibling directories: `population-refinement`,
  `interface-population`, `cost-profile`, `joint-slack`, `adaptive-slack`,
  `reachability-slack` inside `sdp/verification_results/`.
- These reconstruct the scientific contents of the predecessor attachment
  from committed source, not an expired Actions download.
- The final extension's pinned input hashes and the full predecessor replay
  establish compatibility between these two source snapshots.
- The fresh core-only native audit of the original certificate matches
  `population-refinement/certified/source-audit.json` byte for byte.

## Numerical SDP outputs and fiber integral

- Repository: https://github.com/wanda0929/Finite_blockade_pulse
- Revision: `677eba8905756a4dd4d1f0c760b0375ebec67161`
- Retained under `finite-source/`: stationary-torus solver, its complex-moment
  dependency, O6–O11 outputs/logs/environment records, fiber-bound script and
  its derivation.
- The strict upper witness has its separate original provenance under
  `certificates/cz-upper-bound-2.935875225844105-v1/PROVENANCE.md`.

## Missing historical comparison certificate

The three-cell O7 value 117/40 has two recorded exact artifacts, neither
committed in the inspected source tree. Retained reports are under
`sdp/verification_results/split-o7-above-2915/`.

One historical artifact has 279,202,057 bytes and SHA-256
`d695171a6ae420bd35ab23ba2581309657a21525c30b5c08c28dba3a164c155a`.
The original thread records a retained copy at
`.amp/transfer/o7-final-cert2.json`, with three binary chunks under
`.amp/transfer/o7-final-cert2.parts/`:
https://ampcode.com/threads/T-01a06077-742f-716d-81fe-b14ac506e626
Its reported implementation revision is
`5be7360bcfef034f9239110fba336d5f78a28a2d`.
Transfer was blocked because that thread is archived. Recovery requires the
owner to restore it; live file persistence is not yet established.

The other missing artifact has 279,977,609 bytes and SHA-256
`ef1f4f5a193b64100edabddd943386d070af9403c0bdbead09babf4a1c12b9ef`.
Its upstream README explicitly says the payload was not committed.

## Licensing

The owner approved MIT for collaborative software and CC BY 4.0 for scientific
data, with attribution to Han WANG, exAClior, and contributors. `LICENSING.md`
defines the scope; `LICENSE` and `LICENSE-DATA` contain the license texts.
Manuscript and figure reuse rights are not newly granted. Historical notices
inside retained packages are preserved as provenance, not rewritten to erase
their original licensing status. The repository was private at the original
packaging date; it is public as checked on 2026-11-11.
