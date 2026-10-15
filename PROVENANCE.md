# Source provenance

Packaging date: 2026-10-15. Source files are copied without scientific rewrites.
The root manifest records their packaged bytes. No source repository history,
agent instructions, credentials, virtual environments or compiled binaries are
part of the publication snapshot.

## Manuscript, illustrative pulse, and existing proof packages

- Repository: https://github.com/wanda0929/LowerBoundCZ
- Revision: `fb03dd152c69bdf112262945fb176b93d0e20f6b`
- Retained paths: `main.tex`, `main.pdf`; the three included figures;
  selected `proof/data` and the transitive script dependencies; `certificates/`.
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

The Rust workspace declares MIT. This does not automatically license all
manuscript text, proof data, figures or imported Python files. No owner-selected
publication-wide license was supplied. No license has been invented here.
