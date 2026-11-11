import LowerBoundCZ.PinnedAllocations

open LowerBoundCZ LowerBoundCZ.Certification
open PinnedAllocation

-- Kernel proofs are audited separately from the executable data comparison.
run_cmd do
  for name in [``PinnedAllocation.widths, ``PinnedAllocation.checks,
      ``PinnedAllocation.trajectory_slack] do
    for ax in ← Lean.collectAxioms name do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"

example : lower 0 = ![3/4,0,0] := by ext i; fin_cases i <;> norm_num [lower]
example : upper 1023 = ![1,1,1] := by ext i; fin_cases i <;> norm_num [upper]

private def qstr (q : ℚ) : String := s!"{q.num}/{q.den}"
private def join (xs : Array String) : String := String.intercalate " " xs.toList
private def require (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

private def index (a : Fin 15) (b c : Fin 8) :
    (i : Fin 3) → Fin (Slack.allocationDegree i + 1) :=
  fun | ⟨0, _⟩ => a | ⟨1, _⟩ => b | ⟨2, _⟩ => c

/-- Emit the values Lean actually decoded for an independent, entry-by-entry
comparison with the pinned source archive. This executable is not a proof of
PSD or of the final physical bound, and does not introduce any axioms. -/
def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "usage: lake env lean --run AllocationDataAudit.lean OUTPUT")
  require (AllocationCodec.rational "-17/32" == (-17/32 : ℚ)) "signed rational decoder"
  require (AllocationCodec.scalars "-3/7,5/9 0 2" ==
    #[(-3/7,5/9), (0,0), (2,0)]) "quadratic scalar decoder"
  require (AllocationData.sources.size == 736) "source count"
  require (AllocationData.projections.size == 1078) "projection count"
  require (AllocationData.regionGroups.size == 1024) "region count"
  require (AllocationData.profiles.size == 16) "profile count"
  require (AllocationData.groups.size == 1180) "allocation group count"
  let projections := AllocationData.projections.map AllocationCodec.EncodedProjection.decode
  let groups := AllocationData.groups.map AllocationCodec.allocation
  let profiles := AllocationData.profiles.map AllocationCodec.rationals
  let out ← IO.FS.Handle.mk path .write
  for bb in List.finRange 736 do
    let b := bb.val
    let s := AllocationData.sources[b]!.decode
    require (s.rows.size == s.size && s.upper.size == s.size*(s.size+1)/2 && s.localizer < 4)
      s!"source shape {b}"
    out.putStrLn s!"S {b} {s.size} {s.localizer}"
    out.putStrLn s!"B {b} {join (s.basis.map toString)}"
    for i in [:s.rows.size] do
      for (j, _) in s.rows[i]! do
        require (j < s.basis.size) s!"source basis index {b}:{i}:{j}"
      out.putStrLn s!"C {b} {i} {join (s.rows[i]!.map fun (j,c) => s!"{j}:{c}")}"
    let full := (List.range s.size).flatMap fun i => (List.range s.size).map fun j =>
      let (a,c) := s.upper[matrixIndex s.size i j]?.getD (0,0)
      s!"{qstr a},{qstr c}"
    out.putStrLn s!"Q {b} {String.intercalate " " full}"
  for i in [:1078] do
    let p := projections[i]!
    require (p.block < 736 && p.rows.size > 0 && p.matrix.size == p.rows.size^2 &&
      p.population.size == 4 && p.polynomial.size ≤ 15) s!"projection shape {i}"
    require (p.rows.toList.eraseDups.length == p.rows.size) s!"duplicate selected row {i}"
    for row in p.rows do
      require (row < AllocationData.sources[p.block]!.size) s!"selected row {i}:{row}"
    out.putStrLn s!"P {i} {p.originalID} {p.block}"
    out.putStrLn s!"R {i} {join (p.rows.map toString)}"
    out.putStrLn s!"M {i} {join (p.matrix.map qstr)}"
    out.putStrLn s!"E {i} {join (p.population.map toString)}"
    out.putStrLn s!"F {i} {join (p.polynomial.map qstr)}"
  for g in [:groups.size] do
    let entries := groups[g]!
    let mut total : ℚ := 0
    for (i, w) in entries do
      require (i < 1078 && w ≥ 0) s!"allocation entry {g}:{i}"
      total := total+w
    require (total ≤ 1) s!"shared budget {g}"
    out.putStrLn s!"G {g} {join (entries.map fun (i,w) => s!"{i}:{qstr w}")}"
  for r in [:1024] do
    let row := AllocationCodec.naturals AllocationData.regionGroups[r]!
    require (row.size == 736) s!"region block count {r}"
    for b in [:736] do
      require (row[b]! < groups.size) s!"region group {r}:{b}"
      for (i, _) in groups[row[b]!]! do
        require (projections[i]!.block == b) s!"wrong original block {r}:{b}:{i}"
    out.putStrLn s!"A {r} {join (row.map toString)}"
  for i in [:16] do
    require (profiles[i]!.size == 15) s!"profile shape {i}"
    out.putStrLn s!"D {i} {join (profiles[i]!.map qstr)}"
  -- Asymmetric indices and both Bernstein endpoint coefficients detect
  -- transposed tensor axes, sector weights, and incorrect affine offsets.
  for r in ([0, 31, 1000] : List (Fin 1024)) do
    for (a,b,c) in ([(0,0,7), (5,2,6), (14,7,0)] : List (Fin 15 × Fin 8 × Fin 8)) do
      out.putStrLn s!"T {r.val} {a.val} {b.val} {c.val} {qstr (residual r (index a b c))}"
  IO.println "PASS: fixed data shapes, projection ownership, shared budgets; decoded values exported"
