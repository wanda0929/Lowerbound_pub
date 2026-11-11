import LowerBoundCZ.OccupationCoverage

open LowerBoundCZ LowerBoundCZ.Certification OccupationCoverage OccupationLedger
set_option maxRecDepth 10000

run_cmd do
  for name in [``OccupationCoverage.grid_cover, ``excludedQ_iff, ``primitive_derivative,
      ``not_excluded, ``retained_cover, ``xi_mem, ``normalized_coordinate,
      ``selected_checks, ``rate_eq_derivative, ``pointwise_slack,
      ``OccupationCoverage.credited_telescope] do
    for ax in ← Lean.collectAxioms name do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"

-- Endpoint and interior-boundary coverage, including a zero exposure budget.
example : ∃ x : BoxIndex, x.val < 4 ∧ (1 : ℝ) ∈ Set.Icc ((x.val : ℝ)/4) ((x.val+1 : ℝ)/4) :=
  OccupationCoverage.grid_cover (by norm_num) (by norm_num) (by norm_num)
example : ∃ x : BoxIndex, x.val < 8 ∧ (3/8 : ℝ) ∈ Set.Icc ((x.val : ℝ)/8) ((x.val+1 : ℝ)/8) :=
  OccupationCoverage.grid_cover (by norm_num) (by norm_num) (by norm_num)
example : ∃ x : BoxIndex, x.val < 16 ∧ (0 : ℝ) ∈ Set.Icc ((x.val : ℝ)/16) ((x.val+1 : ℝ)/16) :=
  OccupationCoverage.grid_cover (by norm_num) (by norm_num) (by norm_num)
example : ¬ Slack.DarkBoxExcluded 0 0 0 0 0 := by norm_num [Slack.DarkBoxExcluded]
example : ¬ Slack.PopulationBoxExcluded 8 0 0 0 := by
  norm_num [Slack.PopulationBoxExcluded, Slack.barrierEnergy]

private def require (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

private def assignmentValid (i : Slot) (x y : BoxIndex) (c : Nat) : Bool := Id.run do
  if c == 0 || c > 10752 then return false
  let (j, lo, hi, d) := if c ≤ 1024 then
    let r : Fin 1024 := ⟨(c-1)%1024, Nat.mod_lt _ (by decide)⟩
    (2, PinnedAllocation.lower r, PinnedAllocation.upper r, PinnedAllocation.delta r)
  else
    let r : PinnedRegion.Region := ⟨(c-1025)%9728, Nat.mod_lt _ (by decide)⟩
    ((PinnedRegion.cell r).val, PinnedRegion.lower r, PinnedRegion.upper r, PinnedRegion.delta r)
  return j == cell i && (List.finRange 3).all (fun k =>
    lo k == ![loXi i, low i x, low i y] k && hi k == ![hiXi i, high i x, high i y] k) &&
    (List.finRange 15).all (fun k => d k == beta i k)

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "usage: CoverageDataAudit.lean OUTPUT")
  require (CoverageData.grids.size == 321 && CoverageData.kinds.size == 321 && CoverageData.boxes.size == 321) "table shapes"
  let out ← IO.FS.Handle.mk path .write
  let knots : Array ℚ := #[0, 1/36, 1/3, 2/3, 35/36, 1]
  let mut kept := 0
  let mut dropped := 0
  for i in List.finRange 321 do
    let n := grid i
    require (0 < n && n ≤ 16) s!"grid {i.val}"
    require ((AllocationCodec.naturals CoverageData.boxes[i.val]!).size == n*n) s!"box table {i.val}"
    require (0 ≤ loXi i && loXi i < hiXi i && hiXi i ≤ 1) s!"interval {i.val}"
    let j := cell i
    let u : ℚ := 2935887/1000000
    require (left i.val == u*(knots[j]!+(knots[j+1]!-knots[j]!)*loXi i) &&
      right i.val == u*(knots[j]!+(knots[j+1]!-knots[j]!)*hiXi i)) s!"endpoint identity {i.val}"
    require ((AllocationCodec.rationals (profile i).2.2.2).size == 15 &&
      (AllocationCodec.rationals (entry i.val).power).size == 15) s!"coefficient shapes {i.val}"
    for m in List.finRange 15 do
      let coefficient := (List.finRange 15).foldl (fun z k => z +
        if k.val ≤ m.val then beta i k * (Nat.choose 14 k.val : ℚ) *
          Nat.choose (14-k.val) (m.val-k.val) * (-1 : ℚ)^(m.val-k.val) else 0) 0
      require (power i.val m == coefficient) s!"polynomial coefficient identity {i.val}/{m.val}"
    for x in List.finRange 16 do
      for y in List.finRange 16 do
        if x.val < n && y.val < n then
          let c := code i x y
          let ex := excludedQ i x y
          require ((c == 0) == ex) s!"exclusion {i.val}/{x.val}/{y.val}"
          if c == 0 then dropped := dropped+1
          else
            require (assignmentValid i x y c) s!"assignment {i.val}/{x.val}/{y.val}"
            kept := kept+1
          out.putStrLn s!"{i.val} {n} {kind i} {x.val} {y.val} {c} {ex}"
  require (kept == 10752 && dropped == 12336) "classification counts"
  -- Wrong ownership must fail even though the replacement index is in range.
  require (!(assignmentValid 176 0 0 2)) "shifted replacement negative control"
  require (!(assignmentValid 320 0 0 1025)) "tail-to-first-region negative control"
  IO.println "PASS: 23088 boxes, 321 endpoint/polynomial identities; assignments, strict exclusions and negative controls"
