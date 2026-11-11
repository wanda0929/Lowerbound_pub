import LowerBoundCZ.OccupationLedger

open LowerBoundCZ LowerBoundCZ.Certification OccupationLedger
set_option maxRecDepth 10000

run_cmd do
  for name in [``index_unique, ``index_lt, ``primitive_credit, ``interval_credit,
      ``prefix_sum_le, ``traversal_exists, ``occupation_credit, ``slack_nonneg,
      ``credited_telescope] do
    for ax in ← Lean.collectAxioms name do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"

example : 64*4+64 = 320 ∧ count 4 = 65 ∧ count 3 = 64 := by decide
example : ProfileData.profiles.size = 321 := by decide

private def qstr (q : ℚ) : String := s!"{q.num}/{q.den}"
private def require (b : Bool) (s : String) : IO Unit := unless b do throw (IO.userError s)

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "usage: ProfileDataAudit.lean OUTPUT")
  require (ProfileData.profiles.size == 321) "profile count"
  let out ← IO.FS.Handle.mk path .write
  let mut total : ℚ := 0
  for i in List.range 321 do
    let p := entry i
    let xs := AllocationCodec.rationals p.power
    require (xs.size == 15 && left i < right i) s!"profile shape/width {i}"
    require (p.cell == min (i/64) 4) s!"cell ownership {i}"
    if i == 0 then
      require (left i == 0) "prefix start"
    else
      require (left i == right (i-1)) s!"prefix join {i}"
    total := total + credit i
    out.putStrLn (String.intercalate "\t" ([toString i, toString p.cell,
      qstr (left i), qstr (right i)] ++ xs.toList.map qstr ++ [qstr (credit i)]))
  require (right 319 == (2930957146313/1000000000000 : ℚ)) "main prefix endpoint"
  require (right 320 == (1465642825777/500000000000 : ℚ)) "tail endpoint"
  require (total == totalCredit) "nested five-cell sum"
  let knots : Array ℚ := #[0, 1/36, 1/3, 2/3, 35/36, 1]
  for j in List.range 5 do
    let lo := (2935887/1000000 : ℚ) * knots[j]!
    let hi := if j < 4 then (2935887/1000000 : ℚ) * knots[j+1]! else right 320
    require (left (64*j) == lo) s!"layout start {j}"
    for k in List.range (count j+1) do
      require (lo ≤ level j k && level j k ≤ hi) s!"layout bounds {j}/{k}"
      if k < count j then
        require (level j k == left (64*j+k)) s!"layout join {j}/{k}"
  IO.println "PASS: 321 decoded profiles, 4815 power coefficients, widths, joins, ownership and total credit"
