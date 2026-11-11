import LowerBoundCZ.PinnedRegions

open LowerBoundCZ AllocationCodec
open LowerBoundCZ.Certification PinnedRegion
set_option maxRecDepth 10000

run_cmd do
  for name in [``checks, ``trajectory_slack] do
    for ax in ← Lean.collectAxioms name do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"

private def qstr (q : ℚ) : String := s!"{q.num}/{q.den}"
private def join (xs : Array String) := String.intercalate " " xs.toList
private def require (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

private def sampleIndex : (i : Fin 3) → Fin (Slack.allocationDegree i+1) :=
  fun | ⟨0, _⟩ => 3 | ⟨1, _⟩ => 2 | ⟨2, _⟩ => 6

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "usage: RegionalDataAudit.lean OUTPUT")
  let out ← IO.FS.Handle.mk path .write
  require (RegionalData.sources.size == 3680 && RegionalData.profiles.size == 321) "source/profile count"
  require (RegionalData.regions.size == 9728) "region count"
  for i in List.range RegionalData.sources.size do
    let s := RegionalData.sources[i]!.decode
    require (s.upper.size == s.size*(s.size+1)/2 && s.rows.size == s.size) s!"source shape {i}"
    require (s.rows.all (fun row => row.all (fun e => e.1 < s.basis.size))) s!"source row {i}"
    out.putStrLn s!"S {i} {s.size} {s.localizer}"
    out.putStrLn (join (s.basis.map toString))
    out.putStrLn (String.intercalate "|" (s.rows.toList.map (fun row => join (row.map (fun e => s!"{e.1}:{e.2}")))))
    out.putStrLn (join (s.upper.map (fun v => s!"{qstr v.1},{qstr v.2}")))
  for i in List.range RegionalData.projections.size do
    let p := (RegionalData.projections[i]!).decode
    require (p.matrix.size == p.rows.size^2 && p.population.size == 4 && p.polynomial.size ≤ 15) s!"projection shape {i}"
    out.putStrLn s!"P {i} {p.originalID} {p.block}"
    out.putStrLn (join (p.rows.map toString))
    out.putStrLn (join (p.matrix.map qstr))
    out.putStrLn (join (p.polynomial.map qstr))
    out.putStrLn (join (p.population.map toString))
  for i in List.range RegionalData.groups.size do
    let a := allocation RegionalData.groups[i]!
    require (a.all (fun x => x.1 < RegionalData.projections.size && x.2 > 0)) s!"group {i}"
    require (a.foldl (fun z x => z+x.2) 0 ≤ 1) s!"block budget {i}"
    out.putStrLn s!"G {i}"
    out.putStrLn (join (a.map (fun x => s!"{x.1}:{qstr x.2}")))
  for i in List.range RegionalData.maps.size do
    let a := naturals RegionalData.maps[i]!
    require (a.size == 736 && a.all (fun x => x < RegionalData.groups.size)) s!"map {i}"
    for b in List.range 736 do
      require ((allocation RegionalData.groups[a[b]!]!).all (fun x =>
        (RegionalData.projections[x.1]!).block == b)) s!"block ownership {i}/{b}"
    out.putStrLn s!"M {i}"
    out.putStrLn (join (a.map toString))
  for r in List.finRange 9728 do
    let (i, m, x, y, n) := record r
    require (i < 321 && !(176 ≤ i && i < 192) && m < RegionalData.maps.size &&
      n > 0 && x < n && y < n) s!"region {r.val}"
    let p := profile r
    require (p.1 < 5 && (rationals p.2.2.2).size == 15) s!"profile {i}"
    require ((List.finRange 3).all (fun k => lower r k < upper r k)) s!"width {r.val}"
    out.putStrLn s!"R {r.val} {i} {m} {x} {y} {n}"
  for i in List.range 321 do
    let (c, a, b, d) := RegionalData.profiles[i]!
    out.putStrLn s!"D {i} {c} {qstr (rational a)} {qstr (rational b)}"
    out.putStrLn (join ((rationals d).map qstr))
  for i in [0, 1, 237, 320] do
    let some r := (List.finRange 9728).find? (fun r => profileIndex r == i)
      | throw (IO.userError s!"missing sample profile {i}")
    out.putStrLn s!"T {r.val} {qstr (residual r sampleIndex)}"
  IO.println s!"PASS: {RegionalData.sources.size} sources, {RegionalData.projections.size} projections, {RegionalData.regions.size} regions; decoded shapes and ownership"
