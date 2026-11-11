import LowerBoundCZ.PinnedRegions
import LowerBoundCZ.PinnedInterfaces

open LowerBoundCZ LowerBoundCZ.Certification AllocationCodec

private def qstr (q : ℚ) : String := s!"{q.num}/{q.den}"
private def join (xs : Array String) := String.intercalate " " xs.toList
private def index (a : Fin 15) (b c : Fin 8) :
    (i : Fin 3) → Fin (Slack.allocationDegree i+1) :=
  fun | ⟨0,_⟩ => a | ⟨1,_⟩ => b | ⟨2,_⟩ => c

/-- Exhaustive primitive tables for a factored evaluation of residual.
No replacement definition of affineCoefficient or populationCoefficient is
used: the executable calls the definitions appearing in residual itself. -/
def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "usage: ResidualFactorsAudit.lean OUTPUT")
  let out ← IO.FS.Handle.mk path .write
  for p in List.range RegionalData.profiles.size do
    let (_, a, b, _) := RegionalData.profiles[p]!
    let lo := rational a
    let hi := rational b
    let values := (List.range 15).toArray.flatMap fun i =>
      (List.range 15).toArray.map fun k => qstr (PinnedAllocation.affineCoefficient 14 i k lo hi)
    out.putStrLn s!"E {p} {qstr lo} {qstr hi} {join values}"
  for n in [4,8,16,64] do
    for x in List.range n do
      let lo : ℚ := x/n
      let hi : ℚ := (x+1)/n
      let values := (List.range 8).toArray.flatMap fun i =>
        (List.range 8).toArray.map fun k => qstr (PinnedAllocation.affineCoefficient 7 i k lo hi)
      out.putStrLn s!"A {n} {x} {join values}"
      if n != 64 then
        for g in List.range 8 do
          for e in List.range (8-g) do
            let values := (List.range 8).toArray.map fun i =>
              qstr (PinnedAllocation.populationCoefficient i g e lo hi)
            out.putStrLn s!"P {n} {x} {g} {e} {join values}"
  let mut seen : Std.HashSet (Nat × Nat × Nat) := {}
  for r in List.finRange 9728 do
    let (_,_,x,y,n) := PinnedRegion.record r
    if !seen.contains (n,x,y) then
      seen := seen.insert (n,x,y)
      let values := (List.finRange 8).toArray.flatMap fun i =>
        (List.finRange 8).toArray.map fun j => qstr (PinnedRegion.costCoefficient r (index 0 i j))
      out.putStrLn s!"C regional {n} {x} {y} {join values}"
  for r in List.finRange 64 do
    let values := (List.finRange 8).toArray.flatMap fun i =>
      (List.finRange 8).toArray.map fun j =>
        qstr (PinnedAllocation.costCoefficient ⟨r.val, by omega⟩ (index 0 i j))
    out.putStrLn s!"C allocation 8 {r.val/8} {r.val%8} {join values}"
  IO.println s!"PASS: all exposure/affine/population factors and {seen.size} regional cost boxes exported"
