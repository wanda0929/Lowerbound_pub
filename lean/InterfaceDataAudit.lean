import LowerBoundCZ.PinnedInterfaces

open LowerBoundCZ LowerBoundCZ.Certification PinnedInterface

run_cmd do
  for name in [``certificate, ``excluded_iff, ``grid_cover, ``population_cover,
      ``retained, ``point_mem, ``eval_coord, ``crossing_credit, ``credited_telescope] do
    for ax in ← Lean.collectAxioms name do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"

-- Boundary points are covered by closed cells, not silently dropped.
example : (1 : ℝ) ∈ Set.Icc (lo 63 : ℝ) (hi 63 : ℝ) := by norm_num [lo, hi]
example : (0 : ℝ) ∈ Set.Icc (lo 0 : ℝ) (hi 0 : ℝ) := by norm_num [lo, hi]
example : (17/64 : ℝ) ∈ Set.Icc (lo 16 : ℝ) (hi 16 : ℝ) ∧
    (17/64 : ℝ) ∈ Set.Icc (lo 17 : ℝ) (hi 17 : ℝ) := by norm_num [lo, hi]

private def qstr (q : ℚ) : String := s!"{q.num}/{q.den}"
private def join (a : Array String) : String := String.intercalate " " a.toList
private def require (b : Bool) (s : String) : IO Unit := unless b do throw (IO.userError s)
private def index (a b : Fin 8) : (i : Fin 3) → Fin (degree i+1) :=
  fun | ⟨0,_⟩ => 0 | ⟨1,_⟩ => a | ⟨2,_⟩ => b

-- The source-identity checker expands unit columns. The canonical archive
-- instead uses these decoded weights, so equality of used indices is not enough.
private def unitRows (n : Nat) (rows : Array (Array (Nat × Int))) : Bool :=
  rows.size == n && (List.range n).all (fun i => rows[i]? == some #[(i, 1)])

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "usage: InterfaceDataAudit.lean OUTPUT")
  require (unitRows 2 #[#[(0,1)], #[(1,1)]]) "unit rows positive control"
  require (!(unitRows 2 #[#[(0,2)], #[(1,2)]])) "scaled weights negative control"
  require (!(unitRows 2 #[#[(1,1)], #[(0,1)]])) "permuted rows negative control"
  require (InterfaceData.sources.size == 536 && InterfaceData.diagonals.size == 536 &&
    InterfaceData.powers.size == 4 && InterfaceData.credits.size == 4) "data shapes"
  let out ← IO.FS.Handle.mk path .write
  for j in List.finRange 4 do
    for b in List.finRange 134 do
      let id := j.val*134+b.val
      let s := (source j b).decode
      let d := diagonal j b
      require (s.basis.size == s.size && s.upper.size == s.size*(s.size+1)/2 &&
        d.size == s.size && s.localizer == 0) s!"block shape {id}"
      require (unitRows s.size s.rows) s!"unit source rows {id}"
      require (s.basis.all (fun c => c%2 == 0 && c/2%4096 == 0)) s!"state column {id}"
      require (d.all (fun x => x ≥ 0)) s!"negative diagonal {id}"
      out.putStrLn s!"S {id} {s.size}"
      out.putStrLn s!"B {id} {join (s.basis.map toString)}"
      let full := (List.range s.size).flatMap fun i => (List.range s.size).map fun k =>
        let (a,c) := s.upper[PinnedAllocation.matrixIndex s.size i k]?.getD (0,0)
        s!"{qstr a},{qstr c}"
      out.putStrLn s!"Q {id} {String.intercalate " " full}"
      out.putStrLn s!"D {id} {join (d.map qstr)}"
    require ((power j).size == 64) s!"power shape {j.val}"
    out.putStrLn s!"P {j.val} {join ((power j).map qstr)}"
    out.putStrLn s!"K {j.val} {qstr (credit j)}"
  -- Cache the same exact energy function, avoiding 16384 repeated series sums.
  let energies := (List.finRange 64).toArray.map energy
  out.putStrLn s!"E {join (energies.map qstr)}"
  for j in List.finRange 4 do
    let mut bits := ""
    for x in List.finRange 64 do
      for y in List.finRange 64 do
        let A := 8*energies[x.val]!
        let D := energies[y.val]!
        let T := 72*(radius j)^2
        bits := bits ++ (if T < A+D || (T-A-D)^2 < 4*A*D then "1" else "0")
    out.putStrLn s!"X {j.val} {bits}"
    for (x,y) in ([(0,0),(17,42),(63,63)] : List (Fin 64 × Fin 64)) do
      require ((excluded j (x,y)) == (bits.toList[x.val*64+y.val]! == '1')) "cached exclusion"
      for (a,b) in ([(0,7),(3,5),(7,0)] : List (Fin 8 × Fin 8)) do
        out.putStrLn s!"T {j.val} {x.val} {y.val} {a.val} {b.val} {qstr (residual j (x,y) (index a b))}"
  IO.println "PASS: fixed interface shapes and values exported; all box classifications computed"
