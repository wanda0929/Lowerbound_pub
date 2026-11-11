import LowerBoundCZ.FixedArchive

open LowerBoundCZ LowerBoundCZ.Certification FixedArchive AllocationCodec
open CZExposure

run_cmd do
  for ax in ← Lean.collectAxioms ``FixedArchive.lab_window do
    unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
      throwError "Unexpected axiom {ax}"

private def require (b : Bool) (msg : String) : IO Unit :=
  unless b do throw (IO.userError msg)
private def qstr (q : ℚ) := s!"{q.num}/{q.den}"
private def pairstr (q : ℚ × ℚ) := s!"{qstr q.1},{qstr q.2}"

private def block (s : EncodedSource) (kind : Nat) : IO (Array Nat) := do
  let ids := used s
  let basis := naturals s.basis
  require (!ids.isEmpty) "nonempty RawBlock"
  let ex := fun code (k : Fin 11) => code/2/16^k.val%16
  let q := SymmetryGram.monomialCharge (ex basis[ids[0]!]!)
  require (q.1 < 0 || (q.1 == 0 && q.2 ≤ 0)) "kept conjugate charge"
  for i in ids do
    let c := basis[i]!
    let p := ex c
    require (c/2 < 16^11 && c%2 == (p 1+p 2)%2) "powers/rephasing"
    require (SymmetryGram.monomialCharge p == q) "constant block charge"
    require ((p 1 == 0 || p 2 == 0) && (p 3 == 0 || p 4 == 0) &&
      (p 7 == 0 || p 8 == 0)) "normal partner"
    require ((∑ k : Fin 11, p k) ≤ (if kind == 1 then 6 else 7)) "basis degree"
    if kind == 0 then
      require (0 < p 5+p 6+p 9+p 10) "zero-cost-face basis"
    if kind == 2 then
      require (p 0+p 1+p 2 == 0) "interface basis"
  require (s.localizer == (if kind == 1 then 3 else 0)) "archive localizer"
  return ids

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "usage: FixedArchiveAudit.lean OUTPUT")
  let out ← IO.FS.Handle.mk path .write
  for j in List.range 5 do
    for b in List.range 736 do
      let ids ← block (occupationSource j b) (if b < 153 then 0 else 1)
      out.putStrLn s!"B O {j} {b} {String.intercalate " " (ids.toList.map toString)}"
  for j in List.range 4 do
    for b in List.range 134 do
      let ids ← block (interfaceSource j b) 2
      out.putStrLn s!"B I {j} {b} {String.intercalate " " (ids.toList.map toString)}"
  for j in List.range 5 do
    for t in List.range 2 do
      let values := terminalEntries j t
      require (values.size == (8-t)^2) "terminal dimensions"
      out.putStrLn s!"T {j} {t} {String.intercalate " " (values.toList.map pairstr)}"
    let mut coeff := Array.replicate 15 ((0,0) : ℚ × ℚ)
    coeff := coeff.set! 0 CertificateData.offset
    for i in List.range 776 do
      let b := CertificateData.basis[i]!
      let w : ℚ := 0^(Pinned.anti b 1) * 0^(Pinned.holo b 1) *
        (-1)^(Pinned.anti b 2) * (-1)^(Pinned.holo b 2) *
        0^(Pinned.anti b 3) * 0^(Pinned.holo b 3)
      let c := CertificateData.multipliers[j*776+i]!
      let old := coeff[b.1]!
      coeff := coeff.set! b.1 (old.1-c.1*w,old.2-c.2*w)
    out.putStrLn s!"V {j} {String.intercalate " " (coeff.toList.map pairstr)}"
  IO.println "PASS: all fixed archive layouts, phases and localizers; terminal payload exported; axiom allowlist passed"
