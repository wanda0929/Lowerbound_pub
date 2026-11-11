import LowerBoundCZ.PinnedCertificates

open LowerBoundCZ LowerBoundCZ.Certification

private def qstr (q : ℚ) : String := s!"{q.num}/{q.den}"

/-- Export the actual potential decoder input, without rounding Q(sqrt(2)).
The Python identity checker compares its reconstructed derivative with the
full original Gram polynomials. This executable introduces no proof axiom. -/
def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "usage: SourceIdentityDataAudit.lean OUTPUT")
  unless CertificateData.basis.size == 776 && CertificateData.multipliers.size == 3880 do
    throw (IO.userError "potential shape")
  let out ← IO.FS.Handle.mk path .write
  for i in List.range 776 do
    let b := CertificateData.basis[i]!
    unless b.2.1.size == 4 && b.2.2.size == 4 do
      throw (IO.userError "potential basis shape")
    let a := String.intercalate " " (b.2.1.toList.map toString)
    let h := String.intercalate " " (b.2.2.toList.map toString)
    out.putStrLn s!"B {i} {b.1} {a} {h}"
  for i in List.range 3880 do
    let (a,b) := CertificateData.multipliers[i]!
    out.putStrLn s!"C {i} {qstr a} {qstr b}"
  IO.println "PASS: all 776 potential basis entries and 3880 exact multiplier pairs exported"
