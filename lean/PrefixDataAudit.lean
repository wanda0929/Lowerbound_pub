import LowerBoundCZ.StrengthenedBound

open LowerBoundCZ LowerBoundCZ.Certification OccupationLedger
set_option maxRecDepth 10000

run_cmd do
  for name in [``MandatoryPrefix.prefix_credit, ``MandatoryPrefix.endpoint_positive,
      ``MandatoryPrefix.endpoint_value, ``MandatoryPrefix.threshold,
      ``MandatoryPrefix.traversal, ``MandatoryPrefix.credited_telescope,
      ``Strengthened.endpoint_value, ``Strengthened.endpoint_matches,
      ``Strengthened.pulse_lower, ``Strengthened.active_lower,
      ``Strengthened.lab_lower, ``Strengthened.lab_window] do
    for ax in ← Lean.collectAxioms name do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"

-- The bootstrap deliberately excludes slots 319 and 320.
example : MandatoryPrefix.count 4 = 63 ∧ 64*4+63-1 = 318 := by decide

private def require (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)
private def qstr (q : ℚ) : String := s!"{q.num}/{q.den}"

/-- Evaluate each source monomial at (g1,r1,g2,r2)=(1,0,-1,0).
Both rational components are retained until the final exact cancellation. -/
private def terminal : Array (ℚ × ℚ) := Id.run do
  let mut p := Array.replicate 14 ((0,0) : ℚ × ℚ)
  for i in List.finRange 776 do
    let b := CertificateData.basis[i.val]!
    let w : ℚ := 0^(Pinned.anti b 1) * 0^(Pinned.holo b 1) *
      (-1)^(Pinned.anti b 2) * (-1)^(Pinned.holo b 2) *
      0^(Pinned.anti b 3) * 0^(Pinned.holo b 3)
    let c := CertificateData.multipliers[4*776+i.val]!
    let old := p[b.1]!
    p := p.set! b.1 (old.1-c.1*w, old.2-c.2*w)
  return p

private def power (k : Fin 14) (sign : ℚ) (K : ℚ) (B : ℚ := right 320) : ℚ × ℚ := Id.run do
  let U : ℚ := 2935887/1000000
  let a := 36*MandatoryPrefix.base/U-35
  let b := 36*(B-MandatoryPrefix.base)/U
  let mut z : ℚ × ℚ := (0,0)
  for d in List.range 14 do
    if k.val ≤ d then
      let w : ℚ := sign*(Nat.choose d k.val : ℚ)*a^(d-k.val)*b^k.val
      z := (z.1+terminal[d]!.1*w, z.2+terminal[d]!.2*w)
  if k.val == 0 then
    z := (z.1+CertificateData.offset.1+MandatoryPrefix.base+K+
      (∑ j : Fin 4, PinnedInterface.credit j)-B, z.2+CertificateData.offset.2)
  return z

private def endpointValid (beta : Fin 14 → ℚ) (sign K : ℚ) (B : ℚ := right 320) : Bool :=
  (List.finRange 14).all fun m =>
    let c := (List.finRange 14).foldl (fun z k => z +
      if k.val ≤ m.val then beta k * (Nat.choose 13 k.val : ℚ) *
        Nat.choose (13-k.val) (m.val-k.val) * (-1 : ℚ)^(m.val-k.val) else 0) 0
    power m sign K B == (c,0)

def main (args : List String) : IO Unit := do
  let path :: rest := args | throw (IO.userError "usage: PrefixDataAudit.lean OUTPUT [FINAL_OUTPUT]")
  require (rest.length ≤ 1) "at most one final output"
  require (CertificateData.basis.size == 776 && CertificateData.multipliers.size == 3880) "source shape"
  for b in CertificateData.basis do
    require (b.1 ≤ 13 && b.2.1.size == 4 && b.2.2.size == 4) "source basis degree/shape"
  let U : ℚ := 2935887/1000000
  let knots : Array ℚ := #[0, 1/36, 1/3, 2/3, 35/36, 1]
  for j in List.range 5 do
    require (left (64*j) == U*knots[j]!) s!"layout start {j}"
    for k in List.range (count j+1) do
      let v := level j k
      let bound := if j < 4 then U*knots[j+1]! else right 320
      require (U*knots[j]! ≤ v && v ≤ bound) s!"full layout bounds {j}/{k}"
      if k < count j then
        require (level j k == left (64*j+k) && left (64*j+k) < right (64*j+k)) s!"join/width {j}/{k}"
      if k ≤ MandatoryPrefix.count j then
        let bound := if j < 4 then U*knots[j+1]! else MandatoryPrefix.base
        require (v ≤ bound) s!"already-reached prefix {j}/{k}"
  require (right 318 < MandatoryPrefix.base && MandatoryPrefix.base < right 320 && right 320 ≤ 733/250) "thresholds"
  require (!(right 319 ≤ MandatoryPrefix.base)) "unproved next interval negative control"
  require ((List.finRange 14).all (fun k => 0 < PrefixData.beta k)) "positive Bernstein coefficients"
  require (endpointValid PrefixData.beta 1 MandatoryPrefix.credit) "terminal polynomial identity"
  require (!(endpointValid (fun k => PrefixData.beta k + if k.val == 7 then 1/1000000 else 0)
    1 MandatoryPrefix.credit)) "coefficient mutation"
  require (!(endpointValid PrefixData.beta (-1) MandatoryPrefix.credit)) "terminal sign mutation"
  require (!(endpointValid PrefixData.beta 1 totalCredit)) "unproved credits mutation"
  let out ← IO.FS.Handle.mk path .write
  for p in terminal do out.putStrLn s!"{qstr p.1} {qstr p.2}"
  for k in List.finRange 14 do out.putStrLn (qstr (PrefixData.beta k))
  out.putStrLn (qstr MandatoryPrefix.credit)
  for j in List.finRange 4 do out.putStrLn (qstr (PinnedInterface.credit j))
  IO.println "PASS: 319 reachable profiles, full traversal layout, 14 terminal identities/signs and four negative controls"
  if let [finalPath] := rest then
    require (endpointValid SlackData.endpoint 1 totalCredit SlackData.bound) "final terminal identity"
    let rho := (SlackData.bound-MandatoryPrefix.base)/(right 320-MandatoryPrefix.base)
    let delta := totalCredit-MandatoryPrefix.credit+right 320-SlackData.bound
    for k in List.finRange 14 do
      let old := power k 1 MandatoryPrefix.credit
      let new := power k 1 totalCredit SlackData.bound
      require (old.1*rho^k.val + (if k.val == 0 then delta else 0) == new.1 &&
        old.2*rho^k.val == new.2) s!"rescaled bootstrap coefficient {k.val}"
    require (!(endpointValid SlackData.endpoint 1 MandatoryPrefix.credit SlackData.bound)) "missing two credits"
    require (!(endpointValid SlackData.endpoint 1 totalCredit (SlackData.bound+1/1000000000000))) "inflated final bound"
    require (!(endpointValid SlackData.endpoint (-1) totalCredit SlackData.bound)) "final terminal sign"
    let finalOut ← IO.FS.Handle.mk finalPath .write
    for p in terminal do finalOut.putStrLn s!"{qstr p.1} {qstr p.2}"
    for k in List.finRange 14 do finalOut.putStrLn (qstr (SlackData.endpoint k))
    finalOut.putStrLn (qstr totalCredit)
    for j in List.finRange 4 do finalOut.putStrLn (qstr (PinnedInterface.credit j))
    IO.println "PASS: final 321-profile terminal identity, 14 rescaling identities and three final negative controls"
