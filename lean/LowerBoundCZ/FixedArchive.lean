import LowerBoundCZ.StrengthenedBound
import LowerBoundCZ.ArchiveData

/-! Canonical archive for first-tier acceptance. No arbitrary matrices or
archive argument remain in the public acceptance theorem. Layout membership
and numerical checks are explicit external finite obligations. -/
namespace LowerBoundCZ.Certification.FixedArchive
open CZExposure GramBridge AllocationCodec MvPolynomial ConcretePartitioned
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def used (s : EncodedSource) : Array Nat :=
  (List.range (naturals s.basis).size).toArray.filter fun k =>
    (rows s.rows).any (fun row => row.any (fun e => e.1 == k && e.2 != 0))

def code (s : EncodedSource) (i : Nat) : Nat :=
  (naturals s.basis)[(used s)[i]?.getD 0]?.getD 0
def powers (s : EncodedSource) (i : Nat) (k : Fin 11) : Nat := code s i / 2 / 16^k.val % 16
def weight (s : EncodedSource) (i j : Nat) : Int :=
  ((rows s.rows)[i]?.getD #[]).foldl (fun z e =>
    if e.1 == (used s)[j]?.getD 0 then z+e.2 else z) 0
def entry (s : EncodedSource) (i j : Nat) : ℚ × ℚ :=
  (scalars s.upper)[PinnedAllocation.matrixIndex s.size i j]?.getD (0,0)

@[irreducible] def occupationSource (j b : Nat) : EncodedSource := RegionalData.sources[j*736+b]?.getD default
@[irreducible] def interfaceSource (j b : Nat) : EncodedSource := InterfaceData.sources[j*134+b]?.getD default
def terminalEntries (j t : Nat) : Array (ℚ × ℚ) := scalars (ArchiveData.terminal[j*2+t]?.getD "")

noncomputable section
def raw (s : EncodedSource) : RawBlock where
  size := s.size
  columns := (used s).size
  charge := SymmetryGram.monomialCharge (powers s 0)
  powers := fun i => Finsupp.equivFunOnFinite.symm (powers s i.val)
  weights := fun i j => weight s i.val j.val
  entries := fun i j => entry s i.val j.val

structure LayoutChecks : Prop where
  moment : ∀ j : Fin 5, ∀ b : Fin 153,
    (raw (occupationSource j b)).Valid (NormalFaceBasis.basis 7)
  interval : ∀ j : Fin 5, ∀ b : Fin 583,
    (raw (occupationSource j (153+b.val))).Valid (fullBasis 6)
  interface : ∀ j : Fin 4, ∀ b : Fin 134,
    (raw (interfaceSource j b)).Valid (interfaceBasis 7)

def archive (h : LayoutChecks) : Archive Pinned.order7 where
  cells := fun j => {
    moment := (List.finRange 153).map fun (b : Fin 153) =>
      (raw (occupationSource j b)).toBlock (h.moment j b)
    interval := (List.finRange 583).map fun b =>
      (raw (occupationSource j (153+b.val))).toBlock (h.interval j b) }
  interfaces := fun j => (List.finRange 134).map fun (b : Fin 134) =>
    (raw (interfaceSource j b)).toBlock (h.interface j b)
  terminal := fun j => {
    moment := fun i k => scalar ((terminalEntries j 0)[i.val*8+k.val]?.getD (0,0))
    interval := fun i k => scalar ((terminalEntries j 1)[i.val*7+k.val]?.getD (0,0)) }

/-- A field-by-field boundary for the fixed publication certificate.
These are hypotheses, not axioms or an assertion that an external run is a
kernel proof. All data in the base archive are fixed above. -/
structure Acceptance : Prop where
  layout : LayoutChecks
  base : MatrixChecks (archive layout)
  traversal : MandatoryPrefix.LayoutChecks
  bootstrap : MandatoryPrefix.EndpointChecks
  endpoint : Strengthened.EndpointCheck
  coverage : OccupationCoverage.DataChecks
  allocation : PinnedAllocation.NumericalChecks
  regional : PinnedRegion.NumericalChecks
  interfaces : PinnedInterface.NumericalChecks
  upper : Pinned.UpperChecks

theorem lab_window (h : Acceptance) :
    ((SlackData.bound : ℝ) : EReal) ≤ labCstar ∧
      labCstar < (LowerBoundCZ.upperEndpoint : EReal) :=
  Strengthened.lab_window h.traversal h.bootstrap h.endpoint h.coverage
    h.allocation h.regional (archive h.layout) h.base h.interfaces h.upper

end
end LowerBoundCZ.Certification.FixedArchive
