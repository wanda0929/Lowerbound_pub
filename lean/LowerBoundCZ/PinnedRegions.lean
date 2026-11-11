import LowerBoundCZ.PinnedAllocations
import LowerBoundCZ.RegionalData

/-! All remaining retained regional occupation certificates. These fixed data
cover inherited, W8-retained, dark-retained and tail profiles. The 16 allocation
replacements retain their existing PinnedAllocation instance. Coverage of an
actual trajectory by retained boxes is a separate reachability obligation. -/
namespace LowerBoundCZ.Certification.PinnedRegion
open CZExposure Slack AllocationCodec MvPolynomial QuotientNormalForm QuotientCertificate
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

-- The data audit checks this fixed cardinality, without unfolding all table
-- literals whenever the kernel compares two region-index types.
abbrev Region := Fin 9728
@[irreducible] def record (r : Region) := RegionalData.regions[r.val]?.getD (0, 0, 0, 0, 0)
def profileIndex (r : Region) : Nat := (record r).1
@[irreducible] def profile (r : Region) :=
  RegionalData.profiles[profileIndex r]?.getD (0, "0", "0", "")
def cell (r : Region) : Fin 5 := ⟨(profile r).1 % 5, Nat.mod_lt _ (by decide)⟩
@[irreducible] def source (r : Region) (b : Fin 736) : EncodedSource :=
  RegionalData.sources[(cell r).val*736+b.val]?.getD default
@[irreducible] def projection (p : Nat) : Projection :=
  (RegionalData.projections[p]?.getD default).decode
@[irreducible] def allocations (r : Region) (b : Fin 736) : Array (Nat × ℚ) :=
  allocation (RegionalData.groups[
    (naturals (RegionalData.maps[(record r).2.1]?.getD ""))[b.val]?.getD 0]?.getD "")

def lower (r : Region) : Fin 3 → ℚ :=
  ![rational (profile r).2.1, ((record r).2.2.1 : ℚ)/(record r).2.2.2.2,
    ((record r).2.2.2.1 : ℚ)/(record r).2.2.2.2]
def upper (r : Region) : Fin 3 → ℚ :=
  ![rational (profile r).2.2.1, ((record r).2.2.1+1 : ℚ)/(record r).2.2.2.2,
    ((record r).2.2.2.1+1 : ℚ)/(record r).2.2.2.2]
def delta (r : Region) (k : Fin 15) : ℚ :=
  (rationals (profile r).2.2.2)[k.val]?.getD 0

def projectionCoefficient (r : Region) (p : Projection)
    (k : (i : Fin 3) → Fin (allocationDegree i + 1)) : ℚ :=
  (∑ l : Fin 15, p.polynomial[l.val]?.getD 0 *
    PinnedAllocation.affineCoefficient 14 (k 0).val l.val (lower r 0) (upper r 0)) *
  PinnedAllocation.populationCoefficient (k 1).val (p.population[0]?.getD 0)
    (p.population[1]?.getD 0) (lower r 1) (upper r 1) *
  PinnedAllocation.populationCoefficient (k 2).val (p.population[2]?.getD 0)
    (p.population[3]?.getD 0) (lower r 2) (upper r 2)

def costCoefficient (r : Region)
    (k : (i : Fin 3) → Fin (allocationDegree i + 1)) : ℚ :=
  (lower r 1 + (upper r 1-lower r 1)*(k 1).val/7)/2 +
  (lower r 2 + (upper r 2-lower r 2)*(k 2).val/7)/4

def residual (r : Region)
    (k : (i : Fin 3) → Fin (allocationDegree i + 1)) : ℚ :=
  (∑ b : Fin 736, ∑ j : Fin (allocations r b).size,
    let a := (allocations r b)[j]
    a.2 * projectionCoefficient r (projection a.1) k) -
      delta r ⟨(k 0).val, (k 0).isLt⟩ * costCoefficient r k

def matrixEntry (r : Region) (b : Fin 736) (i j : Nat) : ℚ × ℚ :=
  (scalars (source r b).upper)[PinnedAllocation.matrixIndex (source r b).size i j]?.getD (0, 0)

noncomputable section

def sourceMatrix (r : Region) (b : Fin 736) :
    Matrix (Fin (source r b).size) (Fin (source r b).size) ℝ :=
  fun i j => GramBridge.scalar (matrixEntry r b i.val j.val)

def sourceColumn (r : Region) (b : Fin 736) (i : Fin (source r b).size) : MixedPoly :=
  let row := (rows (source r b).rows)[i.val]?.getD #[]
  ∑ j : Fin row.size,
    let entry := row[j]
    let code := (naturals (source r b).basis)[entry.1]?.getD 0
    C (entry.2 : ℂ) * C (if code%2 = 0 then 1 else Complex.I) *
      term (fun k => code/2/16^k.val%16) 1

def embedded (r : Region) (b : Fin 736) (p : Projection) :
    Matrix (Fin (source r b).size) (Fin (source r b).size) ℝ := fun i j =>
  ∑ a : Fin p.rows.size, ∑ c : Fin p.rows.size,
    if p.rows[a] = i.val ∧ p.rows[c] = j.val then
      (p.matrix[a.val*p.rows.size+c.val]?.getD 0 : ℝ) else 0

def localizer (r : Region) (b : Fin 736) : Localizer := match (source r b).localizer with
  | 0 => .one | 1 => .xi | 2 => .oneMinusXi | _ => .xiOneMinusXi

def block (r : Region) (b : Fin 736) : AllocatedBlock where
  size := (source r b).size
  source := sourceColumn r b
  Q := sourceMatrix r b
  localizer := localizer r b
  count := (allocations r b).size
  R := fun j => embedded r b (projection ((allocations r b)[j]).1)
  weight := fun j => ((allocations r b)[j]).2

def region (r : Region) : AllocationRegion where
  cell := cell r
  lo := lower r
  hi := upper r
  delta := delta r
  blockCount := 736
  blocks := block r
  residual := residual r

/-- Finite checks on the pinned payload only. In particular no local physical
inequality, integrated credit, mandatory-prefix or coverage oracle is a field.
All 736 original blocks participate, including those allocated zero weight. -/
structure NumericalChecks : Prop where
  widths : ∀ r i, lower r i < upper r i
  -- Exactly PSD, matrix domination, nonnegative weights and per-block budget.
  blocks : ∀ r b, (block r b).Checks
  source_identity : ∀ r, (region r).drift - ∑ b, (block r b).original ∈ relations
  tensor_identity : ∀ r, (∑ b, (block r b).allocated) -
    (region r).profile * embed cpoly -
      tensorMixed allocationDegree (residual r) (region r).coord ∈ relations
  tensor_nonneg : ∀ r k, 0 ≤ residual r k

theorem checks (h : NumericalChecks) (r : Region) : (region r).Checks where
  widths := h.widths r
  blocks := h.blocks r
  source := h.source_identity r
  residual_identity := h.tensor_identity r
  residual_nonneg := h.tensor_nonneg r

theorem trajectory_slack (h : NumericalChecks) (r : Region)
    (γ : ActivePulse) {s : ℝ} (hs : s ∈ Set.Icc 0 γ.S)
    (hξ : cellXi Pinned.order7.partition Pinned.order7.ceiling γ (cell r).val s ∈ Set.Icc (0 : ℝ) 1)
    (hbox : ∀ i,
      ![cellXi Pinned.order7.partition Pinned.order7.ceiling γ (cell r).val s,
        ‖r1 (γ.traj s)‖^2, ‖r2 (γ.traj s)‖^2] i ∈ Set.Icc (lower r i : ℝ) (upper r i : ℝ)) :
    (region r).rate (cellXi Pinned.order7.partition Pinned.order7.ceiling γ (cell r).val s) *
      cost (γ.traj s) ≤ occupationSlack Pinned.order7.partition Pinned.order7.ceiling
        Pinned.order7.potential γ (cell r).val s :=
  (region r).trajectory_slack (checks h r) γ hs hξ hbox

end
end LowerBoundCZ.Certification.PinnedRegion
