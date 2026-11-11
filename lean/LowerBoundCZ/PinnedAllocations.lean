import LowerBoundCZ.SlackAllocation
import LowerBoundCZ.AllocationData

/-! The 1,024 fixed replacement regions, not a caller-supplied certificate.
Only finite numerical validity is an external input. The source matrices,
facial columns, selected rows, weights and profiles are fixed definitions. -/
namespace LowerBoundCZ.Certification.PinnedAllocation
open CZExposure Slack AllocationCodec MvPolynomial QuotientNormalForm QuotientCertificate
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

@[irreducible] def source (b : Fin 736) : EncodedSource := AllocationData.sources[b.val]?.getD default
@[irreducible] def projection (p : Nat) : Projection :=
  (AllocationData.projections[p]?.getD default).decode
@[irreducible] def allocations (r : Fin 1024) (b : Fin 736) : Array (Nat × ℚ) :=
  allocation (AllocationData.groups[((naturals (AllocationData.regionGroups[r.val]?.getD ""))[b.val]?.getD 0)]?.getD "")

def lower (r : Fin 1024) : Fin 3 → ℚ :=
  ![((48 + r.val/64 : Nat) : ℚ)/64, ((r.val%64/8 : Nat) : ℚ)/8, ((r.val%8 : Nat) : ℚ)/8]
def upper (r : Fin 1024) : Fin 3 → ℚ :=
  ![((49 + r.val/64 : Nat) : ℚ)/64, ((r.val%64/8 + 1 : Nat) : ℚ)/8,
    ((r.val%8 + 1 : Nat) : ℚ)/8]
@[irreducible] def delta (r : Fin 1024) (k : Fin 15) : ℚ :=
  (rationals (AllocationData.profiles[r.val/64]?.getD ""))[k.val]?.getD 0

/-- Power-to-Bernstein conversion after the affine map [a,b]. -/
def affineCoefficient (d i power : Nat) (a b : ℚ) : ℚ :=
  ∑ l : Fin (d+1), if l.val ≤ i ∧ l.val ≤ power then
    (Nat.choose power l.val : ℚ) * Nat.choose i l.val / Nat.choose d l.val *
      a^(power-l.val) * (b-a)^l.val else 0

def populationCoefficient (i g e : Nat) (a b : ℚ) : ℚ :=
  ∑ l : Fin (g+1), (-1 : ℚ)^l.val * Nat.choose g l.val *
    affineCoefficient 7 i (e+l.val) a b

def projectionCoefficient (r : Fin 1024) (p : Projection)
    (k : (i : Fin 3) → Fin (allocationDegree i + 1)) : ℚ :=
  (∑ l : Fin 15, p.polynomial[l.val]?.getD 0 *
    affineCoefficient 14 (k 0).val l.val (lower r 0) (upper r 0)) *
  populationCoefficient (k 1).val (p.population[0]?.getD 0) (p.population[1]?.getD 0)
    (lower r 1) (upper r 1) *
  populationCoefficient (k 2).val (p.population[2]?.getD 0) (p.population[3]?.getD 0)
    (lower r 2) (upper r 2)

def costCoefficient (r : Fin 1024)
    (k : (i : Fin 3) → Fin (allocationDegree i + 1)) : ℚ :=
  (lower r 1 + (upper r 1-lower r 1)*(k 1).val/7)/2 +
  (lower r 2 + (upper r 2-lower r 2)*(k 2).val/7)/4

def residual (r : Fin 1024)
    (k : (i : Fin 3) → Fin (allocationDegree i + 1)) : ℚ :=
  (∑ b : Fin 736, ∑ j : Fin (allocations r b).size,
    let a := (allocations r b)[j]
    a.2 * projectionCoefficient r (projection a.1) k) -
      delta r ⟨(k 0).val, (k 0).isLt⟩ * costCoefficient r k

def matrixIndex (n i j : Nat) : Nat :=
  let lo := min i j
  let hi := max i j
  lo*n-lo*(lo+1)/2+hi

def matrixEntry (b : Fin 736) (i j : Nat) : ℚ × ℚ :=
  (scalars (source b).upper)[matrixIndex (source b).size i j]?.getD (0, 0)

noncomputable section

def sourceMatrix (b : Fin 736) : Matrix (Fin (source b).size) (Fin (source b).size) ℝ :=
  fun i j => GramBridge.scalar (matrixEntry b i.val j.val)

def sourceColumn (b : Fin 736) (i : Fin (source b).size) : MixedPoly :=
  let row := (rows (source b).rows)[i.val]?.getD #[]
  ∑ j : Fin row.size,
    let entry := row[j]
    let code := (naturals (source b).basis)[entry.1]?.getD 0
    C (entry.2 : ℂ) * C (if code%2 = 0 then 1 else Complex.I) *
      term (fun k => code/2/16^k.val%16) 1

/-- Embed the full reduced matrix, including off-diagonal entries, in the
original source row coordinates. No active-face renumbering is implicit. -/
def embedded (b : Fin 736) (p : Projection) :
    Matrix (Fin (source b).size) (Fin (source b).size) ℝ := fun i j =>
  ∑ a : Fin p.rows.size, ∑ c : Fin p.rows.size,
    if p.rows[a] = i.val ∧ p.rows[c] = j.val then
      (p.matrix[a.val*p.rows.size+c.val]?.getD 0 : ℝ) else 0

def localizer (b : Fin 736) : Localizer := match (source b).localizer with
  | 0 => .one | 1 => .xi | 2 => .oneMinusXi | _ => .xiOneMinusXi

def block (r : Fin 1024) (b : Fin 736) : AllocatedBlock where
  size := (source b).size
  source := sourceColumn b
  Q := sourceMatrix b
  localizer := localizer b
  count := (allocations r b).size
  R := fun j => embedded b (projection ((allocations r b)[j]).1)
  weight := fun j => ((allocations r b)[j]).2

def region (r : Fin 1024) : AllocationRegion where
  cell := 2
  lo := lower r
  hi := upper r
  delta := delta r
  blockCount := 736
  blocks := block r
  residual := residual r

theorem widths (r : Fin 1024) (i : Fin 3) : (region r).lo i < (region r).hi i := by
  change lower r i < upper r i
  fin_cases i <;> norm_num [lower, upper] <;> linarith

/-- Only finite tests on FIXED data. No variable archive, profile, trajectory
bound, cone feasibility, or physical-exclusion oracle is accepted. The two
ideal-membership fields are finite coefficient identities, as in GramBridge.
Repeated regional references to a projection can reuse a numerical PSD proof. -/
structure NumericalChecks : Prop where
  source_psd : ∀ b, (sourceMatrix b).PosSemidef
  domination : ∀ r b (j : Fin (allocations r b).size),
    (sourceMatrix b - embedded b (projection ((allocations r b)[j]).1)).PosSemidef
  weights_nonneg : ∀ r b (j : Fin (allocations r b).size), 0 ≤ ((allocations r b)[j]).2
  budgets : ∀ r b, (∑ j : Fin (allocations r b).size, ((allocations r b)[j]).2) ≤ 1
  source_identity : ∀ r, (region r).drift - ∑ b, (block r b).original ∈ relations
  tensor_identity : ∀ r, (∑ b, (block r b).allocated) -
    (region r).profile * embed cpoly -
      tensorMixed allocationDegree (residual r) (region r).coord ∈ relations
  tensor_nonneg : ∀ r k, 0 ≤ residual r k

theorem checks (h : NumericalChecks) (r : Fin 1024) : (region r).Checks where
  widths := widths r
  blocks := fun b => ⟨h.source_psd b, h.domination r b, h.weights_nonneg r b, h.budgets r b⟩
  source := h.source_identity r
  residual_identity := h.tensor_identity r
  residual_nonneg := h.tensor_nonneg r

/-- The fixed-data instance of the physical local slack theorem. -/
theorem trajectory_slack (h : NumericalChecks) (r : Fin 1024)
    (γ : ActivePulse) {s : ℝ} (hs : s ∈ Set.Icc 0 γ.S)
    (hξ : cellXi Pinned.order7.partition Pinned.order7.ceiling γ 2 s ∈ Set.Icc (0 : ℝ) 1)
    (hbox : ∀ i,
      ![cellXi Pinned.order7.partition Pinned.order7.ceiling γ 2 s,
        ‖r1 (γ.traj s)‖^2, ‖r2 (γ.traj s)‖^2] i ∈ Set.Icc (lower r i : ℝ) (upper r i : ℝ)) :
    (region r).rate (cellXi Pinned.order7.partition Pinned.order7.ceiling γ 2 s) *
      cost (γ.traj s) ≤ occupationSlack Pinned.order7.partition Pinned.order7.ceiling
        Pinned.order7.potential γ 2 s :=
  (region r).trajectory_slack (checks h r) γ hs hξ hbox

end
end LowerBoundCZ.Certification.PinnedAllocation
