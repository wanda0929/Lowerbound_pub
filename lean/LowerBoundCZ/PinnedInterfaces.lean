import LowerBoundCZ.SlackCrossing
import LowerBoundCZ.PopulationBarrier
import LowerBoundCZ.PinnedAllocations
import LowerBoundCZ.InterfaceData

/-! Fixed four-interface certificate, including the W64 population cover. -/
namespace LowerBoundCZ.Certification.PinnedInterface
open CZExposure Slack AllocationCodec MvPolynomial QuotientNormalForm QuotientCertificate
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

abbrev Box := Fin 64 × Fin 64
def degree : Fin 3 → ℕ := ![0,7,7]
def lo (i : Fin 64) : ℚ := (i.val : ℚ)/64
def hi (i : Fin 64) : ℚ := ((i.val : ℚ)+1)/64
@[irreducible] def source (j : Fin 4) (b : Fin 134) : EncodedSource :=
  InterfaceData.sources[j.val*134+b.val]?.getD default
@[irreducible] def diagonal (j : Fin 4) (b : Fin 134) : Array ℚ :=
  rationals (InterfaceData.diagonals[j.val*134+b.val]?.getD "")
@[irreducible] def power (j : Fin 4) : Array ℚ :=
  rationals (InterfaceData.powers[j.val]?.getD "")
@[irreducible] def credit (j : Fin 4) : ℚ :=
  rational (InterfaceData.credits[j.val]?.getD "")

def residual (j : Fin 4) (b : Box) (k : (i : Fin 3) → Fin (degree i+1)) : ℚ :=
  (∑ a : Fin 8, ∑ c : Fin 8, (power j)[a.val*8+c.val]?.getD 0 *
    PinnedAllocation.affineCoefficient 7 (k 1).val a.val (lo b.1) (hi b.1) *
    PinnedAllocation.affineCoefficient 7 (k 2).val c.val (lo b.2) (hi b.2)) - credit j

def crossingCost (j : Fin 4) : ℚ :=
  (2935887/1000000) * (![1/36,1/3,2/3,35/36] : Fin 4 → ℚ) j
def radius (j : Fin 4) : ℚ := min (crossingCost j) (733/250-crossingCost j)
def energy (i : Fin 64) : ℚ :=
  (lo i)^3*(∑ k ∈ Finset.range 65, 3*barrierCoeff k/(2*k+3)*(lo i)^k)^2
def excluded (j : Fin 4) (b : Box) : Bool :=
  let A := 8*energy b.1
  let D := energy b.2
  let T := 72*(radius j)^2
  decide (T < A+D ∨ (T-A-D)^2 < 4*A*D)

noncomputable section
def matrix (j : Fin 4) (b : Fin 134) :
    Matrix (Fin (source j b).size) (Fin (source j b).size) ℝ := fun i k =>
  let entries := scalars (source j b).upper
  GramBridge.scalar (entries[PinnedAllocation.matrixIndex (source j b).size i.val k.val]?.getD (0,0))
def column (j : Fin 4) (b : Fin 134) (i : Fin (source j b).size) : MixedPoly :=
  let code := (naturals (source j b).basis)[i.val]?.getD 0
  term (fun k => code/2/16^k.val%16) 1
def allocatedMatrix (j : Fin 4) (b : Fin 134) :
    Matrix (Fin (source j b).size) (Fin (source j b).size) ℝ :=
  Matrix.diagonal (fun i => ((diagonal j b)[i.val]?.getD 0 : ℝ))
def block (j : Fin 4) (b : Fin 134) : AllocatedBlock where
  size := (source j b).size
  source := column j b
  Q := matrix j b
  localizer := .one
  count := 1
  R := fun _ => allocatedMatrix j b
  weight := fun _ => 1
def coord (b : Box) : Fin 3 → MixedPoly :=
  ![0, C (64 : ℂ)*(X 5*X 6-C (lo b.1 : ℂ)),
       C (64 : ℂ)*(X 9*X 10-C (lo b.2 : ℂ))]
def knot (j : Fin 4) : ℝ := Pinned.order7.ceiling * Pinned.partition.a (j.val+1)
def Excluded (j : Fin 4) (b : Box) : Prop :=
  PopulationBoxExcluded 64 (lo b.1) (lo b.2) (min (knot j) (733/250-knot j))

theorem radius_cast (j : Fin 4) :
    (radius j : ℝ) = min (knot j) (733/250-knot j) := by
  fin_cases j <;> norm_num [radius, crossingCost, knot, Pinned.order7, Pinned.partition]

/-- The executable rational discriminator is exactly the physical exclusion
predicate, including its strict inequalities and boundary-equality convention. -/
theorem excluded_iff (j : Fin 4) (b : Box) : excluded j b = true ↔ Excluded j b := by
  have h1 : (energy b.1 : ℝ) = barrierEnergy 64 (lo b.1) := (barrierEnergy_rat 64 _).symm
  have h2 : (energy b.2 : ℝ) = barrierEnergy 64 (lo b.2) := (barrierEnergy_rat 64 _).symm
  unfold excluded Excluded PopulationBoxExcluded
  rw [decide_eq_true_eq, ← h1, ← h2, ← radius_cast]
  dsimp only
  norm_cast

/-- All fields are finite checks of fixed data. Population-box coverage and
physical unreachability of discarded boxes are proved below, not fields. -/
structure NumericalChecks : Prop where
  source_psd : ∀ j b, (matrix j b).PosSemidef
  domination : ∀ j b, (matrix j b - allocatedMatrix j b).PosSemidef
  source_identity : ∀ j, interfacePolynomial Pinned.order7.potential j.val -
    ∑ b, (block j b).original ∈ relations
  tensor_identity : ∀ j b, (∑ a, (block j a).allocated) - C (credit j : ℂ) -
    tensorMixed degree (residual j b) (coord b) ∈ relations
  tensor_nonneg : ∀ j b, ¬ Excluded j b → ∀ k, 0 ≤ residual j b k

def certificate (h : NumericalChecks) (j : Fin 4) (b : Box) (hb : ¬ Excluded j b) :
    InterfaceCertificate Pinned.order7.potential j.val (credit j) where
  blockCount := 134
  blocks := block j
  degree := degree
  coeff := residual j b
  coord := coord b
  matrices := fun a => {
    psd := h.source_psd j a
    domination := fun _ => h.domination j a
    nonneg := fun _ => by change (0 : ℚ) ≤ 1; norm_num
    budget := by change (∑ _ : Fin 1, (1 : ℚ)) ≤ 1; norm_num }
  source := h.source_identity j
  residual := h.tensor_identity j b
  nonneg := h.tensor_nonneg j b hb

/-- Closed boxes cover both endpoints, including population exactly one. -/
theorem grid_cover {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    ∃ i : Fin 64, p ∈ Set.Icc (lo i : ℝ) (hi i : ℝ) := by
  by_cases h1 : p = 1
  · subst p
    exact ⟨63, by norm_num [lo, hi]⟩
  have hp0 : 0 ≤ 64*p := mul_nonneg (by norm_num) hp.1
  have hp1 : p < 1 := lt_of_le_of_ne hp.2 h1
  have hn : ⌊64*p⌋₊ < 64 := (Nat.floor_lt hp0).mpr (by norm_num; linarith)
  refine ⟨⟨⌊64*p⌋₊, hn⟩, ?_, ?_⟩
  · have h := Nat.floor_le hp0
    simp only [lo, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat]
    linarith
  · have h := Nat.lt_floor_add_one (64*p)
    simp only [hi, Rat.cast_div, Rat.cast_add, Rat.cast_natCast, Rat.cast_one, Rat.cast_ofNat]
    linarith

def InBox (x : State) (b : Box) : Prop :=
  ‖r1 x‖^2 ∈ Set.Icc (lo b.1 : ℝ) (hi b.1 : ℝ) ∧
  ‖r2 x‖^2 ∈ Set.Icc (lo b.2 : ℝ) (hi b.2 : ℝ)

theorem population_cover {x : State} (hx : x ∈ Xset) : ∃ b : Box, InBox x b := by
  obtain ⟨a, ha⟩ := grid_cover (p := ‖r1 x‖^2)
    ⟨sq_nonneg _, by nlinarith [norm_r1_le_one hx, norm_nonneg (r1 x)]⟩
  obtain ⟨b, hb⟩ := grid_cover (p := ‖r2 x‖^2)
    ⟨sq_nonneg _, by nlinarith [norm_r2_le_one hx, norm_nonneg (r2 x)]⟩
  exact ⟨(a,b), ha, hb⟩

theorem retained {γ : ActivePulse} (s : Crossings γ)
    (hcap : γ.exposure ≤ 733/250) (j : Fin 4) (b : Box)
    (hb : InBox (γ.traj (s.time (j.val+1))) b) : ¬ Excluded j b := by
  intro hex
  have hs := s.mem (j.val+1) (by omega)
  have hlevel := s.level j.val j.isLt
  rw [γ.traj_eq hs] at hb
  exact population_box_excludes 64 γ hs hcap hlevel.ge hlevel.le
    (by unfold lo; positivity) (by unfold lo; positivity) hb.1.1 hb.2.1 hex

def point (x : State) (b : Box) : Fin 3 → ℝ :=
  ![0,64*(‖r1 x‖^2-lo b.1),64*(‖r2 x‖^2-lo b.2)]

theorem point_mem {x : State} {b : Box} (hb : InBox x b) (i : Fin 3) :
    point x b i ∈ Set.Icc (0 : ℝ) 1 := by
  rcases hb with ⟨⟨h1,h2⟩,⟨h3,h4⟩⟩
  simp only [lo, hi, Rat.cast_div, Rat.cast_add, Rat.cast_natCast,
    Rat.cast_one, Rat.cast_ofNat] at h1 h2 h3 h4 ⊢
  fin_cases i <;> simp [point, lo] <;> constructor <;> linarith

theorem eval_coord (x : State) (b : Box) (i : Fin 3) :
    eval (mixedPoint 0 x 1) (coord b i) = (point x b i : ℂ) := by
  fin_cases i <;> simp [coord, point, mixedPoint, Complex.mul_conj,
    Complex.normSq_eq_norm_sq]

/-- No box membership or box-selection oracle is an external input. -/
theorem crossing_credit (h : NumericalChecks) {γ : ActivePulse} (s : Crossings γ)
    (hcap : γ.exposure ≤ 733/250) (j : Fin 4) :
    (credit j : ℝ) ≤ interfaceSlack Pinned.order7.potential j.val
      (γ.traj (s.time (j.val+1))) := by
  have hs := s.mem (j.val+1) (by omega)
  have hx : γ.traj (s.time (j.val+1)) ∈ Xset := by
    rw [γ.traj_eq hs]; exact γ.x_mem _ hs
  obtain ⟨b, hb⟩ := population_cover hx
  exact s.credit j.isLt (certificate h j b (retained s hcap j b hb))
    (point _ b) (point_mem hb) (eval_coord _ b)

theorem credited_telescope (h : NumericalChecks) {γ : ActivePulse} (s : Crossings γ)
    (hcap : γ.exposure ≤ 733/250) :
    (∑ j ∈ Finset.range 5, ∫ z in s.time j..s.time (j+1),
      occupationSlack Pinned.partition Pinned.order7.ceiling Pinned.order7.potential γ j z) +
    (∑ j : Fin 4, (credit j : ℝ)) +
    evalCell (cellXi Pinned.partition Pinned.order7.ceiling γ 4 γ.S) (γ.traj γ.S)
      (Pinned.order7.potential 4) -
    evalCell 0 (γ.traj 0) (Pinned.order7.potential 0) ≤ γ.exposure := by
  have hb := Finset.sum_le_sum (s := Finset.univ) (fun j _ => crossing_credit h s hcap j)
  rw [Fin.sum_univ_eq_sum_range
    (fun j => interfaceSlack Pinned.order7.potential j (γ.traj (s.time (j+1)))) 4] at hb
  linarith [s.telescope Pinned.order7.potential]

end
end LowerBoundCZ.Certification.PinnedInterface
