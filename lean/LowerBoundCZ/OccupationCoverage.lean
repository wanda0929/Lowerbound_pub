import LowerBoundCZ.OccupationLedger
import LowerBoundCZ.PinnedRegions
import LowerBoundCZ.CoverageData

/-! Fixed closed-box coverage and the Bernstein-to-ledger correspondence.
Only finite data identities/tests are external inputs. Physical box selection,
exclusion and coordinate substitution are proved here. Mandatory-prefix
existence is intentionally still a separate analytic obligation. -/
noncomputable section
namespace LowerBoundCZ.Certification.OccupationCoverage
open CZExposure Slack MvPolynomial Set OccupationLedger

abbrev Slot := Fin 321
abbrev BoxIndex := Fin 16
@[irreducible] def grid (i : Slot) : Nat := CoverageData.grids[i.val]?.getD 0
@[irreducible] def kind (i : Slot) : Nat := CoverageData.kinds[i.val]?.getD 0
@[irreducible] def code (i : Slot) (x y : BoxIndex) : Nat :=
  (AllocationCodec.naturals (CoverageData.boxes[i.val]?.getD ""))[x.val*grid i+y.val]?.getD 0
def low (i : Slot) (x : BoxIndex) : ℚ := (x.val : ℚ)/grid i
def high (i : Slot) (x : BoxIndex) : ℚ := (x.val+1 : ℚ)/grid i
def cell (i : Slot) : Nat := min (i.val/64) 4
@[irreducible] def profile (i : Slot) := RegionalData.profiles[i.val]?.getD (0,"0","0","")
def loXi (i : Slot) : ℚ := AllocationCodec.rational (profile i).2.1
def hiXi (i : Slot) : ℚ := AllocationCodec.rational (profile i).2.2.1
def beta (i : Slot) (k : Fin 15) : ℚ :=
  (AllocationCodec.rationals (profile i).2.2.2)[k.val]?.getD 0

def selected (i : Slot) (x y : BoxIndex) : AllocationRegion :=
  if code i x y ≤ 1024 then
    PinnedAllocation.region ⟨(code i x y-1)%1024, Nat.mod_lt _ (by decide)⟩
  else PinnedRegion.region ⟨(code i x y-1025)%9728, Nat.mod_lt _ (by decide)⟩

def Excluded (i : Slot) (x y : BoxIndex) : Prop :=
  let R : ℝ := min (right i.val) (733/250-left i.val)
  if kind i = 1 then PopulationBoxExcluded 8 (low i x) (low i y) R
  else if kind i = 2 then DarkBoxExcluded (low i x) (high i x) (low i y) (high i y) R
  else False

def energyQ (p : ℚ) : ℚ :=
  p^3*(∑ k ∈ Finset.range 9, 3*barrierCoeff k/(2*k+3)*p^k)^2
def radiusQ (i : Slot) : ℚ := min (right i.val) (733/250-left i.val)
def excludedQ (i : Slot) (x y : BoxIndex) : Bool :=
  if kind i = 1 then
    let A := 8*energyQ (low i x)
    let D := energyQ (low i y)
    let T := 72*(radiusQ i)^2
    decide (T < A+D ∨ (T-A-D)^2 < 4*A*D)
  else if kind i = 2 then
    let a := low i x; let b := high i x; let c := low i y; let d := high i y
    let test := fun A B => B < A ∧ 0 < A+B-(radiusQ i)^2/2 ∧ 4*A*B < (A+B-(radiusQ i)^2/2)^2
    decide (test ((1-b)*c) (2*(1-c)*b) ∨ test (2*(1-d)*a) ((1-a)*d))
  else false

theorem excludedQ_iff (i : Slot) (x y : BoxIndex) : excludedQ i x y = true ↔ Excluded i x y := by
  have hr : (radiusQ i : ℝ) = min (right i.val : ℝ) (733/250-left i.val) := by
    simp [radiusQ]
  have hp : (energyQ (low i x) : ℝ) = barrierEnergy 8 (low i x) := (barrierEnergy_rat 8 _).symm
  have hq : (energyQ (low i y) : ℝ) = barrierEnergy 8 (low i y) := (barrierEnergy_rat 8 _).symm
  unfold excludedQ Excluded
  split_ifs
  · simp only [decide_eq_true_eq, PopulationBoxExcluded]
    rw [← hr, ← hp, ← hq]
    norm_cast
  · simp only [decide_eq_true_eq, DarkBoxExcluded]
    rw [← hr]
    norm_cast
  · simp

def ratePolynomial (i : Slot) : MvPolynomial Unit ℝ :=
  ∑ k : Fin 15, C (beta i k : ℝ) * C (Nat.choose 14 k.val : ℝ) *
    X ()^k.val * (1-X ())^(14-k.val)

def powerPolynomial (i : Slot) : MvPolynomial Unit ℝ :=
  ∑ k : Fin 15, C (power i.val k : ℝ) * X ()^k.val

theorem primitive_derivative (i : Slot) :
    pderiv () (primitive i.val) = powerPolynomial i := by
  classical
  simp only [primitive, powerPolynomial, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp only [Derivation.leibniz, pderiv_C, smul_eq_mul, mul_zero, add_zero, pderiv_pow,
    pderiv_X_self, mul_one, Nat.add_sub_cancel, primitiveCoefficient,
    Rat.cast_div, Rat.cast_add, Rat.cast_natCast, Rat.cast_one, Nat.cast_add, Nat.cast_one]
  have he : ((k.val : MvPolynomial Unit ℝ)+1) = C ((k.val : ℝ)+1) := by simp
  have hn : (k.val : ℝ)+1 ≠ 0 := by positivity
  rw [← mul_assoc, he, ← map_mul, div_mul_cancel₀ _ hn]

/-- Fixed rational table/geometry and finite polynomial coefficient checks.
No assertion about trajectories, box coverage or integrated slack is a field. -/
structure DataChecks : Prop where
  grids : ∀ i, 0 < grid i ∧ grid i ≤ 16
  widths : ∀ i, loXi i < hiXi i
  local_bounds : ∀ i, 0 ≤ loXi i ∧ hiXi i ≤ 1
  endpoints : ∀ i,
    (left i.val : ℝ) = Pinned.order7.ceiling *
      (Pinned.partition.a (cell i) + Pinned.partition.width (cell i)*loXi i) ∧
    (right i.val : ℝ) = Pinned.order7.ceiling *
      (Pinned.partition.a (cell i) + Pinned.partition.width (cell i)*hiXi i)
  coefficients : ∀ i, powerPolynomial i = ratePolynomial i
  assignments : ∀ i x y, x.val < grid i → y.val < grid i → code i x y ≠ 0 →
    (selected i x y).cell.val = cell i ∧
    (selected i x y).lo = ![loXi i, low i x, low i y] ∧
    (selected i x y).hi = ![hiXi i, high i x, high i y] ∧
    (selected i x y).delta = beta i
  discarded : ∀ i x y, x.val < grid i → y.val < grid i → code i x y = 0 → excludedQ i x y = true

theorem cell_lt (i : Slot) : cell i < 5 := by
  have := Nat.min_le_right (i.val/64) 4
  unfold cell; omega

/-- Closed coverage includes p=0, p=1 and either side of every grid edge. -/
theorem grid_cover {n : Nat} (hn : 0 < n) (hn16 : n ≤ 16) {p : ℝ}
    (hp : p ∈ Icc (0 : ℝ) 1) :
    ∃ x : BoxIndex, x.val < n ∧ p ∈ Icc ((x.val : ℝ)/n) ((x.val+1 : ℝ)/n) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  by_cases h1 : p = 1
  · subst p
    refine ⟨⟨n-1, by omega⟩, ?_, ?_, ?_⟩
    · change n-1 < n; omega
    · apply (div_le_one hnR).mpr
      exact_mod_cast Nat.sub_le n 1
    · have he : ((n-1 : Nat) : ℝ)+1 = n := by exact_mod_cast Nat.sub_add_cancel (by omega : 1 ≤ n)
      rw [he, div_self hnR.ne']
  have hp0 : 0 ≤ (n : ℝ)*p := mul_nonneg hnR.le hp.1
  have hp1 : p < 1 := lt_of_le_of_ne hp.2 h1
  have hk : ⌊(n : ℝ)*p⌋₊ < n := (Nat.floor_lt hp0).mpr (by nlinarith)
  refine ⟨⟨⌊(n : ℝ)*p⌋₊, by omega⟩, hk, ?_, ?_⟩
  · apply (div_le_iff₀ hnR).mpr
    simpa [mul_comm] using Nat.floor_le hp0
  · apply (le_div_iff₀ hnR).mpr
    have := Nat.lt_floor_add_one ((n : ℝ)*p)
    nlinarith

theorem not_excluded (h : DataChecks) (i : Slot) (x y : BoxIndex)
    (hx : x.val < grid i) (hy : y.val < grid i)
    (γ : ActivePulse) {s : ℝ} (hs : s ∈ Icc 0 γ.S) (hcap : γ.exposure ≤ 733/250)
    (hc : γ.cumI s ∈ Icc (left i.val : ℝ) (right i.val : ℝ))
    (hp : ‖r1 (γ.traj s)‖^2 ∈ Icc (low i x : ℝ) (high i x : ℝ))
    (hq : ‖r2 (γ.traj s)‖^2 ∈ Icc (low i y : ℝ) (high i y : ℝ)) :
    ¬ Excluded i x y := by
  rw [γ.traj_eq hs] at hp hq
  have ha : (0 : ℝ) ≤ low i x := by unfold low; positivity
  have hc0 : (0 : ℝ) ≤ low i y := by unfold low; positivity
  have hn : (0 : ℝ) < grid i := by exact_mod_cast (h.grids i).1
  have hb : (high i x : ℝ) ≤ 1 := by
    simp only [high, Rat.cast_div, Rat.cast_add, Rat.cast_natCast, Rat.cast_one]
    apply (div_le_one hn).mpr; exact_mod_cast (by omega : x.val+1 ≤ grid i)
  have hd : (high i y : ℝ) ≤ 1 := by
    simp only [high, Rat.cast_div, Rat.cast_add, Rat.cast_natCast, Rat.cast_one]
    apply (div_le_one hn).mpr; exact_mod_cast (by omega : y.val+1 ≤ grid i)
  unfold Excluded
  split_ifs with h1 h2
  · exact fun he => population_box_excludes 8 γ hs hcap hc.1 hc.2 ha hc0 hp.1 hq.1 he
  · exact fun he => dark_box_excludes γ hs hcap hc.1 hc.2 ha hb hc0 hd hp hq he
  · exact not_false

/-- Actual states select a retained fixed box; no box-choice oracle is used. -/
theorem retained_cover (h : DataChecks) (i : Slot) (γ : ActivePulse) {s : ℝ}
    (hs : s ∈ Icc 0 γ.S) (hcap : γ.exposure ≤ 733/250)
    (hc : γ.cumI s ∈ Icc (left i.val : ℝ) (right i.val : ℝ)) :
    ∃ x y : BoxIndex, x.val < grid i ∧ y.val < grid i ∧ code i x y ≠ 0 ∧
      ‖r1 (γ.traj s)‖^2 ∈ Icc (low i x : ℝ) (high i x : ℝ) ∧
      ‖r2 (γ.traj s)‖^2 ∈ Icc (low i y : ℝ) (high i y : ℝ) := by
  have hstate : γ.traj s ∈ Xset := by rw [γ.traj_eq hs]; exact γ.x_mem s hs
  obtain ⟨x, hx, hp⟩ := grid_cover (h.grids i).1 (h.grids i).2
    (p := ‖r1 (γ.traj s)‖^2)
    ⟨sq_nonneg _, by nlinarith [norm_r1_le_one hstate, norm_nonneg (r1 (γ.traj s))]⟩
  obtain ⟨y, hy, hq⟩ := grid_cover (h.grids i).1 (h.grids i).2
    (p := ‖r2 (γ.traj s)‖^2)
    ⟨sq_nonneg _, by nlinarith [norm_r2_le_one hstate, norm_nonneg (r2 (γ.traj s))]⟩
  have hp' : ‖r1 (γ.traj s)‖^2 ∈ Icc (low i x : ℝ) (high i x : ℝ) := by
    simpa [low, high] using hp
  have hq' : ‖r2 (γ.traj s)‖^2 ∈ Icc (low i y : ℝ) (high i y : ℝ) := by
    simpa [low, high] using hq
  exact ⟨x,y,hx,hy,fun hz => not_excluded h i x y hx hy γ hs hcap hc hp' hq'
    ((excludedQ_iff i x y).mp (h.discarded i x y hx hy hz)),hp',hq'⟩

theorem xi_mem (h : DataChecks) (i : Slot) (γ : ActivePulse) {s : ℝ}
    (hc : γ.cumI s ∈ Icc (left i.val : ℝ) (right i.val : ℝ)) :
    cellXi Pinned.partition Pinned.order7.ceiling γ (cell i) s ∈
      Icc (loXi i : ℝ) (hiXi i : ℝ) := by
  have hU : (0 : ℝ) < Pinned.order7.ceiling := by norm_num [Pinned.order7]
  have hw := Pinned.partition.width_pos (j := cell i) (cell_lt i)
  rw [(h.endpoints i).1, (h.endpoints i).2] at hc
  constructor
  · apply (le_div_iff₀ hw).mpr
    have := (le_div_iff₀ hU).mpr (show
      (Pinned.partition.a (cell i)+Pinned.partition.width (cell i)*(loXi i : ℝ))*
        Pinned.order7.ceiling ≤ γ.cumI s by nlinarith [hc.1])
    nlinarith
  · apply (div_le_iff₀ hw).mpr
    have := (div_le_iff₀ hU).mpr (show γ.cumI s ≤
      (Pinned.partition.a (cell i)+Pinned.partition.width (cell i)*(hiXi i : ℝ))*
        Pinned.order7.ceiling by nlinarith [hc.2])
    nlinarith

theorem normalized_coordinate (h : DataChecks) (i : Slot) (γ : ActivePulse) (s : ℝ) :
    (cellXi Pinned.partition Pinned.order7.ceiling γ (cell i) s-loXi i)/(hiXi i-loXi i) =
      (γ.cumI s-left i.val)/(right i.val-left i.val) := by
  have hU : Pinned.order7.ceiling ≠ 0 := by norm_num [Pinned.order7]
  have hw := ne_of_gt (Pinned.partition.width_pos (j := cell i) (cell_lt i))
  have hd : (hiXi i : ℝ)-(loXi i : ℝ) ≠ 0 := ne_of_gt (sub_pos.mpr (Rat.cast_lt.mpr (h.widths i)))
  rw [(h.endpoints i).1, (h.endpoints i).2]
  unfold cellXi
  have he : Pinned.order7.ceiling * (Pinned.partition.a (cell i)+Pinned.partition.width (cell i)*hiXi i) -
      Pinned.order7.ceiling * (Pinned.partition.a (cell i)+Pinned.partition.width (cell i)*loXi i) =
      Pinned.order7.ceiling * Pinned.partition.width (cell i)*((hiXi i : ℝ)-loXi i) := by ring
  rw [he]
  field_simp
  ring

theorem selected_checks (ha : PinnedAllocation.NumericalChecks) (hr : PinnedRegion.NumericalChecks)
    (i : Slot) (x y : BoxIndex) : (selected i x y).Checks := by
  unfold selected
  split_ifs
  · exact PinnedAllocation.checks ha _
  · exact PinnedRegion.checks hr _

theorem rate_eq_derivative (h : DataChecks) (i : Slot) (x y : BoxIndex)
    (hx : x.val < grid i) (hy : y.val < grid i) (hz : code i x y ≠ 0)
    (γ : ActivePulse) (s : ℝ) :
    (selected i x y).rate (cellXi Pinned.partition Pinned.order7.ceiling γ (cell i) s) =
      eval (fun _ : Unit => (γ.cumI s-left i.val)/(right i.val-left i.val))
        (pderiv () (primitive i.val)) := by
  obtain ⟨_, hlo, hhi, hbeta⟩ := h.assignments i x y hx hy hz
  rw [primitive_derivative i, h.coefficients i]
  simp only [AllocationRegion.rate, hlo, hhi, hbeta, Matrix.cons_val_zero,
    ratePolynomial, map_sum, map_mul, eval_C, eval_pow, eval_X, map_sub, map_one]
  rw [normalized_coordinate h i γ s]

theorem pointwise_slack (h : DataChecks) (ha : PinnedAllocation.NumericalChecks)
    (hr : PinnedRegion.NumericalChecks) (i : Slot) (γ : ActivePulse) {s : ℝ}
    (hs : s ∈ Icc 0 γ.S) (hcap : γ.exposure ≤ 733/250)
    (hc : γ.cumI s ∈ Icc (left i.val : ℝ) (right i.val : ℝ)) :
    eval (fun _ : Unit => (γ.cumI s-left i.val)/(right i.val-left i.val))
      (pderiv () (primitive i.val)) * cost (γ.traj s) ≤
      occupationSlack Pinned.partition Pinned.order7.ceiling Pinned.order7.potential γ (cell i) s := by
  obtain ⟨x,y,hx,hy,hz,hp,hq⟩ := retained_cover h i γ hs hcap hc
  obtain ⟨hcell,hlo,hhi,_⟩ := h.assignments i x y hx hy hz
  have hxi := xi_mem h i γ hc
  have hxi01 : cellXi Pinned.partition Pinned.order7.ceiling γ (cell i) s ∈ Icc (0 : ℝ) 1 :=
    ⟨(Rat.cast_nonneg.mpr (h.local_bounds i).1).trans hxi.1,
      hxi.2.trans (by exact_mod_cast (h.local_bounds i).2)⟩
  have hbox : ∀ k,
      ![cellXi Pinned.partition Pinned.order7.ceiling γ (selected i x y).cell.val s,
        ‖r1 (γ.traj s)‖^2, ‖r2 (γ.traj s)‖^2] k ∈
        Icc ((selected i x y).lo k : ℝ) ((selected i x y).hi k : ℝ) := by
    intro k
    rw [hcell, hlo, hhi]
    fin_cases k
    · exact hxi
    · exact hp
    · exact hq
  have hb := (selected i x y).trajectory_slack (selected_checks ha hr i x y) γ hs
    (by simpa only [hcell] using hxi01) hbox
  rw [← rate_eq_derivative h i x y hx hy hz γ s]
  simpa only [hcell] using hb

/-- The ledger's local-inequality premise is discharged for every profile,
including replacements. Only the mandatory-prefix traversal remains analytic. -/
theorem credited_telescope (h : DataChecks) (ha : PinnedAllocation.NumericalChecks)
    (hr : PinnedRegion.NumericalChecks) (A : GramBridge.Archive Pinned.order7)
    (hmatrix : GramBridge.MatrixChecks A) (hinterface : PinnedInterface.NumericalChecks)
    {γ : ActivePulse} (s : Crossings γ) (hcap : γ.exposure ≤ 733/250) (a : Traversal γ s) :
    (totalCredit : ℝ) + (∑ j : Fin 4, (PinnedInterface.credit j : ℝ)) +
    evalCell (cellXi Pinned.partition Pinned.order7.ceiling γ 4 γ.S) (γ.traj γ.S)
      (Pinned.order7.potential 4) -
    evalCell 0 (γ.traj 0) (Pinned.order7.potential 0) ≤ γ.exposure := by
  apply OccupationLedger.credited_telescope A hmatrix hinterface s hcap a
  intro j hj k hk t ht
  let i : Slot := ⟨64*j+k, index_lt hj hk⟩
  have hi : cell i = j := by
    simp only [cell, i]
    simp only [count] at hk
    split_ifs at hk <;> omega
  have ht' : t ∈ Icc 0 γ.S :=
    ⟨(a.mem j hj k (by omega)).1.trans ht.1, ht.2.trans (a.mem j hj (k+1) (by omega)).2⟩
  have hc : γ.cumI t ∈ Icc (left i.val : ℝ) (right i.val : ℝ) := by
    constructor
    · rw [show (left i.val : ℝ) = γ.cumI (a.time j k) from (a.exposure_left j hj k hk).symm]
      exact γ.cumI_mono (a.mem j hj k (by omega)).1 ht.1 ht'.2
    · rw [show (right i.val : ℝ) = γ.cumI (a.time j (k+1)) from (a.exposure_right j hj k hk).symm]
      exact γ.cumI_mono ht'.1 ht.2 (a.mem j hj (k+1) (by omega)).2
  simpa only [hi] using pointwise_slack h ha hr i γ ht' hcap hc

end LowerBoundCZ.Certification.OccupationCoverage
