module
public import RequestProject.AppendixE.PulseExpansion
public import RequestProject.AppendixE.RootRegularity

/-! Signed root reparameterization of actual pulse words. The negative
branch uses the inverse word, including for even bracket orders. -/
@[expose] public section
noncomputable section
namespace CZExposure.SignedRootPulse
open PulseWords PulseExpansion RootRegularity

def curve (w : Word) (k : ℕ) (s : ℝ) : End :=
  if 0 ≤ s then op w (root (k : ℝ)⁻¹ s)
  else op (inv w) (root (k : ℝ)⁻¹ s)

theorem root_pow (k : ℕ) (hk : k ≠ 0) (s : ℝ) :
    (root (k : ℝ)⁻¹ s) ^ k = |s| :=
  Real.rpow_inv_natCast_pow (abs_nonneg s) hk

theorem curve_regular {w : Word} {k : ℕ} {B : End}
    (hk : k ≠ 0) (h : Expanded w k B) :
    ContDiff ℝ 1 (curve w k) ∧ HasDerivAt (curve w k) B 0 := by
  obtain ⟨C, hC, hC0, heq⟩ := h
  let D : ℝ → End := fun t => op (inv w) t * C t
  have hC1 : ContDiff ℝ 1 C :=
    contDiff_iff_contDiffAt.mpr fun t => (hC t).contDiffAt
  have hD1 : ContDiff ℝ 1 D :=
    (contDiff_iff_contDiffAt.mpr fun t => (op_analytic (inv w) t).contDiffAt).mul hC1
  have hD0 : D 0 = B := by simp [D, op_zero, hC0]
  have ha : 0 < (k : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero hk)
  have hi (t : ℝ) : op (inv w) t = 1 - t ^ k • D t := by
    have hh := op_inv w t
    rw [heq, mul_add, mul_one, mul_smul_comm] at hh
    exact eq_sub_of_add_eq hh
  have hc : curve w k = fun s =>
      1 + glue (weighted (k : ℝ)⁻¹ C) (weighted (k : ℝ)⁻¹ D) s := by
    funext s
    by_cases hs : 0 ≤ s
    · simp only [curve, glue, if_pos hs, weighted, heq, root_pow k hk,
        abs_of_nonneg hs]
    · simp only [curve, glue, if_neg hs, weighted, hi, root_pow k hk,
        abs_of_neg (lt_of_not_ge hs)]
      module
  rw [hc]
  constructor
  · exact contDiff_const.add (glued_weighted_contDiff ha hC1 hD1 (hC0.trans hD0.symm))
  · have hd := glue_hasDeriv (weighted_hasDeriv ha hC1) (weighted_hasDeriv ha hD1)
      (by simp [weighted])
      (by simp [weightedDeriv, root_zero ha, hC0, hD0]) 0
    have hh := (hasDerivAt_const (0 : ℝ) (1 : End)).add hd
    simpa only [Pi.add_apply, glue, le_refl, if_true, weightedDeriv,
      root_zero ha, hC0, mul_zero, zero_smul, add_zero, zero_add] using hh

theorem orders_ne_zero (i : Fin 6) : orders i ≠ 0 := by
  fin_cases i <;> simp [orders]

theorem six_contDiff (i : Fin 6) : ContDiff ℝ 1 (curve (six i) (orders i)) :=
  (curve_regular (orders_ne_zero i) (six_expanded i)).1

theorem six_deriv_zero (i : Fin 6) :
    HasDerivAt (curve (six i) (orders i)) (leading i) 0 :=
  (curve_regular (orders_ne_zero i) (six_expanded i)).2

theorem six_state_deriv_zero (i : Fin 6) (x : State) :
    HasDerivAt (fun s => curve (six i) (orders i) s x) (ControlLie.bracketFields i x) 0 := by
  have h := (ContinuousLinearMap.apply ℝ State x).hasFDerivAt.comp_hasDerivAt 0
    (six_deriv_zero i)
  simpa only [ContinuousLinearMap.apply_apply, leading_field] using h

/-- Realization uses only the previously proved finite integral trajectories. -/
def physical (w : Word) (k : ℕ) (s : ℝ) (x : State) (hx : x ∈ Xset) :
    {P : PhysicalSegment // P.path 0 = x} :=
  if 0 ≤ s then run w (root (k : ℝ)⁻¹ s) x hx
  else run (inv w) (root (k : ℝ)⁻¹ s) x hx

theorem physical_terminal (w : Word) (k : ℕ) (s : ℝ) (x : State) (hx : x ∈ Xset) :
    (physical w k s x hx).val.path (physical w k s x hx).val.duration = curve w k s x := by
  by_cases hs : 0 ≤ s <;> simp [physical, curve, hs, run_terminal, op_apply]

theorem physical_duration (w : Word) (k : ℕ) (s : ℝ) (x : State) (hx : x ∈ Xset) :
    (physical w k s x hx).val.duration = w.length * root (k : ℝ)⁻¹ s := by
  have hr : 0 ≤ root (k : ℝ)⁻¹ s := Real.rpow_nonneg (abs_nonneg s) _
  by_cases hs : 0 ≤ s <;>
    simp [physical, hs, run_duration, inv, abs_of_nonneg hr]

theorem physical_unit (w : Word) (k : ℕ) (s : ℝ) (x : State) (hx : x ∈ Xset) :
    (physical w k s x hx).val.UnitControl := by
  unfold physical
  split <;> exact run_unit _ _ _ _

theorem six_zero (i : Fin 6) : curve (six i) (orders i) 0 = 1 := by
  have ha : 0 < (orders i : ℝ)⁻¹ :=
    inv_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero (orders_ne_zero i))
  simp [curve, root_zero ha, op_zero]

end CZExposure.SignedRootPulse
