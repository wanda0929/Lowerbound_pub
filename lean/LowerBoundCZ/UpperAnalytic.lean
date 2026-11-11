import LowerBoundCZ.CertificateContracts
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Star
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Analytic properties of the actual finite upper-certificate recurrence.
No certificate validity, successful pulse, or physical bound is assumed. -/
noncomputable section
namespace LowerBoundCZ.Certification.Upper
open Complex CZExposure Set

@[local fun_prop] private theorem ofReal_diff : Differentiable ℝ (Complex.ofReal) :=
  Complex.ofRealCLM.differentiable
@[local fun_prop] private theorem re_diff : Differentiable ℝ Complex.re :=
  Complex.reCLM.differentiable
@[local fun_prop] private theorem im_diff : Differentiable ℝ Complex.im :=
  Complex.imCLM.differentiable

private def SmoothRecord (z : Parameters → SectorRecord) : Prop :=
  Differentiable ℝ (fun p => (z p).ground) ∧
  Differentiable ℝ (fun p => (z p).rydberg) ∧
  Differentiable ℝ (fun p => (z p).population)

private theorem segment_smooth (k : ℕ) (dt ph : Parameters → ℝ)
    (z : Parameters → SectorRecord) (ht : Differentiable ℝ dt)
    (hp : Differentiable ℝ ph) (hz : SmoothRecord z) :
    SmoothRecord (fun p => segment k (dt p) (ph p) (z p)) := by
  rcases hz with ⟨hg, hr, he⟩
  unfold SmoothRecord segment
  dsimp only
  simp only [Complex.mk_eq_add_mul_I]
  constructor
  · fun_prop
  constructor
  · fun_prop
  · simp only [Complex.normSq_apply]
    fun_prop

theorem phase_differentiable (fixed : Fin 12672 → ℝ) (j : Fin 12672) :
    Differentiable ℝ (fun p => phase fixed p j) := by
  unfold phase
  split_ifs <;> fun_prop

private theorem propagate_smooth (fixed : Fin 12672 → ℝ) (k : ℕ) :
    SmoothRecord (fun p => propagate fixed p k) := by
  have hf (l : List (Fin 12672)) (z : Parameters → SectorRecord) (hz : SmoothRecord z) :
      SmoothRecord (fun p => l.foldl
        (fun q j => segment k (p 0 / 12672) (phase fixed p j) q) (z p)) := by
    induction l generalizing z with
    | nil => exact hz
    | cons j l ih =>
      exact ih _ (segment_smooth k _ _ z (by fun_prop) (phase_differentiable fixed j) hz)
  exact hf _ _ ⟨by fun_prop, by fun_prop, by fun_prop⟩

private theorem cross_differentiable (a b : Parameters → ℂ)
    (ha : Differentiable ℝ a) (hb : Differentiable ℝ b) :
    Differentiable ℝ (fun p => (b p * star (a p * a p)).im) := by
  fun_prop

theorem residual_differentiable (fixed : Fin 12672 → ℝ) :
    Differentiable ℝ (residual fixed) := by
  have ha := propagate_smooth fixed 1
  have hb := propagate_smooth fixed 2
  rcases ha with ⟨hag, har, hae⟩
  rcases hb with ⟨hbg, hbr, hbe⟩
  apply differentiable_pi.mpr
  intro i
  fin_cases i
  · exact re_diff.comp har
  · exact im_diff.comp har
  · exact re_diff.comp hbr
  · exact im_diff.comp hbr
  · exact cross_differentiable _ _ hag hbg

def newton (a : Payload) (p : Parameters) : Parameters := p - a.inverse (residual a.fixed p)

theorem newton_hasFDerivAt (a : Payload) (p : Parameters) :
    HasFDerivAt (newton a)
      (ContinuousLinearMap.id ℝ Parameters - a.inverse.comp (fderiv ℝ (residual a.fixed) p)) p :=
  (hasFDerivAt_id p).sub
    (a.inverse.hasFDerivAt.comp p (residual_differentiable a.fixed p).hasFDerivAt)

private theorem coordinate_mean_value (g : Parameters → Parameters) (D : Parameters → LinearMap)
    (hd : ∀ p, HasFDerivAt g (D p) p) (x y : Parameters) (i : Fin 5) :
    ∃ t ∈ Ioo (0 : ℝ) 1,
      (g y - g x) i = (D (AffineMap.lineMap x y t) (y - x)) i := by
  let f := fun t : ℝ => g (AffineMap.lineMap x y t) i
  have hf (t : ℝ) : HasDerivAt f (D (AffineMap.lineMap x y t) (y - x) i) t := by
    exact (ContinuousLinearMap.proj i : Parameters →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t
      ((hd _).comp_hasDerivAt t AffineMap.hasDerivAt_lineMap)
  obtain ⟨t, ht, he⟩ := exists_hasDerivAt_eq_slope f _ (by norm_num : (0 : ℝ) < 1)
    (fun t _ => (hf t).continuousAt.continuousWithinAt) (fun t _ => hf t)
  exact ⟨t, ht, by simpa [f] using he.symm⟩

theorem Checks.newton_mapsTo {a : Payload} (h : Checks a) :
    MapsTo (newton a) (Metric.closedBall a.center a.radius)
      (Metric.closedBall a.center a.radius) := by
  intro p hp
  rw [Metric.mem_closedBall, dist_eq_norm]
  apply (pi_norm_le_iff_of_nonneg h.radius_pos.le).mpr
  intro i
  obtain ⟨t, ht, he⟩ := coordinate_mean_value (newton a) _ (newton_hasFDerivAt a) a.center p i
  have htbox : AffineMap.lineMap a.center p t ∈ Metric.closedBall a.center a.radius :=
    (convex_closedBall a.center a.radius).segment_subset
      (Metric.mem_closedBall_self h.radius_pos.le) hp
      ((openSegment_subset_segment ℝ a.center p) (lineMap_mem_openSegment ℝ a.center p ht))
  have hk := h.krawczyk_interior p hp _ (h.jacobian_enclosure _ htbox)
  rw [Metric.mem_ball, dist_eq_norm] at hk
  have hi := (norm_le_pi_norm _ i).trans hk.le
  convert hi using 1
  congr 1
  simp only [Pi.sub_apply, Pi.add_apply, newton] at he ⊢
  linarith

/-- The contraction is restricted to the certified closed box, not all parameter space. -/
theorem Checks.newton_lipschitz {a : Payload} (h : Checks a) :
    LipschitzOnWith ⟨a.contraction, h.contraction_nonneg⟩ (newton a)
      (Metric.closedBall a.center a.radius) := by
  apply Convex.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
    (fun p _ => (newton_hasFDerivAt a p).hasFDerivWithinAt)
  · intro p hp
    exact h.defect_bound _ (h.jacobian_enclosure p hp)
  · exact convex_closedBall _ _

/-- The defect bound already guarantees the approximate inverse is injective;
no separate invertibility certificate is necessary. -/
theorem Checks.inverse_injective {a : Payload} (h : Checks a) :
    Function.Injective a.inverse := by
  let A := fderiv ℝ (residual a.fixed) a.center
  have hb := h.defect_bound A
    (h.jacobian_enclosure a.center (Metric.mem_closedBall_self h.radius_pos.le))
  let D := ContinuousLinearMap.id ℝ Parameters - a.inverse.comp A
  have hinj : Function.Injective (a.inverse.comp A) := by
    intro x y hxy
    have hz : D (x-y) = x-y := by
      change (x-y) - (a.inverse.comp A) (x-y) = x-y
      rw [map_sub, hxy, sub_self, sub_zero]
    have hn := (D.le_opNorm (x-y)).trans
      (mul_le_mul_of_nonneg_right hb (norm_nonneg (x-y)))
    rw [hz] at hn
    have he : ‖x-y‖ = 0 := by
      nlinarith [norm_nonneg (x-y), h.contraction_lt_one]
    exact sub_eq_zero.mp (norm_eq_zero.mp he)
  have hs : Function.Surjective (a.inverse.comp A) :=
    (LinearMap.injective_iff_surjective (f := (a.inverse.comp A).toLinearMap)).mp hinj
  apply (LinearMap.injective_iff_surjective (f := a.inverse.toLinearMap)).mpr
  intro y
  obtain ⟨x, hx⟩ := hs y
  exact ⟨A x, hx⟩

/-- Numerical inclusions produce an actual zero; root existence is not an input. -/
theorem Checks.exists_root {a : Payload} (h : Checks a) :
    ∃ p ∈ Metric.closedBall a.center a.radius, residual a.fixed p = 0 := by
  let s := Metric.closedBall a.center a.radius
  have hm := h.newton_mapsTo
  have hc : ContractingWith ⟨a.contraction, h.contraction_nonneg⟩
      (hm.restrict (newton a) s s) := by
    refine ⟨h.contraction_lt_one, ?_⟩
    rw [lipschitzWith_iff_dist_le_mul]
    intro p q
    exact h.newton_lipschitz.dist_le_mul p p.property q q.property
  obtain ⟨p, hp, he, _⟩ := hc.exists_fixedPoint' Metric.isClosed_closedBall.isComplete hm
    (Metric.mem_closedBall_self h.radius_pos.le) (edist_ne_top _ _)
  refine ⟨p, hp, h.inverse_injective ?_⟩
  have hn : p - a.inverse (residual a.fixed p) = p := he
  rw [map_zero]
  exact sub_eq_self.mp hn

end LowerBoundCZ.Certification.Upper
