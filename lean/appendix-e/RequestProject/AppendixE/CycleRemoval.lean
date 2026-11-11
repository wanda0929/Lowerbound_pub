module
public import RequestProject.AppendixE.ExposurePolarCurrent
public import RequestProject.AppendixE.VectorSubcurrent
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpOrder
public import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
public import Mathlib.MeasureTheory.VectorMeasure.Decomposition.RadonNikodym

/-! Boundary-preserving cycle removal in the Euclidean normal-current model.

Hilbert projection supplies a least-L²-norm density in the closed convex set
of densities between zero and one preserving all smooth compact boundary
tests. Any nonzero nonnegative cycle would contradict its optimality.
Radon--Nikodym representation and equality in the variation triangle
inequality show that every normal subcurrent is a density in the parent's
polar direction; thus the result excludes all normal cycles, not just a
previously specified family of densities. No arc decomposition is used. -/
@[expose] public section
noncomputable section
namespace CZExposure
open MeasureTheory Set
open scoped InnerProductSpace

namespace DensityCycleRemoval
variable {X I : Type*} [MeasurableSpace X] {μ : Measure X}

private theorem convex_interval (g : Lp ℝ 2 μ) : Convex ℝ (Icc 0 g) := by
  intro f hf k hk a b ha hb hab
  constructor
  · apply (Lp.coeFn_nonneg _).mp
    filter_upwards [Lp.coeFn_add (a • f) (b • k), Lp.coeFn_smul a f,
      Lp.coeFn_smul b k, (Lp.coeFn_nonneg f).mpr hf.1,
      (Lp.coeFn_nonneg k).mpr hk.1] with x he hf hk hf0 hk0
    simpa only [he, hf, hk, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using
      add_nonneg (mul_nonneg ha hf0) (mul_nonneg hb hk0)
  · apply (Lp.coeFn_le _ _).mp
    filter_upwards [Lp.coeFn_add (a • f) (b • k), Lp.coeFn_smul a f,
      Lp.coeFn_smul b k, (Lp.coeFn_le f g).mpr hf.2,
      (Lp.coeFn_le k g).mpr hk.2] with x he hf hk hfg hkg
    simp only [he, hf, hk, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    calc a * f x + b * k x ≤ a * g x + b * g x :=
          add_le_add (mul_le_mul_of_nonneg_left hfg ha) (mul_le_mul_of_nonneg_left hkg hb)
      _ = g x := by rw [← add_mul, hab, one_mul]

/-- A retained density with the same boundary tests and no nonzero
nonnegative subdensity annihilating every boundary test. The minimizer is
constructed by Hilbert projection, not supplied as an assumption. -/
theorem exists_acyclic_density (g : Lp ℝ 2 μ) (hg : 0 ≤ g)
    (B : I → Lp ℝ 2 μ →L[ℝ] ℝ) :
    ∃ f : Lp ℝ 2 μ, (0 ≤ f ∧ f ≤ g) ∧ (∀ i, B i f = B i g) ∧
      ∀ c : Lp ℝ 2 μ, 0 ≤ c → c ≤ f → (∀ i, B i c = 0) → c = 0 := by
  let K : Set (Lp ℝ 2 μ) := Icc 0 g ∩ {f | ∀ i, B i f = B i g}
  have hclosed : IsClosed K := isClosed_Icc.inter (by
    simp only [setOf_forall]
    exact isClosed_iInter fun i => isClosed_eq (B i).continuous continuous_const)
  have hconvex : Convex ℝ K := (convex_interval g).inter (by
    intro f hf k hk a b ha hb hab i
    simp only [map_add, map_smul, smul_eq_mul, hf i, hk i]
    rw [← add_mul, hab, one_mul])
  obtain ⟨f, hf, hmin⟩ := exists_norm_eq_iInf_of_complete_convex
    (show K.Nonempty from ⟨g, ⟨hg, le_rfl⟩, fun _ => rfl⟩)
    hclosed.isComplete hconvex 0
  refine ⟨f, hf.1, hf.2, ?_⟩
  intro c hc hcf hBc
  have hfc : f - c ∈ K := by
    refine ⟨⟨sub_nonneg.mpr hcf, (sub_le_self _ hc).trans hf.1.2⟩, ?_⟩
    intro i
    rw [map_sub, hBc i, sub_zero, hf.2 i]
  have hinner := (norm_eq_iInf_iff_real_inner_le_zero hconvex hf).mp hmin (f-c) hfc
  have hle : ⟪f, c⟫_ℝ ≤ 0 := by simpa using hinner
  have hcc : ⟪c, c⟫_ℝ ≤ ⟪f, c⟫_ℝ := by
    rw [L2.inner_def, L2.inner_def]
    apply integral_mono_ae (L2.integrable_inner c c) (L2.integrable_inner f c)
    filter_upwards [(Lp.coeFn_nonneg c).mpr hc, (Lp.coeFn_le c f).mpr hcf] with x hc hcf
    simpa only [RCLike.inner_apply, conj_trivial, mul_comm] using mul_le_mul_of_nonneg_right hcf hc
  exact inner_self_eq_zero.mp (le_antisymm (hcc.trans hle) (real_inner_self_nonneg))

end DensityCycleRemoval

namespace EuclideanNormalCurrentData

/-- Smooth compact tests for the distributional boundary. -/
abbrev BoundaryTest := {ψ : ExposureEuclidean → ℝ //
  ContDiff ℝ (⊤ : ℕ∞) ψ ∧ HasCompactSupport ψ}

variable (T : EuclideanNormalCurrentData)
local instance : IsFiniteMeasure T.vectorMeasure.variation := T.finite_variation

theorem boundaryTest_memLp (ψ : BoundaryTest) :
    MemLp (fun z => fderiv ℝ ψ.val z (T.direction z)) 2 T.vectorMeasure.variation := by
  have hc := ψ.property.1.continuous_fderiv (by simp)
  obtain ⟨C, hC⟩ := (ψ.property.2.fderiv (𝕜 := ℝ)).exists_bound_of_continuous hc
  have hm : Measurable (fun z => fderiv ℝ ψ.val z (T.direction z)) := by
    have he : Continuous (fun p : (ExposureEuclidean →L[ℝ] ℝ) × ExposureEuclidean => p.1 p.2) := by
      fun_prop
    exact he.measurable.comp (hc.measurable.prodMk T.measurable_direction)
  apply MemLp.of_bound hm.aestronglyMeasurable C
  filter_upwards [T.direction_unit] with z hz
  calc ‖fderiv ℝ ψ.val z (T.direction z)‖ ≤ ‖fderiv ℝ ψ.val z‖ * ‖T.direction z‖ :=
        (fderiv ℝ ψ.val z).le_opNorm _
    _ ≤ C := by rw [hz, mul_one]; exact hC z

def boundaryFunctional (ψ : BoundaryTest) : Lp ℝ 2 T.vectorMeasure.variation →L[ℝ] ℝ :=
  innerSL ℝ ((T.boundaryTest_memLp ψ).toLp _)

theorem boundaryFunctional_apply (ψ : BoundaryTest) (f : Lp ℝ 2 T.vectorMeasure.variation) :
    T.boundaryFunctional ψ f =
      ∫ z, f z * fderiv ℝ ψ.val z (T.direction z) ∂T.vectorMeasure.variation := by
  change ⟪(T.boundaryTest_memLp ψ).toLp _, f⟫_ℝ = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(T.boundaryTest_memLp ψ).coeFn_toLp] with z hz
  simp [hz, RCLike.inner_apply]

/-- The constant density representing the parent current. -/
def fullDensity : Lp ℝ 2 T.vectorMeasure.variation := (memLp_const (1 : ℝ)).toLp _

theorem fullDensity_ae : T.fullDensity =ᵐ[T.vectorMeasure.variation] fun _ => (1 : ℝ) :=
  (memLp_const (1 : ℝ)).coeFn_toLp

theorem fullDensity_nonneg : 0 ≤ T.fullDensity := by
  apply (Lp.coeFn_nonneg _).mp
  filter_upwards [T.fullDensity_ae] with z hz
  simp [hz]

def densityCurrent (f : Lp ℝ 2 T.vectorMeasure.variation) :
    VectorMeasure ExposureEuclidean ExposureEuclidean :=
  T.vectorMeasure.variation.withDensityᵥ (fun z => f z • T.direction z)

theorem densityCurrent_integrable (f : Lp ℝ 2 T.vectorMeasure.variation)
    (hf : 0 ≤ f ∧ f ≤ T.fullDensity) :
    Integrable (fun z => f z • T.direction z) T.vectorMeasure.variation := by
  apply T.direction_integrable.norm.mono'
    ((Lp.aestronglyMeasurable f).smul T.measurable_direction.aestronglyMeasurable)
  filter_upwards [(Lp.coeFn_nonneg f).mpr hf.1,
    (Lp.coeFn_le f T.fullDensity).mpr hf.2, T.fullDensity_ae] with z h0 h1 he
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg h0]
  exact mul_le_of_le_one_left (norm_nonneg _) (h1.trans he.le)

/-- The retained vector measure is a genuine subcurrent in the original
mass-additivity definition, not merely a measure with smaller total mass. -/
theorem densityCurrent_subcurrent (f : Lp ℝ 2 T.vectorMeasure.variation)
    (hf : 0 ≤ f ∧ f ≤ T.fullDensity) :
    IsVectorSubcurrent (T.densityCurrent f) T.vectorMeasure := by
  have hi := T.densityCurrent_integrable f hf
  have hr : Integrable (fun z => T.direction z - f z • T.direction z)
      T.vectorMeasure.variation := T.direction_integrable.sub hi
  have he : T.vectorMeasure - T.densityCurrent f =
      T.vectorMeasure.variation.withDensityᵥ (fun z => T.direction z - f z • T.direction z) := by
    exact (congrArg (fun V => V - T.densityCurrent f) T.represents).trans
      (withDensityᵥ_sub' T.direction_integrable hi).symm
  unfold IsVectorSubcurrent
  rw [he, densityCurrent, withDensity_vectorMeasure_variation_eq hr,
    withDensity_vectorMeasure_variation_eq hi,
    withDensity_apply _ MeasurableSet.univ, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ,
    ← lintegral_add_left' hr.aestronglyMeasurable.enorm]
  have hae : (fun z => ‖T.direction z - f z • T.direction z‖ₑ +
      ‖f z • T.direction z‖ₑ) =ᵐ[T.vectorMeasure.variation] fun _ => 1 := by
    filter_upwards [(Lp.coeFn_nonneg f).mpr hf.1,
      (Lp.coeFn_le f T.fullDensity).mpr hf.2, T.fullDensity_ae,
      T.direction_unit] with z h0 h1 he hu
    have hf1 : f z ≤ 1 := h1.trans he.le
    have hd : T.direction z - f z • T.direction z = (1 - f z) • T.direction z := by
      rw [sub_smul, one_smul]
    simp only [hd, ← ofReal_norm, norm_smul, Real.norm_eq_abs, hu, mul_one,
      abs_of_nonneg h0, abs_of_nonneg (sub_nonneg.mpr hf1)]
    rw [← ENNReal.ofReal_add (sub_nonneg.mpr hf1) h0, sub_add_cancel]
    simp
  rw [lintegral_congr_ae hae]
  simp

theorem densityCurrent_variation (f : Lp ℝ 2 T.vectorMeasure.variation)
    (hf : 0 ≤ f ∧ f ≤ T.fullDensity) :
    (T.densityCurrent f).variation =
      T.vectorMeasure.variation.withDensity (fun z => ENNReal.ofReal (f z)) := by
  rw [densityCurrent, withDensity_vectorMeasure_variation_eq (T.densityCurrent_integrable f hf)]
  apply withDensity_congr_ae
  filter_upwards [(Lp.coeFn_nonneg f).mpr hf.1, T.direction_unit] with z hz hu
  simp only [← ofReal_norm, norm_smul, Real.norm_eq_abs, abs_of_nonneg hz, hu, mul_one]

/-- Conversion to the existing normal-current record, with exactly the
original boundary measures. Only the actual boundary equalities are needed. -/
def densityCurrentData (f : Lp ℝ 2 T.vectorMeasure.variation)
    (hf : 0 ≤ f ∧ f ≤ T.fullDensity)
    (hb : ∀ ψ : BoundaryTest, T.boundaryFunctional ψ f =
      (∫ z, ψ.val z ∂T.boundaryPlus) - (∫ z, ψ.val z ∂T.boundaryMinus)) :
    EuclideanNormalCurrentData := by
  have hs := T.densityCurrent_subcurrent f hf
  have hv := T.densityCurrent_variation f hf
  have hm : Measurable (fun z => ENNReal.ofReal (f z)) :=
    (Lp.stronglyMeasurable f).measurable.ennreal_ofReal
  have ht : ∀ᵐ z ∂T.vectorMeasure.variation, ENNReal.ofReal (f z) < ⊤ :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have he : (fun z => (ENNReal.ofReal (f z)).toReal • T.direction z) =ᵐ[T.vectorMeasure.variation]
      fun z => f z • T.direction z := by
    filter_upwards [(Lp.coeFn_nonneg f).mpr hf.1] with z hz
    rw [ENNReal.toReal_ofReal hz]
  have hi : Integrable T.direction (T.densityCurrent f).variation := by
    rw [hv, integrable_withDensity_iff_integrable_smul' hm ht]
    exact (T.densityCurrent_integrable f hf).congr he.symm
  refine ⟨T.densityCurrent f, ⟨hs.variation_univ_lt_top (measure_lt_top _ _)⟩,
    T.direction, T.measurable_direction, hi,
    (ae_mono (hs.variation_le (measure_lt_top _ _)) T.direction_unit), ?_,
    T.boundaryPlus, T.finite_boundaryPlus, T.boundaryMinus, T.finite_boundaryMinus, ?_⟩
  · rw [hv]
    exact (WithDensityᵥEq.congr_ae he).symm.trans
      (withDensityᵥ_smul_eq_withDensityᵥ_withDensity' hm.aemeasurable ht (by
        exact (T.densityCurrent_integrable f hf).congr he.symm))
  · intro ψ hψ hc
    let test : BoundaryTest := ⟨ψ, hψ, hc⟩
    have hp : Integrable (fun z => f z * fderiv ℝ ψ z (T.direction z))
        T.vectorMeasure.variation := by
      have h := L2.integrable_inner (𝕜 := ℝ) ((T.boundaryTest_memLp test).toLp _) f
      apply h.congr
      filter_upwards [(T.boundaryTest_memLp test).coeFn_toLp] with z hz
      simp [hz, RCLike.inner_apply, test]
    have heq : (fun z => (ENNReal.ofReal (f z)).toReal • fderiv ℝ ψ z (T.direction z))
        =ᵐ[T.vectorMeasure.variation] fun z => f z * fderiv ℝ ψ z (T.direction z) := by
      filter_upwards [(Lp.coeFn_nonneg f).mpr hf.1] with z hz
      simp [ENNReal.toReal_ofReal hz, smul_eq_mul]
    constructor
    · rw [hv, integrable_withDensity_iff_integrable_smul' hm ht]
      exact hp.congr heq.symm
    · rw [hv, integral_withDensity_eq_integral_toReal_smul hm ht,
        integral_congr_ae heq]
      exact (T.boundaryFunctional_apply test f).symm.trans (hb test)

theorem boundaryFunctional_full (ψ : BoundaryTest) :
    T.boundaryFunctional ψ T.fullDensity =
      (∫ z, ψ.val z ∂T.boundaryPlus) - (∫ z, ψ.val z ∂T.boundaryMinus) := by
  rw [T.boundaryFunctional_apply]
  calc (∫ z, T.fullDensity z * fderiv ℝ ψ.val z (T.direction z) ∂T.vectorMeasure.variation)
      = ∫ z, fderiv ℝ ψ.val z (T.direction z) ∂T.vectorMeasure.variation := by
          apply integral_congr_ae
          filter_upwards [T.fullDensity_ae] with z hz
          simp [hz]
    _ = _ := (T.boundary ψ.val ψ.property.1 ψ.property.2).2

/-- Every normal subcurrent has a nonnegative scalar density in the parent's
polar direction. Mass additivity rules out transverse or opposite directions. -/
theorem subcurrent_density (C : EuclideanNormalCurrentData)
    (hC : IsVectorSubcurrent C.vectorMeasure T.vectorMeasure) :
    ∃ f : Lp ℝ 2 T.vectorMeasure.variation, (0 ≤ f ∧ f ≤ T.fullDensity) ∧
      C.vectorMeasure = T.densityCurrent f ∧
      ∀ ψ : BoundaryTest, T.boundaryFunctional ψ f = C.action (fderiv ℝ ψ.val) := by
  letI := C.finite_variation
  let μ := T.vectorMeasure.variation
  let ν := C.vectorMeasure.variation
  letI : IsFiniteMeasure μ := T.finite_variation
  letI : IsFiniteMeasure ν := C.finite_variation
  letI : ν.HaveLebesgueDecomposition μ := Measure.haveLebesgueDecomposition_of_sigmaFinite ν μ
  let d := ν.rnDeriv μ
  let r := fun z => (d z).toReal
  let v := fun z => r z • C.direction z
  have hle : ν ≤ μ := hC.variation_le (measure_lt_top _ _)
  have hac : ν ≪ μ := Measure.absolutelyContinuous_of_le hle
  have hd : Measurable d := Measure.measurable_rnDeriv _ _
  have hr : Measurable r := hd.ennreal_toReal
  have hd1 : d ≤ᵐ[μ] 1 := Measure.rnDeriv_le_one_of_le hle
  have hr1 : ∀ᵐ z ∂μ, r z ≤ 1 := hd1.mono fun z hz =>
    (ENNReal.toReal_mono ENNReal.one_ne_top hz).trans_eq ENNReal.toReal_one
  have hunit : ∀ᵐ z ∂μ, d z ≠ 0 → ‖C.direction z‖ = 1 := by
    apply (ae_withDensity_iff hd).mp
    rw [Measure.withDensity_rnDeriv_eq ν μ hac]
    exact C.direction_unit
  have hvnorm : ∀ᵐ z ∂μ, ‖v z‖ = r z := by
    filter_upwards [hunit] with z hz
    by_cases h0 : d z = 0
    · simp [v, r, h0]
    · simp [v, norm_smul, Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ r z from ENNReal.toReal_nonneg), hz h0]
  have hvi : Integrable v μ := (integrable_rnDeriv_smul_iff hac).mpr C.direction_integrable
  have hv : μ.withDensityᵥ v = C.vectorMeasure :=
    (withDensityᵥ_rnDeriv_smul hac C.direction_integrable).trans C.represents.symm
  have hw : T.vectorMeasure - C.vectorMeasure =
      μ.withDensityᵥ (fun z => T.direction z - v z) := by
    exact (congrArg₂ (fun A B => A - B) T.represents hv.symm).trans
      (withDensityᵥ_sub' T.direction_integrable hvi).symm
  have hwi : Integrable (fun z => T.direction z - v z) μ := T.direction_integrable.sub hvi
  have hsum : μ.withDensity (fun z => ‖T.direction z - v z‖ₑ + ‖v z‖ₑ) = μ.withDensity (fun _ => 1) := by
    change μ.withDensity ((fun z => ‖T.direction z - v z‖ₑ) + (fun z => ‖v z‖ₑ)) = _
    have hm : Measurable (fun z => ‖T.direction z - v z‖ₑ) :=
      (T.measurable_direction.sub (hr.smul C.measurable_direction)).enorm
    rw [withDensity_add_left hm,
      ← withDensity_vectorMeasure_variation_eq hwi,
      ← withDensity_vectorMeasure_variation_eq hvi, ← hw, hv,
      hC.variation_add_eq (measure_lt_top _ _)]
    exact (withDensity_one (μ := μ)).symm
  have hae := (withDensity_eq_iff_of_sigmaFinite
    (hwi.aestronglyMeasurable.enorm.add hvi.aestronglyMeasurable.enorm)
    aemeasurable_const).mp hsum
  have halign : v =ᵐ[μ] fun z => r z • T.direction z := by
    filter_upwards [hae, hvnorm, T.direction_unit] with z hz hn hu
    have hs : ‖T.direction z - v z‖ + ‖v z‖ = 1 := by
      have h := congrArg ENNReal.toReal hz
      simpa only [ENNReal.toReal_add enorm_ne_top enorm_ne_top, toReal_enorm,
        ENNReal.toReal_one] using h
    have hc : ‖v z‖ • (T.direction z - v z) = ‖T.direction z - v z‖ • v z :=
      norm_add_eq_iff_real.mp (by rw [sub_add_cancel, hu, hs])
    calc v z = (‖T.direction z - v z‖ + ‖v z‖) • v z := by rw [hs, one_smul]
      _ = ‖v z‖ • (T.direction z - v z) + ‖v z‖ • v z := by rw [add_smul, hc]
      _ = r z • T.direction z := by rw [← smul_add, sub_add_cancel, hn]
  have hrLp : MemLp r 2 μ := MemLp.of_bound hr.aestronglyMeasurable 1 (hr1.mono fun z hz => by
    simpa [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ r z from ENNReal.toReal_nonneg)] using hz)
  let f := hrLp.toLp r
  have hf : f =ᵐ[μ] r := hrLp.coeFn_toLp
  have hf0 : 0 ≤ f := (Lp.coeFn_nonneg f).mp (by
    filter_upwards [hf] with z hz
    rw [hz]
    exact ENNReal.toReal_nonneg)
  have hf1 : f ≤ T.fullDensity := (Lp.coeFn_le _ _).mp (by
    filter_upwards [hf, hr1, T.fullDensity_ae] with z hz h1 he
    simpa [hz, he] using h1)
  refine ⟨f, ⟨hf0, hf1⟩, ?_, ?_⟩
  · exact hv.symm.trans (WithDensityᵥEq.congr_ae (halign.trans (by
      filter_upwards [hf] with z hz
      rw [hz])))
  · intro ψ
    rw [T.boundaryFunctional_apply, action]
    change (∫ z, f z * fderiv ℝ ψ.val z (T.direction z) ∂μ) =
      ∫ z, fderiv ℝ ψ.val z (C.direction z) ∂ν
    rw [← Measure.withDensity_rnDeriv_eq ν μ hac,
      integral_withDensity_eq_integral_toReal_smul hd (Measure.rnDeriv_lt_top ν μ)]
    apply integral_congr_ae
    filter_upwards [hf, halign] with z hz ha
    change f z • fderiv ℝ ψ.val z (T.direction z) = r z • fderiv ℝ ψ.val z (C.direction z)
    rw [hz, ← map_smul, ← map_smul, ← ha]

/-- Density-level cycle removal for the actual distributional boundary of
`T`, used below with `subcurrent_density` to eliminate all normal cycles. -/
theorem exists_boundary_preserving_density :
    ∃ f : Lp ℝ 2 T.vectorMeasure.variation,
      (0 ≤ f ∧ f ≤ T.fullDensity) ∧
      (∀ ψ : BoundaryTest, T.boundaryFunctional ψ f =
        (∫ z, ψ.val z ∂T.boundaryPlus) - (∫ z, ψ.val z ∂T.boundaryMinus)) ∧
      ∀ c : Lp ℝ 2 T.vectorMeasure.variation, 0 ≤ c → c ≤ f →
        (∀ ψ : BoundaryTest, T.boundaryFunctional ψ c = 0) → c = 0 := by
  obtain ⟨f, hf, hb, ha⟩ := DensityCycleRemoval.exists_acyclic_density
    T.fullDensity T.fullDensity_nonneg T.boundaryFunctional
  exact ⟨f, hf, fun ψ => (hb ψ).trans (T.boundaryFunctional_full ψ), ha⟩

/-- No nonzero normal subcurrent has zero distributional boundary. -/
def IsAcyclic : Prop :=
  ∀ C : EuclideanNormalCurrentData, IsVectorSubcurrent C.vectorMeasure T.vectorMeasure →
    (∀ ψ : BoundaryTest, C.action (fderiv ℝ ψ.val) = 0) → C.vectorMeasure = 0

theorem density_le_of_variation_le (c f : Lp ℝ 2 T.vectorMeasure.variation)
    (hc : 0 ≤ c ∧ c ≤ T.fullDensity) (hf : 0 ≤ f ∧ f ≤ T.fullDensity)
    (hle : (T.densityCurrent c).variation ≤ (T.densityCurrent f).variation) : c ≤ f := by
  rw [T.densityCurrent_variation c hc, T.densityCurrent_variation f hf] at hle
  have he : (fun z => ENNReal.ofReal (c z)) ≤ᵐ[T.vectorMeasure.variation]
      fun z => ENNReal.ofReal (f z) := by
    apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite
      (Lp.stronglyMeasurable c).measurable.ennreal_ofReal
    intro s hs _
    simpa only [withDensity_apply _ hs] using hle s
  apply (Lp.coeFn_le c f).mp
  filter_upwards [he, (Lp.coeFn_nonneg f).mpr hf.1] with z hz hf0
  exact (ENNReal.ofReal_le_ofReal_iff hf0).mp hz

theorem densityCurrent_zero : T.densityCurrent 0 = 0 := by
  change T.vectorMeasure.variation.withDensityᵥ _ = _
  calc T.vectorMeasure.variation.withDensityᵥ (fun z => (0 : Lp ℝ 2 T.vectorMeasure.variation) z • T.direction z)
      = T.vectorMeasure.variation.withDensityᵥ (fun _ => (0 : ExposureEuclidean)) := by
        apply WithDensityᵥEq.congr_ae
        filter_upwards [Lp.coeFn_zero ℝ 2 T.vectorMeasure.variation] with z hz
        change (0 : Lp ℝ 2 T.vectorMeasure.variation) z • T.direction z = 0
        rw [hz, Pi.zero_apply, zero_smul]
    _ = 0 := withDensityᵥ_zero

/-- Cycle removal in the existing normal-current model: the retained current
is acyclic, preserves the boundary measures, and splits mass locally without
cancellation. No decomposition or compactness assumption is needed. -/
theorem exists_acyclic_subcurrent :
    ∃ S : EuclideanNormalCurrentData,
      IsVectorSubcurrent S.vectorMeasure T.vectorMeasure ∧
      S.boundaryPlus = T.boundaryPlus ∧ S.boundaryMinus = T.boundaryMinus ∧
      S.IsAcyclic ∧
      (T.vectorMeasure - S.vectorMeasure).variation + S.vectorMeasure.variation =
        T.vectorMeasure.variation := by
  obtain ⟨f, hf, hb, ha⟩ := T.exists_boundary_preserving_density
  let S := T.densityCurrentData f hf hb
  have hS : IsVectorSubcurrent S.vectorMeasure T.vectorMeasure := T.densityCurrent_subcurrent f hf
  refine ⟨S, hS, rfl, rfl, ?_, hS.variation_add_eq (measure_lt_top _ _)⟩
  intro C hCS hzero
  obtain ⟨c, hc, he, hbc⟩ := T.subcurrent_density C (hCS.trans hS)
  have hcf : c ≤ f := T.density_le_of_variation_le c f hc hf (by
    have h := hCS.variation_le (hS.variation_univ_lt_top (measure_lt_top _ _))
    rwa [he] at h)
  have hc0 := ha c hc.1 hcf (fun ψ => (hbc ψ).trans (hzero ψ))
  rw [he, hc0, T.densityCurrent_zero]

end EuclideanNormalCurrentData
end CZExposure
