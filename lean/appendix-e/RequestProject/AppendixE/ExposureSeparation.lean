module
public import RequestProject.AppendixE.ExposureCompactness
public import Mathlib.Analysis.LocallyConvex.Separation

/-!
# Finite-dimensional separation for exposure records (Appendix E)

At a mass budget below `pRelaxed`, no feasible exposure record fits the budget. This module reduces that
infeasibility to a finite family of smooth balance tests by compactness, then applies
finite-dimensional Hahn–Banach separation and converts the separating functional back
into a single smooth compactly supported test function.
-/

@[expose] public section

noncomputable section

namespace CZExposure

open MeasureTheory Set Topology Filter BigOperators
open scoped ENNReal NNReal

/-- A smooth, compactly supported balance test function, bundled with its proofs. -/
def ExposureTest :=
  {ψ : (Fin 11 → ℝ) → ℝ // ContDiff ℝ (⊤ : ℕ∞) ψ ∧ HasCompactSupport ψ}

/-- The balance function of a bundled test, continuous on the compact domain. -/
def exposureTestBalance (ψ : ExposureTest) : C(ExposurePoint, ℝ) :=
  exposureBalance ψ.1 (ψ.2.1.of_le (by norm_cast))

/-- The balance integral of a bundled test against a domain measure. -/
def balanceMoment (μ : FiniteMeasure ExposurePoint) (ψ : ExposureTest) : ℝ :=
  ∫ p : ExposurePoint, exposureTestBalance ψ p ∂μ.toMeasure

/-- The endpoint target of a bundled test. -/
def balanceTarget (ψ : ExposureTest) : ℝ := ψ.1 yPi - ψ.1 y0

/-- The finite vector of balance moments of `μ` for the tests in `s`. -/
def finiteBalanceMap (s : Finset ExposureTest) (μ : FiniteMeasure ExposurePoint) :
    (↥s → ℝ) := fun ψ => balanceMoment μ ψ.1

/-- The finite vector of endpoint targets for the tests in `s`. -/
def finiteBalanceTarget (s : Finset ExposureTest) : (↥s → ℝ) :=
  fun ψ => balanceTarget ψ.1

/-- The attainable balance vectors from measures of mass at most `M`. -/
def attainableBalanceSet (s : Finset ExposureTest) (M : ℝ≥0) : Set (↥s → ℝ) :=
  finiteBalanceMap s '' {μ : FiniteMeasure ExposurePoint | μ.mass ≤ M}

/-- Pushing a finite domain measure into the ambient space preserves its mass. -/
theorem pushExposureMeasure_mass (μ : FiniteMeasure ExposurePoint) :
    (pushExposureMeasure μ).mass = μ.mass := by
  show (μ.map (Subtype.val : ExposurePoint → ExposureAmbient)) Set.univ = μ Set.univ
  rw [FiniteMeasure.map_apply μ measurable_subtype_coe MeasurableSet.univ, preimage_univ]

/-- The mass of any feasible domain measure is an upper bound for `pRelaxed`. -/
theorem pRelaxed_le_domainMass {μ : FiniteMeasure ExposurePoint}
    (hμ : IsDomainExposureRecord μ) :
    pRelaxed ≤ ((μ.mass : ℝ) : EReal) := by
  have hrec : IsExposureRecord (pushExposureMeasure μ : Measure ExposureAmbient) :=
    (pushExposureMeasure_record_iff μ).mpr hμ
  have hbound : pRelaxed ≤
      (((pushExposureMeasure μ).toMeasure Set.univ : ℝ≥0∞) : EReal) :=
    iInf₂_le (pushExposureMeasure μ : Measure ExposureAmbient) hrec
  rw [← FiniteMeasure.ennreal_mass, pushExposureMeasure_mass] at hbound
  rwa [EReal.coe_nnreal_eq_coe_real] at hbound

/-- The balance moment is continuous in the measure for the weak topology. -/
theorem continuous_balanceMoment (ψ : ExposureTest) :
    Continuous (fun μ : FiniteMeasure ExposurePoint => balanceMoment μ ψ) :=
  FiniteMeasure.continuous_integral_continuousMap (exposureTestBalance ψ)

/-- Every bundled balance function is integrable against any finite measure. -/
theorem integrable_exposureTestBalance (ψ : ExposureTest)
    (μ : FiniteMeasure ExposurePoint) :
    Integrable (fun p : ExposurePoint => exposureTestBalance ψ p) μ.toMeasure :=
  (exposureTestBalance ψ).continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- The map `μ ↦ finiteBalanceMap s μ` is continuous: each coordinate is a balance integral. -/
theorem continuous_finiteBalanceMap (s : Finset ExposureTest) :
    Continuous (finiteBalanceMap s) :=
  continuous_pi fun ψ => continuous_balanceMoment ψ.1

/-- The balance moment is additive in the measure. -/
theorem balanceMoment_add (μ ν : FiniteMeasure ExposurePoint) (ψ : ExposureTest) :
    balanceMoment (μ + ν) ψ = balanceMoment μ ψ + balanceMoment ν ψ := by
  have hμ := integrable_exposureTestBalance ψ μ
  have hν := integrable_exposureTestBalance ψ ν
  simp only [balanceMoment, FiniteMeasure.toMeasure_add]
  exact integral_add_measure hμ hν

/-- The balance moment respects the `ℝ≥0` scalar action. -/
theorem balanceMoment_smul (c : ℝ≥0) (μ : FiniteMeasure ExposurePoint)
    (ψ : ExposureTest) :
    balanceMoment (c • μ) ψ = (c : ℝ) * balanceMoment μ ψ := by
  simp only [balanceMoment, FiniteMeasure.toMeasure_smul]
  rw [integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul]

/-- Mass is additive for finite measures. -/
theorem mass_add' (μ ν : FiniteMeasure ExposurePoint) :
    (μ + ν).mass = μ.mass + ν.mass := by
  show ⇑(μ + ν) Set.univ = ⇑μ Set.univ + ⇑ν Set.univ
  rw [FiniteMeasure.coeFn_add, Pi.add_apply]

/-- Mass respects `ℝ≥0` scalar multiplication. -/
theorem mass_smul' (c : ℝ≥0) (μ : FiniteMeasure ExposurePoint) :
    (c • μ).mass = c * μ.mass := by
  show ⇑(c • μ) Set.univ = c * ⇑μ Set.univ
  rw [FiniteMeasure.coeFn_smul, Pi.smul_apply, smul_eq_mul]

/-- The finite balance map is additive in the measure. -/
theorem finiteBalanceMap_add (s : Finset ExposureTest)
    (μ ν : FiniteMeasure ExposurePoint) :
    finiteBalanceMap s (μ + ν) = finiteBalanceMap s μ + finiteBalanceMap s ν := by
  funext ψ
  exact balanceMoment_add μ ν ψ.1

/-- The finite balance map respects `ℝ≥0` scalar multiplication. -/
theorem finiteBalanceMap_smul (s : Finset ExposureTest) (c : ℝ≥0)
    (μ : FiniteMeasure ExposurePoint) :
    finiteBalanceMap s (c • μ) = (c : ℝ) • finiteBalanceMap s μ := by
  funext ψ
  exact balanceMoment_smul c μ ψ.1

/-- On a budget below `pRelaxed`, finitely many balance tests obstruct feasibility. -/
theorem exists_finite_balance_obstruction (M : ℝ≥0)
    (hM : ((M : ℝ) : EReal) < pRelaxed) :
    ∃ s : Finset ExposureTest, finiteBalanceTarget s ∉ attainableBalanceSet s M := by
  classical
  have hK : IsCompact {μ : FiniteMeasure ExposurePoint | μ.mass ≤ M} :=
    isCompact_setOf_finiteMeasure_le_of_compactSpace _ M
  have hF : ∀ ψ : ExposureTest, IsClosed {μ : FiniteMeasure ExposurePoint |
      balanceMoment μ ψ = balanceTarget ψ} := fun ψ =>
    isClosed_eq (continuous_balanceMoment ψ) continuous_const
  have hempty : {μ : FiniteMeasure ExposurePoint | μ.mass ≤ M} ∩
      (⋂ ψ : ExposureTest,
        {μ : FiniteMeasure ExposurePoint | balanceMoment μ ψ = balanceTarget ψ}) = ∅ := by
    ext μ
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hμ
    have hμmass : μ.mass ≤ M := hμ.1
    have hμrec : IsDomainExposureRecord μ := fun ψ h1 h2 =>
      Set.mem_iInter.mp hμ.2 ⟨ψ, h1, h2⟩
    have hp := pRelaxed_le_domainMass hμrec
    have hm : ((μ.mass : ℝ) : EReal) ≤ ((M : ℝ) : EReal) := by
      exact_mod_cast hμmass
    exact absurd hM (not_lt_of_ge (hp.trans hm))
  obtain ⟨s, hs⟩ := hK.elim_finite_subfamily_closed
    (fun ψ : ExposureTest =>
      {μ : FiniteMeasure ExposurePoint | balanceMoment μ ψ = balanceTarget ψ})
    hF hempty
  refine ⟨s, fun hmem => ?_⟩
  obtain ⟨μ, hμmass, hμmap⟩ := hmem
  have hμin : μ ∈ ({μ : FiniteMeasure ExposurePoint | μ.mass ≤ M} ∩
      ⋂ i ∈ s,
        {μ : FiniteMeasure ExposurePoint | balanceMoment μ i = balanceTarget i}) := by
    refine ⟨hμmass, ?_⟩
    rw [mem_iInter]
    intro i
    rw [mem_iInter]
    intro hi
    exact congr_fun hμmap ⟨i, hi⟩
  rw [hs] at hμin
  exact hμin

/-- The attainable balance set is compact as a continuous image of the mass ball. -/
theorem isCompact_attainableBalanceSet (s : Finset ExposureTest) (M : ℝ≥0) :
    IsCompact (attainableBalanceSet s M) :=
  (isCompact_setOf_finiteMeasure_le_of_compactSpace _ M).image
    (continuous_finiteBalanceMap s)

/-- The attainable balance set is convex. -/
theorem convex_attainableBalanceSet (s : Finset ExposureTest) (M : ℝ≥0) :
    Convex ℝ (attainableBalanceSet s M) := by
  classical
  rintro x ⟨μ, hμ, rfl⟩ y ⟨ν, hν, rfl⟩ a b ha hb hab
  let ca : ℝ≥0 := ⟨a, ha⟩
  let cb : ℝ≥0 := ⟨b, hb⟩
  have hsum : ca + cb = 1 := by
    apply Subtype.ext
    exact hab
  refine ⟨ca • μ + cb • ν, ?_, ?_⟩
  · show (ca • μ + cb • ν).mass ≤ M
    rw [mass_add', mass_smul', mass_smul']
    calc ca * μ.mass + cb * ν.mass ≤ ca * M + cb * M :=
        add_le_add (mul_le_mul_right hμ ca) (mul_le_mul_right hν cb)
      _ = (ca + cb) * M := by ring
      _ = M := by rw [hsum, one_mul]
  · rw [finiteBalanceMap_add, finiteBalanceMap_smul, finiteBalanceMap_smul]
    rfl

/-- A finite linear combination of bundled tests, back as a single function. -/
def smoothTestCombination (s : Finset ExposureTest) (w : ↥s → ℝ) :
    (Fin 11 → ℝ) → ℝ := fun y => ∑ i : ↥s, w i * i.1.1 y

/-- The combination is smooth. -/
theorem contDiff_smoothTestCombination (s : Finset ExposureTest) (w : ↥s → ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (smoothTestCombination s w) :=
  ContDiff.sum fun i _ => ContDiff.mul contDiff_const i.1.2.1

/-- The combination has compact support. -/
theorem hasCompactSupport_smoothTestCombination (s : Finset ExposureTest)
    (w : ↥s → ℝ) : HasCompactSupport (smoothTestCombination s w) := by
  classical
  have hgen : ∀ u : Finset ↥s, HasCompactSupport fun y => ∑ i ∈ u, w i * i.1.1 y := by
    intro u
    induction u using Finset.induction with
    | empty => simpa using HasCompactSupport.zero
    | insert i u hi ih =>
        simp only [Finset.sum_insert hi]
        exact HasCompactSupport.add
          (HasCompactSupport.mul_left (f := fun _ => w i) i.1.2.2) ih
  exact hgen Finset.univ

/-- The derivative of the combination is the combination of the derivatives. -/
theorem fderiv_smoothTestCombination (s : Finset ExposureTest) (w : ↥s → ℝ)
    (y v : Fin 11 → ℝ) :
    fderiv ℝ (smoothTestCombination s w) y v =
      ∑ i : ↥s, w i * fderiv ℝ i.1.1 y v := by
  show fderiv ℝ (fun y => ∑ i : ↥s, w i * i.1.1 y) y v = _
  rw [fderiv_fun_sum fun i _ =>
    ((i.1.2.1.differentiable (by norm_cast)) y).const_mul (w i)]
  rw [ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fderiv_const_mul ((i.1.2.1.differentiable (by norm_cast)) y) (w i),
    ContinuousLinearMap.smul_apply, smul_eq_mul]

/-- The balance integral of the combination is the combination of balance moments. -/
theorem integral_smoothTestCombination (s : Finset ExposureTest) (w : ↥s → ℝ)
    (μ : FiniteMeasure ExposurePoint) :
    (∫ p : ExposurePoint,
        fderiv ℝ (smoothTestCombination s w) p.1.1 (Bfield p.1.1 p.1.2)
        ∂μ.toMeasure) = ∑ i : ↥s, w i * balanceMoment μ i.1 := by
  simp only [fderiv_smoothTestCombination]
  have hI : ∀ i : ↥s, Integrable
      (fun p : ExposurePoint => w i * fderiv ℝ i.1.1 p.1.1 (Bfield p.1.1 p.1.2))
      μ.toMeasure := fun i => (integrable_exposureTestBalance i.1 μ).const_mul (w i)
  rw [integral_finset_sum Finset.univ fun i _ => hI i]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul]
  rfl

/-- The endpoint difference of the combination is the combination of targets. -/
theorem balanceTarget_smoothTestCombination (s : Finset ExposureTest) (w : ↥s → ℝ) :
    smoothTestCombination s w yPi - smoothTestCombination s w y0 =
      ∑ i : ↥s, w i * balanceTarget i.1 := by
  simp only [smoothTestCombination]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [balanceTarget, mul_sub]

/-- Below `pRelaxed`, Hahn–Banach separation yields a smooth balance separator. -/
theorem exists_smooth_balance_separator (M : ℝ≥0)
    (hM : ((M : ℝ) : EReal) < pRelaxed) :
    ∃ ψ : (Fin 11 → ℝ) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) ψ ∧ HasCompactSupport ψ ∧
      ∃ r : ℝ, 0 < r ∧
        (∀ μ : FiniteMeasure ExposurePoint, μ.mass ≤ M →
          (∫ p : ExposurePoint, fderiv ℝ ψ p.1.1 (Bfield p.1.1 p.1.2)
            ∂μ.toMeasure) < r) ∧
        r < ψ yPi - ψ y0 := by
  classical
  obtain ⟨s, hs⟩ := exists_finite_balance_obstruction M hM
  obtain ⟨f, r, hbelow, habove⟩ := geometric_hahn_banach_closed_point
    (convex_attainableBalanceSet s M) (isCompact_attainableBalanceSet s M).isClosed hs
  let w : ↥s → ℝ := fun i => f (fun j => if i = j then (1 : ℝ) else 0)
  have h0mem : (0 : ↥s → ℝ) ∈ attainableBalanceSet s M := by
    refine ⟨0, ?_, ?_⟩
    · show (0 : FiniteMeasure ExposurePoint) Set.univ ≤ M
      simp
    · funext ψ
      simp [finiteBalanceMap, balanceMoment]
  have hr : 0 < r := by
    have h := hbelow 0 h0mem
    rwa [map_zero] at h
  have hkey : ∀ μ : FiniteMeasure ExposurePoint,
      f (finiteBalanceMap s μ) = ∑ i : ↥s, w i * balanceMoment μ i.1 := by
    intro μ
    show f.toLinearMap (finiteBalanceMap s μ) = _
    rw [LinearMap.pi_apply_eq_sum_univ]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_eq_mul, mul_comm]
    rfl
  refine ⟨smoothTestCombination s w, contDiff_smoothTestCombination s w,
    hasCompactSupport_smoothTestCombination s w, r, hr, fun μ hμ => ?_, ?_⟩
  · rw [integral_smoothTestCombination, ← hkey]
    exact hbelow _ ⟨μ, hμ, rfl⟩
  · rw [balanceTarget_smoothTestCombination]
    have htarget : f (finiteBalanceTarget s) = ∑ i : ↥s, w i * balanceTarget i.1 := by
      show f.toLinearMap (finiteBalanceTarget s) = _
      rw [LinearMap.pi_apply_eq_sum_univ]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_eq_mul, mul_comm]
      rfl
    rw [← htarget]
    exact habove

end CZExposure
