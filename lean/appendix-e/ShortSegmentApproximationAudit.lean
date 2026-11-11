import RequestProject.AppendixE.ShortSegmentApproximation

open CZExposure CZExposure.ShortSegmentApproximation
open CZExposure.AtomicBoundaryCorrection MeasureTheory Set
open scoped BigOperators ENNReal

-- Zero displacement must create neither action nor mass, for every step size.
example (h : ℝ) (x : Fin 3 → ExposureEuclidean) :
    realization h x (fun _ => 0) = 0 := by
  ext s
  simp [realization, correction_apply, AtomicBoundaryCorrection.segment]

-- Constant forms recover the coefficient with its sign, independently of h.
example {h : ℝ} (hh : 0 < h) (x v : Fin 3 → ExposureEuclidean)
    (L : ExposureEuclidean →L[ℝ] ℝ) :
    correctionAction (fun _ => h⁻¹) x (fun i => x i + h • v i) (fun _ => L) =
      ∑ i, L (v i) := by
  have hc : LipschitzWith 0 (fun _ : ExposureEuclidean => L) := fun _ _ => by simp
  have he := realization_action_error hh x v hc
  simp only [NNReal.coe_zero, zero_mul, norm_le_zero_iff, sub_eq_zero] at he
  exact he

run_cmd do
  for name in [``segment_action_error, ``realization_mass_le,
      ``realization_action_error, ``realization_action_error_of_mass,
      ``realization_boundary, ``exists_segment_sampling] do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"
    Lean.logInfo m!"PASS {name}: {axioms}"
