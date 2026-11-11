import RequestProject.AppendixE.CompactQuantization

open CZExposure CZExposure.CompactQuantization MeasureTheory Set
open scoped BigOperators NNReal ENNReal

#check @exists_current_sampling
#check @exists_atomic_correction_sequence
#check @sampled_action_eq_sum
#check @sampled_mass_le
#check @integral_tendsto

-- The construction must also handle a zero measure with an empty carrier.
example {ε : ℝ} (hε : 0 < ε) :
    ∃ q : SimpleFunc ExposureEuclidean ExposureEuclidean,
      ∀ x ∈ (∅ : Set ExposureEuclidean), q x ∈ (∅ : Set ExposureEuclidean) ∧
        dist x (q x) < ε :=
  exists_quantizer isCompact_empty hε

-- Merging unequal atomic masses preserves their sum, not their count.
example (x y z : ExposureEuclidean) :
    ((2 : ENNReal) • Measure.dirac x + (3 : ENNReal) • Measure.dirac y).map
        (SimpleFunc.const ExposureEuclidean z) = (5 : ENNReal) • Measure.dirac z := by
  rw [map_eq_atoms]
  norm_num [SimpleFunc.range_const]

-- The integral error keeps the original weights and orientation.
example (x y z : ExposureEuclidean) (f : ExposureEuclidean → ℝ) :
    (∫ a, f a ∂((2 : ENNReal) • Measure.dirac x + (3 : ENNReal) • Measure.dirac y).map
      (SimpleFunc.const ExposureEuclidean z)) -
      (∫ a, f a ∂((2 : ENNReal) • Measure.dirac x + (3 : ENNReal) • Measure.dirac y)) =
        5 * f z - (2 * f x + 3 * f y) := by
  have hx0 : Integrable f (Measure.dirac x) := integrable_dirac (by finiteness)
  have hy0 : Integrable f (Measure.dirac y) := integrable_dirac (by finiteness)
  have hx := hx0.smul_measure (c := (2 : ENNReal)) (by norm_num)
  have hy := hy0.smul_measure (c := (3 : ENNReal)) (by norm_num)
  rw [map_eq_atoms]
  norm_num [SimpleFunc.range_const, integral_add_measure hx hy, integral_smul_measure]

run_cmd do
  for name in [``exists_quantizer, ``transport_cost_le, ``map_eq_atoms,
      ``map_mass, ``map_carrier, ``integral_error_le, ``integral_tendsto,
      ``exists_quantizer_sequence, ``integrable_sampled_action,
      ``sampled_action_eq_sum, ``sampled_mass_le, ``sampled_action_tendsto,
      ``exists_current_sampling, ``exists_atomic_correction,
      ``exists_atomic_correction_sequence] do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"
    Lean.logInfo m!"PASS {name}: {axioms}"
