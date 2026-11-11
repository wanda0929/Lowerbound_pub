module
public import RequestProject.AppendixE.PolygonalRealization

/-! The finite graph decomposition as an actual measure on stopped paths.
This does not approximate an arbitrary current or assert a limiting arc
decomposition. Its endpoint and duration integrals are exact finite identities. -/
@[expose] public section
noncomputable section
namespace CZExposure.FiniteRouting
open MeasureTheory
open scoped BigOperators

variable {V : Type*} [Fintype V]

namespace Flow

def pathMeasure (f : Flow V) (pos : V → ExposureEuclidean) :
    Measure StoppedPathSpace :=
  ∑ i : Fin f.decomposition.length,
    ENNReal.ofReal (f.decomposition.get i).1 •
      Measure.dirac ((f.decomposition.get i).2.realize pos).curve

theorem integrable_pathMeasure (f : Flow V) (pos : V → ExposureEuclidean)
    (g : StoppedPathSpace → ℝ) : Integrable g (f.pathMeasure pos) := by
  apply integrable_finset_sum_measure.mpr
  intro i _
  exact (integrable_dirac (by finiteness)).smul_measure ENNReal.ofReal_ne_top

instance pathMeasure_finite (f : Flow V) (pos : V → ExposureEuclidean) :
    IsFiniteMeasure (f.pathMeasure pos) :=
  (integrable_const_iff_isFiniteMeasure (by norm_num : (1 : ℝ) ≠ 0)).mp
    (f.integrable_pathMeasure pos (fun _ => 1))

theorem integral_pathMeasure (f : Flow V) (pos : V → ExposureEuclidean)
    (g : StoppedPathSpace → ℝ) :
    (∫ a, g a ∂f.pathMeasure pos) =
      total f.decomposition (fun γ => g (γ.realize pos).curve) := by
  unfold pathMeasure
  rw [integral_finset_sum_measure (fun i _ =>
    (integrable_dirac (by finiteness)).smul_measure ENNReal.ofReal_ne_top)]
  simp only [integral_smul_measure, integral_dirac, smul_eq_mul]
  have hn (i : Fin f.decomposition.length) : 0 ≤ (f.decomposition.get i).1 :=
    f.decomposition_nonneg _ (List.get_mem _ _)
  simp only [ENNReal.toReal_ofReal (hn _)]
  rw [← List.sum_ofFn]
  change (List.ofFn ((fun a : ℝ × Walk V => a.1 * g (a.2.realize pos).curve) ∘
    f.decomposition.get)).sum = _
  rw [← List.map_ofFn, List.ofFn_get]
  rfl

theorem initial_integral (f : Flow V) (pos : V → ExposureEuclidean)
    (g : ExposureEuclidean → ℝ) :
    (∫ a, g (a.path 0) ∂f.pathMeasure pos) =
      ∑ v, f.source v * g (pos v) := by
  rw [f.integral_pathMeasure]
  simpa only [Walk.realize_initial] using f.decomposition_initial (g ∘ pos)

theorem terminal_integral (f : Flow V) (pos : V → ExposureEuclidean)
    (g : ExposureEuclidean → ℝ) :
    (∫ a, g (a.path a.duration) ∂f.pathMeasure pos) =
      ∑ v, f.sink v * g (pos v) := by
  rw [f.integral_pathMeasure]
  simpa only [Walk.realize_terminal] using f.decomposition_terminal (g ∘ pos)

theorem duration_integral (f : Flow V) (pos : V → ExposureEuclidean) :
    (∫ a, a.duration ∂f.pathMeasure pos) =
      ∑ u, ∑ v, f.edge u v * ‖pos v - pos u‖ := by
  rw [f.integral_pathMeasure]
  exact f.geometric_length_ledger pos

theorem pathMeasure_mass (f : Flow V) (pos : V → ExposureEuclidean) :
    (f.pathMeasure pos).real Set.univ = ∑ v, f.source v := by
  simpa using f.initial_integral pos (fun _ => 1)

theorem pathMeasure_probability (f : Flow V) (pos : V → ExposureEuclidean)
    (h : ∑ v, f.source v = 1) : IsProbabilityMeasure (f.pathMeasure pos) := by
  constructor
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) ENNReal.one_ne_top).mp
  simpa only [ENNReal.toReal_one] using (f.pathMeasure_mass pos).trans h

end Flow
end CZExposure.FiniteRouting
