import RequestProject.AppendixE.PhysicalSegment

noncomputable section

namespace CZExposure

open MeasureTheory Set

theorem Pulse.initial_state (P : Pulse) : P.x 0 = x0 := by
  funext i
  simpa using P.ode 0 ⟨le_rfl, P.S_nonneg⟩ i

/-- A successful pulse is already an integral-form physical segment;
no new analytic or dynamical assumptions are required. -/
def Pulse.toPhysicalSegment (P : Pulse) : PhysicalSegment where
  duration := P.S
  duration_nonneg := P.S_nonneg
  path := P.x
  control := P.u
  control_measurable := P.u_measurable
  control_bound := fun t ht => (P.u_unit t ht).le
  path_mem := P.x_mem
  velocity_integrable := by
    rw [intervalIntegrable_iff, IntegrableOn, integrable_pi_iff]
    exact fun i => intervalIntegrable_iff.mp (P.integrable i)
  integralEquation := by
    intro s hs
    have hv : IntervalIntegrable (fun t => vf (P.x t) (P.u t)) volume 0 P.S := by
      rw [intervalIntegrable_iff, IntegrableOn, integrable_pi_iff]
      exact fun i => intervalIntegrable_iff.mp (P.integrable i)
    have hvs := hv.mono_set (uIcc_subset_uIcc_of_mem ⟨le_rfl, P.S_nonneg⟩ hs)
    funext i
    rw [Pi.add_apply, P.initial_state, P.ode s hs i]
    congr 1
    exact (ContinuousLinearMap.proj i : State →L[ℝ] ℝ).intervalIntegral_comp_comm hvs

@[simp] theorem Pulse.toPhysicalSegment_exposure (P : Pulse) :
    P.toPhysicalSegment.exposure = P.exposure := rfl

theorem Pulse.overlap_endpoints (P : Pulse) :
    zObs (P.x 0) = 1 ∧ zObs (P.x P.S) = -1 := by
  constructor
  · rw [P.initial_state]
    change star (1 : ℂ) * 1 ^ 2 + (Real.sqrt 2 : ℂ) * star 0 * 1 * 0 = 1
    simp
  · exact (mem_XCZ_iff_zObs_eq_neg_one
      ⟨P.terminal.1, P.terminal.2.1, P.terminal.2.2.1⟩).mp P.terminal

end CZExposure
