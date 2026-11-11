module
public import RequestProject.AppendixE.CutoffLimit
public import RequestProject.AppendixE.ExposureSuperposition
public import RequestProject.AppendixE.Relaxation
public import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# Conditional physical completeness

Combining the record-to-trajectory bridge, the cutoff limit, and the
proved `pRelaxed ≤ Cstar` yields `Cstar ≤ pRelaxed` and hence
`pRelaxed = Cstar`, conditional on `H : LocalSteering`.  Versions
ending in `_of_superposition` take the superposition statement as an
explicit hypothesis and use only standard Lean axioms; the default
wrappers apply the existing
`External.euclideanDirectedArcSuperposition` axiom.  The main
Completeness API instantiates `H` with the proved finite-pulse construction
and exposes only superposition. Its equality is still conditional on that
remaining input; it does not use the default axiom-backed wrappers.
-/

@[expose] public section

noncomputable section

namespace CZExposure.LocalSteering

open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal

/-- Every feasible record yields an exact-CZ pulse approximating its
mass, conditional on superposition and `H`. -/
theorem exists_pulse_of_record_of_superposition
    (H : LocalSteering)
    (hSuperposition : EuclideanDirectedArcSuperposition)
    (ν : Measure ExposureAmbient) (hν : IsExposureRecord ν)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ γ : Pulse, γ.exposure ≤ (ν Set.univ).toReal + ε := by
  letI : IsFiniteMeasure ν := hν.1
  obtain ⟨T, hTpos, hTmass, y, u, hu, hub, Ky, hstart, hend, hdom, hode⟩ :=
    exists_exposure_time_trajectory_of_record_of_superposition
      hSuperposition ν hν
  obtain ⟨K, hy⟩ := Ky
  have hTmass' : T ≤ (ν Set.univ).toReal :=
    (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top ν Set.univ)).mp hTmass
  obtain ⟨γ, hγ⟩ := H.exists_pulse_approx_exposure_trajectory hTpos.le
    hy hu hub hdom hode hstart hend hε
  exact ⟨γ, by linarith⟩

/-- Same, applying the existing superposition axiom. -/
theorem exists_pulse_of_record
    (H : LocalSteering)
    (ν : Measure ExposureAmbient) (hν : IsExposureRecord ν)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ γ : Pulse, γ.exposure ≤ (ν Set.univ).toReal + ε :=
  H.exists_pulse_of_record_of_superposition
    External.euclideanDirectedArcSuperposition ν hν hε

/-- The reverse inequality, conditional on superposition and `H`. -/
theorem Cstar_le_pRelaxed_of_superposition
    (H : LocalSteering)
    (hSuperposition : EuclideanDirectedArcSuperposition) : Cstar ≤ pRelaxed := by
  unfold pRelaxed
  refine le_iInf fun ν => le_iInf fun hν => ?_
  letI : IsFiniteMeasure ν := hν.1
  have hε : ∀ ε : ℝ, 0 < ε →
      Cstar ≤ (((ν Set.univ).toReal + ε : ℝ) : EReal) := by
    intro ε hε
    obtain ⟨γ, hγ⟩ :=
      H.exists_pulse_of_record_of_superposition hSuperposition ν hν hε
    exact (iInf_le (fun γ : Pulse => (γ.exposure : EReal)) γ).trans
      (EReal.coe_le_coe_iff.mpr hγ)
  have hlim : Tendsto
      (fun ε : ℝ => (((ν Set.univ).toReal + ε : ℝ) : EReal))
      (𝓝[>] (0:ℝ)) (𝓝 (((ν Set.univ).toReal : ℝ) : EReal)) := by
    have hc : Tendsto (fun ε : ℝ => ((ν Set.univ).toReal + ε : ℝ))
        (𝓝 (0:ℝ)) (𝓝 (((ν Set.univ).toReal + 0 : ℝ))) :=
      tendsto_const_nhds.add tendsto_id
    have hc' : Tendsto (fun ε : ℝ => ((ν Set.univ).toReal + ε : ℝ))
        (𝓝[>] (0:ℝ)) (𝓝 (((ν Set.univ).toReal + 0 : ℝ))) :=
      hc.mono_left nhdsWithin_le_nhds
    rw [add_zero] at hc'
    have hcomp := (continuous_coe_real_ereal.tendsto
      ((ν Set.univ).toReal)).comp hc'
    simpa using hcomp
  have hC : Cstar ≤ (((ν Set.univ).toReal : ℝ) : EReal) := by
    apply ge_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin] with ε hpos
    exact hε ε hpos
  rw [EReal.coe_ennreal_toReal (measure_ne_top ν Set.univ)] at hC
  exact hC

/-- Conditional equality. -/
theorem pRelaxed_eq_Cstar_of_superposition
    (H : LocalSteering)
    (hSuperposition : EuclideanDirectedArcSuperposition) : pRelaxed = Cstar :=
  le_antisymm pRelaxed_le_Cstar
    (H.Cstar_le_pRelaxed_of_superposition hSuperposition)

/-- Applying the existing superposition axiom. -/
theorem Cstar_le_pRelaxed (H : LocalSteering) : Cstar ≤ pRelaxed :=
  H.Cstar_le_pRelaxed_of_superposition
    External.euclideanDirectedArcSuperposition

theorem pRelaxed_eq_Cstar (H : LocalSteering) : pRelaxed = Cstar :=
  H.pRelaxed_eq_Cstar_of_superposition
    External.euclideanDirectedArcSuperposition

end CZExposure.LocalSteering
