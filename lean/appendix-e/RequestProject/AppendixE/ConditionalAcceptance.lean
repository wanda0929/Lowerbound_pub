module
public import RequestProject.AppendixE.PolarAlignment
public import RequestProject.AppendixE.ConcretePartitioned

/-! Tier-two acceptance: the external input is the source-shaped geometric
decomposition, not a physical realization or optimal-value equality.
See ../../ConditionalAcceptance.md for its exact scope and literature mapping.
No inhabitant of this input is asserted by this module. -/

@[expose] public section
noncomputable section
namespace CZExposure.ConditionalAcceptance

open Filter Topology MvPolynomial

theorem relaxed_equality (h : EuclideanCurrentSuperposition) :
    pRelaxed = Cstar :=
  pRelaxed_eq_Cstar h.directed

theorem smooth_bounds (h : EuclideanCurrentSuperposition)
    (a : ℝ) (ha : (a : EReal) < Cstar) :
    ∃ φ : (Fin 11 → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧
      (∀ x ∈ Xset, ∀ u : ℂ, ‖u‖ ≤ 1 →
        |fderiv ℝ (fun x' => φ (Jmap x') - φ yPi) x (vf x u)| ≤ cost x) ∧
      (∀ x ∈ XCZ, φ (Jmap x) - φ yPi = 0) ∧
      a < φ (Jmap x0) - φ yPi :=
  smooth_subsolution h.directed a ha

theorem certificates (h : EuclideanCurrentSuperposition)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (d : ℕ) (W : StatePoly), 1 ≤ d ∧ StationaryFeasible d W ∧
      Cstar.toReal - ε < eval x0 W :=
  polynomial_certificates_epsilon h.directed hε

theorem stationary (h : EuclideanCurrentSuperposition) :
    (∀ d, 1 ≤ d → 0 ≤ Lunsplit d ∧ Lunsplit d ≤ Lunsplit (d + 1) ∧
      Lunsplit (d + 1) ≤ Cstar) ∧ Tendsto Lunsplit atTop (𝓝 Cstar) :=
  stationary_completeness h.directed

theorem partitioned (h : EuclideanCurrentSuperposition)
    (P : ExposurePartition) (U : ℝ) (hU : ∃ γ : Pulse, γ.exposure < U) :
    (∀ d, 1 ≤ d → 0 ≤ Lunsplit d ∧ Lunsplit d ≤ Lsplit P U d ∧
      Lsplit P U d ≤ Lsplit P U (d + 1) ∧ Lsplit P U (d + 1) ≤ Cstar) ∧
    Tendsto (Lsplit P U) atTop (𝓝 Cstar) :=
  fixed_partition_convergence h.directed P U hU

theorem concrete_stationary (h : EuclideanCurrentSuperposition)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ D : ℕ, 1 ≤ D ∧ ∀ d ≥ D,
      0 ≤ Cstar.toReal - (ConcreteStationary.optimum d).toReal ∧
        Cstar.toReal - (ConcreteStationary.optimum d).toReal < ε :=
  ConcreteStationary.optimum_epsilon h.directed hε

theorem concrete_partitioned (h : EuclideanCurrentSuperposition)
    (P : ExposurePartition) (U : ℝ) (hU : ∃ γ : Pulse, γ.exposure < U) :
    Tendsto (ConcretePartitioned.optimum P U) atTop (𝓝 Cstar) :=
  ConcretePartitioned.fixed_partition_convergence h.directed P U hU

end CZExposure.ConditionalAcceptance
