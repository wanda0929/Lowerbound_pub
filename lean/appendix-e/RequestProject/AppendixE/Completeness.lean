module
public import RequestProject.AppendixE.Algebra
public import RequestProject.AppendixE.Relaxation
public import RequestProject.AppendixE.RelaxedSubsolution
public import RequestProject.AppendixE.BallBoxSteering
public import RequestProject.AppendixE.SOSRepresentation

/-!
# Appendix E: asymptotic completeness of the real-coefficient SOS hierarchy

Main statements:
* `stationary_completeness` — Theorem 6 (E3);
* `fixed_partition_convergence` — the Corollary of Appendix E 4 (E14);
* `smooth_subsolution` — Lemma 3 (E9);
* `polynomial_certificates` — Lemma 4;
* `pRelaxed_eq_Cstar` — `p = C*` for the relaxed program (E6).

Fully proved here: weak duality for both programs, nesting in the order,
the stationary-to-partitioned embedding, the finite-order inequality
chains, `pRelaxed ≤ Cstar`, and face compression. These results need no
geometric hypotheses. Local controllability is constructed by finite pulse
words and the inverse function theorem. Physical completeness and smooth
subsolutions now require only `EuclideanDirectedArcSuperposition`; their
proofs use the checked endpoint repair and reconstruction.

The polynomial-certificate and convergence theorems use the proved
`matrixPositivstellensatz`. The C¹ polynomial approximation theorem is proved
by Bernstein approximation and affine scaling. Their proofs contain no
admissions or project-axiom dependencies. Only superposition remains an
unproved input: completeness is still conditional on it.
-/

@[expose] public section

noncomputable section

namespace CZExposure

open MvPolynomial Filter Topology

/-! ## Weak duality, nesting and embedding -/

theorem Lunsplit_nonneg {d : ℕ} (hd : 1 ≤ d) : 0 ≤ Lunsplit d := by
  have h := le_iSup₂ (f := fun (W : StatePoly) (_ : StationaryFeasible d W) =>
    ((eval x0 W : ℝ) : EReal)) 0 (stationaryFeasible_zero hd)
  simpa using h

theorem Lunsplit_mono (d : ℕ) : Lunsplit d ≤ Lunsplit (d + 1) :=
  iSup₂_le fun W hW => le_iSup₂_of_le (f := fun (W : StatePoly)
    (_ : StationaryFeasible (d + 1) W) => ((eval x0 W : ℝ) : EReal)) W hW.mono le_rfl

theorem Lunsplit_le_Cstar (d : ℕ) : Lunsplit d ≤ Cstar :=
  iSup₂_le fun _ hW => le_iInf fun γ => EReal.coe_le_coe_iff.2 (stationary_weak_duality hW γ)

theorem Lunsplit_le_Lsplit (P : ExposurePartition) (U : ℝ) (d : ℕ) :
    Lunsplit d ≤ Lsplit P U d := by
  refine iSup₂_le fun W hW => ?_
  have h := le_iSup₂ (f := fun (W : ℕ → CellPoly) (_ : SplitFeasible P U d W) =>
    ((evalCell 0 x0 (W 0) : ℝ) : EReal)) _ (hW.toSplit P U)
  simpa [evalCell_rename_some] using h

theorem Lsplit_mono (P : ExposurePartition) (U : ℝ) (d : ℕ) :
    Lsplit P U d ≤ Lsplit P U (d + 1) :=
  iSup₂_le fun W hW => le_iSup₂_of_le (f := fun (W : ℕ → CellPoly)
    (_ : SplitFeasible P U (d + 1) W) => ((evalCell 0 x0 (W 0) : ℝ) : EReal)) W hW.mono le_rfl

theorem Lsplit_le_Cstar (P : ExposurePartition) {U : ℝ} (hU : ∃ γ : Pulse, γ.exposure < U)
    (d : ℕ) : Lsplit P U d ≤ Cstar := by
  refine iSup₂_le fun W hW => le_iInf fun γ => ?_
  by_cases hγ : γ.exposure < U
  · exact EReal.coe_le_coe_iff.2 (split_weak_duality hW γ hγ)
  · obtain ⟨γ', hγ'⟩ := hU
    exact EReal.coe_le_coe_iff.2 ((split_weak_duality hW γ' hγ').trans (by linarith))

/-- The inequality chain in (E3): `0 ≤ L_d^unsplit ≤ L_{d+1}^unsplit ≤ C*` for every `d ≥ 1`. -/
theorem stationary_hierarchy_bounds (d : ℕ) (hd : 1 ≤ d) :
    0 ≤ Lunsplit d ∧ Lunsplit d ≤ Lunsplit (d + 1) ∧ Lunsplit (d + 1) ≤ Cstar :=
  ⟨Lunsplit_nonneg hd, Lunsplit_mono d, Lunsplit_le_Cstar _⟩

/-- The inequality chain in (E14): for any partition and any ceiling `U` exceeding the exposure of
some successful pulse, `0 ≤ L_d^unsplit ≤ L_d^split ≤ L_{d+1}^split ≤ C*` for every `d ≥ 1`. -/
theorem split_hierarchy_bounds (P : ExposurePartition) {U : ℝ}
    (hU : ∃ γ : Pulse, γ.exposure < U) (d : ℕ) (hd : 1 ≤ d) :
    0 ≤ Lunsplit d ∧ Lunsplit d ≤ Lsplit P U d ∧
      Lsplit P U d ≤ Lsplit P U (d + 1) ∧ Lsplit P U (d + 1) ≤ Cstar :=
  ⟨Lunsplit_nonneg hd, Lunsplit_le_Lsplit P U d, Lsplit_mono P U d, Lsplit_le_Cstar P hU _⟩

/-! ## Appendix E 2: nearly optimal smooth bounds -/

/-- Steps 3–4 of Appendix E 2: constructed local steering and the explicit
directed-arc superposition input give finite-duration realization. -/
theorem Cstar_le_pRelaxed
    (hSuperposition : EuclideanDirectedArcSuperposition) : Cstar ≤ pRelaxed :=
  LocalSteeringConstruction.physicalLocalSteering.Cstar_le_pRelaxed_of_superposition
    hSuperposition

/-- Equality of the physical and relaxed infima, conditional on superposition. -/
theorem pRelaxed_eq_Cstar
    (hSuperposition : EuclideanDirectedArcSuperposition) : pRelaxed = Cstar :=
  le_antisymm pRelaxed_le_Cstar (Cstar_le_pRelaxed hSuperposition)

/-- **Lemma 3** (Smooth subsolutions). For every `a < C*` there is `φ ∈ C_c^∞(ℝ¹¹)` such that
`W₀ = φ ∘ J - φ(y_π)` satisfies `|f_u W₀| ≤ c` (for all states and all controls in the unit disk),
`W₀|_Z = 0` and `W₀(x₀) > a`. Conditional on superposition. -/
theorem smooth_subsolution
    (hSuperposition : EuclideanDirectedArcSuperposition)
    (a : ℝ) (ha : (a : EReal) < Cstar) :
    ∃ φ : (Fin 11 → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧
      (∀ x ∈ Xset, ∀ u : ℂ, ‖u‖ ≤ 1 →
        |fderiv ℝ (fun x' => φ (Jmap x') - φ yPi) x (vf x u)| ≤ cost x) ∧
      (∀ x ∈ XCZ, φ (Jmap x) - φ yPi = 0) ∧
      a < φ (Jmap x0) - φ yPi :=
  smooth_subsolution_of_realization
    (Cstar_le_pRelaxed hSuperposition) a ha

/-! ## Appendix E 3: polynomial SOS certificates -/

/-- **Lemma 4** (Polynomial certificates). For every `a < C*` (equivalently, for every `ε > 0`
with `a = C* - ε`), some real, `G`-invariant stationary polynomial is feasible in (E2) at some
finite order and satisfies `W(x₀) > a`. Conditional only on superposition. -/
theorem polynomial_certificates
    (hSuperposition : EuclideanDirectedArcSuperposition)
    (a : ℝ) (ha : (a : EReal) < Cstar) :
    ∃ (d : ℕ) (W : StatePoly), StationaryFeasible d W ∧ a < eval x0 W := by
  exact SOSRepresentation.exists_stationary_feasible_below_Cstar
    hSuperposition a ha

/-- Exposure is nonnegative even without assuming a successful pulse exists. -/
theorem Cstar_nonneg : 0 ≤ Cstar :=
  le_iInf fun γ => EReal.coe_nonneg.mpr γ.exposure_nonneg

/-- A supplied successful pulse bounds the physical infimum by a finite real. -/
theorem Cstar_finite (γ : Pulse) : Cstar ≠ ⊤ ∧ Cstar ≠ ⊥ := by
  constructor
  · exact ne_top_of_le_ne_top (EReal.coe_ne_top γ.exposure) (iInf_le _ γ)
  · exact ne_bot_of_le_ne_bot (by simp) Cstar_nonneg

/-- Finiteness follows from the accepted controllability input alone;
successful-pulse existence is derived, not an additional hypothesis. -/
theorem Cstar_finite_of_ballBox
    (hBB : ControlGeometry.CompactRegularLevelBallBox) : Cstar ≠ ⊤ ∧ Cstar ≠ ⊥ := by
  obtain ⟨γ⟩ := BallBoxSteering.nonempty_pulse_of_ballBox hBB
  exact Cstar_finite γ

/-- A successful pulse exists using the proved system-specific steering. -/
theorem nonempty_physical_pulse : Nonempty Pulse :=
  BallBoxSteering.nonempty_pulse_of_localSteering
    LocalSteeringConstruction.physicalLocalSteering

/-- Finiteness no longer needs a geometric input or a supplied pulse. -/
theorem Cstar_finite_physical : Cstar ≠ ⊤ ∧ Cstar ≠ ⊥ := by
  obtain ⟨γ⟩ := nonempty_physical_pulse
  exact Cstar_finite γ

/-- `toReal` denotes the real value of an extended real; this equality justifies
using it for Cstar rather than silently replacing an infinite value by zero. -/
theorem coe_Cstar_toReal (γ : Pulse) : (Cstar.toReal : EReal) = Cstar :=
  EReal.coe_toReal (Cstar_finite γ).1 (Cstar_finite γ).2

/-- Lemma 4 in epsilon form, conditional only on superposition.
The returned order is at least one. -/
theorem polynomial_certificates_epsilon
    (hSuperposition : EuclideanDirectedArcSuperposition)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (d : ℕ) (W : StatePoly), 1 ≤ d ∧ StationaryFeasible d W ∧
      Cstar.toReal - ε < eval x0 W := by
  obtain ⟨γ⟩ := nonempty_physical_pulse
  have ha : ((Cstar.toReal - ε : ℝ) : EReal) < Cstar := by
    rw [← coe_Cstar_toReal γ]
    exact EReal.coe_lt_coe_iff.mpr (sub_lt_self _ hε)
  obtain ⟨d, W, hW, hv⟩ :=
    polynomial_certificates hSuperposition _ ha
  refine ⟨d + 1, W, by omega, ?_, hv⟩
  exact hW.mono

/-- **Theorem 6** (Stationary completeness). For every order `d ≥ 1`,
`0 ≤ L_d^unsplit ≤ L_{d+1}^unsplit ≤ C*`, and `L_d^unsplit → C*` as `d → ∞`. -/
theorem stationary_completeness
    (hSuperposition : EuclideanDirectedArcSuperposition) :
    (∀ d, 1 ≤ d → 0 ≤ Lunsplit d ∧ Lunsplit d ≤ Lunsplit (d + 1) ∧ Lunsplit (d + 1) ≤ Cstar) ∧
      Tendsto Lunsplit atTop (𝓝 Cstar) := by
  have hle : ∀ d, Lunsplit d ≤ Cstar := Lunsplit_le_Cstar
  have hmono : Monotone Lunsplit := monotone_nat_of_le_succ Lunsplit_mono
  have hsup : (⨆ d, Lunsplit d) = Cstar := by
    refine le_antisymm (iSup_le hle) ?_
    refine le_of_forall_lt fun b hb => ?_
    induction b using EReal.rec with
    | bot => exact lt_of_lt_of_le (by simp) ((Lunsplit_nonneg le_rfl).trans (le_iSup _ 1))
    | top => exact absurd hb (by simp)
    | coe a =>
      obtain ⟨d, W, hW, haW⟩ :=
        polynomial_certificates hSuperposition a hb
      refine lt_of_lt_of_le (EReal.coe_lt_coe_iff.2 haW) ((le_iSup₂ (f := fun (W : StatePoly)
        (_ : StationaryFeasible d W) => ((eval x0 W : ℝ) : EReal)) W hW).trans
        (le_iSup Lunsplit d))
  refine ⟨stationary_hierarchy_bounds, ?_⟩
  rw [← hsup]
  exact tendsto_atTop_iSup hmono

/-! ## Appendix E 4: convergence on a fixed partition -/

theorem vf_neg (x : State) (u : ℂ) : vf x (-u) = -vf x u := by
  funext i
  fin_cases i <;> simp [vf, fC, map_neg]

theorem cost_eq_zero_of_mem_Fface {x : State} (hx : x ∈ Fface) : cost x = 0 := by
  simp [cost, hx.2.1, hx.2.2]

/-- Face compression (Appendix E 4): if `c + f_u W ≡ ∑ h_ℓ² (mod I)`, then on the zero-cost face
`F × S¹` one has `f_u W = 0` (feasibility for both `u` and `-u`), and every SOS factor `h_ℓ`
vanishes there. -/
theorem sos_factors_vanish_on_face {W : StatePoly} {n : ℕ} {h : Fin n → Poly}
    (hdrift : cpoly + lieDeriv W - ∑ l, h l ^ 2 ∈ normIdeal) {x : State} (hx : x ∈ Fface)
    {u : ℂ} (hu : ‖u‖ = 1) (ξ : ℝ) :
    eval (pt ξ x u) (lieDeriv W) = 0 ∧ ∀ l, eval (pt ξ x u) (h l) = 0 := by
  have hc := cost_eq_zero_of_mem_Fface hx
  have hu' : ‖-u‖ = 1 := by rwa [norm_neg]
  have e1 := eval_eq_zero_of_mem_normIdeal (ξ := ξ) hx.1 hu hdrift
  have e2 := eval_eq_zero_of_mem_normIdeal (ξ := ξ) hx.1 hu' hdrift
  simp only [map_sub, map_add, map_sum, map_pow, eval_pt_cpoly, hc, zero_add] at e1 e2
  have hneg : eval (pt ξ x (-u)) (lieDeriv W) = -eval (pt ξ x u) (lieDeriv W) := by
    rw [eval_pt_lieDeriv, eval_pt_lieDeriv, vf_neg, ← Finset.sum_neg_distrib]
    simp
  have s1 : 0 ≤ ∑ l, eval (pt ξ x u) (h l) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have s2 : 0 ≤ ∑ l, eval (pt ξ x (-u)) (h l) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hlie : eval (pt ξ x u) (lieDeriv W) = 0 := by linarith
  refine ⟨hlie, fun l => ?_⟩
  have hsum : ∑ l, eval (pt ξ x u) (h l) ^ 2 = 0 := by linarith
  have := (Finset.sum_eq_zero_iff_of_nonneg fun l _ => sq_nonneg (eval (pt ξ x u) (h l))).1 hsum l
    (Finset.mem_univ _)
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this


/-- **Corollary** (Fixed exposure partitions). Fix any finite partition with positive cell widths
and a ceiling `U` exceeding the exposure of some known successful pulse. Then for every `d ≥ 1`,
`0 ≤ L_d^unsplit ≤ L_d^split ≤ L_{d+1}^split ≤ C*`, and `L_d^split → C*` as `d → ∞`. -/
theorem fixed_partition_convergence
    (hSuperposition : EuclideanDirectedArcSuperposition)
    (P : ExposurePartition) (U : ℝ)
    (hU : ∃ γ : Pulse, γ.exposure < U) :
    (∀ d, 1 ≤ d → 0 ≤ Lunsplit d ∧ Lunsplit d ≤ Lsplit P U d ∧
        Lsplit P U d ≤ Lsplit P U (d + 1) ∧ Lsplit P U (d + 1) ≤ Cstar) ∧
      Tendsto (Lsplit P U) atTop (𝓝 Cstar) := by
  have h6 := stationary_completeness hSuperposition
  refine ⟨split_hierarchy_bounds P hU, ?_⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le h6.2 tendsto_const_nhds
    (fun d => Lunsplit_le_Lsplit P U d) (fun d => Lsplit_le_Cstar P hU d)

end CZExposure
