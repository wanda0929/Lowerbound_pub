module
public import RequestProject.AppendixE.BallBoxInput
public import RequestProject.AppendixE.StateGeometry
public import RequestProject.AppendixE.PhysicalCompleteness

/-!
# Physical application of the generic ball-box input

The system-specific application of `CompactRegularLevelBallBox`:
the physical normalization/constraint system verifies every input
hypothesis, real quadratures convert to disk controls, and the short
geometric path bounds ambient variation by `16‖y-x‖`. The resulting
`LocalSteering` remains conditional on the unproved generic input.
-/

@[expose] public section

noncomputable section

namespace CZExposure.StateGeometry

open MeasureTheory Set
open scoped NNReal ENNReal

/-- The Euclidean-inverse embedding is `1`-Lipschitz: ambient sup norm
is dominated by Euclidean norm. -/
theorem lipschitz_euclideanEquiv_symm :
    LipschitzWith 1 (euclideanEquiv.symm : StateEuclidean → State) :=
  LipschitzWith.of_dist_le_mul fun a b => by
    rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
    have h := norm_le_euclidean (euclideanEquiv.symm a - euclideanEquiv.symm b)
    rw [map_sub] at h
    have he : euclideanEquiv (euclideanEquiv.symm a) -
        euclideanEquiv (euclideanEquiv.symm b) = a - b := by
      rw [euclideanEquiv.apply_symm_apply, euclideanEquiv.apply_symm_apply]
    rwa [he] at h

/-- Ambient sup-norm variation is dominated by the (Euclidean) path
length. -/
theorem GeometricPath.ambient_variation_le_length {x y : State}
    (P : GeometricPath x y) :
    eVariationOn P.path (Set.Icc 0 1) ≤ P.length := by
  have h : P.path =
      euclideanEquiv.symm ∘ (fun t => euclideanEquiv (P.path t)) := by
    funext t
    exact (euclideanEquiv.symm_apply_apply (P.path t)).symm
  rw [h]
  calc eVariationOn (euclideanEquiv.symm ∘
        (fun t => euclideanEquiv (P.path t))) (Set.Icc 0 1)
      ≤ (1 : NNReal) * eVariationOn
          (fun t => euclideanEquiv (P.path t)) (Set.Icc 0 1) :=
        LipschitzOnWith.comp_eVariationOn_le
          (lipschitz_euclideanEquiv_symm.lipschitzOnWith :
            LipschitzOnWith 1 euclideanEquiv.symm Set.univ)
          (Set.mapsTo_univ _ _)
    _ = P.length := by simp [GeometricPath.length]

end CZExposure.StateGeometry

namespace CZExposure.BallBoxSteering

open MeasureTheory Set
open scoped NNReal ENNReal
open CZExposure.ControlGeometry CZExposure.ControlLie CZExposure.StateGeometry

/-- The physical constraint is smooth (polynomial in the
coordinates). -/
theorem contDiff_normalization : ContDiff ℝ ⊤ ControlLie.normalization := by
  unfold ControlLie.normalization ControlLie.normal
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> simp <;> fun_prop

/-- The constraint differential is surjective on the level set. -/
theorem normalization_fderiv_surjective {x : State} (hx : x ∈ Xset) :
    Function.Surjective (fderiv ℝ ControlLie.normalization x) := by
  intro z
  obtain ⟨v', hv'⟩ := normal_surjective hx z
  refine ⟨(1/2 : ℝ) • v', ?_⟩
  rw [(hasFDerivAt_normalization x).fderiv]
  show (2 • ControlLie.normalCLM x) ((1/2 : ℝ) • v') = z
  rw [ContinuousLinearMap.smul_apply, map_smul, normalCLM_apply, hv']
  module

/-- The kernel of the constraint differential is the bracket tangent
space. -/
theorem normalization_ker (x : State) :
    (fderiv ℝ ControlLie.normalization x).toLinearMap.ker =
      ControlLie.tangentSpace x := by
  ext v
  rw [LinearMap.mem_ker]
  exact (mem_tangentSpace_iff_fderiv x v).symm

/-- The generic six bracket fields are exactly the physical
`bracketFields`. -/
theorem stepFourFields_physical :
    ControlGeometry.stepFourFields ControlLie.driveX ControlLie.driveY =
      ControlLie.bracketFields := by
  funext i
  fin_cases i <;> rfl

/-- The physical system satisfies every input hypothesis. -/
def physicalSystem : RegularStepFourSystem 8 2 where
  constraint := ControlLie.normalization
  level := fun _ => 1
  fieldX := ControlLie.driveX
  fieldY := ControlLie.driveY
  constraint_smooth := contDiff_normalization
  fieldX_smooth := contDiff_bracketFields 0
  fieldY_smooth := contDiff_bracketFields 1
  compact := by
    have hset : {x | ControlLie.normalization x = (fun _ => 1)} = Xset :=
      Set.ext fun x => (mem_Xset_iff_normalization x).symm
    rw [hset]
    exact isCompact_Xset
  regular := fun x hx =>
    normalization_fderiv_surjective ((mem_Xset_iff_normalization x).mpr hx)
  tangentX := fun x hx =>
    (mem_tangentSpace_iff_fderiv x (ControlLie.driveX x)).mp
      (bracketFields_mem_tangent x 0)
  tangentY := fun x hx =>
    (mem_tangentSpace_iff_fderiv x (ControlLie.driveY x)).mp
      (bracketFields_mem_tangent x 1)
  independent := fun x hx => by
    show LinearIndependent ℝ (fun i : Fin 6 => bracketFields i x)
    exact linearIndependent_bracketFields ((mem_Xset_iff_normalization x).mpr hx)
  spanning := fun x hx => by
    show Submodule.span ℝ (Set.range (fun i : Fin 6 => bracketFields i x)) =
      (fderiv ℝ ControlLie.normalization x).toLinearMap.ker
    rw [normalization_ker]
    exact span_bracketFields_eq_tangentSpace ((mem_Xset_iff_normalization x).mpr hx)

/-- Real quadrature as a complex control. -/
def quadratureControl (a b : ℝ) : ℂ := ⟨a, b⟩

theorem norm_quadratureControl_sq (a b : ℝ) :
    ‖quadratureControl a b‖^2 = a^2 + b^2 := by
  rw [← Complex.normSq_eq_norm_sq]
  simp [quadratureControl, Complex.normSq_apply]
  ring

/-- The physical vector field of a quadrature is exactly the real
combination of the two drive fields. -/
theorem vf_quadrature (x : State) (a b : ℝ) :
    vf x (quadratureControl a b) =
      a • ControlLie.driveX x + b • ControlLie.driveY x := by
  rw [vf_eq_act x (quadratureControl a b)]
  show ControlLie.act ![a/2, b/2, 0, Real.sqrt 2 * a/2, Real.sqrt 2 * b/2, 0] x = _
  rw [ControlLie.driveX, ControlLie.driveY, vf_eq_act x 1, vf_eq_act x Complex.I]
  funext i
  fin_cases i <;>
    simp [quadratureControl, ControlLie.act, Pi.smul_apply,
      Pi.add_apply, smul_eq_mul] <;> ring

/-- A generic quadrature segment is a physical segment. -/
def toPhysicalSegment (P : QuadratureSegment physicalSystem) : PhysicalSegment :=
  { duration := P.duration
    duration_nonneg := P.duration_nonneg
    path := P.path
    control := fun t => quadratureControl (P.controlX t) (P.controlY t)
    control_measurable := by
      have hm : Measurable
          (fun t => (P.controlX t : ℂ) + (P.controlY t : ℂ) * Complex.I) :=
        P.controlX_measurable.complex_ofReal.add
          (P.controlY_measurable.complex_ofReal.mul_const _)
      convert hm using 1
      funext t
      simp only [quadratureControl]
      apply Complex.ext <;> simp
    control_bound := fun t ht => by
      have hsq := norm_quadratureControl_sq (P.controlX t) (P.controlY t)
      have hb := P.control_bound t ht
      have hnn := norm_nonneg (quadratureControl (P.controlX t) (P.controlY t))
      nlinarith [hsq, hb, hnn]
    path_mem := fun t ht =>
      (mem_Xset_iff_normalization _).mpr (P.path_mem t ht)
    velocity_integrable := P.velocity_integrable.congr
      (fun t _ => (vf_quadrature (P.path t) (P.controlX t) (P.controlY t)).symm)
    integralEquation := fun s hs => by
      have h := P.integralEquation s hs
      rw [h]
      congr 1
      exact intervalIntegral.integral_congr
        (fun t _ => (vf_quadrature (P.path t) (P.controlX t) (P.controlY t)).symm) }

@[simp] theorem toPhysicalSegment_duration (P : QuadratureSegment physicalSystem) :
    (toPhysicalSegment P).duration = P.duration := rfl
@[simp] theorem toPhysicalSegment_path (P : QuadratureSegment physicalSystem) :
    (toPhysicalSegment P).path = P.path := rfl

/-- Given bound data for the physical system, construct the exact
`LocalSteering` interface. -/
def localSteeringOfBound (B : BallBoxBound physicalSystem) : LocalSteering :=
  { radius := min ((1:ℝ)/4) (B.radius/16)
    radius_pos := lt_min (by norm_num) (div_pos B.radius_pos (by norm_num))
    K := B.K * Real.rpow 16 (1/4 : ℝ)
    K_pos := mul_pos B.K_pos (Real.rpow_pos_of_pos (by norm_num) _)
    connect := by
      intro x hx y hy hnear
      have hsmall : ‖y - x‖ ≤ 1/4 := hnear.trans (min_le_left _ _)
      have hL : 16 * ‖y - x‖ ≤ B.radius := by
        have h := hnear.trans (min_le_right _ _)
        rw [le_div_iff₀ (by norm_num : (0:ℝ) < 16)] at h
        linarith
      set L := 16 * ‖y - x‖ with hLdef
      have hLnn : 0 ≤ L := mul_nonneg (by norm_num) (norm_nonneg _)
      set Pgeom := shortGeometricPath hx hy hsmall
      have hVar : eVariationOn Pgeom.path (Set.Icc 0 1) ≤ ENNReal.ofReal L :=
        Pgeom.ambient_variation_le_length.trans
          (shortGeometricPath_length_le hx hy hsmall)
      obtain ⟨Q, hQ0, hQD, hQdur⟩ := B.connect x y Pgeom.path L hLnn hL
        Pgeom.smooth
        (fun t ht => (mem_Xset_iff_normalization _).mp (Pgeom.path_mem t ht))
        Pgeom.initial Pgeom.terminal hVar
      refine ⟨toPhysicalSegment Q, hQ0, hQD, ?_⟩
      have h16 : Real.rpow L (1/4 : ℝ) =
          Real.rpow 16 (1/4 : ℝ) * Real.rpow ‖y - x‖ (1/4 : ℝ) := by
        show ((16:ℝ) * ‖y - x‖)^(1/4 : ℝ) =
          16^(1/4 : ℝ) * ‖y - x‖^(1/4 : ℝ)
        exact Real.mul_rpow (by norm_num) (norm_nonneg _)
      calc (toPhysicalSegment Q).duration = Q.duration := rfl
        _ ≤ B.K * Real.rpow L (1/4 : ℝ) := hQdur
        _ = B.K * Real.rpow 16 (1/4 : ℝ) * Real.rpow ‖y - x‖ (1/4 : ℝ) := by
          rw [h16]
          ring }

@[simp] theorem localSteeringOfBound_radius (B : BallBoxBound physicalSystem) :
    (localSteeringOfBound B).radius = min ((1:ℝ)/4) (B.radius/16) := rfl
@[simp] theorem localSteeringOfBound_K (B : BallBoxBound physicalSystem) :
    (localSteeringOfBound B).K = B.K * Real.rpow 16 (1/4 : ℝ) := rfl

/-- Conditional constructor; the generic input remains unproved and no
global `H` value is asserted. -/
def localSteeringOfBallBox (hBB : CompactRegularLevelBallBox) : LocalSteering :=
  localSteeringOfBound (Classical.choice (hBB physicalSystem))

/-- Local steering connects any two points of a continuous real-parametrized
curve in the state domain. The curve is only a connectivity witness, not
an asserted solution of the controlled dynamics. -/
theorem exists_segment_along_curve (H : LocalSteering) (w : ℝ → State)
    (hw : Continuous w) (hX : ∀ t, w t ∈ Xset) (a b : ℝ) :
    ∃ P : PhysicalSegment, P.path 0 = w a ∧ P.path P.duration = w b := by
  let R : Set ℝ := {t | ∃ P : PhysicalSegment,
    P.path 0 = w a ∧ P.path P.duration = w t}
  have extend {t s : ℝ} (ht : t ∈ R) (hnear : ‖w s - w t‖ ≤ H.radius) :
      s ∈ R := by
    obtain ⟨P, hP0, hPt⟩ := ht
    obtain ⟨Q, hQ0, hQs, _⟩ := H.connect (w t) (hX t) (w s) (hX s) hnear
    let hmatch := hPt.trans hQ0.symm
    refine ⟨P.concat Q hmatch, ?_, ?_⟩
    · exact (PhysicalSegment.concat_initial P Q hmatch).trans hP0
    · exact (PhysicalSegment.concat_terminal P Q hmatch).trans hQs
  have near (t : ℝ) : ∀ᶠ s in nhds t, ‖w s - w t‖ < H.radius := by
    simpa only [Metric.mem_ball, dist_eq_norm] using
      hw.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds (w t) H.radius_pos)
  have ho : IsOpen R := isOpen_iff_mem_nhds.mpr fun t ht =>
    Filter.mem_of_superset (near t) fun s hs => extend ht hs.le
  have hc : IsOpen Rᶜ := isOpen_iff_mem_nhds.mpr fun t ht =>
    Filter.mem_of_superset (near t) fun s hs hsR =>
      ht (extend hsR (by rw [norm_sub_rev]; exact hs.le))
  have hall : R = Set.univ :=
    (show IsClopen R from ⟨isOpen_compl_iff.mp hc, ho⟩).eq_univ
      ⟨a, PhysicalSegment.zero (w a) (hX a), rfl, rfl⟩
  have hb : b ∈ R := by rw [hall]; trivial
  exact hb

/-- A successful pulse exists from any quantitative local steering package.
The geometric curve rotates g₂ from 1 to -1 with both excited amplitudes
zero. Local steering supplies actual disk-control segments; active-time
conversion supplies unit control without changing their endpoints. -/
theorem nonempty_pulse_of_localSteering (H : LocalSteering) : Nonempty Pulse := by
  let w : ℝ → State := fun t => mkState 1 0 (Complex.exp (t * Complex.I)) 0
  have hw : Continuous w := by
    apply continuous_pi
    intro i
    fin_cases i <;> simp [w, mkState] <;> fun_prop
  have hX : ∀ t, w t ∈ Xset := by
    intro t
    simp [w, Xset, Complex.norm_exp_ofReal_mul_I]
  obtain ⟨P, hP0, hPπ⟩ := exists_segment_along_curve
    H w hw hX 0 Real.pi
  have hstart : P.path 0 = x0 := by
    simpa [w, mkState, x0] using hP0
  have hend : P.path P.duration ∈ XCZ := by
    rw [hPπ]
    simp [w, XCZ, Xset, Complex.exp_pi_mul_I]
  exact ⟨P.toUnitPulse hstart hend⟩

/-- Compatibility wrapper for the alternative generic ball-box route. -/
theorem nonempty_pulse_of_ballBox (hBB : CompactRegularLevelBallBox) : Nonempty Pulse :=
  nonempty_pulse_of_localSteering (localSteeringOfBallBox hBB)

theorem Cstar_le_pRelaxed_of_ballBox_of_superposition
    (hBB : CompactRegularLevelBallBox)
    (hSuperposition : EuclideanDirectedArcSuperposition) : Cstar ≤ pRelaxed :=
  (localSteeringOfBallBox hBB).Cstar_le_pRelaxed_of_superposition hSuperposition

theorem pRelaxed_eq_Cstar_of_ballBox_of_superposition
    (hBB : CompactRegularLevelBallBox)
    (hSuperposition : EuclideanDirectedArcSuperposition) : pRelaxed = Cstar :=
  (localSteeringOfBallBox hBB).pRelaxed_eq_Cstar_of_superposition hSuperposition

/-- Uses only the existing superposition axiom in addition to the
explicit ball-box input. -/
theorem pRelaxed_eq_Cstar_of_ballBox (hBB : CompactRegularLevelBallBox) :
    pRelaxed = Cstar := (localSteeringOfBallBox hBB).pRelaxed_eq_Cstar

end CZExposure.BallBoxSteering
