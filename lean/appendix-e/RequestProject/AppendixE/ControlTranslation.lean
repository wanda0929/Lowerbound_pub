module
public import RequestProject.AppendixE.ControlLieAlgebra
public import RequestProject.AppendixE.PhysicalSegment

/-!
Right translation of the two unit spinors. It commutes with the actual
controlled vector field, so it transports integral trajectories with
unchanged controls and duration. It does not preserve exposure in general.
-/

@[expose] public section
noncomputable section

namespace CZExposure.ControlTranslation

open ControlLie MeasureTheory

/-- Right multiplication by the spinor `a`, in real coordinates. -/
def translate (a x : State) : State :=
  ![x 0*a 0-x 1*a 1-x 2*a 2-x 3*a 3,
    x 0*a 1+x 1*a 0-x 2*a 3+x 3*a 2,
    x 2*a 0-x 3*a 1+x 0*a 2+x 1*a 3,
    x 2*a 1+x 3*a 0+x 0*a 3-x 1*a 2,
    x 4*a 4-x 5*a 5-x 6*a 6-x 7*a 7,
    x 4*a 5+x 5*a 4-x 6*a 7+x 7*a 6,
    x 6*a 4-x 7*a 5+x 4*a 6+x 5*a 7,
    x 6*a 5+x 7*a 4+x 4*a 7-x 5*a 6]

def translateLM (a : State) : State →ₗ[ℝ] State where
  toFun := translate a
  map_add' x y := by
    funext i
    fin_cases i <;> simp [translate, Pi.add_apply] <;> ring
  map_smul' r x := by
    funext i
    fin_cases i <;> simp [translate, Pi.smul_apply, smul_eq_mul] <;> ring

def translateCLM (a : State) : State →L[ℝ] State :=
  LinearMap.toContinuousLinearMap (translateLM a)

@[simp] theorem translateCLM_apply (a x : State) :
    translateCLM a x = translate a x := rfl

theorem translate_act (a x : State) (p : Params) :
    translate a (act p x) = act p (translate a x) := by
  funext i
  fin_cases i <;> simp [translate, act] <;> ring

theorem translate_vf (a x : State) (u : ℂ) :
    translate a (vf x u) = vf (translate a x) u := by
  simp only [vf_eq_act, translate_act]

theorem translate_normalization (a x : State) (i : Fin 2) :
    normalization (translate a x) i = normalization a i * normalization x i := by
  fin_cases i <;> simp [normalization, normal, translate] <;> ring

theorem translate_mem {a x : State} (ha : a ∈ Xset) (hx : x ∈ Xset) :
    translate a x ∈ Xset := by
  rw [mem_Xset_iff_normalization] at ha hx ⊢
  funext i
  rw [translate_normalization, ha, hx]
  exact one_mul 1

@[simp] theorem translate_origin (a : State) : translate a x0 = a := by
  funext i
  fin_cases i <;> simp [translate, x0]

theorem translate_assoc (a b x : State) :
    translate a (translate b x) = translate (translate a b) x := by
  funext i
  fin_cases i <;> simp [translate] <;> ring

def inverse (a : State) : State :=
  ![a 0, -a 1, -a 2, -a 3, a 4, -a 5, -a 6, -a 7]

@[simp] theorem inverse_inverse (a : State) : inverse (inverse a) = a := by
  funext i
  fin_cases i <;> simp [inverse]

theorem inverse_mem {a : State} (ha : a ∈ Xset) : inverse a ∈ Xset := by
  rw [mem_Xset_iff_normalization] at ha ⊢
  have h : normalization (inverse a) = normalization a := by
    funext i
    fin_cases i <;> simp [normalization, normal, inverse]
  exact h.trans ha

theorem translate_inverse_cancel {a : State} (ha : a ∈ Xset) (x : State) :
    translate a (translate (inverse a) x) = x := by
  have h : translate a (translate (inverse a) x) =
      ![normalization a 0*x 0, normalization a 0*x 1,
        normalization a 0*x 2, normalization a 0*x 3,
        normalization a 1*x 4, normalization a 1*x 5,
        normalization a 1*x 6, normalization a 1*x 7] := by
    funext i
    fin_cases i <;> simp [translate, inverse, normalization, normal] <;> ring
  rw [(mem_Xset_iff_normalization a).mp ha] at h
  funext i
  have hi := congrFun h i
  fin_cases i <;> simpa using hi

theorem inverse_translate_cancel {a : State} (ha : a ∈ Xset) (x : State) :
    translate (inverse a) (translate a x) = x := by
  simpa using translate_inverse_cancel (inverse_mem ha) x

theorem inverse_translate_self {a : State} (ha : a ∈ Xset) :
    translate (inverse a) a = x0 := by
  simpa using inverse_translate_cancel ha x0

/-- Cancellation of left evolution, as opposed to the right translations
used to transport a whole trajectory. -/
theorem left_inverse_cancel {p : State} (hp : p ∈ Xset) (x : State) :
    translate (translate x p) (inverse p) = x := by
  rw [← translate_assoc]
  have h : translate p (inverse p) = x0 := by
    simpa using inverse_translate_self (inverse_mem hp)
  rw [h, translate_origin]

/-- Uniform bound in the existing ambient sup norm; no change of norm
or inner product instance on `State` is needed. -/
theorem norm_translate_le {a : State} (ha : a ∈ Xset) (x : State) :
    ‖translate a x‖ ≤ 4 * ‖x‖ := by
  have hb (i j : Fin 8) : ‖x i * a j‖ ≤ ‖x‖ := by
    rw [norm_mul]
    calc
      ‖x i‖ * ‖a j‖ ≤ ‖x i‖ * 1 :=
        mul_le_mul_of_nonneg_left (abs_le_one_of_mem_Xset ha j) (norm_nonneg _)
      _ ≤ ‖x‖ := by simpa using norm_le_pi_norm x i
  have h4 {p q r s : ℝ} (hp : ‖p‖ ≤ ‖x‖) (hq : ‖q‖ ≤ ‖x‖)
      (hr : ‖r‖ ≤ ‖x‖) (hs : ‖s‖ ≤ ‖x‖) :
      ‖p + q + r + s‖ ≤ 4 * ‖x‖ := by
    have h1 := norm_add_le p q
    have h2 := norm_add_le (p + q) r
    have h3 := norm_add_le (p + q + r) s
    linarith
  rw [pi_norm_le_iff_of_nonneg (mul_nonneg (by norm_num) (norm_nonneg x))]
  intro i
  fin_cases i <;> simp [translate, sub_eq_add_neg] <;>
    apply h4 <;> first | exact hb _ _ | simpa only [norm_neg] using hb _ _

theorem relative_target_distance {a : State} (ha : a ∈ Xset) (y : State) :
    ‖translate (inverse a) y - x0‖ ≤ 4 * ‖y - a‖ := by
  rw [← inverse_translate_self ha]
  change ‖translateCLM (inverse a) y - translateCLM (inverse a) a‖ ≤ _
  rw [← map_sub]
  exact norm_translate_le (inverse_mem ha) (y - a)

/-- Transport of a physical integral trajectory, not just an a.e. ODE. -/
def segment (a : State) (ha : a ∈ Xset) (P : PhysicalSegment) : PhysicalSegment where
  duration := P.duration
  duration_nonneg := P.duration_nonneg
  path := fun t => translate a (P.path t)
  control := P.control
  control_measurable := P.control_measurable
  control_bound := P.control_bound
  path_mem := fun t ht => translate_mem ha (P.path_mem t ht)
  velocity_integrable := by
    rw [intervalIntegrable_iff]
    have h := (translateCLM a).integrable_comp
      (intervalIntegrable_iff.mp P.velocity_integrable)
    simpa only [translateCLM_apply, translate_vf] using h
  integralEquation := by
    intro s hs
    have hi := P.velocity_integrable_subinterval
      (Set.left_mem_Icc.mpr P.duration_nonneg) hs
    have h := congrArg (translateCLM a) (P.integralEquation s hs)
    rw [map_add, ← (translateCLM a).intervalIntegral_comp_comm hi] at h
    simpa only [translateCLM_apply, translate_vf] using h

@[simp] theorem segment_duration (a : State) (ha : a ∈ Xset) (P : PhysicalSegment) :
    (segment a ha P).duration = P.duration := rfl

@[simp] theorem segment_control (a : State) (ha : a ∈ Xset) (P : PhysicalSegment) :
    (segment a ha P).control = P.control := rfl

/-- Any actual origin-to-relative-target segment gives the requested
arbitrary-start segment, with exactly the same duration and control. -/
theorem transport_endpoints {a y : State} (ha : a ∈ Xset)
    (P : PhysicalSegment) (hstart : P.path 0 = x0)
    (hend : P.path P.duration = translate (inverse a) y) :
    (segment a ha P).path 0 = a ∧
      (segment a ha P).path (segment a ha P).duration = y := by
  change translate a (P.path 0) = a ∧ translate a (P.path P.duration) = y
  rw [hstart, hend, translate_origin, translate_inverse_cancel ha]
  exact ⟨rfl, rfl⟩

end CZExposure.ControlTranslation
