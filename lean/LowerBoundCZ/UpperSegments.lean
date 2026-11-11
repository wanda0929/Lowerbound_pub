import LowerBoundCZ.CertificateContracts
import RequestProject.AppendixE.PhysicalConcatenation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Complex.RealDeriv

/-! Constant-control evolution and its population primitive for the upper witness. -/
noncomputable section
namespace LowerBoundCZ.Certification.Upper
open Complex CZExposure MeasureTheory Set
set_option maxHeartbeats 2000000

private theorem rotation_norm (a b u : ℂ) (c s : ℝ) :
    normSq (a * c - I * u * b * s) + normSq (b * c - I * star u * a * s) =
      (c*c + s*s*normSq u) * (normSq a + normSq b) := by
  simp only [normSq_apply, sub_re, sub_im, mul_re, mul_im, ofReal_re, ofReal_im,
    I_re, I_im, star_def, conj_re, conj_im]
  ring

theorem segment_normalization (k : ℕ) (dt ph : ℝ) (z : SectorRecord) :
    normSq (segment k dt ph z).ground + normSq (segment k dt ph z).rydberg =
      normSq z.ground + normSq z.rydberg := by
  have hu : normSq (⟨Real.cos ph, Real.sin ph⟩ : ℂ) = 1 := by
    simp [normSq_apply, ← sq]
  have hq : z.rydberg * (Real.cos (dt * (Real.sqrt k / 2)) : ℂ) +
      -I * star (⟨Real.cos ph, Real.sin ph⟩ : ℂ) * z.ground *
        (Real.sin (dt * (Real.sqrt k / 2)) : ℂ) =
      z.rydberg * (Real.cos (dt * (Real.sqrt k / 2)) : ℂ) -
      I * star (⟨Real.cos ph, Real.sin ph⟩ : ℂ) * z.ground *
        (Real.sin (dt * (Real.sqrt k / 2)) : ℂ) := by ring
  dsimp only [segment]
  rw [hq, rotation_norm, hu]
  have ht := Real.cos_sq_add_sin_sq (dt * (Real.sqrt k / 2))
  simp only [mul_one, ← sq, ht, one_mul]

private def Normalized (z : SectorRecord) : Prop := normSq z.ground + normSq z.rydberg = 1

theorem propagate_normalization (fixed : Fin 12672 → ℝ) (p : Parameters) (k : ℕ) :
    normSq (propagate fixed p k).ground + normSq (propagate fixed p k).rydberg = 1 := by
  change Normalized (propagate fixed p k)
  have hf (l : List (Fin 12672)) (z : SectorRecord) (hz : Normalized z) :
      Normalized (l.foldl (fun q j => segment k (p 0 / 12672) (phase fixed p j) q) z) := by
    induction l generalizing z with
    | nil => exact hz
    | cons j l ih => exact ih _ ((segment_normalization _ _ _ _).trans hz)
  unfold propagate
  exact hf (List.finRange 12672) ⟨1, 0, 0⟩ (by norm_num [Normalized])

private theorem population_primitive (b q : ℂ) (r P t : ℝ) (hr : r ≠ 0) :
    HasDerivAt (fun s => P + (s / 2 + Real.sin (2 * (s*r)) / (4*r)) * normSq b +
      (s / 2 - Real.sin (2 * (s*r)) / (4*r)) * normSq q +
      ((1 - Real.cos (2 * (s*r))) / (2*r)) * (b.re*q.re + b.im*q.im))
      (normSq (b * (Real.cos (t*r) : ℂ) + q * (Real.sin (t*r) : ℂ))) t := by
  have ht : HasDerivAt (fun s : ℝ => 2*(s*r)) (2*r) t := by
    convert ((hasDerivAt_id t).mul_const r).const_mul 2 using 1; simp
  have hs := ht.sin
  have hc := ht.cos
  have hb := (((hasDerivAt_id t).div_const 2).add (hs.div_const (4*r))).mul_const (normSq b)
  have hq := (((hasDerivAt_id t).div_const 2).sub (hs.div_const (4*r))).mul_const (normSq q)
  have hx := (((hasDerivAt_const t 1).sub hc).div_const (2*r)).mul_const (b.re*q.re + b.im*q.im)
  have hd := (((hasDerivAt_const t P).add hb).add hq).add hx
  convert hd using 1
  simp only [normSq_apply, add_re, add_im, mul_re, mul_im, ofReal_re, ofReal_im]
  rw [Real.sin_two_mul, Real.cos_two_mul]
  field_simp
  linear_combination 8 * r * (q.re^2 + q.im^2) * Real.sin_sq_add_cos_sq (t*r)

theorem segment_population_deriv (k : ℕ) (hk : k ≠ 0) (ph : ℝ) (z : SectorRecord) (t : ℝ) :
    HasDerivAt (fun s => (segment k s ph z).population)
      (normSq (segment k t ph z).rydberg) t := by
  exact population_primitive z.rydberg
    (-I * star (⟨Real.cos ph, Real.sin ph⟩ : ℂ) * z.ground)
    (Real.sqrt k / 2) z.population t
    (div_ne_zero (Real.sqrt_ne_zero'.mpr (by exact_mod_cast Nat.pos_of_ne_zero hk)) (by norm_num))

private theorem rotation_deriv (a b u : ℂ) (r t : ℝ) (hu : u * star u = 1) :
    HasDerivAt (fun s => a * (Real.cos (s*r) : ℂ) - I*u*b*(Real.sin (s*r) : ℂ))
      (-I * (r : ℂ) * u * (b * (Real.cos (t*r) : ℂ) -
        I * star u * a * (Real.sin (t*r) : ℂ))) t := by
  have hc := (((hasDerivAt_id t).mul_const r).cos).ofReal_comp
  have hs := (((hasDerivAt_id t).mul_const r).sin).ofReal_comp
  convert (hc.const_mul a).sub (hs.const_mul (I*u*b)) using 1
  simp only [id_eq, one_mul, ofReal_mul, ofReal_neg]
  calc
    _ = -a * (Real.sin (t*r) : ℂ) * r - I*u*b*(Real.cos (t*r) : ℂ)*r := by
      linear_combination -(r : ℂ) * a * (Real.sin (t*r) : ℂ) * hu +
        (r : ℂ) * u * star u * a * (Real.sin (t*r) : ℂ) * I_sq
    _ = _ := by ring

theorem segment_ground_deriv (k : ℕ) (ph : ℝ) (z : SectorRecord) (t : ℝ) :
    HasDerivAt (fun s => (segment k s ph z).ground)
      (-I * (Real.sqrt k / 2 : ℝ) * (⟨Real.cos ph, Real.sin ph⟩ : ℂ) *
        (segment k t ph z).rydberg) t := by
  have hu : (⟨Real.cos ph, Real.sin ph⟩ : ℂ) * star (⟨Real.cos ph, Real.sin ph⟩ : ℂ) = 1 := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, ← sq]
    ring
  convert rotation_deriv z.ground z.rydberg (⟨Real.cos ph, Real.sin ph⟩ : ℂ)
    (Real.sqrt k / 2) t hu using 1; dsimp only [segment]; congr 1; ring

theorem segment_rydberg_deriv (k : ℕ) (ph : ℝ) (z : SectorRecord) (t : ℝ) :
    HasDerivAt (fun s => (segment k s ph z).rydberg)
      (-I * (Real.sqrt k / 2 : ℝ) * star (⟨Real.cos ph, Real.sin ph⟩ : ℂ) *
        (segment k t ph z).ground) t := by
  have hu : star (⟨Real.cos ph, Real.sin ph⟩ : ℂ) *
      star (star (⟨Real.cos ph, Real.sin ph⟩ : ℂ)) = 1 := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, ← sq]
    ring
  convert rotation_deriv z.rydberg z.ground (star (⟨Real.cos ph, Real.sin ph⟩ : ℂ))
    (Real.sqrt k / 2) t hu using 1
  · funext s
    simp only [segment]
    ring
  · simp only [segment, star_star]

def stateOf (a b : SectorRecord) : State := mkState a.ground a.rydberg b.ground b.rydberg

def segmentPath (a b : SectorRecord) (ph t : ℝ) : State :=
  stateOf (segment 1 t ph a) (segment 2 t ph b)

theorem segmentPath_deriv (a b : SectorRecord) (ph t : ℝ) :
    HasDerivAt (segmentPath a b ph)
      (vf (segmentPath a b ph t) ⟨Real.cos ph, Real.sin ph⟩) t := by
  have g1 := segment_ground_deriv 1 ph a t
  have r1 := segment_rydberg_deriv 1 ph a t
  have g2 := segment_ground_deriv 2 ph b t
  have r2 := segment_rydberg_deriv 2 ph b t
  have gre1 := reCLM.hasFDerivAt.comp_hasDerivAt t g1
  have gim1 := imCLM.hasFDerivAt.comp_hasDerivAt t g1
  have rre1 := reCLM.hasFDerivAt.comp_hasDerivAt t r1
  have rim1 := imCLM.hasFDerivAt.comp_hasDerivAt t r1
  have gre2 := reCLM.hasFDerivAt.comp_hasDerivAt t g2
  have gim2 := imCLM.hasFDerivAt.comp_hasDerivAt t g2
  have rre2 := reCLM.hasFDerivAt.comp_hasDerivAt t r2
  have rim2 := imCLM.hasFDerivAt.comp_hasDerivAt t r2
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  case' «0» => convert gre1 using 1
  case' «1» => convert gim1 using 1
  case' «2» => convert rre1 using 1
  case' «3» => convert rim1 using 1
  case' «4» => convert gre2 using 1
  case' «5» => convert gim2 using 1
  case' «6» => convert rre2 using 1
  case' «7» => convert rim2 using 1
  all_goals simp [segmentPath, stateOf, vf, fC, CZExposure.g1, CZExposure.r1,
    CZExposure.g2, CZExposure.r2, mkState, Complex.mul_re, Complex.mul_im]; ring

theorem stateOf_mem (a b : SectorRecord)
    (ha : normSq a.ground + normSq a.rydberg = 1)
    (hb : normSq b.ground + normSq b.rydberg = 1) : stateOf a b ∈ Xset := by
  simpa [stateOf, Xset, normSq_eq_norm_sq] using And.intro ha hb

theorem segmentPath_zero (a b : SectorRecord) (ph : ℝ) :
    segmentPath a b ph 0 = stateOf a b := by
  simp [segmentPath, stateOf, segment]

private theorem phase_unit (ph : ℝ) : ‖(⟨Real.cos ph, Real.sin ph⟩ : ℂ)‖ = 1 := by
  simp [Complex.norm_def, normSq_apply, ← sq]

def physicalSegment (a b : SectorRecord) (ph dt : ℝ) (hdt : 0 ≤ dt)
    (ha : normSq a.ground + normSq a.rydberg = 1)
    (hb : normSq b.ground + normSq b.rydberg = 1) : PhysicalSegment := by
  have hc : Continuous (segmentPath a b ph) :=
    continuous_iff_continuousAt.mpr fun t => (segmentPath_deriv a b ph t).continuousAt
  have hv : Continuous (fun t => vf (segmentPath a b ph t) ⟨Real.cos ph, Real.sin ph⟩) :=
    continuous_vf.comp (hc.prodMk continuous_const)
  exact {
    duration := dt
    duration_nonneg := hdt
    path := segmentPath a b ph
    control := fun _ => ⟨Real.cos ph, Real.sin ph⟩
    control_measurable := measurable_const
    control_bound := fun _ _ => (phase_unit ph).le
    path_mem := fun t _ => stateOf_mem _ _ ((segment_normalization 1 t ph a).trans ha)
      ((segment_normalization 2 t ph b).trans hb)
    velocity_integrable := hv.intervalIntegrable _ _
    integralEquation := fun s _ => by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t _ => segmentPath_deriv a b ph t) (hv.intervalIntegrable _ _)]
      abel }

def populationCost (a b : SectorRecord) : ℝ := (2*a.population + b.population)/4

theorem physicalSegment_exposure (a b : SectorRecord) (ph dt : ℝ) (hdt : 0 ≤ dt)
    (ha : normSq a.ground + normSq a.rydberg = 1)
    (hb : normSq b.ground + normSq b.rydberg = 1) :
    (physicalSegment a b ph dt hdt ha hb).exposure =
      populationCost (segment 1 dt ph a) (segment 2 dt ph b) - populationCost a b := by
  have hd (t : ℝ) : HasDerivAt
      (fun s => populationCost (segment 1 s ph a) (segment 2 s ph b))
      (cost (segmentPath a b ph t)) t := by
    convert (((segment_population_deriv 1 (by decide) ph a t).const_mul 2).add
      (segment_population_deriv 2 (by decide) ph b t)).div_const 4 using 1
    simp [cost, segmentPath, stateOf, normSq_eq_norm_sq]
  have hc : Continuous (fun t => cost (segmentPath a b ph t)) := by
    unfold cost segmentPath stateOf
    simp only [r1_mkState, r2_mkState]
    have h1 : Continuous (fun t => (segment 1 t ph a).rydberg) :=
      continuous_iff_continuousAt.mpr fun t => (segment_rydberg_deriv 1 ph a t).continuousAt
    have h2 : Continuous (fun t => (segment 2 t ph b).rydberg) :=
      continuous_iff_continuousAt.mpr fun t => (segment_rydberg_deriv 2 ph b t).continuousAt
    fun_prop
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    (hc.intervalIntegrable 0 dt)
  simpa [PhysicalSegment.exposure, physicalSegment, populationCost, segment] using he

/-- Assemble any finite phase list, preserving the exact recurrence and cost.
The interval equation remains valid at every switching point. -/
theorem exists_assembly {ι : Type*} (ph : ι → ℝ) (dt : ℝ) (hdt : 0 ≤ dt)
    (l : List ι) (a b : SectorRecord)
    (ha : normSq a.ground + normSq a.rydberg = 1)
    (hb : normSq b.ground + normSq b.rydberg = 1) :
    ∃ P : PhysicalSegment, P.UnitControl ∧ P.duration = l.length * dt ∧
      P.path 0 = stateOf a b ∧
      P.path P.duration = stateOf
        (l.foldl (fun z j => segment 1 dt (ph j) z) a)
        (l.foldl (fun z j => segment 2 dt (ph j) z) b) ∧
      P.exposure = populationCost
        (l.foldl (fun z j => segment 1 dt (ph j) z) a)
        (l.foldl (fun z j => segment 2 dt (ph j) z) b) - populationCost a b := by
  induction l generalizing a b with
  | nil =>
    refine ⟨PhysicalSegment.unitZero (stateOf a b) (stateOf_mem a b ha hb),
      PhysicalSegment.unitZero_unit _ _, ?_, rfl, rfl, ?_⟩ <;> simp
  | cons j l ih =>
    let Q := physicalSegment a b (ph j) dt hdt ha hb
    obtain ⟨R, hRu, hRd, hRi, hRe, hRc⟩ := ih
      (segment 1 dt (ph j) a) (segment 2 dt (ph j) b)
      ((segment_normalization _ _ _ _).trans ha) ((segment_normalization _ _ _ _).trans hb)
    have hm : Q.path Q.duration = R.path 0 := hRi.symm
    refine ⟨Q.concat R hm, Q.concat_unit R hm (fun _ _ => phase_unit (ph j)) hRu, ?_, ?_, ?_, ?_⟩
    · rw [PhysicalSegment.concat_duration, hRd]
      change dt + l.length * dt = (l.length + 1 : ℕ) * dt
      push_cast
      ring
    · rw [PhysicalSegment.concat_initial]
      exact segmentPath_zero a b (ph j)
    · rw [PhysicalSegment.concat_duration, PhysicalSegment.concat_terminal]
      exact hRe
    · rw [PhysicalSegment.concat_exposure, hRc]
      have hQ := physicalSegment_exposure a b (ph j) dt hdt ha hb
      change Q.exposure = _ at hQ
      rw [hQ]
      simp only [List.foldl_cons]
      ring

end LowerBoundCZ.Certification.Upper
