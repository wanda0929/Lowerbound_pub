module
public import Mathlib

/-!
# Complex phase transport

For a nonvanishing Lipschitz complex path `f` with a.e. velocity `v`,
its unit phase satisfies
`f(t)/‖f(t)‖ = exp(i∫Im(v/f)) · f(a)/‖f(a)‖` — proved via absolute
continuity, not principal-argument differentiation.  `complexPhaseLift`
is an AC real phase initialized at `arg (f a)`.
-/

@[expose] public section

noncomputable section

namespace CZExposure

open MeasureTheory Set ComplexConjugate

/-- The unit phase `z/‖z‖`. -/
def complexUnitPhase (z : ℂ) : ℂ := (‖z‖ : ℝ)⁻¹ • z

/-- `θ ↦ exp(iθ)`. -/
def phaseFactor (θ : ℝ) : ℂ := Complex.exp (Complex.I * (θ : ℂ))

/-- An unwrapped phase candidate: `arg(f a)` plus the integrated
angular rate. -/
def complexPhaseLift (f v : ℝ → ℂ) (a t : ℝ) : ℝ :=
  Complex.arg (f a) + ∫ s in a..t, (v s / f s).im

@[simp] theorem phaseFactor_zero : phaseFactor 0 = 1 := by
  simp [phaseFactor]

theorem phaseFactor_add (s t : ℝ) :
    phaseFactor (s + t) = phaseFactor s * phaseFactor t := by
  rw [phaseFactor, phaseFactor, phaseFactor, Complex.ofReal_add, mul_add,
    Complex.exp_add]

theorem norm_phaseFactor (θ : ℝ) : ‖phaseFactor θ‖ = 1 :=
  Complex.norm_exp_I_mul_ofReal θ

theorem norm_complexUnitPhase {z : ℂ} (hz : z ≠ 0) :
    ‖complexUnitPhase z‖ = 1 := by
  rw [complexUnitPhase, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg z))]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)

theorem phaseFactor_arg {z : ℂ} (hz : z ≠ 0) :
    phaseFactor (Complex.arg z) = complexUnitPhase z := by
  have h := Complex.norm_mul_exp_arg_mul_I z
  have hn : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hz
  rw [phaseFactor, mul_comm Complex.I]
  have e : Complex.exp ((Complex.arg z : ℂ) * Complex.I) =
      z * (‖z‖ : ℂ)⁻¹ := by
    field_simp
    linear_combination h
  calc Complex.exp ((Complex.arg z : ℂ) * Complex.I)
      = z * (‖z‖ : ℂ)⁻¹ := e
    _ = complexUnitPhase z := by simp [complexUnitPhase, mul_comm]

theorem phaseFactor_sum {A : Type*} (I : Finset A) (θ : A → ℝ) :
    phaseFactor (∑ i ∈ I, θ i) = ∏ i ∈ I, phaseFactor (θ i) := by
  classical
  induction I using Finset.induction with
  | empty => simp [phaseFactor_zero]
  | @insert a s has ih =>
    rw [Finset.sum_insert has, phaseFactor_add, ih, Finset.prod_insert has]

theorem norm_phaseFactor_sub_one_le (θ : ℝ) :
    ‖phaseFactor θ - 1‖ ≤ |θ| :=
  Real.norm_exp_I_mul_ofReal_sub_one_le

theorem lipschitz_phaseFactor : LipschitzWith 1 phaseFactor := by
  rw [lipschitzWith_iff_norm_sub_le]
  intro s t
  simp only [NNReal.coe_one, one_mul]
  have h : phaseFactor s - phaseFactor t =
      (phaseFactor (s - t) - 1) * phaseFactor t := by
    rw [sub_mul, ← phaseFactor_add, sub_add_cancel]
    simp
  rw [h, norm_mul, norm_phaseFactor, mul_one, Real.norm_eq_abs]
  exact norm_phaseFactor_sub_one_le _

theorem hasDerivAt_phaseFactor_comp {θ : ℝ → ℝ} {ω t : ℝ}
    (hθ : HasDerivAt θ ω t) :
    HasDerivAt (fun s => phaseFactor (θ s))
      (phaseFactor (θ t) * Complex.I * (ω : ℂ)) t := by
  have h1 := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t hθ
  have h2 := h1.const_mul Complex.I
  have h3 := h2.cexp
  simpa only [mul_assoc, phaseFactor] using h3

theorem contDiffAt_complexUnitPhase {z : ℂ} (hz : z ≠ 0) :
    ContDiffAt ℝ 1 complexUnitPhase z :=
  ((contDiffAt_norm ℝ hz).inv (norm_ne_zero_iff.mpr hz)).smul
    contDiffAt_id

private theorem hasDerivAt_complex_norm {f : ℝ → ℂ} {v : ℂ} {t : ℝ}
    (hf : HasDerivAt f v t) (hne : f t ≠ 0) :
    HasDerivAt (fun s => ‖f s‖)
      (((f t).re * v.re + (f t).im * v.im) / ‖f t‖) t := by
  have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hf
  have him := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hf
  have hq0 : (⇑Complex.reCLM ∘ f) t ^ 2 +
      (⇑Complex.imCLM ∘ f) t ^ 2 ≠ 0 := by
    simp only [Function.comp_apply, Complex.reCLM_apply, Complex.imCLM_apply]
    intro h0
    have hre0 : (f t).re ^ 2 = 0 := by
      linarith [sq_nonneg (f t).re, sq_nonneg (f t).im]
    have him0 : (f t).im ^ 2 = 0 := by
      linarith [sq_nonneg (f t).re, sq_nonneg (f t).im]
    exact hne (Complex.ext (eq_zero_of_pow_eq_zero hre0)
      (eq_zero_of_pow_eq_zero him0))
  have hsqrt := ((hre.pow 2).add (him.pow 2)).sqrt hq0
  have hnorm : (fun s => ‖f s‖) =
      fun s => Real.sqrt ((f s).re ^ 2 + (f s).im ^ 2) := by
    funext s
    rw [Complex.norm_def]
    congr 1
    simp only [Complex.normSq_apply]
    ring
  rw [hnorm]
  have hsqrt' : Real.sqrt ((f t).re ^ 2 + (f t).im ^ 2) = ‖f t‖ := by
    rw [Complex.norm_def]
    congr 1
    simp only [Complex.normSq_apply]
    ring
  refine hsqrt.congr_deriv ?_
  simp only [Pi.add_apply, Pi.pow_apply, Function.comp_apply,
    Complex.reCLM_apply, Complex.imCLM_apply]
  rw [hsqrt']
  field_simp [norm_ne_zero_iff.mpr hne]
  ring


/-- The unit-phase derivative: `(z/‖z‖)' = i·Im(z'/z)·(z/‖z‖)`. -/
theorem hasDerivAt_complexUnitPhase {f : ℝ → ℂ} {v : ℂ} {t : ℝ}
    (hf : HasDerivAt f v t) (hne : f t ≠ 0) :
    HasDerivAt (fun s => complexUnitPhase (f s))
      (Complex.I * (((v / f t).im : ℝ) : ℂ) * complexUnitPhase (f t)) t := by
  have hn : ‖f t‖ ≠ 0 := norm_ne_zero_iff.mpr hne
  have hnd := hasDerivAt_complex_norm hf hne
  have hprod := (hnd.inv hn).smul hf
  refine hprod.congr_deriv ?_
  have hn2 : ‖f t‖ ^ 2 = (f t).re ^ 2 + (f t).im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have him' : (v / f t).im =
      (v.im * (f t).re - v.re * (f t).im) / ‖f t‖ ^ 2 := by
    rw [Complex.div_im, (Complex.sq_norm (f t)).symm, sub_div]
  have hre1 :
      (Complex.I * ↑((v / f t).im) * complexUnitPhase (f t)).re =
      -(v / f t).im * ‖f t‖⁻¹ * (f t).im := by
    simp [complexUnitPhase, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have him1 :
      (Complex.I * ↑((v / f t).im) * complexUnitPhase (f t)).im =
      (v / f t).im * ‖f t‖⁻¹ * (f t).re := by
    simp [complexUnitPhase, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  apply Complex.ext
  · simp only [Pi.inv_apply, Complex.add_re, Complex.smul_re, smul_eq_mul,
      hre1]
    rw [him']
    field_simp [hn]
    ring_nf
    linear_combination v.re * hn2
  · simp only [Pi.inv_apply, Complex.add_im, Complex.smul_im, smul_eq_mul,
      him1]
    rw [him']
    field_simp [hn]
    ring_nf
    linear_combination v.im * hn2

private theorem unitPhase_comp_lipschitzOn_of_Icc {f : ℝ → ℂ} {K : NNReal}
    {a b : ℝ}
    (hab : a ≤ b) (hf : LipschitzWith K f)
    (hne : ∀ t ∈ Set.Icc a b, f t ≠ 0) :
    ∃ K' : NNReal, LipschitzOnWith K'
      (fun s => complexUnitPhase (f s)) (Set.uIcc a b) := by
  have hloc : LocallyLipschitzOn (Set.Icc a b)
      (fun s => complexUnitPhase (f s)) := by
    intro t ht
    obtain ⟨K', U, hU, hK'⟩ :=
      (contDiffAt_complexUnitPhase (hne t ht)).exists_lipschitzOnWith
    have hpre : f ⁻¹' U ∈ nhds t :=
      hf.continuous.continuousAt.preimage_mem_nhds hU
    refine ⟨K' * K, f ⁻¹' U ∩ Set.Icc a b,
      Filter.inter_mem (nhdsWithin_le_nhds hpre) self_mem_nhdsWithin, ?_⟩
    have hsub : LipschitzOnWith K f (f ⁻¹' U ∩ Set.Icc a b) :=
      fun x _ y _ =>
        hf.lipschitzOnWith (Set.mem_univ x) (Set.mem_univ y)
    exact hK'.comp hsub (fun x hx => hx.1)
  obtain ⟨K', hK'⟩ := hloc.exists_lipschitzOnWith_of_compact isCompact_Icc
  exact ⟨K', hK'.mono (Set.uIcc_of_le hab).le⟩

private theorem absolutelyContinuousOnInterval_oneLip_comp
    {θ : ℝ → ℝ} {g : ℝ → ℂ} {a b : ℝ}
    (hθ : AbsolutelyContinuousOnInterval θ a b) (hg : LipschitzWith 1 g) :
    AbsolutelyContinuousOnInterval (fun t => g (θ t)) a b := by
  rw [absolutelyContinuousOnInterval_iff] at hθ ⊢
  intro ε hε
  obtain ⟨δ, hδ, hsum⟩ := hθ ε hε
  exact ⟨δ, hδ, fun I hI hlen =>
    lt_of_le_of_lt
      (Finset.sum_le_sum fun i _ => by
        simpa [dist_eq_norm, Real.norm_eq_abs] using
          hg.norm_sub_le (θ (I.2 i).1) (θ (I.2 i).2))
      (hsum I hI hlen)⟩

/-- Generic phase transport across a nonvanishing interval. -/
theorem complex_phase_transport {f v : ℝ → ℂ} {K : NNReal} {a b : ℝ}
    (hab : a ≤ b) (hf : LipschitzWith K f)
    (hne : ∀ t ∈ Set.Icc a b, f t ≠ 0)
    (hode : ∀ᵐ t ∂(volume.restrict (Set.Icc a b)), HasDerivAt f (v t) t)
    (hint : IntervalIntegrable (fun t => (v t / f t).im) volume a b) :
    ∀ t ∈ Set.Icc a b,
      complexUnitPhase (f t) =
        phaseFactor (∫ s in a..t, (v s / f s).im) * complexUnitPhase (f a) := by
  set ω : ℝ → ℝ := fun t => (v t / f t).im
  set θ : ℝ → ℝ := fun t => ∫ s in a..t, ω s
  have hθAC : AbsolutelyContinuousOnInterval θ a b :=
    hint.absolutelyContinuousOnInterval_intervalIntegral (Set.mem_uIcc.mpr (Or.inl ⟨le_rfl, hab⟩))
  obtain ⟨Kn, hKn⟩ := unitPhase_comp_lipschitzOn_of_Icc hab hf hne
  have hnAC : AbsolutelyContinuousOnInterval
      (fun t => complexUnitPhase (f t)) a b :=
    hKn.absolutelyContinuousOnInterval
  have hpfAC : AbsolutelyContinuousOnInterval
      (fun t => phaseFactor (-θ t)) a b :=
    absolutelyContinuousOnInterval_oneLip_comp hθAC.neg
      lipschitz_phaseFactor
  have hqAC : AbsolutelyContinuousOnInterval
      (fun t => phaseFactor (-θ t) * complexUnitPhase (f t)) a b := by
    have h := hpfAC.smul hnAC
    convert h using 1
  have hθ' : ∀ᵐ t ∂volume, t ∈ Set.uIoc a b →
      HasDerivAt θ (ω t) t := by
    have h := hint.ae_hasDerivAt_integral
    filter_upwards [h] with t ht htI
    exact ht
      (by
        rw [Set.uIoc_of_le hab] at htI
        rw [Set.uIcc_of_le hab]
        exact Set.Ioc_subset_Icc_self htI)
      a (Set.mem_uIcc.mpr (Or.inl ⟨le_rfl, hab⟩))
  have hode0 : ∀ᵐ t ∂volume, t ∈ Set.uIoc a b → HasDerivAt f (v t) t := by
    have h := (ae_restrict_iff' measurableSet_Icc).mp hode
    filter_upwards [h] with t ht htI
    exact ht (Set.Ioc_subset_Icc_self (Set.uIoc_of_le hab ▸ htI))
  have hder0 : ∀ᵐ t ∂volume, t ∈ Set.uIoc a b →
      HasDerivAt (fun s => phaseFactor (-θ s) * complexUnitPhase (f s)) 0 t := by
    filter_upwards [hθ', hode0] with t htθ htode htI
    have h1 := hasDerivAt_phaseFactor_comp (htθ htI).neg
    have h2 := hasDerivAt_complexUnitPhase (htode htI)
      (hne t (by
        rw [Set.uIoc_of_le hab] at htI
        exact Set.Ioc_subset_Icc_self htI))
    refine (h1.mul h2).congr_deriv ?_
    simp only [Pi.neg_apply, Complex.ofReal_neg]
    ring
  have hderIoc : ∀ᵐ t ∂(volume.restrict (Set.uIoc a b)),
      HasDerivAt (fun s => phaseFactor (-θ s) * complexUnitPhase (f s))
        0 t := by
    rw [ae_restrict_iff' measurableSet_uIoc]
    exact hder0
  have haeq : Set.uIcc a b =ᵐ[volume] Set.uIoc a b := by
    rw [Set.uIcc_of_le hab, Set.uIoc_of_le hab]
    exact Ioc_ae_eq_Icc.symm
  have hderIcc : ∀ᵐ t ∂(volume.restrict (Set.uIcc a b)),
      HasDerivAt (fun s => phaseFactor (-θ s) * complexUnitPhase (f s))
        0 t := by
    rw [Measure.restrict_congr_set haeq]
    exact hderIoc
  have hderVol : ∀ᵐ t ∂volume, t ∈ Set.uIcc a b →
      HasDerivAt (fun s => phaseFactor (-θ s) * complexUnitPhase (f s))
        0 t :=
    (ae_restrict_iff' measurableSet_uIcc).mp hderIcc
  obtain ⟨C, hC⟩ := hqAC.const_of_ae_hasDerivAt_zero hderVol
  intro t ht
  have hqt : phaseFactor (-θ t) * complexUnitPhase (f t) =
      complexUnitPhase (f a) := by
    have hq := hC t (by rw [Set.uIcc_of_le hab]; exact ht)
    have hqa := hC a
      (by rw [Set.uIcc_of_le hab]; exact Set.left_mem_Icc.mpr hab)
    rw [← hqa] at hq
    have hθa : θ a = 0 := by
      show (∫ s in a..a, ω s) = 0
      simp
    rw [hθa, neg_zero, phaseFactor_zero, one_mul] at hq
    exact hq
  calc complexUnitPhase (f t)
      = phaseFactor (θ t) * (phaseFactor (-θ t) * complexUnitPhase (f t)) := by
        rw [← mul_assoc, ← phaseFactor_add, add_neg_cancel,
          phaseFactor_zero, one_mul]
    _ = phaseFactor (θ t) * complexUnitPhase (f a) := by rw [hqt]

theorem complexPhaseLift_spec {f v : ℝ → ℂ} {K : NNReal} {a b : ℝ}
    (hab : a ≤ b) (hf : LipschitzWith K f)
    (hne : ∀ t ∈ Set.Icc a b, f t ≠ 0)
    (hode : ∀ᵐ t ∂(volume.restrict (Set.Icc a b)), HasDerivAt f (v t) t)
    (hint : IntervalIntegrable (fun t => (v t / f t).im) volume a b) :
    complexPhaseLift f v a a = Complex.arg (f a) ∧
    AbsolutelyContinuousOnInterval (complexPhaseLift f v a) a b ∧
    (∀ᵐ t ∂(volume.restrict (Set.Icc a b)),
      HasDerivAt (complexPhaseLift f v a) ((v t / f t).im) t) ∧
    (∀ t ∈ Set.Icc a b,
      phaseFactor (complexPhaseLift f v a t) = complexUnitPhase (f t)) ∧
    complexPhaseLift f v a b - complexPhaseLift f v a a =
      ∫ t in a..b, (v t / f t).im := by
  have ht := complex_phase_transport hab hf hne hode hint
  have hθAC : AbsolutelyContinuousOnInterval
      (fun t => ∫ s in a..t, (v s / f s).im) a b :=
    hint.absolutelyContinuousOnInterval_intervalIntegral (Set.mem_uIcc.mpr (Or.inl ⟨le_rfl, hab⟩))
  have hcAC : AbsolutelyContinuousOnInterval
      (fun _ : ℝ => Complex.arg (f a)) a b :=
    (LipschitzWith.const (Complex.arg (f a))).lipschitzOnWith
      |>.absolutelyContinuousOnInterval
  have hIoc : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)),
      HasDerivAt (fun t => ∫ s in a..t, (v s / f s).im) ((v t / f t).im) t := by
    have h := hint.ae_hasDerivAt_integral
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [h] with t ht htI
    have htI' : t ∈ Set.uIcc a b := by
      rw [Set.uIcc_of_le hab]
      exact Set.Ioc_subset_Icc_self htI
    exact ht htI' a
      (by rw [Set.uIcc_of_le hab]; exact Set.left_mem_Icc.mpr hab)
  have hIcc : ∀ᵐ t ∂(volume.restrict (Set.Icc a b)),
      HasDerivAt (fun t => ∫ s in a..t, (v s / f s).im) ((v t / f t).im) t := by
    have hseq : volume.restrict (Set.Icc a b) =
        volume.restrict (Set.Ioc a b) :=
      Measure.restrict_congr_set
        Ioc_ae_eq_Icc.symm
    rw [hseq]
    exact hIoc
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [complexPhaseLift]
  · exact hcAC.add hθAC
  · filter_upwards [hIcc] with t ht
    exact ht.const_add _
  · intro t htI
    have harg : phaseFactor (Complex.arg (f a)) = complexUnitPhase (f a) :=
      phaseFactor_arg (hne a ⟨le_rfl, hab⟩)
    rw [complexPhaseLift, phaseFactor_add, harg, mul_comm]
    exact (ht t htI).symm
  · simp [complexPhaseLift]

end CZExposure
