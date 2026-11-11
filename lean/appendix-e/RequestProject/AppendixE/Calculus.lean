module
public import Mathlib

/-!
# Calculus of polynomials along absolutely continuous curves

Chain rule and fundamental theorem of calculus for `s ↦ p(y(s))`, where `p` is a real
multivariate polynomial and `y` is a curve whose coordinates are indefinite integrals of
interval-integrable functions (Carathéodory solutions).
-/

@[expose] public section

noncomputable section

namespace CZExposure

open MvPolynomial MeasureTheory Set

theorem contDiff_eval {σ : Type*} [Fintype σ] (p : MvPolynomial σ ℝ) :
    ContDiff ℝ ⊤ (fun x : σ → ℝ => eval x p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simpa using (contDiff_const : ContDiff ℝ ⊤ (fun _ : σ → ℝ => a))
  | add p q hp hq => simpa only [map_add] using hp.add hq
  | mul_X p i hp => simpa only [map_mul, eval_X] using hp.mul (contDiff_apply ℝ ℝ i)

theorem hasDerivAt_eval_comp {σ : Type*} [Fintype σ] (p : MvPolynomial σ ℝ) {y : ℝ → σ → ℝ}
    {y' : σ → ℝ} {t : ℝ} (hy : ∀ k, HasDerivAt (fun s => y s k) (y' k) t) :
    HasDerivAt (fun s => eval (y s) p) (∑ k, eval (y t) (pderiv k p) * y' k) t := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simpa using hasDerivAt_const t a
  | add p q hp hq =>
    simpa [add_mul, Finset.sum_add_distrib] using hp.add hq
  | mul_X p i hp =>
    have h := hp.mul (hy i)
    have hk : ∀ k, eval (y t) (pderiv k (p * X i)) * y' k =
        eval (y t) (pderiv k p) * y' k * y t i + if k = i then eval (y t) p * y' i else 0 := by
      intro k
      by_cases hki : k = i
      · subst hki; simp; ring
      · simp [pderiv_X_of_ne (Ne.symm hki), hki]; ring
    convert h using 1
    · funext s; simp
    rw [Finset.sum_congr rfl fun k _ => hk k, Finset.sum_add_distrib, Finset.sum_ite_eq',
      Finset.sum_mul]
    simp

theorem fderiv_eval_apply {σ : Type*} [Fintype σ]
    (p : MvPolynomial σ ℝ) (x v : σ → ℝ) :
    fderiv ℝ (fun y => eval y p) x v = ∑ i, eval x (pderiv i p) * v i := by
  have hd : HasDerivAt (fun s : ℝ => x + s • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have hline : ∀ k, HasDerivAt (fun s => (x + s • v) k) (v k) (0 : ℝ) := by
    intro k
    convert ((hasDerivAt_id (0 : ℝ)).mul_const (v k)).const_add (x k)
      using 2 with s
    simp
  have hcomp := hasDerivAt_eval_comp p hline
  rw [zero_smul, add_zero] at hcomp
  have hcomp2 :=
    (((contDiff_eval p).differentiable (by simp)).differentiableAt.hasFDerivAt.comp 0
      hd.hasFDerivAt).hasDerivAt
  rw [zero_smul, add_zero] at hcomp2
  have heq : ((fderiv ℝ (fun y => eval y p) x).comp
      (ContinuousLinearMap.toSpanSingleton ℝ v)) 1 =
      fderiv ℝ (fun y => eval y p) x v := by
    simp [ContinuousLinearMap.comp_apply]
  rw [heq] at hcomp2
  exact (HasDerivAt.unique hcomp hcomp2).symm

theorem absolutelyContinuous_eval_comp {σ : Type*} (p : MvPolynomial σ ℝ) {y : ℝ → σ → ℝ}
    {a b : ℝ} (hy : ∀ k, AbsolutelyContinuousOnInterval (fun s => y s k) a b) :
    AbsolutelyContinuousOnInterval (fun s => eval (y s) p) a b := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    simpa using (LipschitzWith.const (α := ℝ) c).lipschitzOnWith.absolutelyContinuousOnInterval
      (a := a) (b := b)
  | add p q hp hq => simpa using hp.add hq
  | mul_X p i hp => simpa using hp.fun_mul (hy i)

/-- Integrated chain rule inequality. Let `y` be a curve with coordinates
`y(s)_k = c_k + ∫_{a₀}^s g_k`, the `g_k` being integrable on `[A, B] ∋ a₀`, and let
`[a, b] ⊆ [A, B]`. If `h ≤ ∇p(y) · g` almost everywhere on `[a, b]`, then
`∫_a^b h ≤ p(y(b)) - p(y(a))`. -/
theorem integral_le_eval_sub {σ : Type*} [Fintype σ] (p : MvPolynomial σ ℝ) {y : ℝ → σ → ℝ}
    {c : σ → ℝ} {g : σ → ℝ → ℝ} {a₀ A B a b : ℝ}
    (hy : ∀ s k, y s k = c k + ∫ t in a₀..s, g k t)
    (hg : ∀ k, IntervalIntegrable (g k) volume A B) (ha₀ : a₀ ∈ Icc A B)
    (hab : a ≤ b) (hsub : Icc a b ⊆ Icc A B) {h : ℝ → ℝ} (hh : IntervalIntegrable h volume a b)
    (hle : ∀ᵐ t, t ∈ Icc a b → h t ≤ ∑ k, eval (y t) (pderiv k p) * g k t) :
    ∫ t in a..b, h t ≤ eval (y b) p - eval (y a) p := by
  have hAB : A ≤ B := ha₀.1.trans ha₀.2
  have hyfun : ∀ k, (fun s => y s k) = fun s => c k + ∫ t in a₀..s, g k t :=
    fun k => funext fun s => hy s k
  have hyAC : ∀ k, AbsolutelyContinuousOnInterval (fun s => y s k) a b := by
    intro k
    rw [hyfun k]
    have h1 := (hg k).absolutelyContinuousOnInterval_intervalIntegral
      (c := a₀) (by rwa [uIcc_of_le hAB])
    have h2 : AbsolutelyContinuousOnInterval (fun s => c k + ∫ t in a₀..s, g k t) A B := by
      simpa using ((LipschitzWith.const (α := ℝ) (c k)).lipschitzOnWith
        |>.absolutelyContinuousOnInterval (a := A) (b := B)).add h1
    exact h2.mono (by rw [uIcc_of_le hab, uIcc_of_le hAB]; exact hsub)
  have hF := absolutelyContinuous_eval_comp p hyAC
  rw [← hF.integral_deriv_eq_sub]
  refine intervalIntegral.integral_mono_ae_restrict hab hh hF.intervalIntegrable_deriv ?_
  have hderiv : ∀ k, ∀ᵐ t, t ∈ uIcc A B → ∀ c' ∈ uIcc A B,
      HasDerivAt (fun x => ∫ s in c'..x, g k s) (g k t) t :=
    fun k => (hg k).ae_hasDerivAt_integral
  rw [← ae_all_iff] at hderiv
  rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Icc]
  filter_upwards [hderiv, hle] with t ht hlet htab
  have htAB : t ∈ uIcc A B := by rw [uIcc_of_le hAB]; exact hsub htab
  have hyd : ∀ k, HasDerivAt (fun s => y s k) (g k t) t := by
    intro k
    rw [hyfun k]
    exact (ht k htAB a₀ (by rwa [uIcc_of_le hAB])).const_add (c k)
  rw [(hasDerivAt_eval_comp p hyd).deriv]
  exact hlet htab

end CZExposure
