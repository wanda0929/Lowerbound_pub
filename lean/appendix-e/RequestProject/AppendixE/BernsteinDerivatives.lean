module
public import RequestProject.AppendixE.BernsteinConvergence

/-! Coordinate slices and the derivative of the tensor Bernstein polynomial. -/
@[expose] public section
noncomputable section
namespace CZExposure.BernsteinC1
open Polynomial Finset Filter
open scoped Topology

def insertIndex {d : ℕ} (i : Fin d) (r : {j : Fin d // j ≠ i} → ℕ)
    (m : ℕ) (j : Fin d) : ℕ := if h : j = i then m else r ⟨j, h⟩

def restBasis {d : ℕ} (N : Fin d → ℕ) (i : Fin d)
    (r : {j : Fin d // j ≠ i} → ℕ) : MvPolynomial (Fin d) ℝ :=
  ∏ j : {j : Fin d // j ≠ i}, coordinateBasis j (N j) (r j)

theorem tensorBasis_insert {d : ℕ} (N : Fin d → ℕ) (i : Fin d)
    (r : {j : Fin d // j ≠ i} → ℕ) (m : ℕ) :
    tensorBasis N (insertIndex i r m) = coordinateBasis i (N i) m * restBasis N i r := by
  classical
  unfold tensorBasis
  rw [← prod_erase_mul _ _ (mem_univ i), mul_comm]
  simp only [insertIndex]
  congr 1
  rw [Finset.prod_subtype (F := inferInstance) (univ.erase i)
    (by simp : ∀ j : Fin d, j ∈ univ.erase i ↔ j ≠ i)]
  unfold restBasis
  apply prod_congr rfl
  intro j _
  simp [j.property]

theorem tensorSampled_slices {d : ℕ} (N : Fin d → ℕ) (i : Fin d)
    (f : (Fin d → ℕ) → ℝ) :
    tensorSampled N (fun k => f (fun j => k j)) =
      ∑ r : ∀ j : {j : Fin d // j ≠ i}, Fin (N j + 1),
        (aeval (MvPolynomial.X i) (sampled (N i) (fun m => f (insertIndex i (fun j => r j) m)))) *
          restBasis N i (fun j => r j) := by
  classical
  unfold tensorSampled
  rw [← (Equiv.piSplitAt i (fun j => Fin (N j + 1))).symm.sum_comp]
  rw [Fintype.sum_prod_type, sum_comm]
  apply sum_congr rfl
  intro r _
  have he (m : Fin (N i + 1)) :
      (fun j => ((Equiv.piSplitAt i (fun j => Fin (N j + 1))).symm (m, r) j : ℕ)) =
        insertIndex i (fun j => r j) m := by
    funext j
    by_cases h : j = i
    · subst j; simp [Equiv.piSplitAt, insertIndex]
    · simp [Equiv.piSplitAt, insertIndex, h]
  simp_rw [he, tensorBasis_insert]
  simp [sampled, coordinateBasis, Finset.sum_range, mul_assoc, Finset.sum_mul]

theorem pderiv_restBasis {d : ℕ} (N : Fin d → ℕ) (i : Fin d)
    (r : {j : Fin d // j ≠ i} → ℕ) :
    MvPolynomial.pderiv i (restBasis N i r) = 0 := by
  classical
  unfold restBasis
  have h (s : Finset {j : Fin d // j ≠ i}) :
      MvPolynomial.pderiv i (∏ j ∈ s, coordinateBasis j (N j) (r j)) = 0 := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert j s hj ih =>
      rw [prod_insert hj, Derivation.leibniz]
      simp [ih, pderiv_coordinateBasis, j.property.symm]
  exact h univ

/-- Exact partial derivative regrouping; all slices use the same original samples. -/
theorem pderiv_tensorSampled_slices {d : ℕ} (N : Fin d → ℕ) (i : Fin d)
    (n : ℕ) (hNi : N i = n + 1) (f : (Fin d → ℕ) → ℝ) :
    MvPolynomial.pderiv i (tensorSampled N (fun k => f (fun j => k j))) =
      ∑ r : ∀ j : {j : Fin d // j ≠ i}, Fin (N j + 1),
        (MvPolynomial.C (n + 1 : ℝ) *
          aeval (MvPolynomial.X i) (sampled n (fun m =>
            f (insertIndex i (fun j => r j) (m + 1)) -
              f (insertIndex i (fun j => r j) m)))) * restBasis N i (fun j => r j) := by
  rw [tensorSampled_slices N i f, map_sum]
  apply sum_congr rfl
  intro r _
  rw [Derivation.leibniz, pderiv_restBasis, hNi, pderiv_sampled]
  simp [mul_comm]

def realPoint {d : ℕ} (x : Cube d) : Fin d → ℝ := fun j => x j

def partialValue {d : ℕ} (f : (Fin d → ℝ) → ℝ) (i : Fin d) (x : Cube d) : ℝ :=
  fderiv ℝ f (realPoint x) (Pi.single i 1)

theorem partialValue_continuous {d : ℕ} (f : (Fin d → ℝ) → ℝ)
    (hf : ContDiff ℝ 1 f) (i : Fin d) : Continuous (partialValue f i) := by
  have hr : Continuous (realPoint : Cube d → (Fin d → ℝ)) := by
    unfold realPoint; fun_prop
  exact ((hf.continuous_fderiv (by decide)).comp hr).clm_apply continuous_const

/-- Uniform secant control with a nearby reference point. The reference need
not be the left endpoint, which accounts for the degree-lowered grid. -/
theorem uniform_secant {d : ℕ} (f : (Fin d → ℝ) → ℝ)
    (hf : ContDiff ℝ 1 f) (i : Fin d) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ x y : Cube d, ∀ h : ℝ, 0 < h →
      (x i : ℝ) + h ≤ 1 → h + dist x y < δ →
      |(f (Function.update (realPoint x) i ((x i : ℝ) + h)) - f (realPoint x)) / h -
        partialValue f i y| < ε := by
  obtain ⟨δ, hδ, hm⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous (partialValue_continuous f hf i)) ε hε
  refine ⟨δ, hδ, ?_⟩
  intro x y h hh hend hnear
  let g := fun t : ℝ => f (Function.update (realPoint x) i t)
  have hg : ContDiff ℝ 1 g := hf.comp (contDiff_update 1 (realPoint x) i)
  obtain ⟨t, ht, hs⟩ := exists_deriv_eq_slope g (by linarith : (x i : ℝ) < x i + h)
    hg.continuous.continuousOn (hg.differentiable (by decide)).differentiableOn
  have htI : t ∈ unitInterval := ⟨le_trans (x i).property.1 ht.1.le, ht.2.le.trans hend⟩
  let z : Cube d := Function.update x i ⟨t, htI⟩
  have hz : realPoint z = Function.update (realPoint x) i t := by
    funext j
    by_cases hj : j = i
    · subst j; simp [realPoint, z]
    · simp [realPoint, z, hj]
  have hd : deriv g t = partialValue f i z := by
    have he := (hf.differentiable (by decide) (Function.update (realPoint x) i t)).hasFDerivAt
      |>.comp_hasDerivAt t (hasDerivAt_update (realPoint x) i t)
    simpa [g, partialValue, hz] using he.deriv
  have hzdist : dist z x ≤ h := by
    apply (dist_pi_le_iff hh.le).mpr
    intro j
    by_cases hj : j = i
    · subst j
      simp only [z, Function.update_self, Subtype.dist_eq, Real.dist_eq]
      rw [abs_of_pos (sub_pos.mpr ht.1)]
      linarith [ht.2]
    · simp [z, Function.update_of_ne hj, hh.le]
  have hn : dist z y < δ := lt_of_le_of_lt
    ((dist_triangle z x y).trans (add_le_add hzdist le_rfl)) hnear
  have he := hm hn
  rw [Real.dist_eq] at he
  rw [← hd, hs] at he
  have hx : Function.update (realPoint x) i (x i : ℝ) = realPoint x :=
    Function.update_eq_self i (realPoint x)
  simpa [g, hx] using he

def derivativeDegrees {d : ℕ} (n : ℕ) (i : Fin d) (j : Fin d) : ℕ :=
  if j = i then n else n + 1

def cellBase {d : ℕ} (n : ℕ) (i : Fin d) (k : Grid (derivativeDegrees n i)) : Cube d :=
  fun j => ⟨(k j : ℝ) / (n + 1), by
    have hk : (k j : ℕ) ≤ n + 1 := by
      have h := (k j).is_le
      unfold derivativeDegrees at h
      split_ifs at h <;> omega
    constructor
    · positivity
    · apply (div_le_one (by positivity : (0 : ℝ) < n + 1)).mpr
      exact_mod_cast hk⟩

theorem cellBase_end {d : ℕ} (n : ℕ) (i : Fin d) (k : Grid (derivativeDegrees n i)) :
    (cellBase n i k i : ℝ) + 1 / (n + 1) ≤ 1 := by
  have hk : (k i : ℕ) ≤ n := by simpa [derivativeDegrees] using (k i).is_le
  change (k i : ℝ) / (n + 1) + 1 / (n + 1) ≤ 1
  rw [← add_div]
  apply (div_le_one (by positivity : (0 : ℝ) < n + 1)).mpr
  exact_mod_cast Nat.add_le_add_right hk 1

theorem cellBase_distance {d : ℕ} {n : ℕ} (hn : 0 < n) (i : Fin d)
    (k : Grid (derivativeDegrees n i)) :
    dist (cellBase n i k) (node k) ≤ 1 / (n + 1) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  apply (dist_pi_le_iff (by positivity)).mpr
  intro j
  rw [Subtype.dist_eq, Real.dist_eq]
  by_cases hj : j = i
  · subst j
    have hk : (k i : ℝ) ≤ n := by exact_mod_cast (show (k i : ℕ) ≤ n from
      by simpa [derivativeDegrees] using (k i).is_le)
    simp only [cellBase, node, bernstein.z, derivativeDegrees, ite_true]
    apply abs_le.mpr
    constructor <;> (field_simp; nlinarith [(show (0 : ℝ) ≤ (k i : ℝ) by positivity)])
  · simp [cellBase, node, bernstein.z, derivativeDegrees, hj]
    positivity

def differenceCoefficient {d : ℕ} (f : (Fin d → ℝ) → ℝ) (n : ℕ) (i : Fin d)
    (k : Grid (derivativeDegrees n i)) : ℝ :=
  (f (Function.update (realPoint (cellBase n i k)) i
      ((cellBase n i k i : ℝ) + 1 / (n + 1))) - f (realPoint (cellBase n i k))) /
    (1 / (n + 1))

/-- Uniform over every sample index, with no second derivative assumption. -/
theorem differenceCoefficient_uniform {d : ℕ} (f : (Fin d → ℝ) → ℝ)
    (hf : ContDiff ℝ 1 f) (i : Fin d) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ k : Grid (derivativeDegrees n i),
      |differenceCoefficient f n i k - partialValue f i (node k)| ≤ ε := by
  intro ε hε
  obtain ⟨δ, hδ, hs⟩ := uniform_secant f hf i hε
  have ht : Tendsto (fun n : ℕ => (2 : ℝ) / (n + 1)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      (tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ)).comp (tendsto_add_atTop_nat 1)
  filter_upwards [ht.eventually_lt_const hδ, eventually_gt_atTop 0] with n hn hn0 k
  apply (hs (cellBase n i k) (node k) (1/(n+1)) (by positivity) (cellBase_end n i k) ?_).le
  have hd := cellBase_distance hn0 i k
  rw [show (2 : ℝ) / (n + 1) = 1 / (n + 1) + 1 / (n + 1) by ring] at hn
  linarith

/-- The mixed-degree Bernstein average of the actual differences converges
uniformly to the corresponding partial derivative. -/
theorem differenceAverage_uniform {d : ℕ} (f : (Fin d → ℝ) → ℝ)
    (hf : ContDiff ℝ 1 f) (i : Fin d) :
    TendstoUniformly (fun n x => ∑ k, differenceCoefficient f n i k *
      weight (derivativeDegrees n i) x k) (partialValue f i) atTop := by
  apply sampled_uniform (fun n => derivativeDegrees n i) ?_
    (partialValue f i) (partialValue_continuous f hf i)
    (fun n => differenceCoefficient f n i) (differenceCoefficient_uniform f hf i)
  intro j
  by_cases hj : j = i
  · simpa [derivativeDegrees, hj] using (tendsto_id : Tendsto (fun n : ℕ => n) atTop atTop)
  · simpa [derivativeDegrees, hj] using tendsto_add_atTop_nat 1

theorem pderiv_tensorSampled_update {d : ℕ} (N : Fin d → ℕ) (i : Fin d)
    (n : ℕ) (f : (Fin d → ℕ) → ℝ) :
    MvPolynomial.pderiv i (tensorSampled (Function.update N i (n+1))
      (fun k => f (fun j => k j))) =
    tensorSampled (Function.update N i n) (fun k => (n+1 : ℝ) *
      (f (Function.update (fun j => (k j : ℕ)) i ((k i : ℕ)+1)) - f (fun j => k j))) := by
  classical
  rw [pderiv_tensorSampled_slices _ i n (by simp)]
  rw [tensorSampled_slices _ i (fun k => (n+1 : ℝ) *
    (f (Function.update k i (k i+1)) - f k))]
  simp only [Function.update_self]
  have hr (m : ℕ) (j : {j : Fin d // j ≠ i}) : Function.update N i m j = N j := by
    simp [j.property]
  let e := Equiv.piCongrRight (fun j : {j : Fin d // j ≠ i} =>
    finCongr (congrArg (· + 1) ((hr (n+1) j).trans (hr n j).symm)))
  apply Fintype.sum_equiv e
  intro r
  change _ = (aeval (MvPolynomial.X i) (sampled n (fun m => (n+1 : ℝ) *
    (f (Function.update (insertIndex i (fun j => r j) m) i
      (insertIndex i (fun j => r j) m i+1)) - f (insertIndex i (fun j => r j) m))))) *
    restBasis (Function.update N i n) i (fun j => r j)
  have hb : restBasis (Function.update N i (n+1)) i (fun j => r j) =
      restBasis (Function.update N i n) i (fun j => r j) := by
    unfold restBasis
    apply prod_congr rfl
    intro j _
    simp [j.property]
  rw [hb]
  congr 1
  have hi (m : ℕ) : Function.update (insertIndex i (fun j => r j) m) i
      (insertIndex i (fun j => r j) m i + 1) = insertIndex i (fun j => r j) (m+1) := by
    funext j
    by_cases hj : j = i
    · subst j; simp [insertIndex]
    · simp [insertIndex, hj]
  simp_rw [hi]
  simp [sampled, map_sum, Finset.mul_sum, mul_assoc]

def approximant {d : ℕ} (f : (Fin d → ℝ) → ℝ) (n : ℕ) : MvPolynomial (Fin d) ℝ :=
  tensorSampled (fun _ => n+1) (fun k => f (fun j => (k j : ℝ) / (n+1)))

theorem pderiv_approximant {d : ℕ} (f : (Fin d → ℝ) → ℝ) (n : ℕ) (i : Fin d) :
    MvPolynomial.pderiv i (approximant f n) =
      tensorSampled (derivativeDegrees n i) (differenceCoefficient f n i) := by
  have hu : Function.update (fun _ : Fin d => n+1) i (n+1) = (fun _ => n+1) :=
    Function.update_eq_self i (fun _ => n+1)
  have hd : Function.update (fun _ : Fin d => n+1) i n = derivativeDegrees n i := by
    funext j
    by_cases hj : j = i
    · subst j; simp [derivativeDegrees]
    · simp [derivativeDegrees, hj]
  have h := pderiv_tensorSampled_update (fun _ => n+1) i n
    (fun k => f (fun j => (k j : ℝ) / (n+1)))
  rw [hu, hd] at h
  rw [approximant, h]
  congr 1
  funext k
  have hp : (fun j => ((Function.update (fun j => (k j : ℕ)) i ((k i : ℕ)+1) j : ℕ) : ℝ) / (n+1)) =
      Function.update (realPoint (cellBase n i k)) i ((cellBase n i k i : ℝ) + 1/(n+1)) := by
    funext j
    by_cases hj : j = i
    · subst j; simp [cellBase, add_div]
    · simp [realPoint, cellBase, hj]
  rw [hp]
  unfold differenceCoefficient
  rw [div_div_eq_mul_div, div_one]
  exact mul_comm _ _

theorem eval_approximant_uniform {d : ℕ} (f : (Fin d → ℝ) → ℝ) (hf : Continuous f) :
    TendstoUniformly (fun (n : ℕ) (x : Cube d) => MvPolynomial.eval (realPoint x) (approximant f n))
      (fun x => f (realPoint x)) atTop := by
  have hr : Continuous (realPoint : Cube d → (Fin d → ℝ)) := by unfold realPoint; fun_prop
  have h := average_uniform (fun n (_ : Fin d) => n+1)
    (fun _ => tendsto_add_atTop_nat 1) (fun x => f (realPoint x)) (hf.comp hr)
  have he (n : ℕ) (x : Cube d) : MvPolynomial.eval (realPoint x) (approximant f n) =
      average (fun _ => n+1) (fun x => f (realPoint x)) x := by
    rw [average_polynomial]
    apply congrArg (MvPolynomial.eval (realPoint x))
    unfold approximant
    congr 1
    funext k
    congr 1
    funext j
    simp [realPoint, node, bernstein.z]
  simp_rw [he]
  exact h

theorem eval_pderiv_approximant_uniform {d : ℕ} (f : (Fin d → ℝ) → ℝ)
    (hf : ContDiff ℝ 1 f) (i : Fin d) :
    TendstoUniformly (fun (n : ℕ) (x : Cube d) =>
      MvPolynomial.eval (realPoint x) (MvPolynomial.pderiv i (approximant f n)))
      (partialValue f i) atTop := by
  simp_rw [pderiv_approximant]
  simpa [tensorSampled, eval_tensorBasis, realPoint, weight, bernstein]
    using differenceAverage_uniform f hf i

/-- One order works for the value and every partial derivative, on the closed cube. -/
theorem exists_cube_C1 {d : ℕ} (f : (Fin d → ℝ) → ℝ) (hf : ContDiff ℝ 1 f)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ P : MvPolynomial (Fin d) ℝ,
      (∀ x : Cube d, |MvPolynomial.eval (realPoint x) P - f (realPoint x)| ≤ ε) ∧
      (∀ (x : Cube d) (i : Fin d),
        |MvPolynomial.eval (realPoint x) (MvPolynomial.pderiv i P) - partialValue f i x| ≤ ε) := by
  have hv := Metric.tendstoUniformly_iff.mp (eval_approximant_uniform f hf.continuous) ε hε
  have hp : ∀ᶠ n in atTop, ∀ i : Fin d, ∀ x : Cube d,
      dist (partialValue f i x)
        (MvPolynomial.eval (realPoint x) (MvPolynomial.pderiv i (approximant f n))) < ε := by
    rw [Filter.eventually_all]
    intro i
    exact Metric.tendstoUniformly_iff.mp (eval_pderiv_approximant_uniform f hf i) ε hε
  obtain ⟨n, hn, hni⟩ := (hv.and hp).exists
  refine ⟨approximant f n, fun x => ?_, fun x i => ?_⟩
  · simpa [Real.dist_eq, abs_sub_comm] using (hn x).le
  · simpa [Real.dist_eq, abs_sub_comm] using (hni i x).le

end CZExposure.BernsteinC1
