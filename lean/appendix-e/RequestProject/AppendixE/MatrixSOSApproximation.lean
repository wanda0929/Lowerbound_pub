module
public import RequestProject.AppendixE.MatrixSOSInput
public import RequestProject.AppendixE.Evaluation
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
public import Mathlib.Topology.Algebra.MvPolynomial
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric

/-! M3: polynomial approximation of continuous matrix square roots on compact
sets, with entrywise control of the resulting Gram error. -/
@[expose] public section
noncomputable section
namespace CZExposure.PolynomialGeometry
open MvPolynomial Set Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator

variable {σ : Type} {k : ℕ}

/-- Polynomial evaluation restricted to a set, as a real algebra homomorphism. -/
def polynomialEvalOn (K : Set (σ → ℝ)) : MvPolynomial σ ℝ →ₐ[ℝ] C(K, ℝ) where
  toFun p := ⟨fun x => eval x.val p, p.continuous_eval.comp continuous_subtype_val⟩
  map_zero' := by ext; simp
  map_one' := by ext; simp
  map_add' p q := by ext; simp
  map_mul' p q := by ext; simp
  commutes' r := by ext; simp

/-- Uniform polynomial approximation on any compact real coordinate set;
no extension of the target function outside the set is required. -/
theorem exists_polynomial_near_continuous (K : Set (σ → ℝ)) (hK : IsCompact K)
    (f : C(K, ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : MvPolynomial σ ℝ, ∀ x : K, |eval x.val p - f x| < ε := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let P := polynomialEvalOn K
  have hsep : P.range.SeparatesPoints := by
    intro x y hxy
    have hne : (x.val : σ → ℝ) ≠ y.val := Subtype.coe_ne_coe.mpr hxy
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
    refine ⟨P (X i), ⟨P (X i), ⟨X i, rfl⟩, rfl⟩, ?_⟩
    simpa [P, polynomialEvalOn] using hi
  obtain ⟨g, hg⟩ :=
    ContinuousMap.exists_mem_subalgebra_near_continuous_of_separatesPoints
      P.range hsep f f.continuous ε hε
  obtain ⟨p, hp⟩ := g.property
  refine ⟨p, fun x => ?_⟩
  simpa only [← hp, P, polynomialEvalOn, ContinuousMap.coe_mk, Real.norm_eq_abs] using hg x

/-- The real matrix functional calculus is isometric in the operator norm.
Unlike complex C-star algebras, real matrices need this spectral argument. -/
private theorem realMatrixIsometricCFC :
    IsometricContinuousFunctionalCalculus ℝ (Matrix (Fin k) (Fin k) ℝ) IsSelfAdjoint where
  isometric A hA := by
    have h : A.IsHermitian := hA
    rw [cfcHom_eq_of_continuous_of_map_id hA h.cfcAux
      h.isClosedEmbedding_cfcAux.continuous h.cfcAux_id]
    apply (AddMonoidHomClass.isometry_iff_norm h.cfcAux).mpr
    intro f
    rw [Matrix.IsHermitian.cfcAux_apply, Unitary.conjStarAlgAut_apply,
      CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem h.eigenvectorUnitary.prop),
      CStarRing.norm_coe_unitary_mul,
      Matrix.l2_opNorm_diagonal]
    change ‖fun i => f ⟨h.eigenvalues i, h.eigenvalues_mem_spectrum_real i⟩‖ = ‖f‖
    apply le_antisymm
    · exact (pi_norm_le_iff_of_nonneg (norm_nonneg f)).mpr
        (fun i => f.norm_coe_le_norm _)
    · apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
      intro x
      have hxrange : (x:ℝ) ∈ Set.range h.eigenvalues := by
        rw [← h.spectrum_real_eq_range_eigenvalues]
        exact x.property
      obtain ⟨i, hi⟩ := hxrange
      have hx : x = ⟨h.eigenvalues i, h.eigenvalues_mem_spectrum_real i⟩ :=
        Subtype.ext hi.symm
      rw [hx]
      exact norm_le_pi_norm (fun j => f ⟨h.eigenvalues j, h.eigenvalues_mem_spectrum_real j⟩) i

/-- The positive semidefinite square root is continuous even at rank loss.
The operator norm is used only to access the C-star functional calculus;
its topology agrees with the entrywise matrix topology. -/
theorem continuous_matrix_sqrt {X : Type*} [TopologicalSpace X]
    (A : X → Matrix (Fin k) (Fin k) ℝ) (hA : Continuous A)
    (hp : ∀ x, (A x).PosSemidef) : Continuous (fun x => CFC.sqrt (A x)) := by
  letI := realMatrixIsometricCFC (k := k)
  exact CFC.continuousOn_sqrt.comp_continuous hA (fun x => (hp x).nonneg)

/-- The canonical square root is an exact Gram factor, including singular
and zero-dimensional matrices. -/
theorem matrix_sqrt_gram (A : Matrix (Fin k) (Fin k) ℝ) (hp : A.PosSemidef) :
    (CFC.sqrt A).transpose * CFC.sqrt A = A := by
  have hs := (CFC.sqrt_nonneg A).posSemidef.isHermitian
  have ht : (CFC.sqrt A).transpose = CFC.sqrt A := by
    simpa only [IsHermitian, conjTranspose_eq_transpose_of_trivial] using hs
  rw [ht]
  exact CFC.sqrt_mul_sqrt_self A hp.nonneg

/-- Simultaneous entrywise polynomial approximation uses one finite matrix,
with one common tolerance for every entry and every point. -/
theorem exists_polynomial_matrix_near (K : Set (σ → ℝ)) (hK : IsCompact K)
    (S : K → Matrix (Fin k) (Fin k) ℝ) (hS : Continuous S)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ H : Matrix (Fin k) (Fin k) (MvPolynomial σ ℝ),
      ∀ x : K, ∀ i j, |eval x.val (H i j) - S x i j| < ε := by
  have hex (i j : Fin k) := exists_polynomial_near_continuous K hK
    ⟨fun x => S x i j, (continuous_apply j).comp ((continuous_apply i).comp hS)⟩ hε
  choose H hH using hex
  exact ⟨H, fun x i j => hH i j x⟩

/-- Entrywise factor error δ gives Gram error at most k δ (2M+δ),
where M bounds the entries of the exact factor. -/
theorem gram_entry_error_le (U V : Matrix (Fin k) (Fin k) ℝ)
    {M δ : ℝ} (hM : 0 ≤ M) (hδ : 0 ≤ δ)
    (hV : ∀ i j, |V i j| ≤ M) (hUV : ∀ i j, |U i j - V i j| ≤ δ)
    (i j : Fin k) :
    |(U.transpose * U) i j - (V.transpose * V) i j| ≤ (k:ℝ)*δ*(2*M+δ) := by
  have hU (l m : Fin k) : |U l m| ≤ M+δ := by
    calc |U l m| = |(U l m-V l m)+V l m| := by congr 1; ring
      _ ≤ |U l m-V l m|+|V l m| := abs_add_le _ _
      _ ≤ M+δ := by linarith [hUV l m, hV l m]
  simp only [Matrix.mul_apply, transpose_apply, ← Finset.sum_sub_distrib]
  calc
    |∑ l, (U l i * U l j - V l i * V l j)|
      ≤ ∑ l, |U l i * U l j - V l i * V l j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _l : Fin k, δ*(2*M+δ) := by
      apply Finset.sum_le_sum
      intro l _
      calc
        |U l i*U l j - V l i*V l j|
          = |(U l i-V l i)*U l j + V l i*(U l j-V l j)| := by congr 1; ring
        _ ≤ |U l i-V l i| * |U l j| + |V l i| * |U l j-V l j| := by
          simpa only [abs_mul] using abs_add_le ((U l i-V l i)*U l j)
            (V l i*(U l j-V l j))
        _ ≤ δ*(M+δ)+M*δ := add_le_add
          (mul_le_mul (hUV l i) (hU l j) (abs_nonneg _) hδ)
          (mul_le_mul (hV l i) (hUV l j) (abs_nonneg _) hM)
        _ = δ*(2*M+δ) := by ring
    _ = (k:ℝ)*δ*(2*M+δ) := by simp; ring

/-- M3 on a compact coordinate set: approximate the canonical continuous
square root and its Gram product with the same finite polynomial matrix.
The conclusion is approximation, not an exact SOS identity. -/
theorem exists_polynomial_sqrt_gram_approximation
    (K : Set (σ → ℝ)) (hK : IsCompact K)
    (A : K → Matrix (Fin k) (Fin k) ℝ) (hA : Continuous A)
    (hp : ∀ x, (A x).PosSemidef) {ε : ℝ} (hε : 0 < ε) :
    ∃ H : Matrix (Fin k) (Fin k) (MvPolynomial σ ℝ), ∀ x : K, ∀ i j,
      |eval x.val (H i j) - CFC.sqrt (A x) i j| < ε ∧
      |((H.map (eval x.val)).transpose * H.map (eval x.val)) i j - A x i j| < ε := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let S : K → Matrix (Fin k) (Fin k) ℝ := fun x => CFC.sqrt (A x)
  have hS : Continuous S := continuous_matrix_sqrt A hA hp
  let f (i j : Fin k) : C(K, ℝ) :=
    ⟨fun x => S x i j, (continuous_apply j).comp ((continuous_apply i).comp hS)⟩
  let M : ℝ := ∑ i, ∑ j, ‖f i j‖
  have hM : 0 ≤ M := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hbound (x : K) (i j : Fin k) : |S x i j| ≤ M := by
    apply (show |S x i j| ≤ ‖f i j‖ by exact (f i j).norm_coe_le_norm x).trans
    exact (Finset.single_le_sum (fun m _ => norm_nonneg (f i m)) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (fun l _ => Finset.sum_nonneg fun m _ => norm_nonneg (f l m))
        (Finset.mem_univ i))
  let D : ℝ := (k:ℝ)*(2*M+1)+1
  have hD : 0 < D := by dsimp [D]; positivity
  let δ : ℝ := min ε (min 1 (ε/D)) / 2
  have hmin : 0 < min ε (min 1 (ε/D)) := lt_min hε (lt_min zero_lt_one (div_pos hε hD))
  have hd : 0 < δ := half_pos hmin
  have hdε : δ < ε := by dsimp [δ]; linarith [min_le_left ε (min 1 (ε/D))]
  have hd1 : δ ≤ 1 := by
    dsimp [δ]
    linarith [(min_le_right ε (min 1 (ε/D))).trans (min_le_left 1 (ε/D))]
  have hdD : δ*D < ε := by
    apply (lt_div_iff₀ hD).mp
    dsimp [δ]
    linarith [(min_le_right ε (min 1 (ε/D))).trans (min_le_right 1 (ε/D))]
  obtain ⟨H, hH⟩ := exists_polynomial_matrix_near K hK S hS hd
  refine ⟨H, fun x i j => ⟨(hH x i j).trans hdε, ?_⟩⟩
  have hgram : (S x).transpose * S x = A x := matrix_sqrt_gram (A x) (hp x)
  rw [← hgram]
  apply (gram_entry_error_le (H.map (eval x.val)) (S x) hM hd.le
    (hbound x) (fun i j => (hH x i j).le) i j).trans_lt
  have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
  calc (k:ℝ)*δ*(2*M+δ) ≤ (k:ℝ)*δ*(2*M+1) :=
        mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hk hd.le)
    _ ≤ δ*D := by dsimp [D]; nlinarith
    _ < ε := hdD

/-- The coordinate Archimedean witness supplies compactness of the full
real zero set. Empty zero sets and zero coordinate dimensions are allowed. -/
theorem IdealArchimedean.isCompact_realZeroSet [Fintype σ]
    (I : Ideal (MvPolynomial σ ℝ)) (hI : IdealArchimedean I) :
    IsCompact {x : σ → ℝ | ∀ p ∈ I, eval x p = 0} := by
  classical
  obtain ⟨N, d, s, hs, hi⟩ := hI
  have hclosed : IsClosed {x : σ → ℝ | ∀ p ∈ I, eval x p = 0} := by
    simp only [setOf_forall]
    exact isClosed_iInter fun p => isClosed_iInter fun (_ : p ∈ I) =>
      isClosed_eq p.continuous_eval continuous_const
  apply (isCompact_univ_pi (fun _ : σ => isCompact_Icc
    (a := -(N:ℝ)-1) (b := (N:ℝ)+1))).of_isClosed_subset hclosed
  intro x hx i _
  have he := hx _ hi
  simp only [eval_sub, eval_C, map_sum, map_pow, eval_X] at he
  have hsum : ∑ j : σ, x j ^ 2 ≤ (N:ℝ) := by linarith [hs.eval_nonneg x]
  have hxi : x i ^ 2 ≤ (N:ℝ) :=
    (Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)).trans hsum
  constructor
  · nlinarith [sq_nonneg (x i + 1/2)]
  · nlinarith [sq_nonneg (x i - 1/2)]

/-- M3 specialized to the exact polynomial-matrix/ideal interface used by
the pending matrix Positivstellensatz. Compactness and continuity are proved,
not added as new inputs. -/
theorem IdealArchimedean.polynomial_matrix_gram_approximation [Fintype σ]
    (I : Ideal (MvPolynomial σ ℝ)) (hI : IdealArchimedean I)
    (A : Matrix (Fin k) (Fin k) (MvPolynomial σ ℝ))
    (hp : ∀ x : σ → ℝ, (∀ p ∈ I, eval x p = 0) → (A.map (eval x)).PosSemidef)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ H : Matrix (Fin k) (Fin k) (MvPolynomial σ ℝ),
      ∀ x : σ → ℝ, (∀ p ∈ I, eval x p = 0) → ∀ i j,
        |eval x (H i j) - CFC.sqrt (A.map (eval x)) i j| < ε ∧
        |eval x (A i j - ∑ l, H l i * H l j)| < ε := by
  let K := {x : σ → ℝ | ∀ p ∈ I, eval x p = 0}
  have hc : Continuous (fun x : K => A.map (eval x.val)) := by
    apply continuous_pi; intro i
    apply continuous_pi; intro j
    exact (A i j).continuous_eval.comp continuous_subtype_val
  obtain ⟨H, hH⟩ := exists_polynomial_sqrt_gram_approximation K
    (hI.isCompact_realZeroSet I) (fun x : K => A.map (eval x.val)) hc
    (fun x => hp x.val x.property) hε
  refine ⟨H, fun x hx i j => ⟨(hH ⟨x, hx⟩ i j).1, ?_⟩⟩
  have he := (hH ⟨x, hx⟩ i j).2
  simpa only [Matrix.mul_apply, transpose_apply, Matrix.map_apply, eval_sub,
    map_sum, map_mul, abs_sub_comm] using he

end CZExposure.PolynomialGeometry
