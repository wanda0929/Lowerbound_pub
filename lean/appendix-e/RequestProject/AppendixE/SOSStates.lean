module
public import RequestProject.AppendixE.SOSSeparation
public import Mathlib.Analysis.Convex.KreinMilman

/-! Compactness and multiplicativity of extreme normalized SOS-positive
functionals, in the topology of pointwise convergence. -/
@[expose] public section
noncomputable section
namespace CZExposure.PolynomialGeometry
open Set

variable {A : Type*} [CommRing A] [Algebra ℝ A]

/-- States are represented as functions so their topology is the product
topology, not an unprovided norm topology on the algebraic dual. -/
def sosStates (A : Type*) [CommRing A] [Algebra ℝ A] : Set (A → ℝ) :=
  {L | (∀ x y, L (x+y) = L x + L y) ∧
    (∀ (r : ℝ) x, L (r • x) = r * L x) ∧ L 1 = 1 ∧
    ∀ x, IsSumSq x → 0 ≤ L x}

def sosStateLinearMap {L : A → ℝ} (hL : L ∈ sosStates A) : A →ₗ[ℝ] ℝ where
  toFun := L
  map_add' := hL.1
  map_smul' := hL.2.1

theorem linearMap_mem_sosStates (L : A →ₗ[ℝ] ℝ) (h1 : L 1 = 1)
    (hp : ∀ x, IsSumSq x → 0 ≤ L x) : (L : A → ℝ) ∈ sosStates A :=
  ⟨L.map_add, L.map_smul, h1, hp⟩

theorem isClosed_sosStates : IsClosed (sosStates A) := by
  simp only [sosStates, setOf_and, setOf_forall]
  apply IsClosed.inter
    (isClosed_iInter fun x => isClosed_iInter fun y =>
      isClosed_eq (continuous_apply (x+y)) ((continuous_apply x).add (continuous_apply y)))
  apply IsClosed.inter
    (isClosed_iInter fun r => isClosed_iInter fun x =>
      isClosed_eq (continuous_apply (r • x)) (continuous_const.mul (continuous_apply x)))
  exact (isClosed_eq (continuous_apply 1) continuous_const).inter
    (isClosed_iInter fun x => isClosed_iInter fun (_ : IsSumSq x) =>
      isClosed_le continuous_const (continuous_apply x))

theorem sosState_bounds {L : A → ℝ} (hL : L ∈ sosStates A) {N : ℕ} {a : A}
    (hp : IsSumSq ((N:A)+a)) (hm : IsSumSq ((N:A)-a)) :
    -(N:ℝ) ≤ L a ∧ L a ≤ N := by
  let l := sosStateLinearMap hL
  have hnat : l (N:A) = (N:ℝ) := by
    have h := l.map_smul (N:ℝ) (1:A)
    simpa [l, sosStateLinearMap, Algebra.smul_def, hL.2.2.1] using h
  have h1 : 0 ≤ l ((N:A)+a) := hL.2.2.2 _ hp
  have h2 : 0 ≤ l ((N:A)-a) := hL.2.2.2 _ hm
  rw [map_add, hnat] at h1
  rw [map_sub, hnat] at h2
  change -(N:ℝ) ≤ l a ∧ l a ≤ N
  constructor <;> linarith

theorem isCompact_sosStates
    (hb : ∀ x : A, ∃ N : ℕ, IsSumSq ((N:A)+x) ∧ IsSumSq ((N:A)-x)) :
    IsCompact (sosStates A) := by
  choose N hN using hb
  apply (isCompact_univ_pi (fun a : A => isCompact_Icc (a := -(N a:ℝ))
    (b := (N a:ℝ)))).of_isClosed_subset isClosed_sosStates
  intro L hL a _
  exact sosState_bounds hL (hN a).1 (hN a).2

/-- Multiplying a state by a positive algebra element and renormalizing
produces another state; commutativity makes the SOS cone multiplicative. -/
def weightedSOSState (L : A →ₗ[ℝ] ℝ) (b : A) : A →ₗ[ℝ] ℝ :=
  (L b)⁻¹ • (L.comp (LinearMap.mul ℝ A b))

theorem weightedSOSState_mem (L : A →ₗ[ℝ] ℝ)
    (hp : ∀ x, IsSumSq x → 0 ≤ L x) {b : A} (hb : IsSumSq b) (hLb : 0 < L b) :
    (weightedSOSState L b : A → ℝ) ∈ sosStates A := by
  apply linearMap_mem_sosStates
  · simp [weightedSOSState, hLb.ne']
  · intro x hx
    exact mul_nonneg (inv_nonneg.mpr hLb.le) (hp _ (hb.mul hx))

/-- Extreme states are real characters. Both components of the convex
decomposition have strictly positive normalization, including boundary cases. -/
theorem extreme_sosState_mul
    (hb : ∀ x : A, ∃ N : ℕ, IsSumSq ((N:A)+x) ∧ IsSumSq ((N:A)-x))
    {L : A → ℝ} (hL : L ∈ (sosStates A).extremePoints ℝ) (a x : A) :
    L (a*x) = L a * L x := by
  let l := sosStateLinearMap hL.1
  obtain ⟨N, hp, hm⟩ := hb a
  have hbound := sosState_bounds hL.1 hp hm
  let b : A := (N:A)+a+1
  let c : A := (N:A)-a+1
  have hbp : IsSumSq b := by simpa [b] using hp.add (IsSumSq.natCast 1)
  have hcp : IsSumSq c := by simpa [c] using hm.add (IsSumSq.natCast 1)
  have hn : l (N:A) = (N:ℝ) := by
    have h := l.map_smul (N:ℝ) (1:A)
    simpa [l, sosStateLinearMap, Algebra.smul_def, hL.1.2.2.1] using h
  have h1 : l 1 = 1 := hL.1.2.2.1
  have hlb : l b = (N:ℝ)+L a+1 := by rw [show b = (N:A)+a+1 from rfl, map_add, map_add, hn, h1]; rfl
  have hlc : l c = (N:ℝ)-L a+1 := by rw [show c = (N:A)-a+1 from rfl, map_add, map_sub, hn, h1]; rfl
  have hLb : 0 < l b := by rw [hlb]; linarith [hbound.1]
  have hLc : 0 < l c := by rw [hlc]; linarith [hbound.2]
  have hsum : l b + l c = 2*((N:ℝ)+1) := by rw [hlb, hlc]; ring
  have hbc : b+c = (2*((N:ℝ)+1)) • (1:A) := by
    simp only [b, c, Algebra.smul_def, map_mul, map_add, map_ofNat, map_natCast, map_one,
      mul_one]
    ring
  have hden : 0 < l b + l c := add_pos hLb hLc
  have hseg : L ∈ openSegment ℝ
      (weightedSOSState l b : A → ℝ) (weightedSOSState l c : A → ℝ) := by
    refine ⟨l b / (l b+l c), l c / (l b+l c), div_pos hLb hden,
      div_pos hLc hden, ?_, ?_⟩
    · rw [← add_div, div_self hden.ne']
    · funext y
      change l b / (l b+l c) * ((l b)⁻¹ * l (b*y)) +
        l c / (l b+l c) * ((l c)⁻¹ * l (c*y)) = l y
      have he : l (b*y) + l (c*y) = (l b+l c)*l y := by
        rw [← map_add, ← add_mul, hbc, smul_mul_assoc, one_mul, map_smul, hsum]
        rfl
      field_simp
      nlinarith
  have heq := hL.2 (weightedSOSState_mem l hL.1.2.2.2 hbp hLb)
    (weightedSOSState_mem l hL.1.2.2.2 hcp hLc) hseg
  have he := congrFun heq x
  change (l b)⁻¹ * l (b*x) = l x at he
  have he' : l (b*x) = l b * l x := by
    calc
      l (b*x) = l b * ((l b)⁻¹ * l (b*x)) := by field_simp
      _ = l b * l x := by rw [he]
  have hex : l (b*x) = ((N:ℝ)+1)*l x + l (a*x) := by
    have hbx : b*x = ((N:ℝ)+1) • x + a*x := by
      simp only [b, Algebra.smul_def, map_add, map_natCast, map_one]
      ring
    rw [hbx, map_add, map_smul]
    rfl
  rw [hex, hlb] at he'
  change l (a*x) = L a * l x
  nlinarith

/-- A real character with nonpositive value witnesses failure of SOS
membership in an Archimedean real algebra. -/
theorem exists_nonpos_character_of_not_sumSq
    (hb : ∀ x : A, ∃ N : ℕ, IsSumSq ((N:A)+x) ∧ IsSumSq ((N:A)-x))
    {a : A} (ha : ¬ IsSumSq a) : ∃ φ : A →ₐ[ℝ] ℝ, φ a ≤ 0 := by
  obtain ⟨L, h1, hp, haL⟩ := exists_sos_separating_state hb ha
  have hc := isCompact_sosStates hb
  have hL := linearMap_mem_sosStates L h1 hp
  obtain ⟨M, hM, hmin⟩ := hc.exists_isMinOn ⟨L, hL⟩ (continuous_apply a).continuousOn
  let F : Set (A → ℝ) := {M ∈ sosStates A | ∀ K ∈ sosStates A, M a ≤ K a}
  have hF : IsExposed ℝ (sosStates A) F := by
    intro _
    refine ⟨-(ContinuousLinearMap.proj a : (A → ℝ) →L[ℝ] ℝ), ?_⟩
    ext K
    simp [F]
  obtain ⟨K, hK⟩ := (hF.isCompact hc).extremePoints_nonempty ⟨M, hM, hmin⟩
  have hext := hF.isExtreme.extremePoints_subset_extremePoints hK
  let k := sosStateLinearMap hext.1
  let φ : A →ₐ[ℝ] ℝ :=
    { k with
      map_zero' := k.map_zero
      map_one' := hext.1.2.2.1
      map_mul' := extreme_sosState_mul hb hext
      commutes' := fun r => by
        have h := k.map_smul r (1:A)
        simpa [Algebra.smul_def, k, sosStateLinearMap, hext.1.2.2.1] using h }
  exact ⟨φ, (hK.1.2 L hL).trans haL⟩

/-- Abstract scalar Archimedean representation, with strict positivity on
all real characters and an exact finite sum of squares as conclusion. -/
theorem isSumSq_of_pos_characters
    (hb : ∀ x : A, ∃ N : ℕ, IsSumSq ((N:A)+x) ∧ IsSumSq ((N:A)-x))
    {a : A} (ha : ∀ φ : A →ₐ[ℝ] ℝ, 0 < φ a) : IsSumSq a := by
  by_contra h
  obtain ⟨φ, hφ⟩ := exists_nonpos_character_of_not_sumSq hb h
  exact (ha φ).not_ge hφ

end CZExposure.PolynomialGeometry
