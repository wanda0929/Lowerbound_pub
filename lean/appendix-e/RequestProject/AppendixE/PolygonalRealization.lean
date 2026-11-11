module
public import RequestProject.AppendixE.ArcCompactness
public import RequestProject.AppendixE.FinitePathDecomposition

/-! Arc-length parametrized finite polygonal paths. Graph simplicity and
geometric simplicity are separate: the latter requires a noncrossing embedding. -/
@[expose] public section
noncomputable section
namespace CZExposure
open Set MeasureTheory
open scoped BigOperators

namespace StoppedPathSpace
theorem duration_nonneg (a : StoppedPathSpace) : 0 ≤ a.duration := a.property.1
theorem lipschitz (a : StoppedPathSpace) : LipschitzWith 1 a.path := a.property.2.1
theorem before (a : StoppedPathSpace) {t : ℝ} (ht : t ≤ 0) : a.path t = a.path 0 := by
  have he : a.path t = a.path (max 0 (min t a.duration)) := a.property.2.2 t
  simpa [min_eq_left (ht.trans a.duration_nonneg), max_eq_left ht] using he
theorem after (a : StoppedPathSpace) {t : ℝ} (ht : a.duration ≤ t) :
    a.path t = a.path a.duration := by
  have he : a.path t = a.path (max 0 (min t a.duration)) := a.property.2.2 t
  simpa [min_eq_right ht, max_eq_right a.duration_nonneg] using he

def ofTails (D : ℝ) (hD : 0 ≤ D) (f : ℝ → ExposureEuclidean)
    (hl : LipschitzWith 1 f) (h0 : ∀ t ≤ 0, f t = f 0)
    (h1 : ∀ t, D ≤ t → f t = f D) : StoppedPathSpace := by
  refine ⟨⟨D, ⟨f, hl.continuous⟩⟩, hD, hl, ?_⟩
  intro t
  by_cases ht : t ≤ 0
  · simpa [min_eq_left (ht.trans hD), max_eq_left ht] using h0 t ht
  · by_cases hT : D ≤ t
    · simpa [min_eq_right hT, max_eq_right hD] using h1 t hT
    · simp [min_eq_left (le_of_not_ge hT), max_eq_right (le_of_not_ge ht)]
end StoppedPathSpace

/-- Finite corners are retained explicitly; differentiability is not claimed
at a join, nor is duration yet identified with mass of a simple current. -/
structure PolygonalPath where
  curve : StoppedPathSpace
  corners : Finset ℝ
  regular : ∀ t, 0 < t → t < curve.duration → t ∉ corners →
    ∃ v, HasDerivAt curve.path v t ∧ ‖v‖ = 1

namespace PolygonalPath
abbrev duration (a : PolygonalPath) := a.curve.duration
abbrev path (a : PolygonalPath) := a.curve.path

def constant (x : ExposureEuclidean) : PolygonalPath where
  curve := StoppedPathSpace.ofTails 0 le_rfl (fun _ => x)
    (LipschitzWith.const' x) (by intros; rfl) (by intros; rfl)
  corners := ∅
  regular := by intros; simp_all [StoppedPathSpace.ofTails, StoppedPathSpace.duration]; linarith

def direction (x y : ExposureEuclidean) : ExposureEuclidean := ‖y-x‖⁻¹ • (y-x)
theorem direction_norm (x y : ExposureEuclidean) (h : x ≠ y) : ‖direction x y‖ = 1 := by
  have hn : ‖y-x‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr h.symm)
  simp [direction, norm_smul, hn]
theorem direction_norm_le (x y : ExposureEuclidean) : ‖direction x y‖ ≤ 1 := by
  by_cases h : x = y
  · subst y; simp [direction]
  · exact (direction_norm x y h).le
theorem length_smul_direction (x y : ExposureEuclidean) : ‖y-x‖ • direction x y = y-x := by
  by_cases h : x = y
  · subst y; simp [direction]
  · have hn : ‖y-x‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr (Ne.symm h))
    simp [direction, smul_smul, hn]

def segment (x y : ExposureEuclidean) : PolygonalPath := by
  let d := ‖y-x‖
  let f : ℝ → ExposureEuclidean := fun t => x + t • direction x y
  have hl : LipschitzWith 1 f := by
    apply lipschitzWith_iff_dist_le_mul.mpr
    intro s t
    have he : f s - f t = (s-t) • direction x y := by dsimp [f]; rw [sub_smul]; abel
    simp only [dist_eq_norm, he, norm_smul, NNReal.coe_one, one_mul]
    exact (mul_le_mul_of_nonneg_left (direction_norm_le x y) (norm_nonneg _)).trans_eq (mul_one _)
  let q : ℝ → ExposureEuclidean := fun t => f (max 0 (min t d))
  have hq : LipschitzWith 1 q := by
    simpa only [one_mul] using hl.comp ((LipschitzWith.id.min_const d).const_max 0)
  refine ⟨StoppedPathSpace.ofTails d (norm_nonneg _) q hq ?_ ?_, ∅, ?_⟩
  · intro t ht
    simp [q, min_eq_left (ht.trans (norm_nonneg _)), max_eq_left ht, d]
  · intro t ht
    simp [q, min_eq_right ht, d]
  · intro t ht hT _
    change 0 < t at ht
    change t < d at hT
    have hxy : x ≠ y := by intro he; subst y; simp [d] at hT; linarith
    refine ⟨direction x y, ?_, direction_norm x y hxy⟩
    have hd : HasDerivAt f (direction x y) t := by
      simpa [f] using ((hasDerivAt_id t).smul_const (direction x y)).const_add x
    apply hd.congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds ht hT] with s hs
    change f (max 0 (min s d)) = f s
    rw [min_eq_left hs.2.le, max_eq_right hs.1.le]

@[simp] theorem segment_duration (x y : ExposureEuclidean) : (segment x y).duration = ‖y-x‖ := rfl
theorem segment_formula (x y : ExposureEuclidean) (t : ℝ) :
    (segment x y).path t = x + max 0 (min t ‖y-x‖) • direction x y := rfl
@[simp] theorem segment_initial (x y : ExposureEuclidean) : (segment x y).path 0 = x := by
  simp [segment_formula]
@[simp] theorem segment_terminal (x y : ExposureEuclidean) :
    (segment x y).path (segment x y).duration = y := by
  simp [segment_formula, length_smul_direction]

def joined (a b : PolygonalPath) (t : ℝ) : ExposureEuclidean :=
  if t ≤ a.duration then a.path t else b.path (t-a.duration)

theorem joined_lipschitz (a b : PolygonalPath) (h : a.path a.duration = b.path 0) :
    LipschitzWith 1 (joined a b) := by
  have cross (s t : ℝ) (hs : s ≤ a.duration) (ht : a.duration < t) :
      dist (a.path s) (b.path (t-a.duration)) ≤ dist s t := by
    calc dist (a.path s) (b.path (t-a.duration))
      ≤ dist (a.path s) (a.path a.duration) + dist (a.path a.duration) (b.path (t-a.duration)) := dist_triangle _ _ _
      _ ≤ dist s a.duration + dist 0 (t-a.duration) := by
        rw [h]
        exact add_le_add (by simpa [← h] using a.curve.lipschitz.dist_le_mul s a.duration)
          (by simpa using b.curve.lipschitz.dist_le_mul 0 (t-a.duration))
      _ = dist s t := by
        simp only [Real.dist_eq]
        rw [abs_of_nonpos (sub_nonpos.mpr hs), abs_of_nonpos (by linarith : 0-(t-a.duration) ≤ 0),
          abs_of_nonpos (by linarith : s-t ≤ 0)]
        ring
  apply lipschitzWith_iff_dist_le_mul.mpr
  intro s t
  simp only [NNReal.coe_one, one_mul]
  by_cases hs : s ≤ a.duration <;> by_cases ht : t ≤ a.duration
  · simpa [joined, hs, ht] using a.curve.lipschitz.dist_le_mul s t
  · simpa [joined, hs, ht] using cross s t hs (lt_of_not_ge ht)
  · simpa [joined, hs, ht, dist_comm] using cross t s ht (lt_of_not_ge hs)
  · simpa [joined, hs, ht, Real.dist_eq, sub_sub_sub_cancel_right] using
      b.curve.lipschitz.dist_le_mul (s-a.duration) (t-a.duration)

def join (a b : PolygonalPath) (h : a.path a.duration = b.path 0) : PolygonalPath := by
  classical
  have hA := a.curve.duration_nonneg
  have hB := b.curve.duration_nonneg
  refine ⟨StoppedPathSpace.ofTails (a.duration+b.duration) (add_nonneg hA hB)
    (joined a b) (joined_lipschitz a b h) ?_ ?_,
    insert a.duration (a.corners ∪ b.corners.image (fun t => t+a.duration)), ?_⟩
  · intro t ht
    simp only [joined, if_pos (ht.trans hA), if_pos hA]
    exact a.curve.before ht
  · intro t ht
    by_cases htA : t ≤ a.duration
    · have hb : b.duration = 0 := by change 0 ≤ b.duration at hB; linarith
      have ht' : t = a.duration := by linarith
      simp [joined, hb, ht']
    · have he : joined a b (a.duration+b.duration) = b.path b.duration := by
        by_cases hb : b.duration = 0
        · simp [joined, hb, h]
        · have hbpos : 0 < b.duration := lt_of_le_of_ne hB (Ne.symm hb)
          have : ¬ a.duration+b.duration ≤ a.duration := by linarith
          simp [joined, this]
      rw [he]
      simp only [joined, if_neg htA]
      exact b.curve.after (by linarith)
  · intro t ht hT hc
    change t ∉ insert a.duration (a.corners ∪ b.corners.image (fun t => t+a.duration)) at hc
    simp only [Finset.mem_insert, Finset.mem_union, not_or] at hc
    change 0 < t at ht
    change t < a.duration+b.duration at hT
    by_cases htA : t < a.duration
    · obtain ⟨v, hv, hn⟩ := a.regular t ht htA hc.2.1
      refine ⟨v, hv.congr_of_eventuallyEq ?_, hn⟩
      filter_upwards [Iio_mem_nhds htA] with s hs
      exact if_pos hs.le
    · have hgt : a.duration < t := lt_of_le_of_ne (le_of_not_gt htA) (Ne.symm hc.1)
      have hcB : t-a.duration ∉ b.corners := by
        intro hm
        apply hc.2.2
        exact Finset.mem_image.mpr ⟨t-a.duration, hm, by ring⟩
      obtain ⟨v, hv, hn⟩ := b.regular (t-a.duration) (by linarith) (by linarith) hcB
      refine ⟨v, ?_, hn⟩
      have hd := hv.scomp t (show HasDerivAt (fun s : ℝ => s-a.duration) 1 t from
        (hasDerivAt_id t).sub_const a.duration)
      simp only [one_smul] at hd
      apply hd.congr_of_eventuallyEq
      filter_upwards [Ioi_mem_nhds hgt] with s hs
      exact if_neg (not_le.mpr hs)

@[simp] theorem join_duration (a b : PolygonalPath) (h) : (join a b h).duration = a.duration+b.duration := rfl
theorem join_formula (a b : PolygonalPath) (h) (t : ℝ) : (join a b h).path t = joined a b t := rfl
@[simp] theorem join_initial (a b : PolygonalPath) (h) : (join a b h).path 0 = a.path 0 := by
  simp [join_formula, joined, a.curve.duration_nonneg]
@[simp] theorem join_terminal (a b : PolygonalPath) (h) :
    (join a b h).path (join a b h).duration = b.path b.duration := by
  by_cases hb : b.duration = 0
  · simp [join_formula, joined, hb, h]
  · have hn := b.curve.duration_nonneg
    have hbpos : 0 < b.duration := lt_of_le_of_ne hn (Ne.symm hb)
    have hh : ¬ a.duration+b.duration ≤ a.duration := by linarith
    simp [join_formula, joined, hh]

theorem unit_speed (a : PolygonalPath) :
    ∀ᵐ t ∂(volume.restrict (Icc 0 a.duration)),
      ∃ v, HasDerivAt a.path v t ∧ ‖v‖ = 1 := by
  have hi : ∀ᵐ t ∂(volume.restrict (Icc 0 a.duration)), t ∈ Ioo 0 a.duration := by
    rw [← Measure.restrict_congr_set Ioo_ae_eq_Icc]
    exact ae_restrict_mem measurableSet_Ioo
  have hc : ∀ᵐ t ∂(volume.restrict (Icc 0 a.duration)), t ∉ a.corners :=
    ae_restrict_of_ae (a.corners.finite_toSet.countable.ae_notMem volume)
  filter_upwards [hi, hc] with t ht hc
  exact a.regular t ht.1 ht.2 hc

def toArc (a : PolygonalPath) (hpos : 0 < a.duration)
    (hinj : InjOn a.path (Icc 0 a.duration)) : EuclideanArc where
  length := a.duration
  length_pos := hpos
  path := a.path
  lipschitz := a.curve.lipschitz
  injectiveOn := hinj
  unit_speed := a.unit_speed

theorem segment_injOn (x y : ExposureEuclidean) :
    InjOn (segment x y).path (Icc 0 (segment x y).duration) := by
  intro s hs t ht he
  by_cases hxy : x = y
  · subst y
    simp only [segment_duration, sub_self, norm_zero, mem_Icc] at hs ht
    linarith [hs.1, hs.2, ht.1, ht.2]
  · have hd : direction x y ≠ 0 := by
      intro hz
      have := direction_norm x y hxy
      simp [hz] at this
    simp only [segment_duration, mem_Icc] at hs ht
    simp only [segment_formula, min_eq_left hs.2, max_eq_right hs.1,
      min_eq_left ht.2, max_eq_right ht.1] at he
    exact smul_left_injective ℝ hd (add_left_cancel he)

theorem join_injOn (a b : PolygonalPath) (h : a.path a.duration = b.path 0)
    (ha : InjOn a.path (Icc 0 a.duration)) (hb : InjOn b.path (Icc 0 b.duration))
    (hsep : ∀ s ∈ Icc 0 a.duration, ∀ t ∈ Icc 0 b.duration,
      a.path s = b.path t → a.path s = a.path a.duration) :
    InjOn (join a b h).path (Icc 0 (join a b h).duration) := by
  have cross (s t : ℝ) (hs : s ∈ Icc 0 a.duration)
      (ht : t ∈ Icc 0 b.duration) (he : a.path s = b.path t) : s = a.duration ∧ t = 0 := by
    have hse := hsep s hs t ht he
    refine ⟨ha hs ⟨a.curve.duration_nonneg, le_rfl⟩ hse, ?_⟩
    apply hb ht ⟨le_rfl, b.curve.duration_nonneg⟩
    exact he.symm.trans (hse.trans h)
  intro s hs t ht he
  simp only [join_duration, mem_Icc] at hs ht
  simp only [join_formula, joined] at he
  by_cases hsA : s ≤ a.duration <;> by_cases htA : t ≤ a.duration
  · simp only [if_pos hsA, if_pos htA] at he
    exact ha ⟨hs.1, hsA⟩ ⟨ht.1, htA⟩ he
  · simp only [if_pos hsA, if_neg htA] at he
    obtain ⟨h1, h2⟩ := cross s (t-a.duration) ⟨hs.1, hsA⟩ ⟨by linarith, by linarith [ht.2]⟩ he
    linarith
  · simp only [if_neg hsA, if_pos htA] at he
    obtain ⟨h1, h2⟩ := cross t (s-a.duration) ⟨ht.1, htA⟩ ⟨by linarith, by linarith [hs.2]⟩ he.symm
    linarith
  · simp only [if_neg hsA, if_neg htA] at he
    have he' := hb (x₁ := s-a.duration) (x₂ := t-a.duration)
      ⟨by linarith, by linarith [hs.2]⟩ ⟨by linarith, by linarith [ht.2]⟩ he
    linarith

end PolygonalPath

namespace FiniteRouting
variable {V : Type*}
open PolygonalPath

def realizeFrom (pos : V → ExposureEuclidean) :
    (γ : Walk V) → {a : PolygonalPath // a.path 0 = pos γ.first}
  | .stop v => ⟨constant (pos v), rfl⟩
  | .step v γ =>
    let b := realizeFrom pos γ
    ⟨join (segment (pos v) (pos γ.first)) b.val (by rw [segment_terminal, b.property]),
      by simp [Walk.first]⟩

def Walk.realize (γ : Walk V) (pos : V → ExposureEuclidean) : PolygonalPath := (realizeFrom pos γ).val
@[simp] theorem Walk.realize_initial (γ : Walk V) (pos : V → ExposureEuclidean) :
    (γ.realize pos).path 0 = pos γ.first := (realizeFrom pos γ).property
theorem Walk.realize_stop (v : V) (pos : V → ExposureEuclidean) :
    (Walk.stop v).realize pos = constant (pos v) := rfl
theorem Walk.realize_step (v : V) (γ : Walk V) (pos : V → ExposureEuclidean) :
    (Walk.step v γ).realize pos =
      join (segment (pos v) (pos γ.first)) (γ.realize pos)
        (by rw [segment_terminal, γ.realize_initial]) := rfl
@[simp] theorem Walk.realize_terminal (γ : Walk V) (pos : V → ExposureEuclidean) :
    (γ.realize pos).path (γ.realize pos).duration = pos γ.last := by
  induction γ with
  | stop v => rfl
  | step v γ ih => rw [Walk.realize_step, join_terminal]; exact ih

theorem Walk.realize_duration (γ : Walk V) (pos : V → ExposureEuclidean) :
    (γ.realize pos).duration = γ.reward (fun _ => 0) (fun u v => ‖pos v-pos u‖) := by
  induction γ with
  | stop v => rfl
  | step v γ ih => simp [Walk.realize_step, Walk.reward, ih]

/-- Closed straight edge, parametrized by its Euclidean length, with
constant tails. Includes both endpoints and permits a zero-length edge. -/
def edgeTrace (x y : ExposureEuclidean) : Set ExposureEuclidean := range (segment x y).path
def Walk.trace (γ : Walk V) (pos : V → ExposureEuclidean) : Set ExposureEuclidean :=
  match γ with
  | .stop v => {pos v}
  | .step v δ => edgeTrace (pos v) (pos δ.first) ∪ δ.trace pos

theorem Walk.realize_mem_trace (γ : Walk V) (pos : V → ExposureEuclidean) (t : ℝ) :
    (γ.realize pos).path t ∈ γ.trace pos := by
  induction γ generalizing t with
  | stop v => exact rfl
  | step v γ ih =>
    rw [Walk.realize_step, join_formula]
    by_cases ht : t ≤ (segment (pos v) (pos γ.first)).duration
    · exact Or.inl ⟨t, by simp only [joined, if_pos ht]⟩
    · exact Or.inr (by simpa only [joined, if_neg ht] using ih (t-(segment (pos v) (pos γ.first)).duration))

/-- Standard straight-edge embedding conditions: distinct vertices, no vertex
in the interior of a nonincident edge, and distinct undirected edges meet
only at a shared vertex. These are geometric hypotheses, not consequences of
acyclicity of the abstract graph. -/
structure StraightEmbedding (edge : V → V → ℝ) where
  pos : V → ExposureEuclidean
  injective : Function.Injective pos
  vertex_on_edge : ∀ u v, 0 < edge u v → ∀ w,
    pos w ∈ edgeTrace (pos u) (pos v) → w = u ∨ w = v
  edge_meet : ∀ u v w z, 0 < edge u v → 0 < edge w z →
    ¬((u=w ∧ v=z) ∨ (u=z ∧ v=w)) →
    ∀ x ∈ edgeTrace (pos u) (pos v), x ∈ edgeTrace (pos w) (pos z) →
      ∃ k, (k=u ∨ k=v) ∧ (k=w ∨ k=z) ∧ x=pos k

theorem Walk.first_mem (γ : Walk V) : γ.first ∈ γ.vertices := by
  cases γ <;> simp [Walk.first, Walk.vertices]

namespace StraightEmbedding
variable {edge : V → V → ℝ} (E : StraightEmbedding edge)

private theorem edge_trace_meet (u v : V) (huv : 0 < edge u v)
    (γ : Walk V) (ha : γ.Allowed edge) (hu : u ∉ γ.vertices)
    (x : ExposureEuclidean) (hx : x ∈ edgeTrace (E.pos u) (E.pos v))
    (hγ : x ∈ γ.trace E.pos) : x = E.pos v := by
  induction γ with
  | stop w =>
    change x = E.pos w at hγ
    rw [hγ] at hx ⊢
    rcases E.vertex_on_edge u v huv w hx with hw | hw
    · subst w; exact False.elim (hu (by simp [Walk.vertices]))
    · rw [hw]
  | step w γ ih =>
    have hun : u ≠ w ∧ u ∉ γ.vertices := by simpa [Walk.vertices] using hu
    have huf : u ≠ γ.first := by intro he; exact hun.2 (he ▸ γ.first_mem)
    rcases hγ with hx' | hx'
    · have hdiff : ¬((u=w ∧ v=γ.first) ∨ (u=γ.first ∧ v=w)) := by tauto
      obtain ⟨k, hk, hk', he⟩ := E.edge_meet u v w γ.first huv ha.1 hdiff x hx hx'
      rcases hk with rfl | rfl
      · exact False.elim (hk'.elim hun.1 huf)
      · exact he
    · exact ih ha.2 hun.2 hx'

theorem realize_injOn (γ : Walk V) (ha : γ.Allowed edge) (hn : γ.vertices.Nodup) :
    InjOn (γ.realize E.pos).path (Icc 0 (γ.realize E.pos).duration) := by
  induction γ with
  | stop v =>
    intro s hs t ht _
    change s ∈ Icc (0:ℝ) 0 at hs
    change t ∈ Icc (0:ℝ) 0 at ht
    linarith [hs.1, hs.2, ht.1, ht.2]
  | step v γ ih =>
    have hnd := List.nodup_cons.mp hn
    rw [Walk.realize_step]
    apply join_injOn _ _ _ (segment_injOn _ _) (ih ha.2 hnd.2)
    intro s _ t _ he
    have hm := E.edge_trace_meet v γ.first ha.1 γ ha.2 hnd.1
      ((segment (E.pos v) (E.pos γ.first)).path s) ⟨s, rfl⟩
      (he ▸ γ.realize_mem_trace E.pos t)
    rw [segment_terminal]
    exact hm

theorem realize_duration_pos (γ : Walk V) (hne : γ.first ≠ γ.last) :
    0 < (γ.realize E.pos).duration := by
  have hn := (γ.realize E.pos).curve.duration_nonneg
  apply lt_of_le_of_ne hn
  intro hz
  change 0 = (γ.realize E.pos).duration at hz
  have he := γ.realize_terminal E.pos
  rw [← hz, γ.realize_initial] at he
  exact hne (E.injective he)

/-- The actual simple, unit-speed Euclidean arc, not just a graph path. -/
def arc (γ : Walk V) (ha : γ.Allowed edge) (hn : γ.vertices.Nodup)
    (hne : γ.first ≠ γ.last) : EuclideanArc :=
  (γ.realize E.pos).toArc (E.realize_duration_pos γ hne) (E.realize_injOn γ ha hn)

end StraightEmbedding

theorem Flow.geometric_length_ledger [Fintype V] (f : Flow V) (pos : V → ExposureEuclidean) :
    total f.decomposition (fun γ => (γ.realize pos).duration) =
      ∑ u, ∑ v, f.edge u v * ‖pos v-pos u‖ := by
  have he : (fun γ : Walk V => (γ.realize pos).duration) =
      Walk.reward (fun _ => 0) (fun u v => ‖pos v-pos u‖) :=
    funext (fun γ => γ.realize_duration pos)
  rw [he, f.decomposition_ledger]
  simp

theorem Flow.geometric_arc [Fintype V] (f : Flow V) (E : StraightEmbedding f.edge)
    (a : ℝ × Walk V) (ha : a ∈ f.decomposition) (hp : 0 < a.1) :
    ∃ γ : EuclideanArc, γ.path = (a.2.realize E.pos).path ∧
      γ.length = a.2.reward (fun _ => 0) (fun u v => ‖E.pos v-E.pos u‖) ∧
      γ.path 0 = E.pos a.2.first ∧ γ.path γ.length = E.pos a.2.last := by
  obtain ⟨hn, hal, hs, ht⟩ := f.decomposition_support a ha hp
  have hne : a.2.first ≠ a.2.last := by
    intro he
    rw [← he] at ht
    rcases f.source_sink_disjoint a.2.first with hz | hz <;> simp_all
  refine ⟨E.arc a.2 hal hn hne, rfl, a.2.realize_duration E.pos,
    a.2.realize_initial E.pos, a.2.realize_terminal E.pos⟩

end FiniteRouting
end CZExposure
