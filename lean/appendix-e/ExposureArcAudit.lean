import RequestProject.AppendixE.ArcCompactness
import RequestProject.AppendixE.CycleRemoval
import RequestProject.AppendixE.FinitePathDecomposition
import RequestProject.AppendixE.PolygonalRealization

open CZExposure

#check @EuclideanArc.lengthMeasure_univ
#check @EuclideanArc.lengthMeasure_eq_map_speed
#check @EuclideanArc.lintegral_lengthMeasure
#check @EuclideanArc.ae_path_of_ae_lengthMeasure
#check @EuclideanArc.mapsTo_of_ae_mem_closed
#check @EuclideanArc.exposureTime_eq_lintegral
#check @EuclideanArc.ae_velocity_ne_zero
#check @EuclideanArc.inverseSpeed_eq_toReal
#check @EuclideanArc.integrable_inverseSpeed
#check @EuclideanArc.integral_inverseSpeed
#check @EuclideanArc.intervalIntegrable_inverseSpeed
#check @EuclideanArc.exposureClock_zero
#check @EuclideanArc.exposureClock_terminal
#check @EuclideanArc.absolutelyContinuous_exposureClock
#check @ExposureArcRealization.exists_arc_le_exposure_mass

#print axioms EuclideanArc.lengthMeasure_univ
#print axioms EuclideanArc.lengthMeasure_eq_map_speed
#print axioms EuclideanArc.lintegral_lengthMeasure
#print axioms EuclideanArc.ae_path_of_ae_lengthMeasure
#print axioms EuclideanArc.mapsTo_of_ae_mem_closed
#print axioms EuclideanArc.exposureTime_eq_lintegral
#print axioms EuclideanArc.ae_velocity_ne_zero
#print axioms EuclideanArc.inverseSpeed_eq_toReal
#print axioms EuclideanArc.integrable_inverseSpeed
#print axioms EuclideanArc.integral_inverseSpeed
#print axioms EuclideanArc.intervalIntegrable_inverseSpeed
#print axioms EuclideanArc.exposureClock_zero
#print axioms EuclideanArc.exposureClock_terminal
#print axioms EuclideanArc.absolutelyContinuous_exposureClock
#print axioms ExposureArcRealization.exists_arc_le_exposure_mass

noncomputable section
open MeasureTheory Set

-- Translate the segment arbitrarily and allow every unit direction and
-- positive length: no origin, orientation, or unit-length special case.
private def straightArc (x v : ExposureEuclidean) (hv : ‖v‖ = 1)
    (L : ℝ) (hL : 0 < L) : EuclideanArc where
  length := L
  length_pos := hL
  path := fun t => x + t • v
  lipschitz := by
    apply lipschitzWith_iff_dist_le_mul.mpr
    intro s t
    have he : (x+s•v)-(x+t•v) = (s-t)•v := by rw [sub_smul]; abel
    simp [dist_eq_norm, he, norm_smul, hv, Real.norm_eq_abs]
  injectiveOn := by
    intro s _ t _ h
    apply smul_left_injective ℝ (show v ≠ 0 from by intro hz; simp [hz] at hv)
    exact add_left_cancel h
  unit_speed := Filter.Eventually.of_forall fun t => ⟨v, by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x, hv⟩

-- The vector total is directed displacement, not scalar arc length.
example (x v : ExposureEuclidean) (hv : ‖v‖ = 1) (L : ℝ) (hL : 0 < L) :
    (straightArc x v hv L hL).vectorCurrent univ = L • v := by
  let γ := straightArc x v hv L hL
  have hd (t : ℝ) : deriv γ.path t = v := by
    simpa [γ, straightArc] using (((hasDerivAt_id t).smul_const v).const_add x).deriv
  change γ.vectorCurrent univ = L • v
  rw [γ.vectorCurrent_apply MeasurableSet.univ]
  simp only [hd, preimage_univ, Measure.restrict_univ, integral_const]
  simp [EuclideanArc.parameterMeasure, γ, straightArc, Measure.real, hL.le]

-- Exact local mass, rather than only total mass, is part of the public contract.
example (γ : EuclideanArc) (s : Set ExposureEuclidean) (hs : MeasurableSet s) :
    γ.vectorCurrent.variation s = volume (γ.path ⁻¹' s ∩ Icc 0 γ.length) := by
  rw [γ.vectorCurrent_variation, EuclideanArc.lengthMeasure,
    Measure.map_apply γ.lipschitz.continuous.measurable hs,
    EuclideanArc.parameterMeasure,
    Measure.restrict_apply (hs.preimage γ.lipschitz.continuous.measurable)]

-- A nonzero endpoint difference excludes the reversed boundary sign.
example (γ : EuclideanArc) (ψ : ExposureEuclidean → ℝ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hs : HasCompactSupport ψ)
    (hne : ψ (γ.path γ.length) ≠ ψ (γ.path 0)) :
    (∫ x, fderiv ℝ ψ x (γ.tangentField x) ∂γ.lengthMeasure) ≠
      ψ (γ.path 0) - ψ (γ.path γ.length) := by
  rw [(γ.boundary ψ hψ hs).2]
  intro h
  apply hne
  linarith

-- The normal-current interface has no additional mass or boundary inputs.
example (γ : EuclideanArc) :
    γ.toNormalCurrentData.boundaryPlus = Measure.dirac (γ.path γ.length) ∧
    γ.toNormalCurrentData.boundaryMinus = Measure.dirac (γ.path 0) := ⟨rfl, rfl⟩

-- Canonicalization clamps both tails but preserves the entire physical interval.
example (γ : EuclideanArc) (t : ℝ) (ht : t ≤ 0) :
    (ArcSpace.ofArc γ).path t = γ.path 0 := by
  exact ((ArcSpace.ofArc γ).property.2.2.2.2.1 t ht).trans
    (ArcSpace.ofArc_path γ ⟨le_rfl, γ.length_pos.le⟩)

example (γ : EuclideanArc) (t : ℝ) (ht : γ.length ≤ t) :
    (ArcSpace.ofArc γ).path t = γ.path γ.length := by
  exact ((ArcSpace.ofArc γ).property.2.2.2.2.2 t ht).trans
    (ArcSpace.ofArc_path γ ⟨γ.length_pos.le, le_rfl⟩)

example (γ : EuclideanArc) :
    (ArcSpace.ofArc γ).toArc.vectorCurrent.variation = γ.lengthMeasure := by
  rw [ArcSpace.ofArc_vectorCurrent, γ.vectorCurrent_variation]

-- A discontinuous switch is allowed: the interface requires measurability,
-- not continuity of the indexing family.
private def switched (a b : ArcSpace) (r : ℝ) : ArcSpace := if r ≤ 0 then a else b

private theorem measurable_switched (a b : ArcSpace) : Measurable (switched a b) :=
  measurable_const.ite measurableSet_Iic measurable_const

example (a b : ArcSpace) : Measurable (fun r : ℝ =>
    ((switched a b r).path 0, (switched a b r).path (switched a b r).length)) :=
  (ArcSpace.continuous_initial.measurable.comp (measurable_switched a b)).prodMk
    (ArcSpace.continuous_terminal.measurable.comp (measurable_switched a b))

example (a b : ArcSpace) (s : Set ExposureEuclidean) (hs : MeasurableSet s) :
    Measurable (fun r : ℝ => (switched a b r).toArc.vectorCurrent s) :=
  (ArcSpace.measurable_vectorCurrent_apply hs).comp (measurable_switched a b)

example {T : EuclideanNormalCurrentData} {source sink : ExposureEuclidean}
    (D : EuclideanCurrentArcData T source sink ℝ) (a b : ArcSpace)
    (he : ∀ r, D.arc r = (switched a b r).toArc) : D.MeasurableArcs :=
  ArcSpace.measurableArcs D (switched a b) (measurable_switched a b) he

-- A wholly cyclic current must leave zero, not an arbitrary smaller cycle.
example (T : EuclideanNormalCurrentData) (hb : T.boundaryPlus = T.boundaryMinus) :
    ∃ S : EuclideanNormalCurrentData,
      IsVectorSubcurrent S.vectorMeasure T.vectorMeasure ∧ S.vectorMeasure = 0 := by
  obtain ⟨S, hs, hp, hm, ha, _⟩ := T.exists_acyclic_subcurrent
  refine ⟨S, hs, ha S (IsVectorSubcurrent.refl _) ?_⟩
  intro ψ
  change (∫ z, fderiv ℝ ψ.val z (S.direction z) ∂S.vectorMeasure.variation) = 0
  rw [(S.boundary ψ.val ψ.property.1 ψ.property.2).2, hp, hm, hb, sub_self]

-- Nonzero boundary cannot be discarded; support cannot grow after removal.
example (T : EuclideanNormalCurrentData) (K : Set ExposureEuclidean)
    (hK : T.vectorMeasure.variation Kᶜ = 0)
    (ψ : EuclideanNormalCurrentData.BoundaryTest)
    (hb : (∫ z, ψ.val z ∂T.boundaryPlus) ≠ (∫ z, ψ.val z ∂T.boundaryMinus)) :
    ∃ S : EuclideanNormalCurrentData,
      IsVectorSubcurrent S.vectorMeasure T.vectorMeasure ∧ S.IsAcyclic ∧
      S.vectorMeasure.variation Kᶜ = 0 ∧ S.vectorMeasure ≠ 0 := by
  letI := T.finite_variation
  obtain ⟨S, hs, hp, hm, ha, _⟩ := T.exists_acyclic_subcurrent
  refine ⟨S, hs, ha, hs.variation_null (measure_lt_top _ _) hK, ?_⟩
  intro hz
  have h := (S.boundary ψ.val ψ.property.1 ψ.property.2).2
  rw [hz, vectorMeasure_variation_zero, integral_zero_measure, hp, hm] at h
  exact hb (sub_eq_zero.mp h.symm)

private def constantStopped (x : ExposureEuclidean) (L : ℝ) (hL : 0 ≤ L) :
    StoppedPathSpace :=
  ⟨⟨L, ContinuousMap.const ℝ x⟩, hL, by
    apply lipschitzWith_iff_dist_le_mul.mpr
    intro s t
    simp, fun _ => rfl⟩

-- Zero-duration limits must be included in the compact space.
example (x : ExposureEuclidean) :
    constantStopped x 0 le_rfl ∈
      {a : StoppedPathSpace | a.duration ≤ 0 ∧ ∀ t, a.path t ∈ ({x} : Set ExposureEuclidean)} := by
  simp [constantStopped, StoppedPathSpace.duration, StoppedPathSpace.path]

-- Duration is not silently identified with length in the relaxed space;
-- test both sides of the cutoff, including its boundary.
example (x : ExposureEuclidean) :
    (constantStopped x 2 (by norm_num)).duration ≤ 2 ∧
      ¬(constantStopped x 2 (by norm_num)).duration ≤ 1 ∧
      ¬InjOn (constantStopped x 2 (by norm_num)).path (Icc 0 2) := by
  refine ⟨by norm_num [constantStopped, StoppedPathSpace.duration],
    by norm_num [constantStopped, StoppedPathSpace.duration], ?_⟩
  intro hi
  have h := hi (show (0 : ℝ) ∈ Icc 0 2 by norm_num)
    (show (1 : ℝ) ∈ Icc 0 2 by norm_num) rfl
  norm_num at h

example (a : ArcSpace) : a.toStoppedPath.duration = a.length ∧
    a.toStoppedPath.path = a.path := ⟨rfl, rfl⟩

open FiniteRouting
open scoped BigOperators

-- A split/merge network with internal source and sink vertices:
-- 0→1:3, 0→2:1, 1→2:1, 1→3:1, 2→3:4.
-- Net sources are (4,0,2,0), net sinks (0,1,0,5).
private def splitMerge : Flow (Fin 4) where
  edge := fun u v => if u.val = 0 ∧ v.val = 1 then 3 else
    if u.val = 0 ∧ v.val = 2 then 1 else if u.val = 1 ∧ v.val = 2 then 1 else
    if u.val = 1 ∧ v.val = 3 then 1 else if u.val = 2 ∧ v.val = 3 then 4 else 0
  nonneg := by intro u v; positivity
  height := fun v => 3 - v.val
  decreases := by intro u v; fin_cases u <;> fin_cases v <;> norm_num

example : total splitMerge.decomposition (fun γ => if γ.first = 2 then 1 else 0) = 2 := by
  rw [splitMerge.decomposition_initial (fun v => if v = 2 then 1 else 0)]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  norm_num [Flow.source, Flow.throughput, Flow.incoming, Flow.outgoing,
    splitMerge, Fin.sum_univ_succ, show (2 : Fin 4) ≠ 0 by decide]

-- A path may stop at vertex 1 even though that vertex has outgoing edges.
example : total splitMerge.decomposition (fun γ => if γ.last = 1 then 1 else 0) = 1 := by
  rw [splitMerge.decomposition_terminal (fun v => if v = 1 then 1 else 0)]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  norm_num [Flow.sink, Flow.throughput, Flow.incoming, Flow.outgoing,
    splitMerge, Fin.sum_univ_succ]

-- Forward usage 4 and reverse usage 0 distinguish direction and multiplicity.
example : total splitMerge.decomposition (Walk.reward (fun _ => 0)
    (fun u v => if u = 2 ∧ v = 3 then 1 else 0)) = 4 ∧
    total splitMerge.decomposition (Walk.reward (fun _ => 0)
    (fun u v => if u = 3 ∧ v = 2 then 1 else 0)) = 0 := by
  rw [splitMerge.decomposition_edge, splitMerge.decomposition_edge]
  norm_num [splitMerge, show (3 : Fin 4) ≠ 0 by decide]

-- Nonuniform edge costs, independent total 9 + 5 + 6 + 8 + 36 = 64.
example : total splitMerge.decomposition (Walk.reward (fun _ => 0)
    (fun u v => (u.val : ℝ) + 2 * v.val + 1)) = 64 := by
  rw [splitMerge.decomposition_ledger]
  norm_num [splitMerge, Fin.sum_univ_succ]

-- At a zero-throughput vertex the construction must not divide by zero
-- and create spurious source or sink mass.
private def zeroFlow : Flow (Fin 1) where
  edge := fun _ _ => 0
  nonneg := by intros; exact le_rfl
  height := fun _ => 0
  decreases := by intros; contradiction

example : total zeroFlow.decomposition (fun _ => 1) = 0 := by
  rw [zeroFlow.decomposition_initial (fun _ => 1)]
  norm_num [Flow.source, Flow.throughput, Flow.incoming, Flow.outgoing, zeroFlow]

-- Unequal edge lengths 2 and 3: a unit-time-per-edge interpolation would fail.
private def rayPositions (e : ExposureEuclidean) (v : ℕ) : ExposureEuclidean :=
  (if v = 0 then 0 else if v = 1 then 2 else 5 : ℝ) • e
private def rayWalk : Walk ℕ := .step 0 (.step 1 (.stop 2))

example (e : ExposureEuclidean) (he : ‖e‖ = 1) :
    (rayWalk.realize (rayPositions e)).duration = 5 := by
  rw [Walk.realize_duration]
  norm_num [rayWalk, rayPositions, Walk.reward, Walk.first,
    ← sub_smul, norm_smul, he]

example (e : ExposureEuclidean) (he : ‖e‖ = 1) :
    (rayWalk.realize (rayPositions e)).path 2 = (2:ℝ) • e ∧
    (rayWalk.realize (rayPositions e)).path 4 = (4:ℝ) • e := by
  simp only [rayWalk, Walk.realize_step, PolygonalPath.join_formula, PolygonalPath.joined,
    PolygonalPath.segment_duration, Walk.first, rayPositions]
  norm_num [PolygonalPath.segment_formula, PolygonalPath.direction,
    ← sub_smul, norm_smul, he, smul_smul]
  module

-- Both tails stop at the actual endpoints, not at an extrapolated line.
example (e : ExposureEuclidean) (he : ‖e‖ = 1) :
    (rayWalk.realize (rayPositions e)).path (-1) = 0 ∧
    (rayWalk.realize (rayPositions e)).path 6 = (5:ℝ) • e := by
  have hd : (rayWalk.realize (rayPositions e)).duration = 5 := by
    rw [Walk.realize_duration]
    norm_num [rayWalk, rayPositions, Walk.reward, Walk.first, ← sub_smul, norm_smul, he]
  constructor
  · rw [StoppedPathSpace.before _ (by norm_num), Walk.realize_initial]
    simp [rayWalk, Walk.first, rayPositions]
  · rw [StoppedPathSpace.after _ (by change (rayWalk.realize (rayPositions e)).duration ≤ 6; rw [hd]; norm_num),
      Walk.realize_terminal]
    simp [rayWalk, Walk.last, rayPositions]

-- A retraced segment is unit speed a.e. but is not a simple arc.
example (x y : ExposureEuclidean) (hxy : x ≠ y) :
    ¬InjOn (PolygonalPath.join (PolygonalPath.segment x y) (PolygonalPath.segment y x)
      (by rw [PolygonalPath.segment_terminal, PolygonalPath.segment_initial])).path
      (Icc 0 (‖y-x‖ + ‖x-y‖)) := by
  intro hi
  have hn : 0 < ‖y-x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hxy))
  have he : (0:ℝ) = ‖y-x‖ + ‖x-y‖ := hi
    ⟨le_rfl, add_nonneg (norm_nonneg _) (norm_nonneg _)⟩
    ⟨add_nonneg (norm_nonneg _) (norm_nonneg _), le_rfl⟩ (by
      rw [← PolygonalPath.segment_duration x y, ← PolygonalPath.segment_duration y x,
        ← PolygonalPath.join_duration _ _ (by rw [PolygonalPath.segment_terminal, PolygonalPath.segment_initial]),
        PolygonalPath.join_terminal, PolygonalPath.join_initial,
        PolygonalPath.segment_initial, PolygonalPath.segment_terminal])
  linarith [norm_nonneg (x-y)]

-- The geometric hypotheses are inhabited: an arbitrary nondegenerate edge.
private def oneEdge (u v : Bool) : ℝ := if u = false ∧ v = true then 1 else 0
private def oneEdgeEmbedding (x y : ExposureEuclidean) (hxy : x ≠ y) : StraightEmbedding oneEdge where
  pos := fun b => if b then y else x
  injective := by intro a b h; cases a <;> cases b <;> simp_all
  vertex_on_edge := by intro u v h w _; cases u <;> cases v <;> cases w <;> simp_all [oneEdge]
  edge_meet := by
    intro u v w z h1 h2 hd
    cases u <;> cases v <;> cases w <;> cases z <;> simp_all [oneEdge]

example (x y : ExposureEuclidean) (hxy : x ≠ y) :
    ∃ γ : EuclideanArc, γ.length = ‖y-x‖ ∧ γ.path 0 = x ∧ γ.path γ.length = y := by
  let E := oneEdgeEmbedding x y hxy
  let w : Walk Bool := .step false (.stop true)
  let γ := E.arc w (by simp [w, Walk.Allowed, Walk.first, oneEdge])
    (by simp [w, Walk.vertices]) (by simp [w, Walk.first, Walk.last])
  refine ⟨γ, ?_, ?_, ?_⟩
  · change (w.realize E.pos).duration = _
    rw [Walk.realize_duration]
    simp [w, E, oneEdgeEmbedding, Walk.reward, Walk.first]
  · exact w.realize_initial E.pos
  · exact w.realize_terminal E.pos

run_cmd do
  for name in [``EuclideanArc.measurable_tangentField, ``EuclideanArc.tangentField_path,
      ``EuclideanArc.tangentField_unit, ``EuclideanArc.integrable_tangentField,
      ``EuclideanArc.vectorCurrent_apply, ``EuclideanArc.integrable_deriv,
      ``EuclideanArc.vectorCurrent_eq_map, ``EuclideanArc.vectorCurrent_variation,
      ``EuclideanArc.vectorCurrent_mass, ``EuclideanArc.vectorCurrent_compact_support,
      ``EuclideanArc.integral_tangentField, ``EuclideanArc.boundary,
      ``EuclideanArc.toNormalCurrentData, ``EuclideanArc.action_eq,
      ``ArcSpace.ofArc, ``ArcSpace.ofArc_path, ``ArcSpace.ofArc_deriv,
      ``ArcSpace.ofArc_lengthMeasure, ``ArcSpace.ofArc_vectorCurrent,
      ``ArcSpace.continuous_length, ``ArcSpace.continuous_eval,
      ``ArcSpace.continuous_initial, ``ArcSpace.continuous_terminal,
      ``ArcSpace.measurable_tangent, ``ArcSpace.measurable_lengthMeasure,
      ``ArcSpace.measurable_vectorCurrent_apply, ``ArcSpace.measurable_pairing,
      ``ArcSpace.measurableArcs,
      ``DensityCycleRemoval.exists_acyclic_density,
      ``EuclideanNormalCurrentData.boundaryFunctional_apply,
      ``EuclideanNormalCurrentData.densityCurrent_subcurrent,
      ``EuclideanNormalCurrentData.densityCurrent_variation,
      ``EuclideanNormalCurrentData.densityCurrentData,
      ``EuclideanNormalCurrentData.subcurrent_density,
      ``EuclideanNormalCurrentData.exists_boundary_preserving_density,
      ``EuclideanNormalCurrentData.exists_acyclic_subcurrent,
      ``StoppedPathSpace.isClosed_carrier,
      ``StoppedPathSpace.continuous_duration, ``StoppedPathSpace.continuous_eval,
      ``StoppedPathSpace.continuous_initial, ``StoppedPathSpace.isClosed_endpointLaws,
      ``StoppedPathSpace.continuous_terminal, ``StoppedPathSpace.isCompact_cutoff,
      ``StoppedPathSpace.cutoff_compl_le, ``StoppedPathSpace.isTight_of_duration_bound,
      ``StoppedPathSpace.isCompact_closure_ensembles,
      ``ArcSpace.toStoppedPath, ``ArcSpace.continuous_toStoppedPath,
      ``FiniteRouting.Flow.ofAcyclic, ``FiniteRouting.exists_decomposition,
      ``FiniteRouting.Flow.decomposition_nonneg, ``FiniteRouting.Flow.decomposition_support,
      ``FiniteRouting.Flow.decomposition_initial, ``FiniteRouting.Flow.decomposition_terminal,
      ``FiniteRouting.Flow.decomposition_edge, ``FiniteRouting.Flow.decomposition_ledger,
      ``PolygonalPath.segment, ``PolygonalPath.join, ``PolygonalPath.unit_speed,
      ``PolygonalPath.segment_injOn, ``PolygonalPath.join_injOn,
      ``FiniteRouting.Walk.realize, ``FiniteRouting.Walk.realize_initial,
      ``FiniteRouting.Walk.realize_terminal, ``FiniteRouting.Walk.realize_duration,
      ``FiniteRouting.Walk.realize_mem_trace,
      ``FiniteRouting.StraightEmbedding.realize_injOn,
      ``FiniteRouting.StraightEmbedding.arc,
      ``FiniteRouting.Flow.geometric_length_ledger, ``FiniteRouting.Flow.geometric_arc] do
    for ax in ← Lean.collectAxioms name do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"
