module
public import RequestProject.AppendixE.ControlLieAlgebra
public import RequestProject.AppendixE.FaceProjection
public import Mathlib.Analysis.Normed.Module.Normalize
public import Mathlib.Topology.EMetricSpace.BoundedVariation
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# State geometry: local geometric paths and length comparison

`Xset` is identified topologically with the product of two unit
spheres in Euclidean four-space, using the first and last four real
coordinates.  For ambient sup distance `‖y−x‖ ≤ 1/4`, the normalized
affine chords in each sector stay within `Xset` and have Euclidean
arc length at most `16 ‖y−x‖`; each sector chord has norm at least
`1/2`, so no amplitude division is needed anywhere.

The length is Euclidean total variation (`eVariationOn`), an extended
nonnegative real.  Its infimum `geometricEDist` over smooth paths in
`Xset` lies between the ambient chord distance and the stated local
upper bound.  No manifold/metric structure on `State` is introduced;
the paths are geometric, not `vf`-controlled, and nothing here is a
physical steering trajectory or a ball-box theorem.
-/

@[expose] public section

noncomputable section

namespace CZExposure.StateGeometry

open MeasureTheory Set
open ControlLie
open scoped NNReal ENNReal

abbrev SectorEuclidean := EuclideanSpace ℝ (Fin 4)
abbrev StateEuclidean := EuclideanSpace ℝ (Fin 8)

def euclideanEquiv : State ≃L[ℝ] StateEuclidean :=
  (EuclideanSpace.equiv (Fin 8) ℝ).symm

/-- Sector coordinate maps into Euclidean four-space. -/
def sector1 (x : State) : SectorEuclidean :=
  WithLp.toLp 2 ![x 0, x 1, x 2, x 3]
def sector2 (x : State) : SectorEuclidean :=
  WithLp.toLp 2 ![x 4, x 5, x 6, x 7]

def join (a b : SectorEuclidean) : State :=
  ![a 0, a 1, a 2, a 3, b 0, b 1, b 2, b 3]

@[simp] theorem sector1_join (a b : SectorEuclidean) :
    sector1 (join a b) = a := by
  ext i
  fin_cases i <;> simp [sector1, join]

@[simp] theorem sector2_join (a b : SectorEuclidean) :
    sector2 (join a b) = b := by
  ext i
  fin_cases i <;> simp [sector2, join]

@[simp] theorem join_sectors (x : State) :
    join (sector1 x) (sector2 x) = x := by
  funext i
  fin_cases i <;> simp [join, sector1, sector2]

private def sector1LM : State →ₗ[ℝ] SectorEuclidean where
  toFun := sector1
  map_add' := fun x y => by
    ext i
    fin_cases i <;> simp [sector1, Pi.add_apply]
  map_smul' := fun r x => by
    ext i
    fin_cases i <;> simp [sector1, Pi.smul_apply, smul_eq_mul]

private def sector2LM : State →ₗ[ℝ] SectorEuclidean where
  toFun := sector2
  map_add' := fun x y => by
    ext i
    fin_cases i <;> simp [sector2, Pi.add_apply]
  map_smul' := fun r x => by
    ext i
    fin_cases i <;> simp [sector2, Pi.smul_apply, smul_eq_mul]

private def sector1CLM : State →L[ℝ] SectorEuclidean :=
  LinearMap.toContinuousLinearMap sector1LM

private def sector2CLM : State →L[ℝ] SectorEuclidean :=
  LinearMap.toContinuousLinearMap sector2LM

theorem contDiff_sector1 : ContDiff ℝ ⊤ sector1 :=
  sector1CLM.contDiff

theorem contDiff_sector2 : ContDiff ℝ ⊤ sector2 :=
  sector2CLM.contDiff

private def joinLM : (SectorEuclidean × SectorEuclidean) →ₗ[ℝ] State where
  toFun := fun ab => join ab.1 ab.2
  map_add' := fun x y => by
    funext i
    fin_cases i <;> simp [join, Pi.add_apply]
  map_smul' := fun r x => by
    funext i
    fin_cases i <;> simp [join, Pi.smul_apply, smul_eq_mul]

private def joinCLM : (SectorEuclidean × SectorEuclidean) →L[ℝ] State :=
  LinearMap.toContinuousLinearMap joinLM

theorem contDiff_join : ContDiff ℝ ⊤
    (fun ab : SectorEuclidean × SectorEuclidean => join ab.1 ab.2) :=
  joinCLM.contDiff

theorem norm_sector1_sq (x : State) :
    ‖sector1 x‖ ^ 2 = ControlLie.normalization x 0 := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp [sector1, ControlLie.normalization, ControlLie.normal,
    Fin.sum_univ_succ, sq_abs]
  ring

theorem norm_sector2_sq (x : State) :
    ‖sector2 x‖ ^ 2 = ControlLie.normalization x 1 := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp [sector2, ControlLie.normalization, ControlLie.normal,
    Fin.sum_univ_succ, sq_abs]
  ring

theorem mem_Xset_iff_sector_norms (x : State) :
    x ∈ Xset ↔ ‖sector1 x‖ = 1 ∧ ‖sector2 x‖ = 1 := by
  rw [mem_Xset_iff_normalization]
  constructor
  · intro h
    have h0 : ControlLie.normalization x 0 = 1 := congrFun h 0
    have h1 : ControlLie.normalization x 1 = 1 := congrFun h 1
    have e1 : ‖sector1 x‖ ^ 2 = 1 := by rw [norm_sector1_sq, h0]
    have e2 : ‖sector2 x‖ ^ 2 = 1 := by rw [norm_sector2_sq, h1]
    constructor
    · rcases sq_eq_one_iff.mp e1 with hh | hh
      · exact hh
      · linarith [norm_nonneg (sector1 x)]
    · rcases sq_eq_one_iff.mp e2 with hh | hh
      · exact hh
      · linarith [norm_nonneg (sector2 x)]
  · rintro ⟨h1, h2⟩
    funext i
    fin_cases i
    · show ControlLie.normalization x 0 = 1
      rw [← norm_sector1_sq x, h1]
      norm_num
    · show ControlLie.normalization x 1 = 1
      rw [← norm_sector2_sq x, h2]
      norm_num

private theorem norm_coord_le (x : State) (i : Fin 8) : |x i| ≤ ‖x‖ := by
  simpa only [Real.norm_eq_abs] using (norm_le_pi_norm x i)

theorem norm_sector1_le (x : State) : ‖sector1 x‖ ≤ 2 * ‖x‖ := by
  have hbound : ‖sector1 x‖ ^ 2 ≤ (2 * ‖x‖) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp [sector1, Fin.sum_univ_succ, sq_abs]
    have e0 : |x 0| ≤ ‖x‖ := norm_coord_le x 0
    have e1 : |x 1| ≤ ‖x‖ := norm_coord_le x 1
    have e2 : |x 2| ≤ ‖x‖ := norm_coord_le x 2
    have e3 : |x 3| ≤ ‖x‖ := norm_coord_le x 3
    nlinarith [sq_abs (x 0), sq_abs (x 1), sq_abs (x 2), sq_abs (x 3),
      mul_le_mul e0 e0 (abs_nonneg _) (norm_nonneg _),
      mul_le_mul e1 e1 (abs_nonneg _) (norm_nonneg _),
      mul_le_mul e2 e2 (abs_nonneg _) (norm_nonneg _),
      mul_le_mul e3 e3 (abs_nonneg _) (norm_nonneg _)]
  have h := abs_le_of_sq_le_sq hbound (by positivity : (0:ℝ) ≤ 2 * ‖x‖)
  rwa [abs_of_nonneg (norm_nonneg _)] at h

theorem norm_sector2_le (x : State) : ‖sector2 x‖ ≤ 2 * ‖x‖ := by
  have hbound : ‖sector2 x‖ ^ 2 ≤ (2 * ‖x‖) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp [sector2, Fin.sum_univ_succ, sq_abs]
    have e0 : |x 4| ≤ ‖x‖ := norm_coord_le x 4
    have e1 : |x 5| ≤ ‖x‖ := norm_coord_le x 5
    have e2 : |x 6| ≤ ‖x‖ := norm_coord_le x 6
    have e3 : |x 7| ≤ ‖x‖ := norm_coord_le x 7
    nlinarith [sq_abs (x 4), sq_abs (x 5), sq_abs (x 6), sq_abs (x 7),
      mul_le_mul e0 e0 (abs_nonneg _) (norm_nonneg _),
      mul_le_mul e1 e1 (abs_nonneg _) (norm_nonneg _),
      mul_le_mul e2 e2 (abs_nonneg _) (norm_nonneg _),
      mul_le_mul e3 e3 (abs_nonneg _) (norm_nonneg _)]
  have h := abs_le_of_sq_le_sq hbound (by positivity : (0:ℝ) ≤ 2 * ‖x‖)
  rwa [abs_of_nonneg (norm_nonneg _)] at h

theorem norm_euclidean_join_le (a b : SectorEuclidean) :
    ‖euclideanEquiv (join a b)‖ ≤ ‖a‖ + ‖b‖ := by
  have hs : ‖euclideanEquiv (join a b)‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2 (x := a),
      PiLp.norm_sq_eq_of_L2 (x := b)]
    simp [euclideanEquiv, join, Fin.sum_univ_succ,
      sq_abs]
    ring
  have hsq : ‖euclideanEquiv (join a b)‖ ^ 2 ≤ (‖a‖ + ‖b‖) ^ 2 := by
    rw [hs]
    nlinarith [mul_nonneg (norm_nonneg a) (norm_nonneg b)]
  have h := abs_le_of_sq_le_sq hsq
    (add_nonneg (norm_nonneg a) (norm_nonneg b))
  rwa [abs_of_nonneg (norm_nonneg _)] at h

theorem norm_le_euclidean (x : State) :
    ‖x‖ ≤ ‖euclideanEquiv x‖ := by
  have h : Finset.sup Finset.univ (fun i : Fin 8 => ‖x i‖₊) ≤
      ‖euclideanEquiv x‖₊ := by
    apply Finset.sup_le
    intro i _
    exact PiLp.nnnorm_apply_le (euclideanEquiv x) i
  exact NNReal.coe_le_coe.mpr h

abbrev UnitSector := ↥(Metric.sphere (0 : SectorEuclidean) 1)

/-- `Xset` is homeomorphic to `S³ × S³` via the sector maps. -/
def stateSphereHomeomorph : ↥Xset ≃ₜ (UnitSector × UnitSector) where
  toFun x :=
    (⟨sector1 (x : State), by
        rw [Metric.mem_sphere, dist_zero_right]
        exact ((mem_Xset_iff_sector_norms x).mp x.2).1⟩,
     ⟨sector2 (x : State), by
        rw [Metric.mem_sphere, dist_zero_right]
        exact ((mem_Xset_iff_sector_norms x).mp x.2).2⟩)
  invFun ab := ⟨join (ab.1 : SectorEuclidean) (ab.2 : SectorEuclidean), by
    have ha : ‖(ab.1 : SectorEuclidean)‖ = 1 := by
      have h := ab.1.2
      rwa [Metric.mem_sphere, dist_zero_right] at h
    have hb : ‖(ab.2 : SectorEuclidean)‖ = 1 := by
      have h := ab.2.2
      rwa [Metric.mem_sphere, dist_zero_right] at h
    rw [mem_Xset_iff_sector_norms]
    constructor <;> simp [ha, hb]⟩
  left_inv := fun x => Subtype.ext (join_sectors (x : State))
  right_inv := fun ab => by
    ext i <;> fin_cases i <;> simp
  continuous_toFun := by
    apply Continuous.prodMk
    · exact Continuous.subtype_mk
        (contDiff_sector1.continuous.comp continuous_subtype_val) _
    · exact Continuous.subtype_mk
        (contDiff_sector2.continuous.comp continuous_subtype_val) _
  continuous_invFun := by
    apply Continuous.subtype_mk
    have hpair : Continuous fun ab : UnitSector × UnitSector =>
        ((↑ab.1, ↑ab.2) : SectorEuclidean × SectorEuclidean) :=
      Continuous.prodMk (continuous_subtype_val.comp continuous_fst)
        (continuous_subtype_val.comp continuous_snd)
    exact contDiff_join.continuous.comp hpair

/-! ## Normalized chords and short geometric paths -/

theorem norm_normalize_sub_le_four {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {a b : E} (ha : (1:ℝ)/2 ≤ ‖a‖)
    (hb : (1:ℝ)/2 ≤ ‖b‖) :
    ‖NormedSpace.normalize a - NormedSpace.normalize b‖ ≤ 4 * ‖a - b‖ := by
  have har : (0:ℝ) < ‖a‖ := lt_of_lt_of_le (by norm_num) ha
  have hbr : (0:ℝ) < ‖b‖ := lt_of_lt_of_le (by norm_num) hb
  have hkey : NormedSpace.normalize a - NormedSpace.normalize b =
      ‖a‖⁻¹ • (a - b) + (‖a‖⁻¹ - ‖b‖⁻¹) • b := by
    simp only [NormedSpace.normalize]
    module
  rw [hkey]
  calc ‖‖a‖⁻¹ • (a - b) + (‖a‖⁻¹ - ‖b‖⁻¹) • b‖
      ≤ ‖a‖⁻¹ * ‖a - b‖ + |‖a‖⁻¹ - ‖b‖⁻¹| * ‖b‖ := by
        refine (norm_add_le _ _).trans ?_
        refine add_le_add ?_ ?_
        · rw [norm_smul, Real.norm_eq_abs,
            abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
        · rw [norm_smul, Real.norm_eq_abs]
    _ = (‖a - b‖ + |‖b‖ - ‖a‖|) / ‖a‖ := by
        rw [inv_sub_inv har.ne' hbr.ne', abs_div,
          abs_of_pos (mul_pos har hbr)]
        field_simp
    _ ≤ (2 * ‖a - b‖) / ‖a‖ := by
        have hsub : |‖b‖ - ‖a‖| ≤ ‖a - b‖ := by
          rw [abs_sub_comm]
          exact abs_norm_sub_norm_le _ _
        rw [div_eq_mul_inv, div_eq_mul_inv]
        nlinarith [hsub, inv_nonneg.mpr (norm_nonneg a),
          norm_nonneg (a - b)]
    _ ≤ 4 * ‖a - b‖ := by
        have h : ‖a‖⁻¹ ≤ 2 := by
          have h := (inv_le_inv₀ har
            (show (0:ℝ) < 1/2 by norm_num)).mpr ha
          norm_num at h
          exact h
        rw [div_eq_mul_inv, show (4 : ℝ) * ‖a - b‖ =
          (2 * ‖a - b‖) * 2 from by ring]
        nlinarith [h, norm_nonneg (a - b)]

def chord (a b : SectorEuclidean) (t : ℝ) : SectorEuclidean :=
  a + t • (b - a)

def normalizedChord (a b : SectorEuclidean) (t : ℝ) : SectorEuclidean :=
  NormedSpace.normalize (chord a b t)

theorem chord_norm_lower {a b : SectorEuclidean} (ha : ‖a‖ = 1)
    (hab : ‖b - a‖ ≤ (1:ℝ)/2) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    (1:ℝ)/2 ≤ ‖chord a b t‖ := by
  have htr : ‖a‖ - ‖chord a b t‖ ≤ |t| * ‖b - a‖ := by
    have h1 : ‖a‖ - ‖chord a b t‖ ≤ ‖a - chord a b t‖ :=
      norm_sub_norm_le _ _
    have hsub : a - chord a b t = -(t • (b - a)) := by
      simp [chord]
    rw [hsub, norm_neg, norm_smul, Real.norm_eq_abs] at h1
    exact h1
  have ht1 : |t| ≤ 1 := by
    rw [abs_le]
    exact ⟨by linarith [ht.1], ht.2⟩
  have : |t| * ‖b - a‖ ≤ 1/2 := by
    calc |t| * ‖b - a‖ ≤ 1 * (1/2) :=
        mul_le_mul ht1 hab (norm_nonneg _) zero_le_one
      _ = 1/2 := by ring
  have : ‖a‖ - ‖chord a b t‖ ≤ 1/2 := le_trans htr this
  linarith

theorem normalizedChord_norm {a b : SectorEuclidean} (ha : ‖a‖ = 1)
    (hab : ‖b - a‖ ≤ (1:ℝ)/2) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    ‖normalizedChord a b t‖ = 1 := by
  have hc : chord a b t ≠ 0 := by
    have h := chord_norm_lower ha hab ht
    exact norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) h)
  exact NormedSpace.norm_normalize hc

theorem normalizedChord_dist_le {a b : SectorEuclidean} (ha : ‖a‖ = 1)
    (hab : ‖b - a‖ ≤ (1:ℝ)/2) {s t : ℝ}
    (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 1) :
    ‖normalizedChord a b s - normalizedChord a b t‖ ≤
      4 * ‖b - a‖ * |s - t| := by
  have hcs : (1:ℝ)/2 ≤ ‖chord a b s‖ := chord_norm_lower ha hab hs
  have hct : (1:ℝ)/2 ≤ ‖chord a b t‖ := chord_norm_lower ha hab ht
  have hsub : chord a b s - chord a b t = (s - t) • (b - a) := by
    simp [chord]
    module
  calc ‖normalizedChord a b s - normalizedChord a b t‖
      ≤ 4 * ‖chord a b s - chord a b t‖ :=
        norm_normalize_sub_le_four (E := SectorEuclidean) hcs hct
    _ = 4 * (|s - t| * ‖b - a‖) := by
        rw [hsub, norm_smul, Real.norm_eq_abs]
    _ = 4 * ‖b - a‖ * |s - t| := by ring

theorem contDiffOn_normalizedChord {a b : SectorEuclidean} (ha : ‖a‖ = 1)
    (hab : ‖b - a‖ ≤ (1:ℝ)/2) :
    ContDiffOn ℝ ⊤ (normalizedChord a b) (Set.Icc 0 1) := by
  have hch : ContDiff ℝ ⊤ (chord a b) :=
    contDiff_const.add (contDiff_id.smul contDiff_const)
  have hne : ∀ t ∈ Set.Icc 0 1, chord a b t ≠ 0 := fun t ht =>
    norm_pos_iff.mp (lt_of_lt_of_le (by norm_num)
      (chord_norm_lower ha hab ht))
  have hnorm : ContDiffOn ℝ ⊤ (fun t => ‖chord a b t‖) (Set.Icc 0 1) :=
    ContDiffOn.norm ℝ hch.contDiffOn hne
  have hinv : ContDiffOn ℝ ⊤ (fun t => ‖chord a b t‖⁻¹) (Set.Icc 0 1) :=
    hnorm.inv (fun t ht => norm_ne_zero_iff.mpr (hne t ht))
  have : ContDiffOn ℝ ⊤
      (fun t => ‖chord a b t‖⁻¹ • chord a b t) (Set.Icc 0 1) :=
    hinv.smul hch.contDiffOn
  unfold normalizedChord NormedSpace.normalize
  exact this

/-! ## The short path between nearby states -/

def shortPath (x y : State) (t : ℝ) : State :=
  join (normalizedChord (sector1 x) (sector1 y) t)
    (normalizedChord (sector2 x) (sector2 y) t)

theorem shortPath_zero {x y : State} (hx : x ∈ Xset) :
    shortPath x y 0 = x := by
  have h1 : ‖sector1 x‖ = 1 := ((mem_Xset_iff_sector_norms x).mp hx).1
  have h2 : ‖sector2 x‖ = 1 := ((mem_Xset_iff_sector_norms x).mp hx).2
  simp only [shortPath, normalizedChord, chord, zero_smul, add_zero]
  rw [NormedSpace.normalize_eq_self_of_norm_eq_one h1,
    NormedSpace.normalize_eq_self_of_norm_eq_one h2,
    join_sectors]

theorem shortPath_one {x y : State} (hy : y ∈ Xset) :
    shortPath x y 1 = y := by
  have h1 : ‖sector1 y‖ = 1 := ((mem_Xset_iff_sector_norms y).mp hy).1
  have h2 : ‖sector2 y‖ = 1 := ((mem_Xset_iff_sector_norms y).mp hy).2
  simp only [shortPath, normalizedChord, chord, one_smul]
  rw [show sector1 x + (sector1 y - sector1 x) = sector1 y from by abel,
    show sector2 x + (sector2 y - sector2 x) = sector2 y from by abel,
    NormedSpace.normalize_eq_self_of_norm_eq_one h1,
    NormedSpace.normalize_eq_self_of_norm_eq_one h2,
    join_sectors]

theorem shortPath_self {x : State} (hx : x ∈ Xset) (t : ℝ) :
    shortPath x x t = x := by
  have h1 : ‖sector1 x‖ = 1 := ((mem_Xset_iff_sector_norms x).mp hx).1
  have h2 : ‖sector2 x‖ = 1 := ((mem_Xset_iff_sector_norms x).mp hx).2
  simp only [shortPath, normalizedChord, chord, sub_self, smul_zero,
    add_zero]
  rw [NormedSpace.normalize_eq_self_of_norm_eq_one h1,
    NormedSpace.normalize_eq_self_of_norm_eq_one h2,
    join_sectors]

private theorem sector1_sub (x y : State) :
    sector1 y - sector1 x = sector1 (y - x) := by
  ext i
  fin_cases i <;> simp [sector1, Pi.sub_apply]

private theorem sector2_sub (x y : State) :
    sector2 y - sector2 x = sector2 (y - x) := by
  ext i
  fin_cases i <;> simp [sector2, Pi.sub_apply]

private theorem join_sub (a₁ a₂ b₁ b₂ : SectorEuclidean) :
    join a₁ b₁ - join a₂ b₂ = join (a₁ - a₂) (b₁ - b₂) := by
  funext i
  fin_cases i <;> simp [join, Pi.sub_apply]

theorem shortPath_mem {x y : State} (hx : x ∈ Xset) (_hy : y ∈ Xset)
    (hclose : ‖y - x‖ ≤ (1:ℝ)/4) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    shortPath x y t ∈ Xset := by
  have hx1 : ‖sector1 x‖ = 1 := ((mem_Xset_iff_sector_norms x).mp hx).1
  have hx2 : ‖sector2 x‖ = 1 := ((mem_Xset_iff_sector_norms x).mp hx).2
  have hn1 : ‖sector1 y - sector1 x‖ ≤ (1:ℝ)/2 := by
    rw [sector1_sub]
    calc ‖sector1 (y - x)‖ ≤ 2 * ‖y - x‖ := norm_sector1_le _
      _ ≤ 1/2 := by linarith
  have hn2 : ‖sector2 y - sector2 x‖ ≤ (1:ℝ)/2 := by
    rw [sector2_sub]
    calc ‖sector2 (y - x)‖ ≤ 2 * ‖y - x‖ := norm_sector2_le _
      _ ≤ 1/2 := by linarith
  rw [mem_Xset_iff_sector_norms]
  unfold shortPath
  simp only [sector1_join, sector2_join]
  exact ⟨normalizedChord_norm hx1 hn1 ht,
    normalizedChord_norm hx2 hn2 ht⟩

theorem contDiffOn_shortPath {x y : State} (hx : x ∈ Xset) (_hy : y ∈ Xset)
    (hclose : ‖y - x‖ ≤ (1:ℝ)/4) :
    ContDiffOn ℝ ⊤ (shortPath x y) (Set.Icc 0 1) := by
  have hx1 : ‖sector1 x‖ = 1 := ((mem_Xset_iff_sector_norms x).mp hx).1
  have hx2 : ‖sector2 x‖ = 1 := ((mem_Xset_iff_sector_norms x).mp hx).2
  have hn1 : ‖sector1 y - sector1 x‖ ≤ (1:ℝ)/2 := by
    rw [sector1_sub]
    exact (norm_sector1_le _).trans (by linarith)
  have hn2 : ‖sector2 y - sector2 x‖ ≤ (1:ℝ)/2 := by
    rw [sector2_sub]
    exact (norm_sector2_le _).trans (by linarith)
  unfold shortPath
  exact contDiff_join.contDiffOn.comp
    ((contDiffOn_normalizedChord hx1 hn1).prodMk
      (contDiffOn_normalizedChord hx2 hn2))
    (mapsTo_univ _ _)

theorem euclidean_shortPath_dist_le {x y : State} (hx : x ∈ Xset)
    (_hy : y ∈ Xset) (hclose : ‖y - x‖ ≤ (1:ℝ)/4) {s t : ℝ}
    (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 1) :
    ‖euclideanEquiv (shortPath x y s) - euclideanEquiv (shortPath x y t)‖ ≤
      16 * ‖y - x‖ * |s - t| := by
  have hx1 : ‖sector1 x‖ = 1 := ((mem_Xset_iff_sector_norms x).mp hx).1
  have hx2 : ‖sector2 x‖ = 1 := ((mem_Xset_iff_sector_norms x).mp hx).2
  have hn1 : ‖sector1 y - sector1 x‖ ≤ (1:ℝ)/2 := by
    rw [sector1_sub]
    exact (norm_sector1_le _).trans (by linarith)
  have hn2 : ‖sector2 y - sector2 x‖ ≤ (1:ℝ)/2 := by
    rw [sector2_sub]
    exact (norm_sector2_le _).trans (by linarith)
  rw [← map_sub]
  simp only [shortPath]
  rw [join_sub]
  calc ‖euclideanEquiv (join
        (normalizedChord (sector1 x) (sector1 y) s -
          normalizedChord (sector1 x) (sector1 y) t)
        (normalizedChord (sector2 x) (sector2 y) s -
          normalizedChord (sector2 x) (sector2 y) t))‖
      ≤ ‖normalizedChord (sector1 x) (sector1 y) s -
          normalizedChord (sector1 x) (sector1 y) t‖ +
        ‖normalizedChord (sector2 x) (sector2 y) s -
          normalizedChord (sector2 x) (sector2 y) t‖ :=
        norm_euclidean_join_le _ _
    _ ≤ 4 * ‖sector1 y - sector1 x‖ * |s - t| +
          4 * ‖sector2 y - sector2 x‖ * |s - t| :=
        add_le_add (normalizedChord_dist_le hx1 hn1 hs ht)
          (normalizedChord_dist_le hx2 hn2 hs ht)
    _ ≤ 4 * (2 * ‖y - x‖) * |s - t| + 4 * (2 * ‖y - x‖) * |s - t| := by
        refine add_le_add
          (mul_le_mul_of_nonneg_right ?_ (abs_nonneg _))
          (mul_le_mul_of_nonneg_right ?_ (abs_nonneg _))
        · rw [sector1_sub]
          exact mul_le_mul_of_nonneg_left (norm_sector1_le _)
            (show (0:ℝ) ≤ 4 by norm_num)
        · rw [sector2_sub]
          exact mul_le_mul_of_nonneg_left (norm_sector2_le _)
            (show (0:ℝ) ≤ 4 by norm_num)
    _ = 16 * ‖y - x‖ * |s - t| := by ring

private theorem enn_coe_eq_ofReal (p : ℝ≥0) :
    (↑p : ℝ≥0∞) = ENNReal.ofReal (p : ℝ) :=
  (ENNReal.ofReal_coe_nnreal (p := p)).symm

private theorem edist_eq_ofReal_norm {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (a b : E) :
    edist a b = ENNReal.ofReal ‖a - b‖ := by
  rw [edist_dist, dist_eq_norm]

theorem lipschitzOn_euclidean_shortPath {x y : State} (hx : x ∈ Xset)
    (hy : y ∈ Xset) (hclose : ‖y - x‖ ≤ (1:ℝ)/4) :
    LipschitzOnWith ⟨16 * ‖y - x‖, by positivity⟩
      (fun t => euclideanEquiv (shortPath x y t)) (Set.Icc 0 1) := by
  intro s hs t ht
  have h := euclidean_shortPath_dist_le hx hy hclose hs ht
  have he : edist s t = ENNReal.ofReal |s - t| := by
    rw [edist_dist, Real.dist_eq]
  rw [he, edist_eq_ofReal_norm, enn_coe_eq_ofReal]
  rw [← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal h

/-! ## Geometric paths and Euclidean length -/

structure GeometricPath (x y : State) where
  path : ℝ → State
  smooth : ContDiffOn ℝ ⊤ path (Set.Icc 0 1)
  path_mem : ∀ t ∈ Set.Icc 0 1, path t ∈ Xset
  initial : path 0 = x
  terminal : path 1 = y

def GeometricPath.length {x y : State} (P : GeometricPath x y) :
    ℝ≥0∞ :=
  eVariationOn (fun t => euclideanEquiv (P.path t)) (Set.Icc 0 1)

theorem GeometricPath.chord_le_length {x y : State} (P : GeometricPath x y) :
    ENNReal.ofReal ‖y - x‖ ≤ P.length := by
  have h : edist (euclideanEquiv (P.path 0)) (euclideanEquiv (P.path 1)) ≤
      P.length :=
    eVariationOn.edist_le _ (Set.left_mem_Icc.mpr zero_le_one)
      (Set.right_mem_Icc.mpr zero_le_one)
  rw [P.initial, P.terminal] at h
  calc ENNReal.ofReal ‖y - x‖
      = ENNReal.ofReal ‖x - y‖ := by rw [norm_sub_rev]
    _ ≤ ENNReal.ofReal ‖euclideanEquiv x - euclideanEquiv y‖ := by
        apply ENNReal.ofReal_le_ofReal
        have := norm_le_euclidean (x - y)
        rw [map_sub] at this
        exact this
    _ = edist (euclideanEquiv x) (euclideanEquiv y) := by
        rw [edist_eq_ofReal_norm]
    _ ≤ P.length := h

def shortGeometricPath {x y : State} (hx : x ∈ Xset) (hy : y ∈ Xset)
    (hclose : ‖y - x‖ ≤ (1:ℝ)/4) : GeometricPath x y where
  path := shortPath x y
  smooth := contDiffOn_shortPath hx hy hclose
  path_mem := fun _ ht => shortPath_mem hx hy hclose ht
  initial := shortPath_zero hx
  terminal := shortPath_one hy

theorem shortGeometricPath_length_le {x y : State} (hx : x ∈ Xset)
    (hy : y ∈ Xset) (hclose : ‖y - x‖ ≤ (1:ℝ)/4) :
    (shortGeometricPath hx hy hclose).length ≤
      ENNReal.ofReal (16 * ‖y - x‖) := by
  have hid : MonotoneOn (id : ℝ → ℝ) (Set.Icc 0 1) :=
    fun _ _ _ _ h => h
  have hvar : eVariationOn (id : ℝ → ℝ) (Set.Icc 0 1) ≤ 1 := by
    have h := hid.eVariationOn_le
      (Set.left_mem_Icc.mpr (zero_le_one : (0:ℝ) ≤ 1))
      (Set.right_mem_Icc.mpr (zero_le_one : (0:ℝ) ≤ 1))
    simpa using h
  have hcomp := (lipschitzOn_euclidean_shortPath hx hy hclose).comp_eVariationOn_le
    (g := (id : ℝ → ℝ)) (s := Set.Icc 0 1) (fun _ ht => ht)
  refine le_trans hcomp ?_
  refine le_trans (mul_le_mul' le_rfl hvar) ?_
  rw [mul_one]
  exact (enn_coe_eq_ofReal _).le

/-- Infimum of Euclidean lengths of smooth paths within `Xset`.  Not
identified with mathlib's manifold Riemannian distance. -/
def geometricEDist (x y : State) : ℝ≥0∞ :=
  iInf (fun P : GeometricPath x y => P.length)

theorem chord_le_geometricEDist (x y : State) :
    ENNReal.ofReal ‖y - x‖ ≤ geometricEDist x y :=
  le_iInf fun P => GeometricPath.chord_le_length P

theorem geometricEDist_le_length {x y : State} (P : GeometricPath x y) :
    geometricEDist x y ≤ P.length :=
  iInf_le _ P

theorem geometricEDist_le {x y : State} (hx : x ∈ Xset) (hy : y ∈ Xset)
    (hclose : ‖y - x‖ ≤ (1:ℝ)/4) :
    geometricEDist x y ≤ ENNReal.ofReal (16 * ‖y - x‖) :=
  (geometricEDist_le_length (shortGeometricPath hx hy hclose)).trans
    (shortGeometricPath_length_le hx hy hclose)

theorem geometricEDist_self {x : State} (hx : x ∈ Xset) :
    geometricEDist x x = 0 := by
  have hclose : ‖x - x‖ ≤ (1:ℝ)/4 := by
    rw [sub_self, norm_zero]
    norm_num
  have h := geometricEDist_le hx hx hclose
  rw [sub_self, norm_zero, mul_zero] at h
  exact le_antisymm (by simpa using h) (zero_le _)

/-! ## Applications: projection and CZ target paths -/

theorem exists_projection_path {x : State} (hx : x ∈ Xset)
    (hc : cost x ≤ (1:ℝ)/16384) :
    ∃ P : GeometricPath x (faceProjection x),
      P.length ≤ ENNReal.ofReal (512 * Real.sqrt (cost x)) := by
  have hc12 : cost x ≤ 1/12 := le_trans hc (by norm_num)
  have hproj : faceProjection x ∈ Xset :=
    (faceProjection_mem hx hc12).1
  have hd : ‖faceProjection x - x‖ ≤ 32 * Real.sqrt (cost x) :=
    norm_faceProjection_sub_le hx hc12
  have hclose : ‖faceProjection x - x‖ ≤ (1:ℝ)/4 := by
    refine hd.trans ?_
    have hsq := Real.sq_sqrt (show (0:ℝ) ≤ cost x from cost_nonneg x)
    nlinarith [Real.sqrt_nonneg (cost x), hsq]
  refine ⟨shortGeometricPath hx hproj hclose, ?_⟩
  refine (shortGeometricPath_length_le hx hproj hclose).trans ?_
  refine ENNReal.ofReal_le_ofReal ?_
  nlinarith [hd, Real.sqrt_nonneg (cost x)]

theorem exists_CZ_target_path {x : State} (hx : x ∈ Fface) {θ : ℝ}
    (hz : zObs x = -phaseFactor θ) (hθ : |θ| ≤ (1:ℝ)/4) :
    ∃ P : GeometricPath x (faceCZTarget x),
      P.length ≤ ENNReal.ofReal (16 * |θ|) := by
  have htgt : faceCZTarget x ∈ Xset := (faceCZTarget_mem hx).1
  have hd : ‖faceCZTarget x - x‖ ≤ |θ| :=
    norm_faceCZTarget_sub_le_phase hx hz
  have hclose : ‖faceCZTarget x - x‖ ≤ (1:ℝ)/4 := hd.trans hθ
  refine ⟨shortGeometricPath hx.1 htgt hclose, ?_⟩
  refine (shortGeometricPath_length_le hx.1 htgt hclose).trans ?_
  refine ENNReal.ofReal_le_ofReal ?_
  linarith [hd, abs_nonneg θ]

end CZExposure.StateGeometry
