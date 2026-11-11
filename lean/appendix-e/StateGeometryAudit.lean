import RequestProject.AppendixE.StateGeometry
import RequestProject.AppendixE.SteeringExposure
import RequestProject.AppendixE.RelaxedSubsolution

/-!
# Audit: local geometric paths and length comparison

Aggregate-import axiom audit of `StateGeometry.lean`, composed with
`SteeringExposure` and `RelaxedSubsolution` to check namespace
compatibility.  Expected axioms are only
`[propext, Classical.choice, Quot.sound]`.

The scope checked here is geometric only: the paths are smooth curves
inside `Xset` with Euclidean length bounds, not `vf`-controlled
trajectories, and `geometricEDist` is not identified with mathlib's
manifold Riemannian distance.
-/

open CZExposure
open scoped NNReal ENNReal

namespace CZExposure.StateGeometry

-- Euclidean models of the state and its two four-coordinate sectors.
#check @SectorEuclidean
#check @StateEuclidean
#check @euclideanEquiv
#print axioms euclideanEquiv
#check @sector1
#print axioms sector1
#check @sector2
#print axioms sector2
#check @join
#print axioms join
#check @sector1_join
#print axioms sector1_join
#check @sector2_join
#print axioms sector2_join
#check @join_sectors
#print axioms join_sectors
#check @contDiff_sector1
#print axioms contDiff_sector1
#check @contDiff_sector2
#print axioms contDiff_sector2
#check @contDiff_join
#print axioms contDiff_join

-- Sector norms versus the sup norm on `State`, and the
-- product-sphere identification of `Xset`.
#check @norm_sector1_sq
#print axioms norm_sector1_sq
#check @norm_sector2_sq
#print axioms norm_sector2_sq
#check @mem_Xset_iff_sector_norms
#print axioms mem_Xset_iff_sector_norms
#check @norm_sector1_le
#print axioms norm_sector1_le
#check @norm_sector2_le
#print axioms norm_sector2_le
#check @norm_euclidean_join_le
#print axioms norm_euclidean_join_le
#check @norm_le_euclidean
#print axioms norm_le_euclidean
#check @UnitSector
#check @stateSphereHomeomorph
#print axioms stateSphereHomeomorph

-- Radial normalization and the normalized affine chords.
#check @norm_normalize_sub_le_four
#print axioms norm_normalize_sub_le_four
#check @chord
#print axioms chord
#check @normalizedChord
#print axioms normalizedChord
#check @chord_norm_lower
#print axioms chord_norm_lower
#check @normalizedChord_norm
#print axioms normalizedChord_norm
#check @normalizedChord_dist_le
#print axioms normalizedChord_dist_le
#check @contDiffOn_normalizedChord
#print axioms contDiffOn_normalizedChord

-- The explicit short path between nearby states.
#check @shortPath
#print axioms shortPath
#check @shortPath_zero
#print axioms shortPath_zero
#check @shortPath_one
#print axioms shortPath_one
#check @shortPath_self
#print axioms shortPath_self
#check @shortPath_mem
#print axioms shortPath_mem
#check @contDiffOn_shortPath
#print axioms contDiffOn_shortPath
#check @euclidean_shortPath_dist_le
#print axioms euclidean_shortPath_dist_le
#check @lipschitzOn_euclidean_shortPath
#print axioms lipschitzOn_euclidean_shortPath

-- Geometric paths, Euclidean length, and the length infimum.
-- `GeometricPath.mk` shows the stored assumptions: smoothness on
-- `Icc 0 1`, membership in `Xset`, and the exact endpoints.
#check @GeometricPath
#check @GeometricPath.mk
#check @GeometricPath.length
#print axioms GeometricPath.length
#check @GeometricPath.chord_le_length
#print axioms GeometricPath.chord_le_length
#check @shortGeometricPath
#print axioms shortGeometricPath
#check @shortGeometricPath_length_le
#print axioms shortGeometricPath_length_le
#check @geometricEDist
#print axioms geometricEDist
#check @chord_le_geometricEDist
#print axioms chord_le_geometricEDist
#check @geometricEDist_le_length
#print axioms geometricEDist_le_length
#check @geometricEDist_le
#print axioms geometricEDist_le
#check @geometricEDist_self
#print axioms geometricEDist_self

-- Application theorems: print the full declarations so the exact
-- bounds `512 √c(x)` and `16 |θ|` are visible.
#print exists_projection_path
#check @exists_projection_path
#print axioms exists_projection_path
#print exists_CZ_target_path
#check @exists_CZ_target_path
#print axioms exists_CZ_target_path

/-! ## Edge examples -/

/-- The initial state lies in `Xset`. -/
example : x0 ∈ Xset := by
  rw [ControlLie.mem_Xset_iff_normalization]
  funext i
  fin_cases i <;> simp [ControlLie.normalization, ControlLie.normal, x0]

/-- Zero geometric distance at `x0` and the two-sided comparison. -/
example : geometricEDist x0 x0 = 0 :=
  geometricEDist_self (x := x0) (by
    rw [ControlLie.mem_Xset_iff_normalization]
    funext i
    fin_cases i <;> simp [ControlLie.normalization, ControlLie.normal, x0])

example : ENNReal.ofReal ‖x0 - x0‖ ≤ geometricEDist x0 x0 :=
  chord_le_geometricEDist x0 x0

example : geometricEDist x0 x0 ≤ ENNReal.ofReal (16 * ‖x0 - x0‖) :=
  geometricEDist_le (x := x0) (y := x0)
    (by
      rw [ControlLie.mem_Xset_iff_normalization]
      funext i
      fin_cases i <;> simp [ControlLie.normalization, ControlLie.normal, x0])
    (by
      rw [ControlLie.mem_Xset_iff_normalization]
      funext i
      fin_cases i <;> simp [ControlLie.normalization, ControlLie.normal, x0])
    (by simp)

/-- `shortPath x x t = x` for arbitrary `t : ℝ`, not only `t ∈ [0,1]`:
the zero-distance case needs no chord lower bound. -/
example (t : ℝ) : shortPath x0 x0 t = x0 :=
  shortPath_self (x := x0)
    (by
      rw [ControlLie.mem_Xset_iff_normalization]
      funext i
      fin_cases i <;> simp [ControlLie.normalization, ControlLie.normal, x0]) t

/-- The fully excited state `mkState 0 1 0 1` lies in `Xset`; the
short path is the constant path there even with vanishing ground
amplitudes (no amplitude division anywhere). -/
example : mkState 0 1 0 1 ∈ Xset := by
  rw [ControlLie.mem_Xset_iff_normalization]
  funext i
  fin_cases i <;> simp [ControlLie.normalization, ControlLie.normal, mkState]

example (t : ℝ) :
    shortPath (mkState 0 1 0 1) (mkState 0 1 0 1) t = mkState 0 1 0 1 :=
  shortPath_self (x := mkState 0 1 0 1)
    (by
      rw [ControlLie.mem_Xset_iff_normalization]
      funext i
      fin_cases i <;> simp [ControlLie.normalization, ControlLie.normal, mkState]) t

/-- Product-sphere homeomorphism round trips, in both directions. -/
example (x : ↥Xset) :
    stateSphereHomeomorph.symm (stateSphereHomeomorph x) = x :=
  stateSphereHomeomorph.symm_apply_apply x

example (ab : UnitSector × UnitSector) :
    stateSphereHomeomorph (stateSphereHomeomorph.symm ab) = ab :=
  stateSphereHomeomorph.apply_symm_apply ab

end CZExposure.StateGeometry
