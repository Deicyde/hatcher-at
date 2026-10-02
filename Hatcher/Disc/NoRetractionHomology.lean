/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Hatcher.Singular.PointedRelative
import Hatcher.Sphere.Homology
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Analysis.Normed.Module.Connected

/-!
# The boundary sphere is not a retract of the disk

Reduced integral homology rules out a retraction from a positive-dimensional
disk onto its boundary sphere.
-/

noncomputable section

open CategoryTheory Limits

namespace Hatcher.Disc

/-- **Hatcher, Corollary 2.15 (pages 114–115).** The boundary sphere of a
positive-dimensional disk is not a retract of the disk. -/
theorem not_exists_diskBoundary_retraction (n : ℕ) :
    ¬ ∃ r : TopCat.disk.{0} (n + 1) ⟶ TopCat.diskBoundary.{0} (n + 1),
        TopCat.diskBoundaryInclusion.{0} (n + 1) ≫ r = 𝟙 _ := by
  rintro ⟨r, hr⟩
  let F : TopCat.{0} ⥤ AddCommGrpCat.{0} :=
    Hatcher.Reduced.homologyFunctor (AddCommGrpCat.of ℤ) n
  have hcomp :
      F.map (TopCat.diskBoundaryInclusion.{0} (n + 1)) ≫ F.map r = 𝟙 _ := by
    rw [← F.map_comp]
    exact (congrArg F.map hr).trans (F.map_id _)
  let _ : ContractibleSpace
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
    Metric.contractibleSpace_closedBall (by positivity)
  let _ : ContractibleSpace
      (ULift.{0} (Metric.closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) :=
    Homeomorph.ulift.contractibleSpace
  have hDisk : IsZero (F.obj (TopCat.disk.{0} (n + 1))) := by
    dsimp only [F]
    exact Hatcher.Reduced.isZero_homology_of_contractible
      (AddCommGrpCat.of ℤ) n
  have hInclusionZero :
      F.map (TopCat.diskBoundaryInclusion.{0} (n + 1)) = 0 :=
    hDisk.eq_of_tgt _ _
  have hBoundaryIdZero :
      𝟙 (F.obj (TopCat.diskBoundary.{0} (n + 1))) = 0 := by
    calc
      𝟙 (F.obj (TopCat.diskBoundary.{0} (n + 1))) =
          F.map (TopCat.diskBoundaryInclusion.{0} (n + 1)) ≫ F.map r := hcomp.symm
      _ = 0 := by rw [hInclusionZero, zero_comp]
  have hBoundary : IsZero (F.obj (TopCat.diskBoundary.{0} (n + 1))) :=
    (IsZero.iff_id_eq_zero _).2 hBoundaryIdZero
  obtain ⟨e⟩ := (Hatcher.Sphere.reducedHomology_sphere_int n).1
  have hInt : IsZero (AddCommGrpCat.of ℤ) := hBoundary.of_iso e.symm
  have hsub : Subsingleton (AddCommGrpCat.of ℤ) :=
    AddCommGrpCat.subsingleton_of_isZero hInt
  exact zero_ne_one (@Subsingleton.elim ℤ hsub 0 1)

end Hatcher.Disc
