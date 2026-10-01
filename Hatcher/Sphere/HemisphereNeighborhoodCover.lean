/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Hatcher.MayerVietoris.Neighborhood
import Hatcher.Sphere.HemisphereCharts
import Hatcher.Sphere.RadialDeformationRetract

/-!
# A neighborhood-retract cover by hemispheres

The opposite-pole stereographic charts transport the radial strong deformation
retractions of Euclidean space to Hatcher's literal closed northern and
southern hemispheres.  On the overlap, the punctured-space radial deformation
retract transports to the equator.
-/

noncomputable section

open Metric Set Topology

namespace Hatcher.Sphere

universe u

/-- Transport a strong deformation retract across homeomorphisms when the
square formed by the two inclusions commutes. -/
private def strongDeformationRetractOfHomeomorphSquare
    {A Y B Z : Type u}
    [TopologicalSpace A] [TopologicalSpace Y]
    [TopologicalSpace B] [TopologicalSpace Z]
    (i : C(A, Y)) (j : C(B, Z))
    (hA : A ≃ₜ B) (hY : Y ≃ₜ Z)
    (square : ∀ a, hY (i a) = j (hA a))
    (sdr : Hatcher.StrongDeformationRetract j) :
    Hatcher.StrongDeformationRetract i where
  retract :=
    ⟨fun y ↦ hA.symm (sdr.retract (hY y)),
      hA.symm.continuous.comp (sdr.retract.continuous.comp hY.continuous)⟩
  retract_inclusion := by
    ext a
    apply hA.injective
    change hA (hA.symm (sdr.retract (hY (i a)))) = hA a
    rw [hA.apply_symm_apply, square]
    have hs := congrArg (fun g : C(B, B) ↦ g (hA a))
      sdr.retract_inclusion
    simpa only [ContinuousMap.comp_apply, ContinuousMap.id_apply] using hs
  deformation := {
    toFun := fun p ↦ hY.symm (sdr.deformation (p.1, hY p.2))
    continuous_toFun := hY.symm.continuous.comp
      (sdr.deformation.continuous.comp
        (continuous_fst.prodMk (hY.continuous.comp continuous_snd)))
    map_zero_left := by
      intro y
      change hY.symm (sdr.deformation (0, hY y)) = y
      rw [sdr.deformation.apply_zero]
      exact hY.symm_apply_apply y
    map_one_left := by
      intro y
      change hY.symm (sdr.deformation (1, hY y)) =
        i (hA.symm (sdr.retract (hY y)))
      rw [sdr.deformation.apply_one]
      change hY.symm (j (sdr.retract (hY y))) =
        i (hA.symm (sdr.retract (hY y)))
      apply hY.injective
      rw [hY.apply_symm_apply,
        square (hA.symm (sdr.retract (hY y))), hA.apply_symm_apply]
    prop' := by
      intro t y hy
      rcases hy with ⟨a, rfl⟩
      change hY.symm (sdr.deformation (t, hY (i a))) = i a
      apply hY.injective
      rw [hY.apply_symm_apply, square a]
      exact sdr.deformation.eq_fst t ⟨hA a, rfl⟩ }

private noncomputable def northHemisphereStrongDeformationRetract (n : ℕ) :
    Hatcher.StrongDeformationRetract
      (Hatcher.MayerVietoris.inclusionOfSubset
        ((northHemisphere_subset_interior_northNeighborhood n).trans
          interior_subset)) :=
  strongDeformationRetractOfHomeomorphSquare
    (Hatcher.MayerVietoris.inclusionOfSubset
      ((northHemisphere_subset_interior_northNeighborhood n).trans
        interior_subset))
    (⟨Subtype.val, continuous_subtype_val⟩ :
      C(Metric.closedBall
          (0 : EuclideanSpace ℝ (Fin (n + 1))) 2,
        EuclideanSpace ℝ (Fin (n + 1))))
    (northHemisphereHomeomorph n)
    (northStereographicHomeomorph n)
    (northHemisphere_inclusion_square n)
    (closedBallStrongDeformationRetract 2 (by norm_num))

private noncomputable def southHemisphereStrongDeformationRetract (n : ℕ) :
    Hatcher.StrongDeformationRetract
      (Hatcher.MayerVietoris.inclusionOfSubset
        ((southHemisphere_subset_interior_southNeighborhood n).trans
          interior_subset)) :=
  strongDeformationRetractOfHomeomorphSquare
    (Hatcher.MayerVietoris.inclusionOfSubset
      ((southHemisphere_subset_interior_southNeighborhood n).trans
        interior_subset))
    (⟨Subtype.val, continuous_subtype_val⟩ :
      C(Metric.closedBall
          (0 : EuclideanSpace ℝ (Fin (n + 1))) 2,
        EuclideanSpace ℝ (Fin (n + 1))))
    (southHemisphereHomeomorph n)
    (southStereographicHomeomorph n)
    (southHemisphere_inclusion_square n)
    (closedBallStrongDeformationRetract 2 (by norm_num))

private noncomputable def equatorStrongDeformationRetract (n : ℕ) :
    Hatcher.StrongDeformationRetract
      (Hatcher.MayerVietoris.inclusionOfSubset
        (equator_subset_overlap n)) :=
  strongDeformationRetractOfHomeomorphSquare
    (Hatcher.MayerVietoris.inclusionOfSubset (equator_subset_overlap n))
    (spherePuncturedInclusion
      (E := EuclideanSpace ℝ (Fin (n + 1))) 2 (by norm_num))
    (equatorStereographicHomeomorph n)
    (overlapStereographicHomeomorph n)
    (fun x ↦ by
      apply Subtype.ext
      change
        ((overlapStereographicHomeomorph n)
          ⟨x.1, equator_subset_overlap n x.2⟩).1 =
        (equatorStereographicHomeomorph n x).1
      exact congrArg Subtype.val (equator_inclusion_square n x))
    (spherePuncturedStrongDeformationRetract 2 (by norm_num))

private noncomputable def
    hemisphereIntersectionStrongDeformationRetract (n : ℕ) :
    Hatcher.StrongDeformationRetract
      (Hatcher.MayerVietoris.inclusionOfSubset
        (Hatcher.MayerVietoris.intersectionSubset
          ((northHemisphere_subset_interior_northNeighborhood n).trans
            interior_subset)
          ((southHemisphere_subset_interior_southNeighborhood n).trans
            interior_subset))) := by
  exact strongDeformationRetractOfHomeomorphSquare
    (Hatcher.MayerVietoris.inclusionOfSubset
      (Hatcher.MayerVietoris.intersectionSubset
        ((northHemisphere_subset_interior_northNeighborhood n).trans
          interior_subset)
        ((southHemisphere_subset_interior_southNeighborhood n).trans
          interior_subset)))
    (Hatcher.MayerVietoris.inclusionOfSubset (equator_subset_overlap n))
    (Homeomorph.setCongr (hemisphere_intersection n))
    (Homeomorph.refl _)
    (fun _ ↦ by
      apply Subtype.ext
      rfl)
    (equatorStrongDeformationRetract n)

/-- Hatcher's literal closed north and south hemispheres, equipped with their
opposite-pole neighborhoods and the three compatible strong deformation
retractions required by neighborhood Mayer--Vietoris. -/
noncomputable def hemisphereNeighborhoodCover (n : ℕ) :
    Hatcher.MayerVietoris.NeighborhoodCover
      (northHemisphere n) (southHemisphere n) where
  U := northNeighborhood n
  V := southNeighborhood n
  union_eq_univ := hemisphere_union n
  left_subset_interior :=
    northHemisphere_subset_interior_northNeighborhood n
  right_subset_interior :=
    southHemisphere_subset_interior_southNeighborhood n
  leftRetract := northHemisphereStrongDeformationRetract n
  rightRetract := southHemisphereStrongDeformationRetract n
  intersectionRetract :=
    hemisphereIntersectionStrongDeformationRetract n

private noncomputable def radiusTwoSpherePoint (n : ℕ) :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 2 :=
  ⟨EuclideanSpace.single (0 : Fin (n + 1)) 2, by
    simp⟩

/-- A distinguished point on the equator, obtained from the first coordinate
point of the radius-two stereographic sphere. -/
noncomputable def equatorPoint (n : ℕ) : equator n :=
  (equatorStereographicHomeomorph n).symm (radiusTwoSpherePoint n)

/-- The equator in `TopCat.sphere (n+1)` is nonempty. -/
theorem equatorNonempty (n : ℕ) : Nonempty (equator n) :=
  ⟨equatorPoint n⟩

/-- A point of the literal intersection of the two closed hemispheres. -/
noncomputable def hemisphereIntersectionPoint (n : ℕ) :
    ↑(northHemisphere n ∩ southHemisphere n) :=
  ⟨equatorPoint n, by
    rw [hemisphere_intersection]
    exact (equatorPoint n).2⟩

/-- The intersection of the two closed hemispheres is nonempty, as required
at the terminal end of the reduced Mayer--Vietoris sequence. -/
theorem hemisphereIntersectionNonempty (n : ℕ) :
    Nonempty (↑(northHemisphere n ∩ southHemisphere n)) :=
  ⟨hemisphereIntersectionPoint n⟩

end Hatcher.Sphere
