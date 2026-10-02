/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Hatcher.MayerVietoris.ReducedNeighborhood
import Hatcher.Singular.PointedRelative
import Hatcher.Sphere.HemisphereNeighborhoodCover
import Mathlib.Analysis.Normed.Module.Connected

/-!
# The reduced-homology recurrence for spheres

The reduced Mayer--Vietoris sequence of the two closed hemispheres identifies
the reduced homology of a positive-dimensional sphere with the reduced
homology of its equator in the preceding degree.  The terminal part of the
same sequence gives vanishing in degree zero.
-/

noncomputable section

open CategoryTheory Limits ZeroObject

namespace Hatcher.Sphere

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C]
  [HasCoproducts.{w} C]

local instance : HasFiniteCoproducts C :=
  hasFiniteCoproducts_of_hasCoproducts C

local instance : HasBinaryBiproducts C :=
  HasBinaryBiproducts.of_hasBinaryCoproducts

/-- The literal intersection of the two closed hemispheres is the preceding
sphere. -/
private noncomputable def hemisphereIntersectionSphereHomeomorph (n : ℕ) :
    ↥(northHemisphere.{w} n ∩ southHemisphere.{w} n) ≃ₜ
      ((TopCat.sphere.{w} n : TopCat.{w}) : Type w) :=
  (Homeomorph.setCongr (hemisphere_intersection.{w} n)).trans
    (equatorSphereHomeomorph.{w} n)

/-- **Hatcher, Example 2.46 (page 150).** Reduced homology of spheres obeys
the suspension recurrence, and reduced zeroth homology vanishes in every
positive sphere dimension. -/
theorem reducedHomology_sphereSucc (R : C) (n : ℕ) :
    (∀ i, Nonempty
      ((Hatcher.Reduced.homologyFunctor.{w} R (i + 1)).obj
          (TopCat.sphere.{w} (n + 1)) ≅
        (Hatcher.Reduced.homologyFunctor.{w} R i).obj
          (TopCat.sphere.{w} n))) ∧
      IsZero ((Hatcher.Reduced.homologyFunctor.{w} R 0).obj
        (TopCat.sphere.{w} (n + 1))) := by
  let : ContractibleSpace
      (Metric.closedBall
        (0 : EuclideanSpace ℝ (Fin (n + 1))) 2) :=
    Metric.contractibleSpace_closedBall (by norm_num)
  let : ContractibleSpace (northHemisphere.{w} n) :=
    (northHemisphereHomeomorph.{w} n).contractibleSpace
  let : ContractibleSpace (southHemisphere.{w} n) :=
    (southHemisphereHomeomorph.{w} n).contractibleSpace
  let h := hemisphereNeighborhoodCover.{w} n
  have hMiddle (j : ℕ) :
      IsZero
        ((Hatcher.Reduced.homologyFunctor.{w} R j).obj
              (TopCat.of (northHemisphere.{w} n)) ⊞
          (Hatcher.Reduced.homologyFunctor.{w} R j).obj
              (TopCat.of (southHemisphere.{w} n))) :=
    (biprod_isZero_iff _ _).2
      ⟨Hatcher.Reduced.isZero_homology_of_contractible R j,
        Hatcher.Reduced.isZero_homology_of_contractible R j⟩
  have hLong :=
    Hatcher.MayerVietoris.reducedNeighborhoodLongExact h R
      (hemisphereIntersectionNonempty.{w} n)
  constructor
  · intro i
    let S :=
      Hatcher.MayerVietoris.reducedNeighborhoodSequence h R
        (i + 1) i rfl
    have hS : S.Exact := hLong.1 (i + 1) i rfl
    let δ := S.map' 2 3
    have : Mono δ :=
      (hS.exact 1).mono_g ((hMiddle (i + 1)).eq_of_src _ _)
    have : Epi δ :=
      (hS.exact 2).epi_f ((hMiddle i).eq_of_tgt _ _)
    have hδ : IsIso δ := isIso_of_mono_of_epi δ
    exact ⟨(@asIso _ _ _ _ δ hδ) ≪≫
      Hatcher.Reduced.homologyIsoOfHomotopyEquiv
        (hemisphereIntersectionSphereHomeomorph.{w} n).toHomotopyEquiv R i⟩
  · let S₀ :=
      Hatcher.MayerVietoris.reducedNeighborhoodZeroSequence h R
    have hS₀ : S₀.Exact := hLong.2
    have hz : IsZero (S₀.obj' 2) :=
      (hS₀.exact 1).isZero_X₂
        ((hMiddle 0).eq_of_src _ _)
        ((isZero_zero C).eq_of_tgt _ _)
    exact hz

end Hatcher.Sphere
