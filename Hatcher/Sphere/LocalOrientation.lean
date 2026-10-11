/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Hatcher.Singular.ContractibleSubspaceRelative
import Hatcher.Singular.LocalHomology
import Hatcher.Sphere.DegreeOrientation
import Hatcher.Sphere.PuncturedStereographic

/-!
# Integral orientations of local homology on a sphere

The ordered reduced fundamental class of a positive-dimensional sphere
projects to a canonical generator of its local homology at every point.  The
same generator is transported to each open neighborhood through the local
excision isomorphism, compatibly with restriction to smaller neighborhoods.
-/

noncomputable section

open AlgebraicTopology CategoryTheory Set Topology

namespace Hatcher.Sphere

private theorem sphereT1Space (n : ℕ) :
    T1Space (TopCat.sphere.{0} n) :=
  (sphereULiftHomeomorph n).symm.t1Space

/-- The ordered integral local fundamental class at a point of a
positive-dimensional sphere. -/
noncomputable def integralSphereLocalFundamentalClass
    (n : ℕ) (_hn : 0 < n) (y : TopCat.sphere.{0} n) :
    AddCommGrpCat.of ℤ ⟶
      (Hatcher.Relative.homologyFunctor (AddCommGrpCat.of ℤ) n).obj
        (Hatcher.Relative.puncturedPair (TopCat.sphere.{0} n) y) :=
  Hatcher.Simplex.doubleSimplexSphereFundamentalClass
      (AddCommGrpCat.of ℤ) n ≫
    Hatcher.Relative.reducedPairProjection
      (Hatcher.Relative.puncturedPair (TopCat.sphere.{0} n) y)
      (AddCommGrpCat.of ℤ) n

/-- The ordered local fundamental class generates integral local homology of
the sphere. -/
theorem integralSphereLocalFundamentalClass_isIso
    (n : ℕ) (hn : 0 < n) (y : TopCat.sphere.{0} n) :
    IsIso (integralSphereLocalFundamentalClass n hn y) := by
  let _ : ContractibleSpace
      (Hatcher.Relative.puncturedPair (TopCat.sphere.{0} n) y).snd := by
    change ContractibleSpace ({y}ᶜ : Set (TopCat.sphere.{0} n))
    exact puncturedSphereContractibleSpace n y
  dsimp only [integralSphereLocalFundamentalClass]
  exact IsIso.comp_isIso'
    (Hatcher.Simplex.doubleSimplexSphereFundamentalClass_isIso
      (AddCommGrpCat.of ℤ) n)
    (Hatcher.Relative.reducedPairProjection_isIso_of_contractibleSubspace
      (Hatcher.Relative.puncturedPair (TopCat.sphere.{0} n) y)
      (AddCommGrpCat.of ℤ) n)

/-- Integral local homology of an oriented positive-dimensional sphere is
canonically identified with `ℤ`. -/
noncomputable def integralSphereLocalHomologyIso
    (n : ℕ) (hn : 0 < n) (y : TopCat.sphere.{0} n) :
    (Hatcher.Relative.homologyFunctor (AddCommGrpCat.of ℤ) n).obj
        (Hatcher.Relative.puncturedPair (TopCat.sphere.{0} n) y) ≅
      AddCommGrpCat.of ℤ := by
  let _ : IsIso (integralSphereLocalFundamentalClass n hn y) :=
    integralSphereLocalFundamentalClass_isIso n hn y
  exact (asIso (integralSphereLocalFundamentalClass n hn y)).symm

/-- The inverse of the oriented local-homology isomorphism is exactly the
ordered local fundamental class. -/
@[simp]
theorem integralSphereLocalHomologyIso_inv
    (n : ℕ) (hn : 0 < n) (y : TopCat.sphere.{0} n) :
    (integralSphereLocalHomologyIso n hn y).inv =
      integralSphereLocalFundamentalClass n hn y := by
  rfl

/-- The ordered local fundamental class and the oriented local-homology
isomorphism are inverse morphisms. -/
@[simp]
theorem integralSphereLocalFundamentalClass_comp_homologyIso
    (n : ℕ) (hn : 0 < n) (y : TopCat.sphere.{0} n) :
    integralSphereLocalFundamentalClass n hn y ≫
        (integralSphereLocalHomologyIso n hn y).hom =
      𝟙 (AddCommGrpCat.of ℤ) := by
  exact (integralSphereLocalHomologyIso n hn y).inv_hom_id

set_option backward.isDefEq.respectTransparency false in
/-- The local orientation has exactly the sign fixed by the ordinary ordered
sphere class and the positive-degree comparison from reduced to ordinary
homology. -/
theorem integralSphereFundamentalClass_to_local
    (n : ℕ) (hn : 0 < n) (y : TopCat.sphere.{0} n) :
    integralSphereFundamentalClass n hn ≫
        (Hatcher.Reduced.homologyIsoOfPositiveDegree
          (C := AddCommGrpCat.{0}) (AddCommGrpCat.of ℤ) n hn).inv.app
            (TopCat.sphere.{0} n) ≫
        Hatcher.Relative.reducedPairProjection
          (Hatcher.Relative.puncturedPair (TopCat.sphere.{0} n) y)
          (AddCommGrpCat.of ℤ) n =
      integralSphereLocalFundamentalClass n hn y := by
  simp [integralSphereFundamentalClass,
    integralSphereLocalFundamentalClass, Category.assoc]

/-- The ordered local fundamental class transported to an open neighborhood
of its distinguished point. -/
noncomputable def integralSphereNeighborhoodFundamentalClass
    (n : ℕ) (hn : 0 < n) (x : TopCat.sphere.{0} n)
    (U : Set (TopCat.sphere.{0} n)) (hx : x ∈ U) (hU : IsOpen U) :
    AddCommGrpCat.of ℤ ⟶
      (Hatcher.Relative.homologyFunctor (AddCommGrpCat.of ℤ) n).obj
        (Hatcher.Relative.puncturedPair (TopCat.of U) ⟨x, hx⟩) := by
  let _ : T1Space (TopCat.sphere.{0} n) := sphereT1Space n
  let _ : IsIso (Hatcher.Relative.localHomologyOpenNeighborhoodMap
      x U hx (AddCommGrpCat.of ℤ) n) :=
    Hatcher.Relative.localHomologyOpenNeighborhoodMap_isIso_of_t1
      x U hx hU (AddCommGrpCat.of ℤ) n
  exact integralSphereLocalFundamentalClass n hn x ≫
    inv (Hatcher.Relative.localHomologyOpenNeighborhoodMap
      x U hx (AddCommGrpCat.of ℤ) n)

/-- Transporting the neighborhood fundamental class to ambient local homology
recovers the global local fundamental class. -/
@[reassoc]
theorem integralSphereNeighborhoodFundamentalClass_map
    (n : ℕ) (hn : 0 < n) (x : TopCat.sphere.{0} n)
    (U : Set (TopCat.sphere.{0} n)) (hx : x ∈ U) (hU : IsOpen U) :
    integralSphereNeighborhoodFundamentalClass n hn x U hx hU ≫
        Hatcher.Relative.localHomologyOpenNeighborhoodMap
          x U hx (AddCommGrpCat.of ℤ) n =
      integralSphereLocalFundamentalClass n hn x := by
  let _ : T1Space (TopCat.sphere.{0} n) := sphereT1Space n
  let _ : IsIso (Hatcher.Relative.localHomologyOpenNeighborhoodMap
      x U hx (AddCommGrpCat.of ℤ) n) :=
    Hatcher.Relative.localHomologyOpenNeighborhoodMap_isIso_of_t1
      x U hx hU (AddCommGrpCat.of ℤ) n
  simp [integralSphereNeighborhoodFundamentalClass, Category.assoc]

/-- The transported fundamental class generates the local homology of every
open neighborhood of its distinguished point. -/
theorem integralSphereNeighborhoodFundamentalClass_isIso
    (n : ℕ) (hn : 0 < n) (x : TopCat.sphere.{0} n)
    (U : Set (TopCat.sphere.{0} n)) (hx : x ∈ U) (hU : IsOpen U) :
    IsIso (integralSphereNeighborhoodFundamentalClass n hn x U hx hU) := by
  let _ : T1Space (TopCat.sphere.{0} n) := sphereT1Space n
  let _ : IsIso (Hatcher.Relative.localHomologyOpenNeighborhoodMap
      x U hx (AddCommGrpCat.of ℤ) n) :=
    Hatcher.Relative.localHomologyOpenNeighborhoodMap_isIso_of_t1
      x U hx hU (AddCommGrpCat.of ℤ) n
  let _ : IsIso (integralSphereLocalFundamentalClass n hn x) :=
    integralSphereLocalFundamentalClass_isIso n hn x
  exact IsIso.of_isIso_fac_right
    (integralSphereNeighborhoodFundamentalClass_map n hn x U hx hU)

/-- The oriented neighborhood fundamental classes are natural under
restriction from a smaller open neighborhood `V` to a larger one `U`. -/
@[reassoc]
theorem integralSphereNeighborhoodFundamentalClass_restrict
    (n : ℕ) (hn : 0 < n) (x : TopCat.sphere.{0} n)
    (V U : Set (TopCat.sphere.{0} n)) (hxV : x ∈ V) (hxU : x ∈ U)
    (hV : IsOpen V) (hU : IsOpen U) (hVU : V ⊆ U) :
    integralSphereNeighborhoodFundamentalClass n hn x V hxV hV ≫
        Hatcher.Relative.localHomologyOpenNeighborhoodRestrictionMap
          x V U hxV hxU hVU (AddCommGrpCat.of ℤ) n =
      integralSphereNeighborhoodFundamentalClass n hn x U hxU hU := by
  let _ : T1Space (TopCat.sphere.{0} n) := sphereT1Space n
  let _ : IsIso (Hatcher.Relative.localHomologyOpenNeighborhoodMap
      x U hxU (AddCommGrpCat.of ℤ) n) :=
    Hatcher.Relative.localHomologyOpenNeighborhoodMap_isIso_of_t1
      x U hxU hU (AddCommGrpCat.of ℤ) n
  rw [← cancel_mono (Hatcher.Relative.localHomologyOpenNeighborhoodMap
    x U hxU (AddCommGrpCat.of ℤ) n)]
  simp only [Category.assoc]
  rw [Hatcher.Relative.localHomologyOpenNeighborhoodRestrictionMap_comp,
    integralSphereNeighborhoodFundamentalClass_map,
    integralSphereNeighborhoodFundamentalClass_map]

end Hatcher.Sphere
