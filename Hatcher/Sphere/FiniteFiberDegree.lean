/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Hatcher.Sphere.Degree
import Hatcher.Sphere.FiniteFiberNeighborhoods
import Hatcher.Sphere.LocalOrientation

/-!
# The global degree on the finite-fiber relative pair

The ordered reduced sphere class projects to the relative pair obtained by
deleting a fiber.  Naturality of this projection identifies its image under the
fiber pair map with the global-degree multiple of the ordered target local
class.  Neither construction requires the fiber itself to be finite.
-/

noncomputable section

open AlgebraicTopology CategoryTheory Set

namespace Hatcher.Sphere

/-- The ordered sphere class projected to the relative pair obtained by
deleting the fiber of `f` over `y`. -/
noncomputable def finitePunctureFundamentalClass
    (n : ℕ) (f : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n)
    (y : TopCat.sphere.{0} n) :
    AddCommGrpCat.of ℤ ⟶
      (Hatcher.Relative.homologyFunctor (AddCommGrpCat.of ℤ) n).obj
        (TopPair.ofSubset
          ((fiber f y)ᶜ : Set (TopCat.sphere.{0} n))) :=
  Hatcher.Simplex.doubleSimplexSphereFundamentalClass
      (AddCommGrpCat.of ℤ) n ≫
    Hatcher.Relative.reducedPairProjection
      (TopPair.ofSubset ((fiber f y)ᶜ : Set (TopCat.sphere.{0} n)))
      (AddCommGrpCat.of ℤ) n

private theorem orderedReducedSphereFundamentalClass_map
    (n : ℕ) (hn : 0 < n)
    (f : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n) :
    Hatcher.Simplex.doubleSimplexSphereFundamentalClass
          (AddCommGrpCat.of ℤ) n ≫
        (Hatcher.Reduced.homologyFunctor
          (AddCommGrpCat.of ℤ) n).map f =
      AddCommGrpCat.asHom (degree n hn f) ≫
        Hatcher.Simplex.doubleSimplexSphereFundamentalClass
          (AddCommGrpCat.of ℤ) n := by
  let e := Hatcher.Reduced.homologyIsoOfPositiveDegree
    (C := AddCommGrpCat.{0}) (AddCommGrpCat.of ℤ) n hn
  have hnat := e.hom.naturality f
  rw [← cancel_mono (e.hom.app (TopCat.sphere.{0} n))]
  rw [Category.assoc, hnat]
  change integralSphereFundamentalClass n hn ≫
      ((singularHomologyFunctor AddCommGrpCat n).obj
        (AddCommGrpCat.of ℤ)).map f =
    AddCommGrpCat.asHom (degree n hn f) ≫
      integralSphereFundamentalClass n hn
  exact integralSphereFundamentalClass_map n hn f

set_option backward.isDefEq.respectTransparency false in
/-- **Hatcher, lower square in Proposition 2.30 (printed page 136).** The
finite-fiber pair map sends the projected ordered sphere class to the exact
global-degree multiple of the ordered target local class. -/
@[reassoc]
theorem finiteFiberFundamentalClass_map
    (n : ℕ) (hn : 0 < n)
    (f : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n)
    (y : TopCat.sphere.{0} n) :
    finitePunctureFundamentalClass n f y ≫
        (Hatcher.Relative.homologyFunctor
          (AddCommGrpCat.of ℤ) n).map (finiteFiberPairMap f y) =
      AddCommGrpCat.asHom (degree n hn f) ≫
        integralSphereLocalFundamentalClass n hn y := by
  dsimp only [finitePunctureFundamentalClass,
    integralSphereLocalFundamentalClass]
  rw [Category.assoc,
    Hatcher.Relative.reducedPairProjection_naturality,
    finiteFiberPairMap_fst]
  rw [← Category.assoc,
    orderedReducedSphereFundamentalClass_map n hn f,
    Category.assoc]

end Hatcher.Sphere
