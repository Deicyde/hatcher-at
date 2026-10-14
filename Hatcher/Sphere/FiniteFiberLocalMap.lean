/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Hatcher.Sphere.FinitePunctureExcision
import Hatcher.Sphere.LocalDegree

/-!
# Local degrees in a finite fiber

The map from a chosen punctured fiber neighborhood through the sphere with the
whole fiber deleted to the target punctured sphere is exactly the local pair
map.  Consequently, the corresponding composite on relative integral homology
sends the ordered local class by multiplication with the public local degree.
-/

noncomputable section

open AlgebraicTopology CategoryTheory

namespace Hatcher.Sphere

/-- The inclusion of one chosen punctured fiber neighborhood followed by the
finite-fiber pair map is the local pair map of that neighborhood. -/
@[reassoc]
theorem finitePuncturePairHomComponent_comp_finiteFiberPairMap {n : ℕ}
    {f : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n}
    {y : TopCat.sphere.{0} n} (D : FiniteFiberNeighborhoods f y)
    (i : fiber f y) :
    finitePunctureNeighborhoodPairHom D i ≫ finiteFiberPairMap f y =
      (D.neighborhood i).pairHom := by
  apply MorphismProperty.Arrow.Hom.ext
  · ext z
    rfl
  · ext z
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- **Hatcher, upper square in Proposition 2.30 (printed page 136).** The
finite-fiber pair map sends the ordered class from each chosen local summand to
the exact public-local-degree multiple of the target local class. -/
@[reassoc]
theorem finiteFiberPairMap_localClass
    (n : ℕ) (hn : 0 < n)
    (f : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n)
    (y : TopCat.sphere.{0} n) (D : FiniteFiberNeighborhoods f y)
    (i : fiber f y) :
    integralSphereNeighborhoodFundamentalClass
          n hn i.1 (D.U i) (D.center_mem i) (D.isOpen_U i) ≫
        (Hatcher.Relative.homologyFunctor
          (AddCommGrpCat.of ℤ) n).map
            (finitePunctureNeighborhoodPairHom D i) ≫
        (Hatcher.Relative.homologyFunctor
          (AddCommGrpCat.of ℤ) n).map (finiteFiberPairMap f y) =
      AddCommGrpCat.asHom
          (localDegree n hn f i.1 y
            (D.neighborhood i).isolatedPreimage) ≫
        integralSphereLocalFundamentalClass n hn y := by
  rw [← Functor.map_comp,
    finitePuncturePairHomComponent_comp_finiteFiberPairMap]
  exact localFundamentalClass_map_eq_localDegree
    n hn f i.1 y (D.neighborhood i).isolatedPreimage (D.neighborhood i)

end Hatcher.Sphere
