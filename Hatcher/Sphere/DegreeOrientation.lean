/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Hatcher.Singular.DoubleSimplexSphere
import Mathlib.Algebra.Category.Grp.Abelian

/-!
# The integral orientation of a positive-dimensional sphere

The ordered first-simplex-minus-second-simplex class supplies a named reduced
integral orientation of the standard sphere.  In positive degree, the natural
comparison between reduced and ordinary homology transports that class to an
ordinary fundamental class and hence fixes the orientation used to define
degree.
-/

noncomputable section

open AlgebraicTopology CategoryTheory

namespace Hatcher.Sphere

/-- The ordinary integral fundamental class of a positive-dimensional sphere,
obtained from the ordered double-simplex class through the natural comparison
from reduced to ordinary homology. -/
noncomputable def integralSphereFundamentalClass (n : ℕ) (hn : 0 < n) :
    AddCommGrpCat.of ℤ ⟶
      (((singularHomologyFunctor AddCommGrpCat n).obj
        (AddCommGrpCat.of ℤ)).obj (TopCat.sphere.{0} n)) :=
  Hatcher.Simplex.doubleSimplexSphereFundamentalClass
      (AddCommGrpCat.of ℤ) n ≫
    ((Hatcher.Reduced.homologyIsoOfPositiveDegree
      (C := AddCommGrpCat.{0}) (AddCommGrpCat.of ℤ) n hn).hom.app
        (TopCat.sphere.{0} n))

/-- The ordered ordinary fundamental class generates the top-dimensional
integral homology of a positive-dimensional sphere. -/
theorem integralSphereFundamentalClass_isIso (n : ℕ) (hn : 0 < n) :
    IsIso (integralSphereFundamentalClass n hn) := by
  dsimp only [integralSphereFundamentalClass]
  exact IsIso.comp_isIso'
    (Hatcher.Simplex.doubleSimplexSphereFundamentalClass_isIso
      (AddCommGrpCat.of ℤ) n)
    (by infer_instance)

/-- **Hatcher, degree orientation (printed page 134).** Ordinary integral
homology in the top degree of a positive-dimensional standard sphere is
oriented by the transported ordered double-simplex class. -/
noncomputable def integralSphereHomologyIso (n : ℕ) (hn : 0 < n) :
    (((singularHomologyFunctor AddCommGrpCat n).obj
      (AddCommGrpCat.of ℤ)).obj (TopCat.sphere.{0} n)) ≅
      AddCommGrpCat.of ℤ :=
  ((Hatcher.Reduced.homologyIsoOfPositiveDegree
      (C := AddCommGrpCat.{0}) (AddCommGrpCat.of ℤ) n hn).app
        (TopCat.sphere.{0} n)).symm ≪≫
    Hatcher.Simplex.sphereHomologyIsoFromDoubleSimplex
      (AddCommGrpCat.of ℤ) n

/-- The inverse of `integralSphereHomologyIso` is exactly the named ordinary
fundamental class, rather than an arbitrary generator. -/
@[simp]
theorem integralSphereHomologyIso_inv (n : ℕ) (hn : 0 < n) :
    (integralSphereHomologyIso n hn).inv =
      integralSphereFundamentalClass n hn := by
  rfl

/-- The named fundamental class and the oriented sphere-homology isomorphism
are inverse morphisms. -/
@[simp]
theorem integralSphereFundamentalClass_comp_homologyIso
    (n : ℕ) (hn : 0 < n) :
    integralSphereFundamentalClass n hn ≫
        (integralSphereHomologyIso n hn).hom =
      𝟙 (AddCommGrpCat.of ℤ) := by
  exact (integralSphereHomologyIso n hn).inv_hom_id

end Hatcher.Sphere
