/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Hatcher.Sphere.DegreeOrientation

/-!
# Degree of a self-map of a sphere

For a positive-dimensional sphere, the ordered integral orientation identifies
the endomorphism induced on top-dimensional ordinary homology with an
endomorphism of `ℤ`.  Its value at `1` is Hatcher's degree.  The conjugation
order in `degreeEndomorphism` is fixed so that categorical composition of
sphere maps induces the same-order composition of the corresponding integer
endomorphisms.
-/

noncomputable section

open AlgebraicTopology CategoryTheory

namespace Hatcher.Sphere

/-- The endomorphism of `ℤ` obtained by conjugating the map induced on
top-dimensional ordinary integral homology through the ordered sphere
orientation. -/
noncomputable def degreeEndomorphism (n : ℕ) (hn : 0 < n)
    (f : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n) :
    AddCommGrpCat.of ℤ ⟶ AddCommGrpCat.of ℤ :=
  (integralSphereHomologyIso n hn).inv ≫
    ((singularHomologyFunctor AddCommGrpCat n).obj
      (AddCommGrpCat.of ℤ)).map f ≫
    (integralSphereHomologyIso n hn).hom

/-- **Hatcher, degree (printed page 134).** The degree of a self-map of a
positive-dimensional standard sphere is the image of `1` under its oriented
top-dimensional integral-homology endomorphism. -/
noncomputable def degree (n : ℕ) (hn : 0 < n)
    (f : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n) : ℤ :=
  degreeEndomorphism n hn f (1 : ℤ)

/-- The conjugated homology endomorphism is multiplication by the degree. -/
theorem degreeEndomorphism_eq_asHom (n : ℕ) (hn : 0 < n)
    (f : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n) :
    degreeEndomorphism n hn f = AddCommGrpCat.asHom (degree n hn f) := by
  apply AddCommGrpCat.int_hom_ext
  change degree n hn f = (1 : ℤ) • degree n hn f
  simp

/-- **Hatcher, degree characterization (printed page 134).** The induced map
on top-dimensional integral homology sends the ordered fundamental class to
its degree multiple.  This equation fixes the sign convention for all later
degree calculations. -/
theorem integralSphereFundamentalClass_map (n : ℕ) (hn : 0 < n)
    (f : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n) :
    integralSphereFundamentalClass n hn ≫
        ((singularHomologyFunctor AddCommGrpCat n).obj
          (AddCommGrpCat.of ℤ)).map f =
      AddCommGrpCat.asHom (degree n hn f) ≫
        integralSphereFundamentalClass n hn := by
  rw [← cancel_mono (integralSphereHomologyIso n hn).hom]
  simp only [Category.assoc,
    integralSphereFundamentalClass_comp_homologyIso,
    Category.comp_id]
  rw [← integralSphereHomologyIso_inv]
  exact degreeEndomorphism_eq_asHom n hn f

end Hatcher.Sphere
