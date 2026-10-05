/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Hatcher.Singular.PointedRelative
import Hatcher.Sphere.Degree
import Hatcher.Sphere.PuncturedStereographic

/-!
# Degree of a nonsurjective sphere map

A nonsurjective sphere map factors through the complement of a missed point.
That complement is contractible, so its positive-dimensional ordinary homology
vanishes and the induced endomorphism defining degree is zero.
-/

noncomputable section

open AlgebraicTopology CategoryTheory Limits Set ZeroObject

namespace Hatcher.Sphere

/-- **Hatcher, degree property (b), printed page 134.** A nonsurjective
self-map of a positive-dimensional sphere has degree zero. -/
theorem degree_eq_zero_of_not_surjective
    (n : ℕ) (hn : 0 < n)
    (f : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n)
    (hf : ¬Function.Surjective f) :
    degree n hn f = 0 := by
  unfold Function.Surjective at hf
  push Not at hf
  obtain ⟨p, hp⟩ := hf
  let U : Set (TopCat.sphere.{0} n) := {p}ᶜ
  let lift : TopCat.sphere.{0} n ⟶ TopCat.of U :=
    TopCat.ofHom
      { toFun := fun x ↦ ⟨f x, by simpa [U] using hp x⟩
        continuous_toFun := f.hom.continuous.subtype_mk
          (fun x ↦ by simpa [U] using hp x) }
  let inclusion : TopCat.of U ⟶ TopCat.sphere.{0} n :=
    TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  have hfactor : f = lift ≫ inclusion := by
    ext x
    rfl
  let H := (singularHomologyFunctor AddCommGrpCat n).obj
    (AddCommGrpCat.of ℤ)
  let _ : ContractibleSpace U := puncturedSphereContractibleSpace n p
  have hred : IsZero
      ((Hatcher.Reduced.homologyFunctor (AddCommGrpCat.of ℤ) n).obj
        (TopCat.of U)) :=
    Hatcher.Reduced.isZero_homology_of_contractible
      (AddCommGrpCat.of ℤ) n
  have hord : IsZero (H.obj (TopCat.of U)) :=
    hred.of_iso
      ((Hatcher.Reduced.homologyIsoOfPositiveDegree
        (C := AddCommGrpCat.{0}) (AddCommGrpCat.of ℤ) n hn).app
          (TopCat.of U)).symm
  have hlift : H.map lift = 0 := hord.eq_of_tgt _ _
  have hmap : H.map f = 0 := by
    rw [hfactor, Functor.map_comp, hlift, zero_comp]
  simp [degree, degreeEndomorphism, H, hmap]

end Hatcher.Sphere
