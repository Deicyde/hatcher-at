/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Hatcher.Sphere.Degree
import Mathlib.Algebra.Ring.Int.Units
import Mathlib.Topology.Homotopy.Equiv

/-!
# Formal properties of sphere degree

Degree preserves the identity, is multiplicative in the categorical order of
`TopCat`, and is invariant under homotopy.  A sphere self-homotopy-equivalence
therefore has degree a unit of `ℤ`, hence `1` or `-1`.
-/

noncomputable section

open AlgebraicTopology CategoryTheory
open scoped ContinuousMap

namespace Hatcher.Sphere

/-- Conjugating the identity homology map through the sphere orientation gives
the identity endomorphism of `ℤ`. -/
@[simp]
theorem degreeEndomorphism_id (n : ℕ) (hn : 0 < n) :
    degreeEndomorphism n hn (𝟙 (TopCat.sphere.{0} n)) = 𝟙 _ := by
  simp [degreeEndomorphism]

/-- **Hatcher, degree property (a), printed page 134.** The identity map of a
positive-dimensional sphere has degree one. -/
@[simp]
theorem degree_id (n : ℕ) (hn : 0 < n) :
    degree n hn (𝟙 (TopCat.sphere.{0} n)) = 1 := by
  change degreeEndomorphism n hn (𝟙 (TopCat.sphere.{0} n)) (1 : ℤ) = 1
  rw [degreeEndomorphism_id]
  rfl

/-- The endomorphism associated to `f ≫ g` is the same-order composite of
the endomorphisms associated to `f` and `g`. -/
theorem degreeEndomorphism_comp (n : ℕ) (hn : 0 < n)
    (f g : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n) :
    degreeEndomorphism n hn (f ≫ g) =
      degreeEndomorphism n hn f ≫ degreeEndomorphism n hn g := by
  dsimp only [degreeEndomorphism]
  rw [Functor.map_comp]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

/-- **Hatcher, degree property (d), printed page 134.** Degree is
multiplicative in the categorical composition order used by `TopCat`. -/
theorem degree_comp (n : ℕ) (hn : 0 < n)
    (f g : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n) :
    degree n hn (f ≫ g) = degree n hn f * degree n hn g := by
  calc
    degree n hn (f ≫ g) =
        (degreeEndomorphism n hn (f ≫ g)) (1 : ℤ) := rfl
    _ = (degreeEndomorphism n hn f ≫
          degreeEndomorphism n hn g) (1 : ℤ) := by
      rw [degreeEndomorphism_comp]
    _ = degree n hn f * degree n hn g := by
      rw [ConcreteCategory.comp_apply,
        degreeEndomorphism_eq_asHom,
        degreeEndomorphism_eq_asHom,
        AddCommGrpCat.asHom_hom_apply,
        AddCommGrpCat.asHom_hom_apply]
      simp

/-- Homotopic sphere self-maps have the same conjugated endomorphism of `ℤ`. -/
theorem degreeEndomorphism_eq_of_homotopy (n : ℕ) (hn : 0 < n)
    {f g : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n}
    (H : TopCat.Homotopy f g) :
    degreeEndomorphism n hn f = degreeEndomorphism n hn g := by
  have hmap :=
    TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor
      H (AddCommGrpCat.of ℤ) n
  change
    ((singularHomologyFunctor AddCommGrpCat n).obj
        (AddCommGrpCat.of ℤ)).map f =
      ((singularHomologyFunctor AddCommGrpCat n).obj
        (AddCommGrpCat.of ℤ)).map g at hmap
  simp [degreeEndomorphism, hmap]

/-- **Hatcher, degree property (c), printed page 134.** Homotopic sphere maps
have equal degree. -/
theorem degree_eq_of_homotopy (n : ℕ) (hn : 0 < n)
    {f g : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n}
    (H : TopCat.Homotopy f g) :
    degree n hn f = degree n hn g := by
  change degreeEndomorphism n hn f (1 : ℤ) =
    degreeEndomorphism n hn g (1 : ℤ)
  rw [degreeEndomorphism_eq_of_homotopy n hn H]

/-- The degrees of the forward and inverse maps of a sphere
self-homotopy-equivalence multiply to one. -/
theorem degree_mul_degree_invFun_of_homotopyEquiv
    (n : ℕ) (hn : 0 < n)
    (e : ((TopCat.sphere.{0} n : TopCat.{0}) : Type) ≃ₕ
      ((TopCat.sphere.{0} n : TopCat.{0}) : Type)) :
    degree n hn (TopCat.ofHom e.toFun) *
        degree n hn (TopCat.ofHom e.invFun) =
      1 := by
  let f := TopCat.ofHom e.toFun
  let g := TopCat.ofHom e.invFun
  have H : TopCat.Homotopy (f ≫ g) (𝟙 _) := by
    change (e.invFun.comp e.toFun).Homotopy (ContinuousMap.id _)
    exact e.left_inv.some
  calc
    degree n hn f * degree n hn g = degree n hn (f ≫ g) :=
      (degree_comp n hn f g).symm
    _ = degree n hn (𝟙 _) := degree_eq_of_homotopy n hn H
    _ = 1 := degree_id n hn

/-- The degree of the forward map of a sphere self-homotopy-equivalence is a
unit of `ℤ`. -/
theorem isUnit_degree_of_homotopyEquiv
    (n : ℕ) (hn : 0 < n)
    (e : ((TopCat.sphere.{0} n : TopCat.{0}) : Type) ≃ₕ
      ((TopCat.sphere.{0} n : TopCat.{0}) : Type)) :
    IsUnit (degree n hn (TopCat.ofHom e.toFun)) :=
  IsUnit.of_mul_eq_one
    (degree n hn (TopCat.ofHom e.invFun))
    (degree_mul_degree_invFun_of_homotopyEquiv n hn e)

/-- The degree of a sphere homeomorphism is a unit of `ℤ`. -/
theorem isUnit_degree_of_homeomorph
    (n : ℕ) (hn : 0 < n)
    (e : ((TopCat.sphere.{0} n : TopCat.{0}) : Type) ≃ₜ
      ((TopCat.sphere.{0} n : TopCat.{0}) : Type)) :
    IsUnit (degree n hn (TopCat.isoOfHomeo e).hom) := by
  exact isUnit_degree_of_homotopyEquiv n hn e.toHomotopyEquiv

/-- **Hatcher, degree property (d), printed page 134.** The forward map of a
sphere self-homotopy-equivalence has degree `1` or `-1`. -/
theorem degree_eq_one_or_neg_one_of_homotopyEquiv
    (n : ℕ) (hn : 0 < n)
    (e : ((TopCat.sphere.{0} n : TopCat.{0}) : Type) ≃ₕ
      ((TopCat.sphere.{0} n : TopCat.{0}) : Type)) :
    degree n hn (TopCat.ofHom e.toFun) = 1 ∨
      degree n hn (TopCat.ofHom e.toFun) = -1 := by
  obtain ⟨u, hu⟩ := isUnit_degree_of_homotopyEquiv n hn e
  obtain rfl | rfl := Int.units_eq_one_or u
  · left
    simpa using hu.symm
  · right
    simpa using hu.symm

/-- In particular, a sphere homeomorphism has degree `1` or `-1`. -/
theorem degree_eq_one_or_neg_one_of_homeomorph
    (n : ℕ) (hn : 0 < n)
    (e : ((TopCat.sphere.{0} n : TopCat.{0}) : Type) ≃ₜ
      ((TopCat.sphere.{0} n : TopCat.{0}) : Type)) :
    degree n hn (TopCat.isoOfHomeo e).hom = 1 ∨
      degree n hn (TopCat.isoOfHomeo e).hom = -1 := by
  change degree n hn (TopCat.ofHom e.toHomotopyEquiv.toFun) = 1 ∨
    degree n hn (TopCat.ofHom e.toHomotopyEquiv.toFun) = -1
  exact degree_eq_one_or_neg_one_of_homotopyEquiv
    n hn e.toHomotopyEquiv

end Hatcher.Sphere
