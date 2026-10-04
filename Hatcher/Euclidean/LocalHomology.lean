/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Hatcher.Singular.ContractibleAmbientRelative
import Hatcher.Singular.LocalHomology
import Hatcher.Sphere.HemisphereCharts
import Hatcher.Sphere.Homology
import Hatcher.Sphere.RadialDeformationRetract
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Analysis.Convex.Contractible

/-!
# Local homology of positive-dimensional Euclidean space

The local relative homology of Euclidean `(d+1)`-space is the coefficient
object in degree `d+1` and vanishes in every other degree.
-/

noncomputable section

open CategoryTheory Limits Set
open scoped EuclideanSpace

namespace Hatcher.Euclidean

universe v u

private abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin (d + 1))

/-- The local pair of Euclidean `(d+1)`-space at `x`. -/
abbrev localPair (d : ℕ) (x : E d) : TopPair.{0} :=
  Hatcher.Relative.puncturedPair (TopCat.of (E d)) x

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{0} C]

private noncomputable def puncturedReducedHomologyIsoSphere
    (R : C) (d i : ℕ) :
    (Hatcher.Reduced.homologyFunctor R i).obj (localPair d 0).snd ≅
      (Hatcher.Reduced.homologyFunctor R i).obj (TopCat.sphere.{0} d) :=
  Hatcher.Reduced.homologyIsoOfHomotopyEquiv
      (Hatcher.Sphere.spherePuncturedStrongDeformationRetract
        (E := E d) 1 zero_lt_one).toHomotopyEquiv R i ≪≫
    Hatcher.Reduced.homologyIsoOfHomotopyEquiv
      (Hatcher.Sphere.sphereULiftHomeomorph d).symm.toHomotopyEquiv R i

private def puncturedZeroPoint (d : ℕ) : (localPair d 0).snd :=
  ⟨EuclideanSpace.single 0 1, by
    simp⟩

private theorem localHomology_zero_center (R : C) (d : ℕ) :
    Nonempty ((Hatcher.Relative.homologyFunctor R (d + 1)).obj
      (localPair d 0) ≅ R) ∧
      ∀ i, i ≠ d + 1 →
        IsZero ((Hatcher.Relative.homologyFunctor R i).obj
          (localPair d 0)) := by
  let _ : ContractibleSpace (localPair d 0).fst :=
    (inferInstance : ContractibleSpace (E d))
  have hSphere := Hatcher.Sphere.reducedHomology_sphere R d
  constructor
  · obtain ⟨eSphere⟩ := hSphere.1
    exact ⟨Hatcher.Relative.contractibleAmbientRelativeHomologyIso
        (localPair d 0) R (d + 1) d rfl ≪≫
      puncturedReducedHomologyIsoSphere R d d ≪≫ eSphere⟩
  · intro i hi
    cases i with
    | zero =>
        exact Hatcher.Relative.isZero_relativeHomology_zero_of_contractibleAmbient
          (localPair d 0) R (puncturedZeroPoint d)
    | succ k =>
        have hk : k ≠ d := by
          intro h
          apply hi
          simp [h]
        have hPunctured : IsZero
            ((Hatcher.Reduced.homologyFunctor R k).obj (localPair d 0).snd) :=
          (hSphere.2 k hk).of_iso
            (puncturedReducedHomologyIsoSphere R d k)
        exact hPunctured.of_iso
          (Hatcher.Relative.contractibleAmbientRelativeHomologyIso
            (localPair d 0) R (k + 1) k rfl)

private noncomputable def translateToZero (d : ℕ) (x : E d) : E d ≃ₜ E d :=
  Homeomorph.addRight (-x)

@[simp]
private theorem translateToZero_self (d : ℕ) (x : E d) :
    translateToZero d x x = 0 := by
  simp [translateToZero]

private noncomputable def localPairIsoZero (d : ℕ) (x : E d) :
    localPair d x ≅ localPair d 0 :=
  Hatcher.Relative.puncturedPairIso (translateToZero d x)
    (translateToZero_self d x)

/-- **Hatcher, proof of Theorem 2.26 (page 126).** Local homology of
positive-dimensional Euclidean space is the coefficient object in the ambient
dimension and vanishes in every other degree. -/
theorem localHomology (R : C) (d : ℕ) (x : E d) :
    Nonempty ((Hatcher.Relative.homologyFunctor R (d + 1)).obj
      (localPair d x) ≅ R) ∧
      ∀ i, i ≠ d + 1 →
        IsZero ((Hatcher.Relative.homologyFunctor R i).obj
          (localPair d x)) := by
  have hzero := localHomology_zero_center R d
  constructor
  · obtain ⟨eZero⟩ := hzero.1
    exact ⟨(Hatcher.Relative.homologyFunctor R (d + 1)).mapIso
        (localPairIsoZero d x) ≪≫ eZero⟩
  · intro i hi
    exact (hzero.2 i hi).of_iso
      ((Hatcher.Relative.homologyFunctor R i).mapIso (localPairIsoZero d x))

/-- Integral specialization of Euclidean local homology. -/
theorem localHomology_int (d : ℕ) (x : E d) :
    Nonempty ((Hatcher.Relative.homologyFunctor
      (AddCommGrpCat.of ℤ) (d + 1)).obj (localPair d x) ≅
        AddCommGrpCat.of ℤ) ∧
      ∀ i, i ≠ d + 1 →
        IsZero ((Hatcher.Relative.homologyFunctor
          (AddCommGrpCat.of ℤ) i).obj (localPair d x)) :=
  localHomology (C := AddCommGrpCat.{0}) (AddCommGrpCat.of ℤ) d x

end Hatcher.Euclidean
