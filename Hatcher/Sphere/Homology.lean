/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Hatcher.Sphere.HomologyRecurrence
import Hatcher.Sphere.ZeroSphereHomology
import Mathlib.Algebra.Category.Grp.Abelian

/-!
# Reduced homology of spheres

The direct calculation for the zero-sphere and the suspension recurrence
compute reduced singular homology in every sphere dimension.
-/

noncomputable section

open CategoryTheory Limits

namespace Hatcher.Sphere

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C]
  [HasCoproducts.{w} C]

/-- **Hatcher, Corollary 2.14 (page 114).** Reduced homology of the
`n`-sphere is the coefficient object in degree `n` and vanishes in every
other degree.  The diagonal isomorphism is returned under `Nonempty` rather
than choosing an orientation. -/
theorem reducedHomology_sphere (R : C) (n : ℕ) :
    Nonempty
        ((Hatcher.Reduced.homologyFunctor.{w} R n).obj
          (TopCat.sphere.{w} n) ≅ R) ∧
      ∀ i, i ≠ n →
        IsZero ((Hatcher.Reduced.homologyFunctor.{w} R i).obj
          (TopCat.sphere.{w} n)) := by
  induction n with
  | zero =>
      exact reducedHomology_sphere_zero R
  | succ n ih =>
      have hSucc := reducedHomology_sphereSucc R n
      constructor
      · obtain ⟨eSucc⟩ := hSucc.1 n
        obtain ⟨eDiag⟩ := ih.1
        exact ⟨eSucc ≪≫ eDiag⟩
      · intro i hi
        cases i with
        | zero =>
            exact hSucc.2
        | succ i =>
            have hi' : i ≠ n := by
              intro h
              apply hi
              rw [h]
            obtain ⟨eSucc⟩ := hSucc.1 i
            exact (ih.2 i hi').of_iso eSucc

/-- The integral specialization of the reduced homology calculation for
spheres, as displayed in Hatcher's Corollary 2.14. -/
theorem reducedHomology_sphere_int (n : ℕ) :
    Nonempty
        ((Hatcher.Reduced.homologyFunctor.{0}
            (AddCommGrpCat.of ℤ) n).obj
          (TopCat.sphere.{0} n) ≅ AddCommGrpCat.of ℤ) ∧
      ∀ i, i ≠ n →
        IsZero ((Hatcher.Reduced.homologyFunctor.{0}
          (AddCommGrpCat.of ℤ) i).obj (TopCat.sphere.{0} n)) :=
  reducedHomology_sphere (C := AddCommGrpCat.{0})
    (AddCommGrpCat.of ℤ) n

end Hatcher.Sphere
