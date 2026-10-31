/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Hatcher.Sphere.CirclePower
import Hatcher.Sphere.ReflectionDegree

/-!
# Circle inversion is a coordinate reflection

The fixed real-to-complex coordinates identify reflection in the second
coordinate with complex conjugation. On the unit circle conjugation is
inversion, so the actual negative-one power has signed degree minus one.
-/

noncomputable section

open CategoryTheory

namespace Hatcher.Sphere

private theorem circle_coordinateReflection_last
    (x : TopCat.sphere.{0} 1) :
    (diskBoundaryTwoHomeomorphCircle.{0}
        ((coordinateReflectionIso 1 (Fin.last 1)).hom x) : ℂ) =
      star (diskBoundaryTwoHomeomorphCircle.{0} x : ℂ) := by
  change Complex.orthonormalBasisOneI.repr.symm
      (sphereULiftHomeomorph 1 ((coordinateReflectionIso 1 (Fin.last 1)).hom x)).1 =
    star (Complex.orthonormalBasisOneI.repr.symm (sphereULiftHomeomorph 1 x).1)
  rw [Complex.orthonormalBasisOneI_repr_symm_apply,
    Complex.orthonormalBasisOneI_repr_symm_apply]
  simp only [sphereULiftHomeomorph_coordinateReflectionIso_apply]
  simp

/-- The negative-one power is the standard second-coordinate reflection. -/
theorem circlePowerMap_neg_one_eq_coordinateReflection :
    circlePowerMap (-1) = (coordinateReflectionIso 1 (Fin.last 1)).hom := by
  apply TopCat.ext
  intro x
  apply diskBoundaryTwoHomeomorphCircle.{0}.injective
  apply Subtype.ext
  rw [circlePowerMap_coordinate, zpow_neg_one, _root_.Circle.coe_inv_eq_conj,
    circle_coordinateReflection_last]
  rfl

/-- The actual inversion map has signed homological degree minus one. -/
theorem degree_circlePowerMap_neg_one :
    degree 1 (by decide) (circlePowerMap (-1)) = -1 := by
  rw [circlePowerMap_neg_one_eq_coordinateReflection]
  exact degree_coordinateReflection_last 1 (by decide)

/-- Circle inversion is the standard coordinate reflection and has degree `-1`. -/
theorem circlePowerMap_inversion_reflection_and_degree :
    circlePowerMap (-1) = (coordinateReflectionIso 1 (Fin.last 1)).hom ∧
      degree 1 (by decide) (circlePowerMap (-1)) = -1 :=
  ⟨circlePowerMap_neg_one_eq_coordinateReflection, degree_circlePowerMap_neg_one⟩

end Hatcher.Sphere
