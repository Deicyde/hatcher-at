/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Hatcher.VanKampen.DiskBoundaryCircle
import Hatcher.VanKampen.CyclicPresentationAlgebra
import Mathlib.Topology.Algebra.Group.ZPow

/-!
# Integer powers on the standard circle

The fixed disk-boundary homeomorphism transports the continuous integer-power
operation on the complex unit circle to the standard one-sphere. Natural powers
agree with the existing circle map, and negative powers factor through inversion.
-/

noncomputable section

open CategoryTheory

namespace Hatcher.Sphere

/-- The actual integer-power self-map of the standard one-sphere. -/
noncomputable def circlePowerMap (d : ℤ) :
    TopCat.sphere.{0} 1 ⟶ TopCat.sphere.{0} 1 :=
  TopCat.ofHom
    { toFun := fun x ↦
        diskBoundaryTwoHomeomorphCircle.{0}.symm
          ((diskBoundaryTwoHomeomorphCircle.{0} x) ^ d)
      continuous_toFun :=
        diskBoundaryTwoHomeomorphCircle.{0}.symm.continuous.comp
          ((continuous_zpow d).comp diskBoundaryTwoHomeomorphCircle.{0}.continuous) }

/-- The integer-power map in the fixed circle coordinates. -/
theorem circlePowerMap_apply (d : ℤ) (x : TopCat.sphere.{0} 1) :
    circlePowerMap d x =
      diskBoundaryTwoHomeomorphCircle.{0}.symm
        ((diskBoundaryTwoHomeomorphCircle.{0} x) ^ d) :=
  rfl

/-- Transport to the unit circle recovers the integer-power operation. -/
@[simp]
theorem circlePowerMap_coordinate (d : ℤ) (x : TopCat.sphere.{0} 1) :
    diskBoundaryTwoHomeomorphCircle.{0} (circlePowerMap d x) =
      (diskBoundaryTwoHomeomorphCircle.{0} x) ^ d := by
  simp [circlePowerMap_apply]

/-- In complex coordinates the map is exactly `z ↦ z ^ d`. -/
theorem circlePowerMap_complex_coordinate (d : ℤ) (x : TopCat.sphere.{0} 1) :
    (diskBoundaryTwoHomeomorphCircle.{0} (circlePowerMap d x) : ℂ) =
      (diskBoundaryTwoHomeomorphCircle.{0} x : ℂ) ^ d := by
  rw [circlePowerMap_coordinate, _root_.Circle.coe_zpow]

/-- The zero power is the constant map at the standard circle basepoint. -/
@[simp]
theorem circlePowerMap_zero :
    circlePowerMap 0 = TopCat.const diskBoundaryTwoBasepoint.{0} := by
  apply TopCat.ext
  intro x
  change circlePowerMap 0 x = diskBoundaryTwoBasepoint.{0}
  simp [circlePowerMap_apply]
  rfl

/-- Natural powers reuse the previously constructed natural circle map. -/
theorem circlePowerMap_natCast (k : ℕ) :
    circlePowerMap (k : ℤ) =
      (TopCat.isoOfHomeo diskBoundaryTwoHomeomorphCircle.{0}).hom ≫
        TopCat.ofHom (Hatcher.Circle.degreeMap k) ≫
          (TopCat.isoOfHomeo diskBoundaryTwoHomeomorphCircle.{0}).inv := by
  apply TopCat.ext
  intro x
  change circlePowerMap (k : ℤ) x =
    diskBoundaryTwoHomeomorphCircle.{0}.symm
      (Hatcher.Circle.degreeMap k (diskBoundaryTwoHomeomorphCircle.{0} x))
  simp [circlePowerMap_apply, Hatcher.Circle.degreeMap_apply]
  rfl

/-- Negative natural powers are a natural power followed by inversion. -/
theorem circlePowerMap_neg_natCast (k : ℕ) :
    circlePowerMap (-(k : ℤ)) = circlePowerMap (k : ℤ) ≫ circlePowerMap (-1) := by
  apply TopCat.ext
  intro x
  change circlePowerMap (-(k : ℤ)) x = circlePowerMap (-1) (circlePowerMap (k : ℤ) x)
  apply diskBoundaryTwoHomeomorphCircle.{0}.injective
  simp only [circlePowerMap_coordinate, zpow_neg, zpow_one]

end Hatcher.Sphere
