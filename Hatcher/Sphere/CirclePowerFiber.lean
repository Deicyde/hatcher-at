/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Hatcher.Sphere.CirclePower
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-!
# The actual fibers of positive circle powers

Choose one root of the target on the unit circle and multiply it by the kth
roots of unity. The resulting equivalence enumerates every point of the actual
sphere-map fiber and proves that the fiber has exactly k elements.
-/

noncomputable section

namespace Hatcher.Sphere

/-- A positive circle power has exactly k preimages, enumerated by actual roots. -/
theorem circlePowerMap_positive_fiber
    (k : ℕ) (hk : 0 < k) (y : TopCat.sphere.{0} 1) :
    ∃ a : _root_.Circle,
      a ^ k = diskBoundaryTwoHomeomorphCircle.{0} y ∧
      ∃ E :
          {z : TopCat.sphere.{0} 1 // circlePowerMap (k : ℤ) z = y} ≃ Fin k,
        ∀ j : Fin k,
          diskBoundaryTwoHomeomorphCircle.{0} ((E.symm j).val) =
            a * _root_.Circle.exp (2 * Real.pi * ((j.val : ℝ) / (k : ℝ))) := by
  classical
  let : NeZero k := ⟨Nat.ne_of_gt hk⟩
  let e : TopCat.sphere.{0} 1 ≃ₜ _root_.Circle := diskBoundaryTwoHomeomorphCircle.{0}
  obtain ⟨a, ha⟩ := (_root_.Circle.isQuotientCoveringMap_npow k).surjective (e y)
  change a ^ k = e y at ha
  let F :
      {z : TopCat.sphere.{0} 1 // circlePowerMap (k : ℤ) z = y} ≃
        rootsOfUnity k _root_.Circle :=
    { toFun := fun z ↦
        rootsOfUnity.mkOfPowEq (e z.val / a) (by
          have hz := congrArg e z.property
          change diskBoundaryTwoHomeomorphCircle.{0}
            (circlePowerMap (k : ℤ) z.val) = e y at hz
          rw [circlePowerMap_coordinate, zpow_natCast] at hz
          change e z.val ^ k = e y at hz
          rw [div_pow, hz, ha, div_self'])
      invFun := fun ζ ↦
        ⟨e.symm (a * ζ.val.val), by
          apply e.injective
          change diskBoundaryTwoHomeomorphCircle.{0}
            (circlePowerMap (k : ℤ) (e.symm (a * ζ.val.val))) = e y
          rw [circlePowerMap_coordinate, zpow_natCast]
          change (e (e.symm (a * ζ.val.val))) ^ k = e y
          rw [e.apply_symm_apply, mul_pow, ha,
            (mem_rootsOfUnity' k ζ.val).mp ζ.property, mul_one]⟩
      left_inv := fun z ↦ by
        apply Subtype.ext
        change e.symm (a * (e z.val / a)) = z.val
        rw [mul_div_cancel, e.symm_apply_apply]
      right_inv := fun ζ ↦ by
        apply rootsOfUnity.coe_injective
        change e (e.symm (a * ζ.val.val)) / a = ζ.val.val
        rw [e.apply_symm_apply, mul_div_cancel_left] }
  let R : ZMod k ≃ rootsOfUnity k _root_.Circle :=
    Equiv.ofBijective (ZMod.rootsOfUnityAddChar k) (bijective_rootsOfUnityAddChar k)
  let E := F.trans (R.symm.trans (ZMod.finEquiv k).toEquiv.symm)
  refine ⟨a, ha, E, ?_⟩
  intro j
  have hval : ((ZMod.finEquiv k) j).val = j.val := by
    cases k with
    | zero => exact Fin.elim0 j
    | succ n => rfl
  change e (e.symm (a * ZMod.toCircle ((ZMod.finEquiv k) j))) = _
  rw [e.apply_symm_apply, ZMod.toCircle_eq_circleExp, hval]

end Hatcher.Sphere
