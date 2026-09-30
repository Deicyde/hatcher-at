/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Mathlib.Topology.Category.TopCat.Sphere
import Mathlib.Topology.Category.TopCat.ULift
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# The zero-sphere

This file identifies Mathlib's universe-lifted zero-sphere with a lifted
two-point space. The point-level formulas are exposed for the subsequent
degree-zero homology calculation.
-/

open CategoryTheory

namespace Hatcher.Sphere

private abbrev RawZeroSphere :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1

private noncomputable def rawZeroSpherePoint (b : Bool) : RawZeroSphere :=
  match b with
  | false => ⟨EuclideanSpace.single 0 (-1),
      mem_sphere_zero_iff_norm.2 (by simp)⟩
  | true => ⟨EuclideanSpace.single 0 1,
      mem_sphere_zero_iff_norm.2 (by simp)⟩

private theorem rawZeroSpherePoint_cases (x : RawZeroSphere) :
    x = rawZeroSpherePoint false ∨ x = rawZeroSpherePoint true := by
  have hnorm : ‖x.1‖ = 1 := by
    simpa only [mem_sphere_zero_iff_norm] using x.2
  have hsquare : (x.1 0) ^ 2 = 1 := by
    have h := EuclideanSpace.real_norm_sq_eq x.1
    rw [hnorm] at h
    simpa using h.symm
  have hfactor : (x.1 0 - 1) * (x.1 0 + 1) = 0 := by
    nlinarith
  rcases mul_eq_zero.mp hfactor with hnegative | hpositive
  · right
    apply Subtype.ext
    ext i
    fin_cases i
    simpa [rawZeroSpherePoint] using sub_eq_zero.mp hnegative
  · left
    apply Subtype.ext
    ext i
    fin_cases i
    have : x.1 0 = -1 := by linarith
    simpa [rawZeroSpherePoint] using this

private noncomputable def rawZeroSphereEquivBool : RawZeroSphere ≃ Bool where
  toFun x := if x.1 0 = 1 then true else false
  invFun := rawZeroSpherePoint
  left_inv x := by
    rcases rawZeroSpherePoint_cases x with hnegative | hpositive
    · subst x
      norm_num [rawZeroSpherePoint]
    · subst x
      simp [rawZeroSpherePoint]
  right_inv b := by
    cases b <;> norm_num [rawZeroSpherePoint]

private noncomputable def rawZeroSphereHomeomorphBool :
    RawZeroSphere ≃ₜ Bool := by
  let e := rawZeroSphereEquivBool
  letI : Finite RawZeroSphere := Finite.of_injective e e.injective
  exact
    { toEquiv := e
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }

private noncomputable def zeroSphereHomeomorphTwoPoint.{w} :
    TopCat.sphere.{w} 0 ≃ₜ ULift.{w} Bool := by
  change ULift.{w} RawZeroSphere ≃ₜ ULift.{w} Bool
  exact Homeomorph.ulift.trans
    (rawZeroSphereHomeomorphBool.trans Homeomorph.ulift.symm)

/-- The point of the zero-sphere with coordinate `-1` when `b = false` and
coordinate `1` when `b = true`. -/
noncomputable def zeroSpherePoint.{w} (b : Bool) :
    TopCat.sphere.{w} 0 :=
  ⟨rawZeroSpherePoint b⟩

/-- The zero-sphere is explicitly the lifted two-point space. -/
noncomputable def zeroSphereIsoTwoPoint.{w} :
    TopCat.sphere.{w} 0 ≅ TopCat.of (ULift.{w} Bool) :=
  TopCat.isoOfHomeo zeroSphereHomeomorphTwoPoint.{w}

@[simp]
theorem zeroSphereIsoTwoPoint_inv_apply.{w} (b : ULift.{w} Bool) :
    zeroSphereIsoTwoPoint.{w}.inv b = zeroSpherePoint.{w} b.down := by
  cases b
  rfl

@[simp]
theorem zeroSphereIsoTwoPoint_hom_point.{w} (b : Bool) :
    zeroSphereIsoTwoPoint.{w}.hom (zeroSpherePoint.{w} b) =
      ULift.up b := by
  rw [← zeroSphereIsoTwoPoint_inv_apply (b := ULift.up b)]
  simp

theorem zeroSpherePoint_false_ne_true.{w} :
    zeroSpherePoint.{w} false ≠ zeroSpherePoint.{w} true := by
  intro h
  have hcoord := congrArg
    (fun x : TopCat.sphere.{w} 0 ↦ x.down.1 0) h
  norm_num [zeroSpherePoint, rawZeroSpherePoint] at hcoord

end Hatcher.Sphere
