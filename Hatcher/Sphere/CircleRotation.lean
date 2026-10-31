/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Hatcher.VanKampen.DiskBoundaryCircle
import Hatcher.Sphere.DegreeProperties

/-!
# Rotations of the standard circle

Multiplication by a unit complex number is transported through the fixed
sphere-to-circle homeomorphism. Choosing an argument inside the construction
gives an explicit homotopy from the identity, hence signed degree one.
-/

noncomputable section

open CategoryTheory unitInterval

namespace Hatcher.Sphere

/-- Multiplication by `r`, transported to the standard one-sphere. -/
noncomputable def circleRotation (r : _root_.Circle) :
    TopCat.sphere.{0} 1 ⟶ TopCat.sphere.{0} 1 :=
  let e : TopCat.sphere.{0} 1 ≃ₜ _root_.Circle :=
    diskBoundaryTwoHomeomorphCircle.{0}
  TopCat.ofHom
    { toFun := fun x ↦ e.symm (r * e x)
      continuous_toFun := e.symm.continuous.comp
        (continuous_const.mul e.continuous) }

/-- A homotopy obtained by choosing an argument of the fixed rotation. -/
noncomputable def circleRotationHomotopy (r : _root_.Circle) :
    TopCat.Homotopy (𝟙 (TopCat.sphere.{0} 1)) (circleRotation r) := by
  let e : TopCat.sphere.{0} 1 ≃ₜ _root_.Circle :=
    diskBoundaryTwoHomeomorphCircle.{0}
  let θ : ℝ := Complex.arg (r : ℂ)
  refine
    { toFun := fun p ↦
        e.symm (_root_.Circle.exp ((p.1 : ℝ) * θ) * e p.2)
      continuous_toFun := ?_
      map_zero_left := ?_
      map_one_left := ?_ }
  · have ht : Continuous
        (fun p : I × TopCat.sphere.{0} 1 ↦ (p.1 : ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    exact e.symm.continuous.comp
      ((_root_.Circle.exp.continuous.comp
          (ht.mul continuous_const)).mul
        (e.continuous.comp continuous_snd))
  · intro x
    change e.symm (_root_.Circle.exp (((0 : I) : ℝ) * θ) * e x) = x
    simp
  · intro x
    change e.symm (_root_.Circle.exp (((1 : I) : ℝ) * θ) * e x) =
      e.symm (r * e x)
    simp [θ]

/-- Every circle rotation is homotopic to the identity and has degree one. -/
theorem circleRotation_homotopic_identity_and_degree (r : _root_.Circle) :
    Nonempty
      (TopCat.Homotopy (𝟙 (TopCat.sphere.{0} 1)) (circleRotation r)) ∧
      degree 1 (by decide) (circleRotation r) = 1 := by
  refine ⟨⟨circleRotationHomotopy r⟩, ?_⟩
  calc
    degree 1 (by decide) (circleRotation r) =
        degree 1 (by decide) (𝟙 (TopCat.sphere.{0} 1)) :=
      (degree_eq_of_homotopy 1 (by decide) (circleRotationHomotopy r)).symm
    _ = 1 := degree_id 1 (by decide)

end Hatcher.Sphere
