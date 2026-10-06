/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Hatcher.Sphere.AntipodalDegree
import Hatcher.Sphere.TangentVectorField
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# The parity obstruction for tangent vector fields on spheres

A nonvanishing tangent field can be normalized. Hatcher's explicit
cosine--sine formula then rotates each sphere point through its tangent vector
and gives a homotopy from the identity to the antipodal map. Their degrees can
agree only in odd sphere dimension.
-/

noncomputable section

open CategoryTheory Metric
open scoped EuclideanSpace InnerProductSpace unitInterval

namespace Hatcher.Sphere

private def tangentFieldRotationVector {n : ℕ}
    (v : TangentVectorField n) (hv : v.Nonvanishing)
    (p : I × ((TopCat.sphere.{0} n : TopCat.{0}) : Type)) :
    EuclideanSpace ℝ (Fin (n + 1)) :=
  Real.cos (Real.pi * (p.1 : ℝ)) • ambientPoint n p.2 +
    Real.sin (Real.pi * (p.1 : ℝ)) • v.normalize hv p.2

private theorem continuous_tangentFieldRotationVector {n : ℕ}
    (v : TangentVectorField n) (hv : v.Nonvanishing) :
    Continuous (tangentFieldRotationVector v hv) := by
  have hangle : Continuous
      (fun p : I × ((TopCat.sphere.{0} n : TopCat.{0}) : Type) ↦
        Real.pi * (p.1 : ℝ)) :=
    continuous_const.mul (continuous_subtype_val.comp continuous_fst)
  exact
    (Real.continuous_cos.comp hangle).smul
        ((continuous_ambientPoint n).comp continuous_snd)
      |>.add ((Real.continuous_sin.comp hangle).smul
        ((v.normalize hv).continuous.comp continuous_snd))

private theorem norm_tangentFieldRotationVector {n : ℕ}
    (v : TangentVectorField n) (hv : v.Nonvanishing)
    (p : I × ((TopCat.sphere.{0} n : TopCat.{0}) : Type)) :
    ‖tangentFieldRotationVector v hv p‖ = 1 := by
  let angle := Real.pi * (p.1 : ℝ)
  let x := ambientPoint n p.2
  let w := v.normalize hv p.2
  have horth : ⟪x, w⟫_ℝ = 0 := by
    exact TangentVectorField.normalize_orthogonal v hv p.2
  have hscaled :
      ⟪Real.cos angle • x, Real.sin angle • w⟫_ℝ = 0 := by
    simp [real_inner_smul_left, real_inner_smul_right, horth]
  have hx : ‖x‖ = 1 := norm_ambientPoint n p.2
  have hw : ‖w‖ = 1 := TangentVectorField.norm_normalize v hv p.2
  have hsquare : ‖tangentFieldRotationVector v hv p‖ ^ 2 = 1 := by
    calc
      ‖tangentFieldRotationVector v hv p‖ ^ 2 =
          ‖Real.cos angle • x‖ ^ 2 + ‖Real.sin angle • w‖ ^ 2 := by
        simpa only [tangentFieldRotationVector, angle, x, w, pow_two] using
          norm_add_sq_eq_norm_sq_add_norm_sq_real hscaled
      _ = Real.cos angle ^ 2 + Real.sin angle ^ 2 := by
        simp [norm_smul, Real.norm_eq_abs, sq_abs, hx, hw]
      _ = 1 := Real.cos_sq_add_sin_sq angle
  nlinarith [norm_nonneg (tangentFieldRotationVector v hv p)]

private def tangentFieldRotationPoint {n : ℕ}
    (v : TangentVectorField n) (hv : v.Nonvanishing)
    (p : I × ((TopCat.sphere.{0} n : TopCat.{0}) : Type)) :
    ((TopCat.sphere.{0} n : TopCat.{0}) : Type) :=
  (sphereULiftHomeomorph n).symm
    ⟨tangentFieldRotationVector v hv p, by
      rw [mem_sphere_zero_iff_norm]
      exact norm_tangentFieldRotationVector v hv p⟩

private theorem continuous_tangentFieldRotationPoint {n : ℕ}
    (v : TangentVectorField n) (hv : v.Nonvanishing) :
    Continuous (tangentFieldRotationPoint v hv) :=
  (sphereULiftHomeomorph n).symm.continuous.comp
    ((continuous_tangentFieldRotationVector v hv).subtype_mk _)

private theorem tangentFieldRotationPoint_zero {n : ℕ}
    (v : TangentVectorField n) (hv : v.Nonvanishing)
    (x : ((TopCat.sphere.{0} n : TopCat.{0}) : Type)) :
    tangentFieldRotationPoint v hv (0, x) = x := by
  apply (sphereULiftHomeomorph n).injective
  apply Subtype.ext
  simp [tangentFieldRotationPoint, tangentFieldRotationVector, ambientPoint]

private theorem tangentFieldRotationPoint_one {n : ℕ}
    (v : TangentVectorField n) (hv : v.Nonvanishing)
    (x : ((TopCat.sphere.{0} n : TopCat.{0}) : Type)) :
    tangentFieldRotationPoint v hv (1, x) = (antipodalIso n).hom x := by
  apply (sphereULiftHomeomorph n).injective
  rw [sphereULiftHomeomorph_antipodalIso_apply]
  apply Subtype.ext
  simp [tangentFieldRotationPoint, tangentFieldRotationVector, ambientPoint]

/-- **Hatcher, Theorem 2.28 (printed page 135), forward implication.** A
nonvanishing tangent field gives the explicit cosine--sine homotopy from the
identity map of `Sⁿ` to the antipodal map. -/
noncomputable def identityHomotopyAntipodalOfNonvanishingTangentVectorField
    {n : ℕ} (v : TangentVectorField n) (hv : v.Nonvanishing) :
    TopCat.Homotopy (𝟙 (TopCat.sphere.{0} n)) (antipodalIso n).hom where
  toFun := tangentFieldRotationPoint v hv
  continuous_toFun := continuous_tangentFieldRotationPoint v hv
  map_zero_left := tangentFieldRotationPoint_zero v hv
  map_one_left := tangentFieldRotationPoint_one v hv

/-- **Hatcher, Theorem 2.28 (printed page 135), forward implication.** A
positive-dimensional sphere with a nonvanishing tangent vector field has odd
dimension. -/
theorem odd_of_nonvanishingTangentVectorField
    (n : ℕ) (hn : 0 < n) (v : TangentVectorField n)
    (hv : v.Nonvanishing) : Odd n := by
  have hdegree := degree_eq_of_homotopy n hn
    (identityHomotopyAntipodalOfNonvanishingTangentVectorField v hv)
  rw [degree_id, degree_antipodal] at hdegree
  have hpow : (-1 : ℤ) ^ (n + 1) = 1 := hdegree.symm
  apply Nat.not_even_iff_odd.mp
  intro heven
  have hodd : Odd (n + 1) := heven.add_one
  have hneg : (-1 : ℤ) ^ (n + 1) = -1 := hodd.neg_one_pow
  rw [hpow] at hneg
  norm_num at hneg

end Hatcher.Sphere
