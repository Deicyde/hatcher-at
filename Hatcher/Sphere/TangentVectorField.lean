/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Hatcher.Sphere.HemisphereCharts
import Mathlib.Analysis.Normed.Module.Normalize

/-!
# Tangent vector fields on spheres

Following Hatcher's ambient convention, a tangent vector field on the standard
`n`-sphere is a continuous map into the ambient Euclidean `(n+1)`-space whose
value at each point is orthogonal to that point. A nowhere-zero field can be
normalized pointwise without changing its zero set.
-/

noncomputable section

open Metric Set
open scoped EuclideanSpace InnerProductSpace

namespace Hatcher.Sphere

/-- The ambient vector represented by a point of Mathlib's public standard
sphere. -/
def ambientPoint (n : ℕ)
    (x : ((TopCat.sphere.{0} n : TopCat.{0}) : Type)) :
    EuclideanSpace ℝ (Fin (n + 1)) :=
  (sphereULiftHomeomorph n x).1

/-- The ambient-point map is continuous. -/
theorem continuous_ambientPoint (n : ℕ) : Continuous (ambientPoint n) :=
  continuous_subtype_val.comp (sphereULiftHomeomorph n).continuous

/-- A standard sphere point has ambient norm one. -/
@[simp]
theorem norm_ambientPoint (n : ℕ)
    (x : ((TopCat.sphere.{0} n : TopCat.{0}) : Type)) :
    ‖ambientPoint n x‖ = 1 := by
  simpa only [ambientPoint, mem_sphere_zero_iff_norm] using
    (sphereULiftHomeomorph n x).2

/-- **Hatcher, Theorem 2.28 (printed page 135), tangent-field convention.**
A tangent vector field on `Sⁿ` is a continuous ambient vector field in
`ℝⁿ⁺¹` whose value at `x` is orthogonal to `x`. -/
structure TangentVectorField (n : ℕ) where
  toContinuousMap :
    C(((TopCat.sphere.{0} n : TopCat.{0}) : Type),
      EuclideanSpace ℝ (Fin (n + 1)))
  orthogonal : ∀ x, ⟪ambientPoint n x, toContinuousMap x⟫_ℝ = 0

namespace TangentVectorField

variable {n : ℕ}

instance : CoeFun (TangentVectorField n) fun _ ↦
    ((TopCat.sphere.{0} n : TopCat.{0}) : Type) →
      EuclideanSpace ℝ (Fin (n + 1)) :=
  ⟨fun v ↦ v.toContinuousMap⟩

/-- A tangent vector field is continuous as an ambient vector-valued map. -/
theorem continuous (v : TangentVectorField n) : Continuous v :=
  v.toContinuousMap.continuous

/-- A tangent vector field is nonvanishing when it is nonzero at every point. -/
def Nonvanishing (v : TangentVectorField n) : Prop :=
  ∀ x, v x ≠ 0

/-- The zero set of a tangent vector field. -/
def zeroSet (v : TangentVectorField n) :
    Set (((TopCat.sphere.{0} n : TopCat.{0}) : Type)) :=
  {x | v x = 0}

/-- Pointwise normalization of a nonvanishing tangent vector field. -/
def normalize (v : TangentVectorField n) (hv : v.Nonvanishing) :
    TangentVectorField n where
  toContinuousMap :=
    ⟨fun x ↦ NormedSpace.normalize (v x), by
      rw [show (fun x ↦ NormedSpace.normalize (v x)) =
          fun x ↦ ‖v x‖⁻¹ • v x by
        funext x
        rfl]
      exact (v.continuous.norm.inv₀ fun x ↦
        norm_ne_zero_iff.mpr (hv x)).smul v.continuous⟩
  orthogonal := by
    intro x
    simp [NormedSpace.normalize, real_inner_smul_right, v.orthogonal]

@[simp]
theorem normalize_apply (v : TangentVectorField n) (hv : v.Nonvanishing)
    (x : ((TopCat.sphere.{0} n : TopCat.{0}) : Type)) :
    v.normalize hv x = NormedSpace.normalize (v x) :=
  rfl

/-- The normalized field remains continuous. -/
theorem continuous_normalize (v : TangentVectorField n)
    (hv : v.Nonvanishing) : Continuous (v.normalize hv) :=
  (v.normalize hv).continuous

/-- Normalization preserves tangency. -/
@[simp]
theorem normalize_orthogonal (v : TangentVectorField n)
    (hv : v.Nonvanishing)
    (x : ((TopCat.sphere.{0} n : TopCat.{0}) : Type)) :
    ⟪ambientPoint n x, v.normalize hv x⟫_ℝ = 0 :=
  (v.normalize hv).orthogonal x

/-- A normalized nonvanishing field has unit norm at every point. -/
@[simp]
theorem norm_normalize (v : TangentVectorField n) (hv : v.Nonvanishing)
    (x : ((TopCat.sphere.{0} n : TopCat.{0}) : Type)) :
    ‖v.normalize hv x‖ = 1 :=
  NormedSpace.norm_normalize (hv x)

/-- Pointwise normalization does not create or remove zeros. -/
@[simp]
theorem normalize_eq_zero_iff (v : TangentVectorField n)
    (hv : v.Nonvanishing)
    (x : ((TopCat.sphere.{0} n : TopCat.{0}) : Type)) :
    v.normalize hv x = 0 ↔ v x = 0 :=
  NormedSpace.normalize_eq_zero_iff (v x)

/-- The normalized field has exactly the same zero set as the original one. -/
@[simp]
theorem zeroSet_normalize (v : TangentVectorField n)
    (hv : v.Nonvanishing) :
    (v.normalize hv).zeroSet = v.zeroSet := by
  ext x
  exact v.normalize_eq_zero_iff hv x

/-- Normalization preserves nonvanishing. -/
theorem nonvanishing_normalize (v : TangentVectorField n)
    (hv : v.Nonvanishing) : (v.normalize hv).Nonvanishing := by
  intro x hx
  exact hv x ((v.normalize_eq_zero_iff hv x).mp hx)

end TangentVectorField

end Hatcher.Sphere
