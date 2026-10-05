/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Hatcher.Sphere.TangentVectorField
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-!
# A nonvanishing tangent vector field on an odd-dimensional sphere

When `n` is odd, the ambient dimension `n + 1` is even. Pairing its coordinates
and applying `(x₁, x₂) ↦ (-x₂, x₁)` in every pair gives Hatcher's
explicit unit tangent vector field on `Sⁿ`.
-/

noncomputable section

open scoped EuclideanSpace InnerProductSpace

namespace Hatcher.Sphere

private def finTwoSwap : Equiv.Perm (Fin 2) :=
  Equiv.swap 0 1

private def pairIndexSwap (k : ℕ) : Equiv.Perm (Fin k × Fin 2) :=
  (Equiv.refl (Fin k)).prodCongr finTwoSwap

private noncomputable def pairCoordinateSign (p : Fin k × Fin 2) :
    ℝ ≃ₗᵢ[ℝ] ℝ :=
  if p.2 = 0 then LinearIsometryEquiv.neg ℝ else LinearIsometryEquiv.refl ℝ ℝ

/-- The paired-coordinate quarter turn
`(x₁,x₂,…) ↦ (-x₂,x₁,…)` on `k` coordinate pairs. -/
private noncomputable def pairedQuarterTurn (k : ℕ) :
    EuclideanSpace ℝ (Fin k × Fin 2) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin k × Fin 2) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (pairIndexSwap k)).trans
    (LinearIsometryEquiv.piLpCongrRight 2 pairCoordinateSign)

@[simp]
private theorem pairedQuarterTurn_apply_zero (k : ℕ)
    (x : EuclideanSpace ℝ (Fin k × Fin 2)) (i : Fin k) :
    pairedQuarterTurn k x (i, 0) = -x (i, 1) := by
  simp [pairedQuarterTurn, pairCoordinateSign, pairIndexSwap, finTwoSwap,
    Equiv.piCongrLeft']

@[simp]
private theorem pairedQuarterTurn_apply_one (k : ℕ)
    (x : EuclideanSpace ℝ (Fin k × Fin 2)) (i : Fin k) :
    pairedQuarterTurn k x (i, 1) = x (i, 0) := by
  simp [pairedQuarterTurn, pairCoordinateSign, pairIndexSwap, finTwoSwap,
    Equiv.piCongrLeft']

private theorem pairedQuarterTurn_sq (k : ℕ)
    (x : EuclideanSpace ℝ (Fin k × Fin 2)) :
    pairedQuarterTurn k (pairedQuarterTurn k x) = -x := by
  apply PiLp.ext
  rintro ⟨i, j⟩
  fin_cases j <;> simp

/-- The number of coordinate pairs in the ambient space of `Sⁿ` when `n`
is odd. -/
noncomputable def oddSpherePairCount (n : ℕ) (hn : Odd n) : ℕ :=
  Classical.choose hn + 1

theorem oddSpherePairCount_dimension (n : ℕ) (hn : Odd n) :
    n + 1 = oddSpherePairCount n hn * 2 := by
  have h := Classical.choose_spec hn
  simp only [oddSpherePairCount]
  omega

/-- The explicit reindexing of the `n+1` ambient coordinates into pairs when
`n` is odd. -/
noncomputable def oddSphereCoordinateEquiv (n : ℕ) (hn : Odd n) :
    Fin (n + 1) ≃ Fin (oddSpherePairCount n hn) × Fin 2 :=
  (finCongr (oddSpherePairCount_dimension n hn)).trans finProdFinEquiv.symm

/-- Reindexing ambient Euclidean vectors by Hatcher's coordinate pairs. -/
noncomputable def oddSphereCoordinateReindex (n : ℕ) (hn : Odd n) :
    EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin (oddSpherePairCount n hn) × Fin 2) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (oddSphereCoordinateEquiv n hn)

/-- Hatcher's paired-coordinate quarter turn on the ambient space of an
odd-dimensional sphere. -/
noncomputable def oddSphereQuarterTurn (n : ℕ) (hn : Odd n) :
    EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin (n + 1)) :=
  (oddSphereCoordinateReindex n hn).trans
    ((pairedQuarterTurn (oddSpherePairCount n hn)).trans
      (oddSphereCoordinateReindex n hn).symm)

/-- In paired coordinates, the first coordinate of each pair is the negative
of the original second coordinate. -/
@[simp]
theorem oddSphereQuarterTurn_pair_zero (n : ℕ) (hn : Odd n)
    (x : EuclideanSpace ℝ (Fin (n + 1)))
    (i : Fin (oddSpherePairCount n hn)) :
    oddSphereCoordinateReindex n hn (oddSphereQuarterTurn n hn x) (i, 0) =
      -(oddSphereCoordinateReindex n hn x) (i, 1) := by
  simp [oddSphereQuarterTurn]

/-- In paired coordinates, the second coordinate of each pair is the original
first coordinate. -/
@[simp]
theorem oddSphereQuarterTurn_pair_one (n : ℕ) (hn : Odd n)
    (x : EuclideanSpace ℝ (Fin (n + 1)))
    (i : Fin (oddSpherePairCount n hn)) :
    oddSphereCoordinateReindex n hn (oddSphereQuarterTurn n hn x) (i, 1) =
      oddSphereCoordinateReindex n hn x (i, 0) := by
  simp [oddSphereQuarterTurn]

private theorem oddSphereQuarterTurn_sq (n : ℕ) (hn : Odd n)
    (x : EuclideanSpace ℝ (Fin (n + 1))) :
    oddSphereQuarterTurn n hn (oddSphereQuarterTurn n hn x) = -x := by
  simp [oddSphereQuarterTurn, pairedQuarterTurn_sq]

private theorem inner_oddSphereQuarterTurn (n : ℕ) (hn : Odd n)
    (x : EuclideanSpace ℝ (Fin (n + 1))) :
    ⟪x, oddSphereQuarterTurn n hn x⟫_ℝ = 0 := by
  let J := oddSphereQuarterTurn n hn
  have h := J.inner_map_map x (J x)
  rw [oddSphereQuarterTurn_sq, inner_neg_right] at h
  have hcomm : ⟪J x, x⟫_ℝ = ⟪x, J x⟫_ℝ := real_inner_comm _ _
  rw [hcomm] at h
  change ⟪x, J x⟫_ℝ = 0
  linarith

/-- **Hatcher, Theorem 2.28 (printed page 135), reverse implication.**
If `n` is odd, pairing the ambient coordinates and rotating each pair by a
quarter turn defines a tangent vector field on `Sⁿ`. -/
noncomputable def nonvanishingTangentVectorFieldOfOdd (n : ℕ) (hn : Odd n) :
    TangentVectorField n where
  toContinuousMap :=
    ⟨fun x ↦ oddSphereQuarterTurn n hn (ambientPoint n x),
      (oddSphereQuarterTurn n hn).continuous.comp (continuous_ambientPoint n)⟩
  orthogonal := fun x ↦ inner_oddSphereQuarterTurn n hn (ambientPoint n x)

/-- Hatcher's explicit odd-sphere field has unit norm at every point. -/
@[simp]
theorem norm_nonvanishingTangentVectorFieldOfOdd (n : ℕ) (hn : Odd n)
    (x : ((TopCat.sphere.{0} n : TopCat.{0}) : Type)) :
    ‖nonvanishingTangentVectorFieldOfOdd n hn x‖ = 1 := by
  simp [nonvanishingTangentVectorFieldOfOdd]

/-- Hatcher's explicit odd-sphere tangent vector field is nowhere zero. -/
theorem nonvanishingTangentVectorFieldOfOdd_nonvanishing (n : ℕ)
    (hn : Odd n) :
    (nonvanishingTangentVectorFieldOfOdd n hn).Nonvanishing := by
  intro x hx
  have hnorm := congrArg norm hx
  simp at hnorm

end Hatcher.Sphere
