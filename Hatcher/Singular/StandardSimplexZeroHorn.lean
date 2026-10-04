/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Hatcher.Singular.StandardSimplexBoundaryHorn
import Hatcher.Topology.StrongDeformationRetract
import Mathlib.Topology.Order.Lattice

/-!
# The standard simplex retracts onto its zero horn

This file constructs the strong deformation retraction used in Hatcher's
induction for the relative fundamental class of a simplex.  In barycentric
coordinates, the endpoint subtracts the least positive-index coordinate from
every positive-index coordinate and transfers the removed mass to coordinate
zero.
-/

noncomputable section

open Set Topology
open scoped unitInterval

namespace Hatcher.Simplex

/-- The least barycentric coordinate having positive index. -/
def zeroHornMinimum (n : ℕ) (x : StandardSimplex (n + 1)) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty
    (fun i : Fin (n + 1) ↦ x.weights i.succ)

theorem zeroHornMinimum_nonneg (n : ℕ) (x : StandardSimplex (n + 1)) :
    0 ≤ zeroHornMinimum n x := by
  apply Finset.le_inf' Finset.univ_nonempty
  intro i _
  exact x.weights_nonneg i.succ

theorem zeroHornMinimum_le_weight_succ (n : ℕ)
    (x : StandardSimplex (n + 1)) (i : Fin (n + 1)) :
    zeroHornMinimum n x ≤ x.weights i.succ :=
  Finset.inf'_le _ (Finset.mem_univ i)

@[fun_prop]
theorem continuous_zeroHornMinimum (n : ℕ) :
    Continuous (zeroHornMinimum n) := by
  apply Continuous.finset_inf'_apply Finset.univ_nonempty
  intro i _
  exact Convexity.StdSimplex.continuous_weights_apply ℝ i.succ

/-- The endpoint of the zero-horn deformation, as a point of the ambient
simplex. -/
def zeroHornRetractionPoint (n : ℕ)
    (x : StandardSimplex (n + 1)) : StandardSimplex (n + 1) where
  weights := Finsupp.equivFunOnFinite.symm <|
    Fin.cases
      (x.weights 0 + (n + 1 : ℝ) * zeroHornMinimum n x)
      (fun i ↦ x.weights i.succ - zeroHornMinimum n x)
  nonneg := by
    intro j
    refine Fin.cases ?_ (fun i ↦ ?_) j
    · exact add_nonneg (x.weights_nonneg 0)
        (mul_nonneg (by positivity) (zeroHornMinimum_nonneg n x))
    · exact sub_nonneg.mpr (zeroHornMinimum_le_weight_succ n x i)
  total := by
    rw [Finsupp.equivFunOnFinite_symm_sum]
    rw [Fin.sum_univ_succ]
    simp only [Fin.cases_zero, Fin.cases_succ,
      Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    have hx := x.total_of_fintype
    rw [Fin.sum_univ_succ] at hx
    norm_num [Nat.cast_add] at *
    linarith

@[simp]
theorem zeroHornRetractionPoint_weight_zero (n : ℕ)
    (x : StandardSimplex (n + 1)) :
    (zeroHornRetractionPoint n x).weights 0 =
      x.weights 0 + (n + 1 : ℝ) * zeroHornMinimum n x :=
  rfl

@[simp]
theorem zeroHornRetractionPoint_weight_succ (n : ℕ)
    (x : StandardSimplex (n + 1)) (i : Fin (n + 1)) :
    (zeroHornRetractionPoint n x).weights i.succ =
      x.weights i.succ - zeroHornMinimum n x :=
  rfl

@[fun_prop]
theorem continuous_zeroHornRetractionPoint (n : ℕ) :
    Continuous (zeroHornRetractionPoint n) := by
  rw [(Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ
    (Fin (n + 2))).continuous_iff]
  unfold Function.comp
  apply continuous_pi
  intro j
  refine Fin.cases ?_ (fun i ↦ ?_) j
  · simp only [zeroHornRetractionPoint_weight_zero]
    exact (Convexity.StdSimplex.continuous_weights_apply ℝ 0).add
      (continuous_const.mul (continuous_zeroHornMinimum n))
  · simp only [zeroHornRetractionPoint_weight_succ]
    exact (Convexity.StdSimplex.continuous_weights_apply ℝ i.succ).sub
      (continuous_zeroHornMinimum n)

theorem exists_weight_succ_eq_zeroHornMinimum (n : ℕ)
    (x : StandardSimplex (n + 1)) :
    ∃ i : Fin (n + 1), x.weights i.succ = zeroHornMinimum n x := by
  obtain ⟨i, _, hi⟩ :=
    (Finset.inf'_le_iff Finset.univ_nonempty).mp
      (le_refl (zeroHornMinimum n x))
  exact ⟨i, le_antisymm hi (zeroHornMinimum_le_weight_succ n x i)⟩

theorem zeroHornRetractionPoint_mem_zeroHorn (n : ℕ)
    (x : StandardSimplex (n + 1)) :
    zeroHornRetractionPoint n x ∈ standardSimplexZeroHorn n := by
  obtain ⟨i, hi⟩ := exists_weight_succ_eq_zeroHornMinimum n x
  exact ⟨i.succ, Fin.succ_ne_zero i, by simp [hi]⟩

theorem zeroHornMinimum_eq_zero_of_mem (n : ℕ)
    {x : StandardSimplex (n + 1)} (hx : x ∈ standardSimplexZeroHorn n) :
    zeroHornMinimum n x = 0 := by
  obtain ⟨j, hj, hjzero⟩ := hx
  obtain ⟨i, rfl⟩ := Fin.eq_succ_of_ne_zero hj
  apply le_antisymm
  · simpa [hjzero] using zeroHornMinimum_le_weight_succ n x i
  · exact zeroHornMinimum_nonneg n x

/-- The zero-horn endpoint fixes every point already lying in the horn. -/
theorem zeroHornRetractionPoint_eq_self_of_mem (n : ℕ)
    {x : StandardSimplex (n + 1)} (hx : x ∈ standardSimplexZeroHorn n) :
    zeroHornRetractionPoint n x = x := by
  have hmin := zeroHornMinimum_eq_zero_of_mem n hx
  ext j
  obtain rfl | ⟨i, rfl⟩ := Fin.eq_zero_or_eq_succ j
  · simp [hmin]
  · simp [hmin]

/-- The canonical inclusion of the zero horn into its ambient successor
simplex. -/
def standardSimplexZeroHornInclusion (n : ℕ) :
    C(standardSimplexZeroHorn n, StandardSimplex (n + 1)) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- Subtract the least positive-index coordinate and restrict the result to
the zero horn. -/
def zeroHornRetraction (n : ℕ) :
    C(StandardSimplex (n + 1), standardSimplexZeroHorn n) where
  toFun x := ⟨zeroHornRetractionPoint n x,
    zeroHornRetractionPoint_mem_zeroHorn n x⟩
  continuous_toFun := (continuous_zeroHornRetractionPoint n).subtype_mk _

@[simp]
theorem zeroHornRetraction_coe (n : ℕ) (x : StandardSimplex (n + 1)) :
    (zeroHornRetraction n x : StandardSimplex (n + 1)) =
      zeroHornRetractionPoint n x :=
  rfl

/-- Linear interpolation from a simplex point to its zero-horn endpoint. -/
def zeroHornDeformationPoint (n : ℕ)
    (tx : unitInterval × StandardSimplex (n + 1)) :
    StandardSimplex (n + 1) :=
  Convexity.convexCombPair (R := ℝ)
    (unitInterval.symm tx.1) tx.1
    (unitInterval.nonneg _) (unitInterval.nonneg _) (by simp)
    tx.2 (zeroHornRetractionPoint n tx.2)

theorem continuous_zeroHornDeformationPoint (n : ℕ) :
    Continuous (zeroHornDeformationPoint n) := by
  rw [(Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ
    (Fin (n + 2))).continuous_iff]
  unfold Function.comp
  apply continuous_pi
  intro j
  simp only [zeroHornDeformationPoint,
    Convexity.StdSimplex.weights_convexCombPair,
    Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, unitInterval.coe_symm_eq]
  have ht : Continuous
      (fun tx : unitInterval × StandardSimplex (n + 1) ↦ (tx.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hx : Continuous
      (fun tx : unitInterval × StandardSimplex (n + 1) ↦ tx.2.weights j) :=
    (Convexity.StdSimplex.continuous_weights_apply ℝ j).comp continuous_snd
  have hr : Continuous
      (fun tx : unitInterval × StandardSimplex (n + 1) ↦
        (zeroHornRetractionPoint n tx.2).weights j) :=
    (Convexity.StdSimplex.continuous_weights_apply ℝ j).comp
      ((continuous_zeroHornRetractionPoint n).comp continuous_snd)
  exact ((continuous_const.sub ht).mul hx).add (ht.mul hr)

@[simp]
theorem zeroHornDeformationPoint_zero (n : ℕ)
    (x : StandardSimplex (n + 1)) :
    zeroHornDeformationPoint n (0, x) = x := by
  simp [zeroHornDeformationPoint]

@[simp]
theorem zeroHornDeformationPoint_one (n : ℕ)
    (x : StandardSimplex (n + 1)) :
    zeroHornDeformationPoint n (1, x) = zeroHornRetractionPoint n x := by
  simp [zeroHornDeformationPoint]

theorem zeroHornDeformationPoint_eq_self_of_mem (n : ℕ)
    (t : unitInterval) {x : StandardSimplex (n + 1)}
    (hx : x ∈ standardSimplexZeroHorn n) :
    zeroHornDeformationPoint n (t, x) = x := by
  rw [zeroHornDeformationPoint,
    zeroHornRetractionPoint_eq_self_of_mem n hx]
  simp

/-- The barycentric interpolation is a deformation of the identity to the
zero-horn retraction and is pointwise fixed on the horn. -/
def zeroHornDeformation (n : ℕ) :
    (ContinuousMap.id (StandardSimplex (n + 1))).HomotopyRel
      ((standardSimplexZeroHornInclusion n).comp (zeroHornRetraction n))
      (Set.range (standardSimplexZeroHornInclusion n)) where
  toFun tx := zeroHornDeformationPoint n tx
  continuous_toFun := continuous_zeroHornDeformationPoint n
  map_zero_left := zeroHornDeformationPoint_zero n
  map_one_left := zeroHornDeformationPoint_one n
  prop' t x hx := by
    obtain ⟨y, rfl⟩ := hx
    exact zeroHornDeformationPoint_eq_self_of_mem n t y.2

/-- Every successor standard simplex strongly deformation retracts onto its
zero horn by subtracting the least positive-index barycentric coordinate. -/
def zeroHornStrongDeformationRetract (n : ℕ) :
    Hatcher.StrongDeformationRetract
      (standardSimplexZeroHornInclusion n) where
  retract := zeroHornRetraction n
  retract_inclusion := by
    apply ContinuousMap.ext
    intro x
    apply Subtype.ext
    exact zeroHornRetractionPoint_eq_self_of_mem n x.2
  deformation := zeroHornDeformation n

end Hatcher.Simplex
