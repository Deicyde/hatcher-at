/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Hatcher.Singular.GoodPair
import Hatcher.Singular.StandardSimplexBoundaryHorn
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Topology.ContinuousMap.Lattice

/-!
# Good pairs from boundaries and zero horns of standard simplices

This file constructs the explicit good-pair witnesses used in Hatcher's
induction for the relative fundamental class of a standard simplex.
-/

noncomputable section

open CategoryTheory Set Topology
open scoped unitInterval

namespace Hatcher.Simplex

private noncomputable def minimumWeight (n : ℕ) :
    C(StandardSimplex n, ℝ) :=
  Finset.univ.inf' Finset.univ_nonempty fun (i : Fin (n + 1)) ↦
    ⟨fun x ↦ x.weights i,
      Convexity.StdSimplex.continuous_weights_apply (R := ℝ) i⟩

@[simp]
private lemma minimumWeight_apply (n : ℕ) (x : StandardSimplex n) :
    minimumWeight n x =
      Finset.univ.inf' Finset.univ_nonempty (fun i ↦ x.weights i) := by
  simp [minimumWeight, ContinuousMap.inf'_apply]

private lemma minimumWeight_nonneg (n : ℕ) (x : StandardSimplex n) :
    0 ≤ minimumWeight n x := by
  rw [minimumWeight_apply]
  exact Finset.le_inf' _ _ fun _ _ ↦ x.weights_nonneg _

private lemma minimumWeight_le (n : ℕ) (x : StandardSimplex n)
    (i : Fin (n + 1)) :
    minimumWeight n x ≤ x.weights i := by
  rw [minimumWeight_apply]
  exact Finset.inf'_le _ (Finset.mem_univ i)

private lemma exists_weight_eq_minimumWeight (n : ℕ)
    (x : StandardSimplex n) :
    ∃ i : Fin (n + 1), x.weights i = minimumWeight n x := by
  rw [minimumWeight_apply]
  obtain ⟨i, _, hi⟩ :=
    Finset.exists_mem_eq_inf' Finset.univ_nonempty (fun i ↦ x.weights i)
  exact ⟨i, hi.symm⟩

private lemma mem_boundary_iff_minimumWeight_eq_zero (n : ℕ)
    (x : StandardSimplex n) :
    x ∈ standardSimplexBoundary n ↔ minimumWeight n x = 0 := by
  constructor
  · rintro ⟨i, hi⟩
    exact le_antisymm (hi ▸ minimumWeight_le n x i)
      (minimumWeight_nonneg n x)
  · intro h
    obtain ⟨i, hi⟩ := exists_weight_eq_minimumWeight n x
    exact ⟨i, hi.trans h⟩

/-- The standard open neighborhood of the boundary of a positive-dimensional
simplex.  It is the complement of the barycenter, expressed by saying that
the least barycentric coordinate is strictly smaller than their average. -/
def standardSimplexBoundaryNeighborhood (n : ℕ) :
    Set (StandardSimplex (n + 1)) :=
  {x | minimumWeight (n + 1) x < ((n + 2 : ℕ) : ℝ)⁻¹}

private lemma isOpen_standardSimplexBoundaryNeighborhood (n : ℕ) :
    IsOpen (standardSimplexBoundaryNeighborhood n) :=
  isOpen_lt (minimumWeight (n + 1)).continuous continuous_const

private lemma range_standardSimplexPair_map (n : ℕ) :
    Set.range (standardSimplexPair n).map = standardSimplexBoundary n := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact a.2
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

private lemma standardSimplexBoundary_isClosed (n : ℕ) :
    IsClosed (standardSimplexBoundary n) := by
  have hset : standardSimplexBoundary n =
      minimumWeight n ⁻¹' ({0} : Set ℝ) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact mem_boundary_iff_minimumWeight_eq_zero n x
  rw [hset]
  exact isClosed_singleton.preimage (minimumWeight n).continuous

private lemma standardSimplexBoundary_nonempty (n : ℕ) :
    Nonempty (standardSimplexBoundary (n + 1)) := by
  let x : StandardSimplex (n + 1) :=
    Convexity.StdSimplex.single (R := ℝ) (0 : Fin (n + 2))
  exact ⟨⟨x, ⟨1, by simp [x]⟩⟩⟩

private lemma standardSimplexBoundary_subset_neighborhood (n : ℕ) :
    standardSimplexBoundary (n + 1) ⊆
      standardSimplexBoundaryNeighborhood n := by
  intro x hx
  change minimumWeight (n + 1) x < ((n + 2 : ℕ) : ℝ)⁻¹
  rw [show minimumWeight (n + 1) x = 0 from
    (mem_boundary_iff_minimumWeight_eq_zero (n + 1) x).mp hx]
  positivity

private lemma range_standardSimplexPair_subset_interior_neighborhood (n : ℕ) :
    Set.range (standardSimplexPair (n + 1)).map ⊆
      interior (standardSimplexBoundaryNeighborhood n) := by
  intro x hx
  change (x : StandardSimplex (n + 1)) ∈
    interior (standardSimplexBoundaryNeighborhood n)
  rw [(isOpen_standardSimplexBoundaryNeighborhood n).interior_eq]
  apply standardSimplexBoundary_subset_neighborhood n
  rcases hx with ⟨a, rfl⟩
  exact a.2

private lemma boundary_card_pos (n : ℕ) :
    0 < ((n + 2 : ℕ) : ℝ) := by positivity

private lemma boundary_card_mul_minimum_lt_one (n : ℕ)
    (x : standardSimplexBoundaryNeighborhood n) :
    ((n + 2 : ℕ) : ℝ) * minimumWeight (n + 1) x.1 < 1 := by
  calc
    ((n + 2 : ℕ) : ℝ) * minimumWeight (n + 1) x.1 <
        ((n + 2 : ℕ) : ℝ) * ((n + 2 : ℕ) : ℝ)⁻¹ :=
      mul_lt_mul_of_pos_left x.2 (boundary_card_pos n)
    _ = 1 := mul_inv_cancel₀ (boundary_card_pos n).ne'

private def boundaryDeformationDenominator (n : ℕ)
    (p : unitInterval × standardSimplexBoundaryNeighborhood n) : ℝ :=
  1 - (p.1 : ℝ) *
    (((n + 2 : ℕ) : ℝ) * minimumWeight (n + 1) p.2.1)

private lemma boundaryDeformationDenominator_pos (n : ℕ)
    (p : unitInterval × standardSimplexBoundaryNeighborhood n) :
    0 < boundaryDeformationDenominator n p := by
  have hm : 0 ≤ minimumWeight (n + 1) p.2.1 :=
    minimumWeight_nonneg (n + 1) p.2.1
  have hkm : 0 ≤ ((n + 2 : ℕ) : ℝ) *
      minimumWeight (n + 1) p.2.1 :=
    mul_nonneg (boundary_card_pos n).le hm
  have ht : (p.1 : ℝ) *
      (((n + 2 : ℕ) : ℝ) * minimumWeight (n + 1) p.2.1) ≤
      ((n + 2 : ℕ) : ℝ) * minimumWeight (n + 1) p.2.1 :=
    mul_le_of_le_one_left hkm p.1.2.2
  unfold boundaryDeformationDenominator
  linarith [boundary_card_mul_minimum_lt_one n p.2]

private def boundaryDeformationCoordinate (n : ℕ)
    (p : unitInterval × standardSimplexBoundaryNeighborhood n)
    (i : Fin (n + 2)) : ℝ :=
  (p.2.1.weights i - (p.1 : ℝ) * minimumWeight (n + 1) p.2.1) /
    boundaryDeformationDenominator n p

private lemma boundaryDeformationCoordinate_nonneg (n : ℕ)
    (p : unitInterval × standardSimplexBoundaryNeighborhood n)
    (i : Fin (n + 2)) :
    0 ≤ boundaryDeformationCoordinate n p i := by
  apply div_nonneg
  · apply sub_nonneg.mpr
    calc
      (p.1 : ℝ) * minimumWeight (n + 1) p.2.1 ≤
          minimumWeight (n + 1) p.2.1 :=
        mul_le_of_le_one_left (minimumWeight_nonneg (n + 1) p.2.1)
          p.1.2.2
      _ ≤ p.2.1.weights i := minimumWeight_le (n + 1) p.2.1 i
  · exact (boundaryDeformationDenominator_pos n p).le

private def boundaryDeformationPoint (n : ℕ)
    (p : unitInterval × standardSimplexBoundaryNeighborhood n) :
    StandardSimplex (n + 1) where
  weights := Finsupp.equivFunOnFinite.symm (boundaryDeformationCoordinate n p)
  nonneg := by
    intro i
    change 0 ≤ boundaryDeformationCoordinate n p i
    exact boundaryDeformationCoordinate_nonneg n p i
  total := by
    rw [Finsupp.equivFunOnFinite_symm_sum]
    simp only [boundaryDeformationCoordinate]
    rw [← Finset.sum_div, Finset.sum_sub_distrib,
      p.2.1.total_of_fintype]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    have hnum :
        1 - ((n + 2 : ℕ) : ℝ) *
              ((p.1 : ℝ) * minimumWeight (n + 1) p.2.1) =
          boundaryDeformationDenominator n p := by
      unfold boundaryDeformationDenominator
      ring
    rw [hnum, div_self (boundaryDeformationDenominator_pos n p).ne']

@[simp]
private lemma boundaryDeformationPoint_weights (n : ℕ)
    (p : unitInterval × standardSimplexBoundaryNeighborhood n)
    (i : Fin (n + 2)) :
    (boundaryDeformationPoint n p).weights i =
      boundaryDeformationCoordinate n p i := by
  rfl

private lemma boundaryDeformationCoordinate_at_min_lt_average (n : ℕ)
    (p : unitInterval × standardSimplexBoundaryNeighborhood n)
    (i : Fin (n + 2))
    (hi : p.2.1.weights i = minimumWeight (n + 1) p.2.1) :
    boundaryDeformationCoordinate n p i < ((n + 2 : ℕ) : ℝ)⁻¹ := by
  let k : ℝ := ((n + 2 : ℕ) : ℝ)
  let m : ℝ := minimumWeight (n + 1) p.2.1
  let t : ℝ := p.1
  have hk : 0 < k := boundary_card_pos n
  have hkm : k * m < 1 := boundary_card_mul_minimum_lt_one n p.2
  have hd : 0 < boundaryDeformationDenominator n p :=
    boundaryDeformationDenominator_pos n p
  have hscaled : (p.2.1.weights i - t * m) * k <
      boundaryDeformationDenominator n p := by
    rw [hi]
    dsimp [t, m, k]
    unfold boundaryDeformationDenominator
    nlinarith
  have hdiv : p.2.1.weights i - t * m <
      boundaryDeformationDenominator n p / k :=
    (lt_div_iff₀ hk).2 hscaled
  have havg : boundaryDeformationDenominator n p / k =
      k⁻¹ * boundaryDeformationDenominator n p := by
    field_simp [hk.ne']
  rw [boundaryDeformationCoordinate, div_lt_iff₀ hd, ← havg]
  exact hdiv

private lemma boundaryDeformationPoint_mem_neighborhood (n : ℕ)
    (p : unitInterval × standardSimplexBoundaryNeighborhood n) :
    boundaryDeformationPoint n p ∈ standardSimplexBoundaryNeighborhood n := by
  obtain ⟨i, hi⟩ := exists_weight_eq_minimumWeight (n + 1) p.2.1
  change minimumWeight (n + 1) (boundaryDeformationPoint n p) <
    ((n + 2 : ℕ) : ℝ)⁻¹
  calc
    minimumWeight (n + 1) (boundaryDeformationPoint n p) ≤
        (boundaryDeformationPoint n p).weights i :=
      minimumWeight_le (n + 1) _ i
    _ = boundaryDeformationCoordinate n p i := rfl
    _ < ((n + 2 : ℕ) : ℝ)⁻¹ :=
      boundaryDeformationCoordinate_at_min_lt_average n p i hi

private theorem continuous_boundaryDeformationPoint (n : ℕ) :
    Continuous (boundaryDeformationPoint n) := by
  rw [(Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ
    (Fin (n + 2))).continuous_iff]
  rw [continuous_pi_iff]
  intro i
  change Continuous (fun p :
      unitInterval × standardSimplexBoundaryNeighborhood n ↦
    boundaryDeformationCoordinate n p i)
  have ht : Continuous (fun p :
      unitInterval × standardSimplexBoundaryNeighborhood n ↦ (p.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hx : Continuous (fun p :
      unitInterval × standardSimplexBoundaryNeighborhood n ↦
      p.2.1.weights i) :=
    (Convexity.StdSimplex.continuous_weights_apply (R := ℝ) i).comp
      (continuous_subtype_val.comp continuous_snd)
  have hm : Continuous (fun p :
      unitInterval × standardSimplexBoundaryNeighborhood n ↦
      minimumWeight (n + 1) p.2.1) :=
    (minimumWeight (n + 1)).continuous.comp
      (continuous_subtype_val.comp continuous_snd)
  have hd : Continuous (fun p :
      unitInterval × standardSimplexBoundaryNeighborhood n ↦
      boundaryDeformationDenominator n p) := by
    unfold boundaryDeformationDenominator
    fun_prop
  unfold boundaryDeformationCoordinate
  exact (hx.sub (ht.mul hm)).div hd fun p ↦
    (boundaryDeformationDenominator_pos n p).ne'

private def boundaryDeformationMap (n : ℕ) :
    unitInterval × standardSimplexBoundaryNeighborhood n →
      standardSimplexBoundaryNeighborhood n :=
  fun p ↦ ⟨boundaryDeformationPoint n p,
    boundaryDeformationPoint_mem_neighborhood n p⟩

private theorem continuous_boundaryDeformationMap (n : ℕ) :
    Continuous (boundaryDeformationMap n) :=
  (continuous_boundaryDeformationPoint n).subtype_mk _

private lemma boundaryDeformationPoint_zero (n : ℕ)
    (x : standardSimplexBoundaryNeighborhood n) :
    boundaryDeformationPoint n (0, x) = x.1 := by
  apply Convexity.StdSimplex.ext
  apply Finsupp.ext
  intro i
  simp [boundaryDeformationCoordinate, boundaryDeformationDenominator]

private lemma boundaryDeformationPoint_eq_self_of_mem_boundary (n : ℕ)
    (t : unitInterval) (x : standardSimplexBoundaryNeighborhood n)
    (hx : x.1 ∈ standardSimplexBoundary (n + 1)) :
    boundaryDeformationPoint n (t, x) = x.1 := by
  have hm : minimumWeight (n + 1) x.1 = 0 :=
    (mem_boundary_iff_minimumWeight_eq_zero (n + 1) x.1).mp hx
  apply Convexity.StdSimplex.ext
  apply Finsupp.ext
  intro i
  simp [boundaryDeformationCoordinate, boundaryDeformationDenominator, hm]

private lemma boundaryDeformationPoint_one_mem_boundary (n : ℕ)
    (x : standardSimplexBoundaryNeighborhood n) :
    boundaryDeformationPoint n (1, x) ∈ standardSimplexBoundary (n + 1) := by
  obtain ⟨i, hi⟩ := exists_weight_eq_minimumWeight (n + 1) x.1
  refine ⟨i, ?_⟩
  simp [boundaryDeformationCoordinate, hi]

private def boundaryRetraction (n : ℕ) :
    C(standardSimplexBoundaryNeighborhood n,
      standardSimplexBoundary (n + 1)) where
  toFun x := ⟨boundaryDeformationPoint n (1, x),
    boundaryDeformationPoint_one_mem_boundary n x⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_boundaryDeformationPoint n).comp
      (continuous_const.prodMk continuous_id)

private def boundaryNeighborhoodInclusion (n : ℕ) :
    C(standardSimplexBoundary (n + 1),
      standardSimplexBoundaryNeighborhood n) :=
  Hatcher.Relative.goodPairNeighborhoodInclusion
    (standardSimplexPair (n + 1))
    (standardSimplexBoundaryNeighborhood n)
    ((range_standardSimplexPair_subset_interior_neighborhood n).trans
      interior_subset)

private lemma boundaryRetraction_inclusion (n : ℕ) :
    (boundaryRetraction n).comp (boundaryNeighborhoodInclusion n) =
      ContinuousMap.id (standardSimplexBoundary (n + 1)) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  exact boundaryDeformationPoint_eq_self_of_mem_boundary n 1
    ⟨x.1, standardSimplexBoundary_subset_neighborhood n x.2⟩ x.2

private def boundaryDeformation (n : ℕ) :
    (ContinuousMap.id (standardSimplexBoundaryNeighborhood n)).HomotopyRel
      ((boundaryNeighborhoodInclusion n).comp (boundaryRetraction n))
      (Set.range (boundaryNeighborhoodInclusion n)) where
  toFun := boundaryDeformationMap n
  continuous_toFun := continuous_boundaryDeformationMap n
  map_zero_left x := by
    apply Subtype.ext
    exact boundaryDeformationPoint_zero n x
  map_one_left x := by
    rfl
  prop' t x hx := by
    obtain ⟨a, rfl⟩ := hx
    apply Subtype.ext
    exact boundaryDeformationPoint_eq_self_of_mem_boundary n t
      ⟨a.1, standardSimplexBoundary_subset_neighborhood n a.2⟩ a.2

private def standardSimplexBoundaryStrongDeformationRetract (n : ℕ) :
    Hatcher.StrongDeformationRetract (boundaryNeighborhoodInclusion n) where
  retract := boundaryRetraction n
  retract_inclusion := boundaryRetraction_inclusion n
  deformation := boundaryDeformation n

/-- The boundary of every positive-dimensional standard simplex is a good
subspace.  The index `n` describes the pair `(Δ[n+1], ∂Δ[n+1])`, so the
empty boundary of `Δ[0]` is deliberately excluded. -/
def standardSimplexBoundaryGoodPairData (n : ℕ) :
    Hatcher.Relative.GoodPairData (standardSimplexPair (n + 1)) where
  nonempty := standardSimplexBoundary_nonempty n
  isClosed_range := by
    rw [range_standardSimplexPair_map]
    exact standardSimplexBoundary_isClosed (n + 1)
  V := standardSimplexBoundaryNeighborhood n
  range_subset_interior :=
    range_standardSimplexPair_subset_interior_neighborhood n
  strongDeformationRetract := standardSimplexBoundaryStrongDeformationRetract n

private noncomputable def positiveMinimumWeight (n : ℕ) :
    C(standardSimplexBoundary (n + 1), ℝ) :=
  Finset.univ.inf' Finset.univ_nonempty fun (i : Fin (n + 1)) ↦
    ⟨fun x ↦ x.1.weights i.succ,
      (Convexity.StdSimplex.continuous_weights_apply (R := ℝ) i.succ).comp
        continuous_subtype_val⟩

@[simp]
private lemma positiveMinimumWeight_apply (n : ℕ)
    (x : standardSimplexBoundary (n + 1)) :
    positiveMinimumWeight n x =
      Finset.univ.inf' Finset.univ_nonempty
        (fun i : Fin (n + 1) ↦ x.1.weights i.succ) := by
  simp [positiveMinimumWeight, ContinuousMap.inf'_apply]

private lemma positiveMinimumWeight_nonneg (n : ℕ)
    (x : standardSimplexBoundary (n + 1)) :
    0 ≤ positiveMinimumWeight n x := by
  rw [positiveMinimumWeight_apply]
  exact Finset.le_inf' _ _ fun _ _ ↦ x.1.weights_nonneg _

private lemma positiveMinimumWeight_le (n : ℕ)
    (x : standardSimplexBoundary (n + 1)) (i : Fin (n + 1)) :
    positiveMinimumWeight n x ≤ x.1.weights i.succ := by
  rw [positiveMinimumWeight_apply]
  exact Finset.inf'_le _ (Finset.mem_univ i)

private lemma exists_positive_weight_eq_positiveMinimumWeight (n : ℕ)
    (x : standardSimplexBoundary (n + 1)) :
    ∃ i : Fin (n + 1), x.1.weights i.succ = positiveMinimumWeight n x := by
  rw [positiveMinimumWeight_apply]
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty
    (fun i : Fin (n + 1) ↦ x.1.weights i.succ)
  exact ⟨i, hi.symm⟩

private lemma mem_zeroHorn_iff_positiveMinimumWeight_eq_zero (n : ℕ)
    (x : standardSimplexBoundary (n + 1)) :
    x.1 ∈ standardSimplexZeroHorn n ↔ positiveMinimumWeight n x = 0 := by
  constructor
  · rintro ⟨j, hj, hjzero⟩
    obtain rfl | ⟨i, rfl⟩ := j.eq_zero_or_eq_succ
    · exact (hj rfl).elim
    · exact le_antisymm (hjzero ▸ positiveMinimumWeight_le n x i)
        (positiveMinimumWeight_nonneg n x)
  · intro h
    obtain ⟨i, hi⟩ := exists_positive_weight_eq_positiveMinimumWeight n x
    exact ⟨i.succ, by simp, hi.trans h⟩

/-- The open neighborhood of the zero horn inside the boundary.  It removes
the barycenter of the omitted zero face by requiring the least positive-index
coordinate to be smaller than the positive coordinates' average. -/
def boundaryZeroHornNeighborhood (n : ℕ) :
    Set (standardSimplexBoundary (n + 1)) :=
  {x | positiveMinimumWeight n x < ((n + 1 : ℕ) : ℝ)⁻¹}

private lemma isOpen_boundaryZeroHornNeighborhood (n : ℕ) :
    IsOpen (boundaryZeroHornNeighborhood n) :=
  isOpen_lt (positiveMinimumWeight n).continuous continuous_const

private lemma zeroHorn_subset_boundaryNeighborhood (n : ℕ) :
    {x : standardSimplexBoundary (n + 1) |
      x.1 ∈ standardSimplexZeroHorn n} ⊆ boundaryZeroHornNeighborhood n := by
  intro x hx
  change positiveMinimumWeight n x < ((n + 1 : ℕ) : ℝ)⁻¹
  rw [(mem_zeroHorn_iff_positiveMinimumWeight_eq_zero n x).mp hx]
  positivity

private lemma range_boundaryZeroHornPair_map (n : ℕ) :
    Set.range
        (Hatcher.Relative.TopTriple.pairAB.obj
          (standardSimplexBoundaryHornTriple n)).map =
      {x : standardSimplexBoundary (n + 1) |
        x.1 ∈ standardSimplexZeroHorn n} := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact a.2
  · intro hx
    exact ⟨⟨x.1, hx⟩, rfl⟩

private lemma boundaryZeroHorn_nonempty (n : ℕ) :
    Nonempty (standardSimplexZeroHorn n) := by
  let x : StandardSimplex (n + 1) :=
    Convexity.StdSimplex.single (R := ℝ) (0 : Fin (n + 2))
  exact ⟨⟨x, ⟨1, by simp, by simp [x]⟩⟩⟩

private lemma range_boundaryZeroHornPair_isClosed (n : ℕ) :
    IsClosed (Set.range
      (Hatcher.Relative.TopTriple.pairAB.obj
        (standardSimplexBoundaryHornTriple n)).map) := by
  rw [range_boundaryZeroHornPair_map]
  have hset : {x : standardSimplexBoundary (n + 1) |
      x.1 ∈ standardSimplexZeroHorn n} =
      positiveMinimumWeight n ⁻¹' ({0} : Set ℝ) := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff]
    exact mem_zeroHorn_iff_positiveMinimumWeight_eq_zero n x
  rw [hset]
  exact isClosed_singleton.preimage (positiveMinimumWeight n).continuous

private lemma range_boundaryZeroHornPair_subset_interior_neighborhood (n : ℕ) :
    Set.range
        (Hatcher.Relative.TopTriple.pairAB.obj
          (standardSimplexBoundaryHornTriple n)).map ⊆
      interior (boundaryZeroHornNeighborhood n) := by
  intro x hx
  change (x : standardSimplexBoundary (n + 1)) ∈
    interior (boundaryZeroHornNeighborhood n)
  rw [(isOpen_boundaryZeroHornNeighborhood n).interior_eq]
  apply zeroHorn_subset_boundaryNeighborhood n
  rcases hx with ⟨a, rfl⟩
  exact a.2

private lemma positive_card_pos (n : ℕ) :
    0 < ((n + 1 : ℕ) : ℝ) := by positivity

private lemma positive_card_mul_minimum_lt_one (n : ℕ)
    (x : boundaryZeroHornNeighborhood n) :
    ((n + 1 : ℕ) : ℝ) * positiveMinimumWeight n x.1 < 1 := by
  calc
    ((n + 1 : ℕ) : ℝ) * positiveMinimumWeight n x.1 <
        ((n + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ)⁻¹ :=
      mul_lt_mul_of_pos_left x.2 (positive_card_pos n)
    _ = 1 := mul_inv_cancel₀ (positive_card_pos n).ne'

private def hornDeformationDenominator (n : ℕ)
    (p : unitInterval × boundaryZeroHornNeighborhood n) : ℝ :=
  1 - (p.1 : ℝ) *
    (((n + 1 : ℕ) : ℝ) * positiveMinimumWeight n p.2.1)

private lemma hornDeformationDenominator_pos (n : ℕ)
    (p : unitInterval × boundaryZeroHornNeighborhood n) :
    0 < hornDeformationDenominator n p := by
  have hm : 0 ≤ positiveMinimumWeight n p.2.1 :=
    positiveMinimumWeight_nonneg n p.2.1
  have hkm : 0 ≤ ((n + 1 : ℕ) : ℝ) * positiveMinimumWeight n p.2.1 :=
    mul_nonneg (positive_card_pos n).le hm
  have ht : (p.1 : ℝ) *
      (((n + 1 : ℕ) : ℝ) * positiveMinimumWeight n p.2.1) ≤
      ((n + 1 : ℕ) : ℝ) * positiveMinimumWeight n p.2.1 :=
    mul_le_of_le_one_left hkm p.1.2.2
  unfold hornDeformationDenominator
  linarith [positive_card_mul_minimum_lt_one n p.2]

private def hornDeformationCoordinate (n : ℕ)
    (p : unitInterval × boundaryZeroHornNeighborhood n) :
    Fin (n + 2) → ℝ :=
  Fin.cases
    (p.2.1.1.weights 0 / hornDeformationDenominator n p)
    (fun i ↦
      (p.2.1.1.weights i.succ -
          (p.1 : ℝ) * positiveMinimumWeight n p.2.1) /
        hornDeformationDenominator n p)

private lemma hornDeformationCoordinate_nonneg (n : ℕ)
    (p : unitInterval × boundaryZeroHornNeighborhood n)
    (j : Fin (n + 2)) :
    0 ≤ hornDeformationCoordinate n p j := by
  refine Fin.cases ?_ (fun i ↦ ?_) j
  · exact div_nonneg (p.2.1.1.weights_nonneg 0)
      (hornDeformationDenominator_pos n p).le
  · apply div_nonneg
    · apply sub_nonneg.mpr
      calc
        (p.1 : ℝ) * positiveMinimumWeight n p.2.1 ≤
            positiveMinimumWeight n p.2.1 :=
          mul_le_of_le_one_left (positiveMinimumWeight_nonneg n p.2.1)
            p.1.2.2
        _ ≤ p.2.1.1.weights i.succ :=
          positiveMinimumWeight_le n p.2.1 i
    · exact (hornDeformationDenominator_pos n p).le

private def hornDeformationSimplexPoint (n : ℕ)
    (p : unitInterval × boundaryZeroHornNeighborhood n) :
    StandardSimplex (n + 1) where
  weights := Finsupp.equivFunOnFinite.symm (hornDeformationCoordinate n p)
  nonneg := by
    intro j
    change 0 ≤ hornDeformationCoordinate n p j
    exact hornDeformationCoordinate_nonneg n p j
  total := by
    rw [Finsupp.equivFunOnFinite_symm_sum, Fin.sum_univ_succ]
    simp only [hornDeformationCoordinate, Fin.cases_zero, Fin.cases_succ]
    rw [← Finset.sum_div, ← add_div, Finset.sum_sub_distrib]
    have htotal : p.2.1.1.weights 0 +
        ∑ i : Fin (n + 1), p.2.1.1.weights i.succ = 1 := by
      simpa only [Fin.sum_univ_succ] using p.2.1.1.total_of_fintype
    rw [show p.2.1.1.weights 0 +
          ((∑ i : Fin (n + 1), p.2.1.1.weights i.succ) -
            ∑ _i : Fin (n + 1),
              (p.1 : ℝ) * positiveMinimumWeight n p.2.1) =
        1 - ∑ _i : Fin (n + 1),
          (p.1 : ℝ) * positiveMinimumWeight n p.2.1 by
      rw [← htotal]
      ring]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    have hnum :
        1 - ((n + 1 : ℕ) : ℝ) *
              ((p.1 : ℝ) * positiveMinimumWeight n p.2.1) =
          hornDeformationDenominator n p := by
      unfold hornDeformationDenominator
      ring
    rw [hnum, div_self (hornDeformationDenominator_pos n p).ne']

@[simp]
private lemma hornDeformationSimplexPoint_weights (n : ℕ)
    (p : unitInterval × boundaryZeroHornNeighborhood n)
    (j : Fin (n + 2)) :
    (hornDeformationSimplexPoint n p).weights j =
      hornDeformationCoordinate n p j := by
  rfl

private lemma hornDeformationSimplexPoint_mem_boundary (n : ℕ)
    (p : unitInterval × boundaryZeroHornNeighborhood n) :
    hornDeformationSimplexPoint n p ∈ standardSimplexBoundary (n + 1) := by
  obtain ⟨j, hj⟩ := p.2.1.2
  obtain rfl | ⟨i, rfl⟩ := j.eq_zero_or_eq_succ
  · refine ⟨0, ?_⟩
    simp [hornDeformationCoordinate, hj]
  · have hm : positiveMinimumWeight n p.2.1 = 0 :=
      le_antisymm (hj ▸ positiveMinimumWeight_le n p.2.1 i)
        (positiveMinimumWeight_nonneg n p.2.1)
    refine ⟨i.succ, ?_⟩
    simp [hornDeformationCoordinate, hj, hm]

private def hornDeformationBoundaryPoint (n : ℕ)
    (p : unitInterval × boundaryZeroHornNeighborhood n) :
    standardSimplexBoundary (n + 1) :=
  ⟨hornDeformationSimplexPoint n p,
    hornDeformationSimplexPoint_mem_boundary n p⟩

private lemma hornDeformationCoordinate_at_min_lt_average (n : ℕ)
    (p : unitInterval × boundaryZeroHornNeighborhood n)
    (i : Fin (n + 1))
    (hi : p.2.1.1.weights i.succ = positiveMinimumWeight n p.2.1) :
    hornDeformationCoordinate n p i.succ < ((n + 1 : ℕ) : ℝ)⁻¹ := by
  let k : ℝ := ((n + 1 : ℕ) : ℝ)
  let m : ℝ := positiveMinimumWeight n p.2.1
  let t : ℝ := p.1
  have hk : 0 < k := positive_card_pos n
  have hkm : k * m < 1 := positive_card_mul_minimum_lt_one n p.2
  have hd : 0 < hornDeformationDenominator n p :=
    hornDeformationDenominator_pos n p
  have hscaled : (p.2.1.1.weights i.succ - t * m) * k <
      hornDeformationDenominator n p := by
    rw [hi]
    dsimp [t, m, k]
    unfold hornDeformationDenominator
    nlinarith
  have hdiv : p.2.1.1.weights i.succ - t * m <
      hornDeformationDenominator n p / k :=
    (lt_div_iff₀ hk).2 hscaled
  have havg : hornDeformationDenominator n p / k =
      k⁻¹ * hornDeformationDenominator n p := by
    field_simp [hk.ne']
  rw [hornDeformationCoordinate, Fin.cases_succ,
    div_lt_iff₀ hd, ← havg]
  exact hdiv

private lemma hornDeformationBoundaryPoint_mem_neighborhood (n : ℕ)
    (p : unitInterval × boundaryZeroHornNeighborhood n) :
    hornDeformationBoundaryPoint n p ∈ boundaryZeroHornNeighborhood n := by
  obtain ⟨i, hi⟩ :=
    exists_positive_weight_eq_positiveMinimumWeight n p.2.1
  change positiveMinimumWeight n (hornDeformationBoundaryPoint n p) <
    ((n + 1 : ℕ) : ℝ)⁻¹
  calc
    positiveMinimumWeight n (hornDeformationBoundaryPoint n p) ≤
        (hornDeformationBoundaryPoint n p).1.weights i.succ :=
      positiveMinimumWeight_le n _ i
    _ = hornDeformationCoordinate n p i.succ := rfl
    _ < ((n + 1 : ℕ) : ℝ)⁻¹ :=
      hornDeformationCoordinate_at_min_lt_average n p i hi

private theorem continuous_hornDeformationSimplexPoint (n : ℕ) :
    Continuous (hornDeformationSimplexPoint n) := by
  rw [(Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ
    (Fin (n + 2))).continuous_iff]
  rw [continuous_pi_iff]
  intro j
  change Continuous (fun p : unitInterval × boundaryZeroHornNeighborhood n ↦
    hornDeformationCoordinate n p j)
  have ht : Continuous (fun p : unitInterval × boundaryZeroHornNeighborhood n ↦
      (p.1 : ℝ)) := continuous_subtype_val.comp continuous_fst
  have hx (j : Fin (n + 2)) :
      Continuous (fun p : unitInterval × boundaryZeroHornNeighborhood n ↦
        p.2.1.1.weights j) :=
    (Convexity.StdSimplex.continuous_weights_apply (R := ℝ) j).comp
      (continuous_subtype_val.comp
        (continuous_subtype_val.comp continuous_snd))
  have hm : Continuous (fun p : unitInterval × boundaryZeroHornNeighborhood n ↦
      positiveMinimumWeight n p.2.1) :=
    (positiveMinimumWeight n).continuous.comp
      (continuous_subtype_val.comp continuous_snd)
  have hd : Continuous (fun p : unitInterval × boundaryZeroHornNeighborhood n ↦
      hornDeformationDenominator n p) := by
    unfold hornDeformationDenominator
    fun_prop
  obtain rfl | ⟨i, rfl⟩ := j.eq_zero_or_eq_succ
  · exact (hx 0).div hd fun p ↦ (hornDeformationDenominator_pos n p).ne'
  · exact ((hx i.succ).sub (ht.mul hm)).div hd fun p ↦
      (hornDeformationDenominator_pos n p).ne'

private theorem continuous_hornDeformationBoundaryPoint (n : ℕ) :
    Continuous (hornDeformationBoundaryPoint n) :=
  (continuous_hornDeformationSimplexPoint n).subtype_mk _

private def hornDeformationMap (n : ℕ) :
    unitInterval × boundaryZeroHornNeighborhood n →
      boundaryZeroHornNeighborhood n :=
  fun p ↦ ⟨hornDeformationBoundaryPoint n p,
    hornDeformationBoundaryPoint_mem_neighborhood n p⟩

private theorem continuous_hornDeformationMap (n : ℕ) :
    Continuous (hornDeformationMap n) :=
  (continuous_hornDeformationBoundaryPoint n).subtype_mk _

private lemma hornDeformationSimplexPoint_zero (n : ℕ)
    (x : boundaryZeroHornNeighborhood n) :
    hornDeformationSimplexPoint n (0, x) = x.1.1 := by
  apply Convexity.StdSimplex.ext
  apply Finsupp.ext
  intro j
  obtain rfl | ⟨i, rfl⟩ := j.eq_zero_or_eq_succ
  · simp [hornDeformationCoordinate, hornDeformationDenominator]
  · simp [hornDeformationCoordinate, hornDeformationDenominator]

private lemma hornDeformationSimplexPoint_eq_self_of_mem_zeroHorn (n : ℕ)
    (t : unitInterval) (x : boundaryZeroHornNeighborhood n)
    (hx : x.1.1 ∈ standardSimplexZeroHorn n) :
    hornDeformationSimplexPoint n (t, x) = x.1.1 := by
  have hm : positiveMinimumWeight n x.1 = 0 :=
    (mem_zeroHorn_iff_positiveMinimumWeight_eq_zero n x.1).mp hx
  apply Convexity.StdSimplex.ext
  apply Finsupp.ext
  intro j
  obtain rfl | ⟨i, rfl⟩ := j.eq_zero_or_eq_succ
  · simp [hornDeformationCoordinate, hornDeformationDenominator, hm]
  · simp [hornDeformationCoordinate, hornDeformationDenominator, hm]

private lemma hornDeformationSimplexPoint_one_mem_zeroHorn (n : ℕ)
    (x : boundaryZeroHornNeighborhood n) :
    hornDeformationSimplexPoint n (1, x) ∈ standardSimplexZeroHorn n := by
  obtain ⟨i, hi⟩ :=
    exists_positive_weight_eq_positiveMinimumWeight n x.1
  refine ⟨i.succ, by simp, ?_⟩
  simp [hornDeformationCoordinate, hi]

private def hornRetraction (n : ℕ) :
    C(boundaryZeroHornNeighborhood n, standardSimplexZeroHorn n) where
  toFun x := ⟨hornDeformationSimplexPoint n (1, x),
    hornDeformationSimplexPoint_one_mem_zeroHorn n x⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_hornDeformationSimplexPoint n).comp
      (continuous_const.prodMk continuous_id)

private def hornNeighborhoodInclusion (n : ℕ) :
    C(standardSimplexZeroHorn n, boundaryZeroHornNeighborhood n) :=
  Hatcher.Relative.goodPairNeighborhoodInclusion
    (Hatcher.Relative.TopTriple.pairAB.obj
      (standardSimplexBoundaryHornTriple n))
    (boundaryZeroHornNeighborhood n)
    ((range_boundaryZeroHornPair_subset_interior_neighborhood n).trans
      interior_subset)

private lemma hornRetraction_inclusion (n : ℕ) :
    (hornRetraction n).comp (hornNeighborhoodInclusion n) =
      ContinuousMap.id (standardSimplexZeroHorn n) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  exact hornDeformationSimplexPoint_eq_self_of_mem_zeroHorn n 1
    ⟨⟨x.1, standardSimplexZeroHorn_subset_boundary n x.2⟩,
      zeroHorn_subset_boundaryNeighborhood n
        (a := ⟨x.1, standardSimplexZeroHorn_subset_boundary n x.2⟩) x.2⟩
    x.2

private def hornDeformation (n : ℕ) :
    (ContinuousMap.id (boundaryZeroHornNeighborhood n)).HomotopyRel
      ((hornNeighborhoodInclusion n).comp (hornRetraction n))
      (Set.range (hornNeighborhoodInclusion n)) where
  toFun := hornDeformationMap n
  continuous_toFun := continuous_hornDeformationMap n
  map_zero_left x := by
    apply Subtype.ext
    apply Subtype.ext
    exact hornDeformationSimplexPoint_zero n x
  map_one_left x := by
    rfl
  prop' t x hx := by
    obtain ⟨a, rfl⟩ := hx
    apply Subtype.ext
    apply Subtype.ext
    exact hornDeformationSimplexPoint_eq_self_of_mem_zeroHorn n t
      ⟨⟨a.1, standardSimplexZeroHorn_subset_boundary n a.2⟩,
        zeroHorn_subset_boundaryNeighborhood n
          (a := ⟨a.1, standardSimplexZeroHorn_subset_boundary n a.2⟩) a.2⟩
      a.2

private def boundaryZeroHornStrongDeformationRetract (n : ℕ) :
    Hatcher.StrongDeformationRetract (hornNeighborhoodInclusion n) where
  retract := hornRetraction n
  retract_inclusion := hornRetraction_inclusion n
  deformation := hornDeformation n

/-- In the boundary of `Δ[n+1]`, the zero horn is a good subspace.  The
chosen neighborhood removes the barycenter of the omitted zero face, and the
deformation subtracts the least positive-index barycentric coordinate. -/
def boundaryZeroHornGoodPairData (n : ℕ) :
    Hatcher.Relative.GoodPairData
      (Hatcher.Relative.TopTriple.pairAB.obj
        (standardSimplexBoundaryHornTriple n)) where
  nonempty := boundaryZeroHorn_nonempty n
  isClosed_range := range_boundaryZeroHornPair_isClosed n
  V := boundaryZeroHornNeighborhood n
  range_subset_interior :=
    range_boundaryZeroHornPair_subset_interior_neighborhood n
  strongDeformationRetract := boundaryZeroHornStrongDeformationRetract n

end Hatcher.Simplex
