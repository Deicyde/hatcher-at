/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Hatcher.Appendix.CellBoundaryCollar
import Hatcher.Appendix.SubcomplexIntersection
import Hatcher.Appendix.SuccessorSkeletonQuotient

/-!
# Regular neighborhoods of classical CW subcomplexes

This file carries out the fixed-width version of Hatcher's construction of
`Nε(A)`.  At a point in the open part of an `n`-cell, the construction either
keeps the point when it is in the inner half and the cell belongs to `A`, or,
in the outer half, asks whether its radial projection to the cell boundary
belongs to the neighborhood already constructed on the preceding skeleton.

The use of the same cutoff, `1 / 2`, for every subcomplex is what makes the
construction preserve intersections exactly.
-/

noncomputable section

open Metric Set Topology

namespace Hatcher.ClassicalCW

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X]
variable (C : Set X) [CWComplex C]

private abbrev CellModel (n : ℕ) := Fin n → ℝ

/-- The part of the regular neighborhood constructed through the cells of
dimension strictly less than `n`. -/
def regularNeighborhoodStage (A : CWComplex.Subcomplex C) : ℕ → Set X
  | 0 => ∅
  | n + 1 =>
      regularNeighborhoodStage A n ∪
        ⋃ i : Topology.CWComplex.cell C n,
          Topology.CWComplex.map n i ''
            {z : CellModel n |
              z ∈ ball 0 1 ∧
                if (1 / 2 : ℝ) < ‖z‖ then
                  Topology.CWComplex.map n i (NormedSpace.normalize z) ∈
                    regularNeighborhoodStage A n
                else i ∈ A.I n}

/-- Hatcher's fixed-width regular neighborhood, as a subset of the ambient
space.  It is contained in `C` and open in the subspace topology on `C`. -/
def regularNeighborhood (A : CWComplex.Subcomplex C) : Set X :=
  ⋃ n, regularNeighborhoodStage C A n

omit [T2Space X] in
@[simp]
theorem regularNeighborhoodStage_zero (A : CWComplex.Subcomplex C) :
    regularNeighborhoodStage C A 0 = ∅ :=
  rfl

omit [T2Space X] in
theorem regularNeighborhoodStage_succ (A : CWComplex.Subcomplex C) (n : ℕ) :
    regularNeighborhoodStage C A (n + 1) =
      regularNeighborhoodStage C A n ∪
        ⋃ i : Topology.CWComplex.cell C n,
          Topology.CWComplex.map n i ''
            {z : CellModel n |
              z ∈ ball 0 1 ∧
                if (1 / 2 : ℝ) < ‖z‖ then
                  Topology.CWComplex.map n i (NormedSpace.normalize z) ∈
                    regularNeighborhoodStage C A n
                else i ∈ A.I n} :=
  rfl

omit [T2Space X] in
theorem regularNeighborhoodStage_mono (A : CWComplex.Subcomplex C) (n : ℕ) :
    regularNeighborhoodStage C A n ⊆
      regularNeighborhoodStage C A (n + 1) := by
  rw [regularNeighborhoodStage_succ]
  exact subset_union_left

omit [T2Space X] in
theorem regularNeighborhoodStage_mono_of_le
    (A : CWComplex.Subcomplex C) {n m : ℕ} (hnm : n ≤ m) :
    regularNeighborhoodStage C A n ⊆ regularNeighborhoodStage C A m := by
  induction m generalizing n with
  | zero =>
      have hn : n = 0 := Nat.eq_zero_of_le_zero hnm
      subst n
      exact Subset.rfl
  | succ m ih =>
      rcases Nat.eq_or_lt_of_le hnm with h | h
      · subst n
        exact Subset.rfl
      · exact (ih (Nat.le_of_lt_succ h)).trans
          (regularNeighborhoodStage_mono C A m)

theorem regularNeighborhoodStage_subset_skeletonLT
    (A : CWComplex.Subcomplex C) (n : ℕ) :
    regularNeighborhoodStage C A n ⊆
      (Topology.RelCWComplex.skeletonLT C n : Set X) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [regularNeighborhoodStage_succ]
      apply union_subset
      · exact ih.trans (Topology.RelCWComplex.skeletonLT_mono (C := C) (by norm_num))
      · apply iUnion_subset
        intro i
        refine (image_mono ?_).trans
          (Topology.RelCWComplex.openCell_subset_skeletonLT (C := C) n i)
        intro z hz
        exact hz.1

/-- Membership on the open part of a new cell is given by the fixed radial
rule appearing in the definition. -/
theorem map_mem_regularNeighborhoodStage_succ_iff
    (A : CWComplex.Subcomplex C) (n : ℕ)
    (i : Topology.CWComplex.cell C n) (z : CellModel n)
    (hz : z ∈ ball 0 1) :
    Topology.CWComplex.map n i z ∈ regularNeighborhoodStage C A (n + 1) ↔
      (if (1 / 2 : ℝ) < ‖z‖ then
        Topology.CWComplex.map n i (NormedSpace.normalize z) ∈
          regularNeighborhoodStage C A n
      else i ∈ A.I n) := by
  rw [regularNeighborhoodStage_succ]
  constructor
  · intro hx
    rcases hx with hxold | hxnew
    · have hopen : Topology.CWComplex.map n i z ∈
          Topology.CWComplex.openCell (C := C) n i := ⟨z, hz, rfl⟩
      exact ((Topology.RelCWComplex.disjoint_skeletonLT_openCell
        (C := C) (n := (n : ℕ∞)) (m := n) (j := i) le_rfl).notMem_of_mem_left
          (regularNeighborhoodStage_subset_skeletonLT C A n hxold) hopen).elim
    · obtain ⟨j, w, hw, hmap⟩ := Set.mem_iUnion.mp hxnew
      have hwopen : w ∈ ball (0 : CellModel n) 1 := hw.1
      have hjopen : Topology.CWComplex.map n i z ∈
          Topology.CWComplex.openCell (C := C) n j := ⟨w, hwopen, hmap⟩
      have hiopen : Topology.CWComplex.map n i z ∈
          Topology.CWComplex.openCell (C := C) n i := ⟨z, hz, rfl⟩
      have hnot : ¬ Disjoint
          (Topology.CWComplex.openCell (C := C) n j)
          (Topology.CWComplex.openCell (C := C) n i) :=
        not_disjoint_iff.mpr ⟨_, hjopen, hiopen⟩
      have hji : j = i := by
        have hsigma := Topology.CWComplex.eq_of_not_disjoint_openCell hnot
        exact eq_of_heq (Sigma.mk.inj_iff.mp hsigma).2
      subst j
      have hwz : w = z := (Topology.CWComplex.map n i).injOn
        (by rwa [Topology.CWComplex.source_eq])
        (by rwa [Topology.CWComplex.source_eq]) hmap
      subst w
      exact hw.2
  · intro hzrule
    right
    exact Set.mem_iUnion.mpr ⟨i, ⟨z, ⟨hz, hzrule⟩, rfl⟩⟩

/-- Passing to the next stage does not change points in the preceding
skeleton. -/
theorem mem_regularNeighborhoodStage_succ_iff_of_mem_skeletonLT
    (A : CWComplex.Subcomplex C) (n : ℕ) {x : X}
    (hxsk : x ∈ (Topology.RelCWComplex.skeletonLT C n : Set X)) :
    x ∈ regularNeighborhoodStage C A (n + 1) ↔
      x ∈ regularNeighborhoodStage C A n := by
  rw [regularNeighborhoodStage_succ]
  constructor
  · rintro (hxold | hxnew)
    · exact hxold
    · obtain ⟨i, z, hz, rfl⟩ := Set.mem_iUnion.mp hxnew
      have hopen : Topology.CWComplex.map n i z ∈
          Topology.CWComplex.openCell (C := C) n i := ⟨z, hz.1, rfl⟩
      exact ((Topology.RelCWComplex.disjoint_skeletonLT_openCell
        (C := C) (n := (n : ℕ∞)) (m := n) (j := i) le_rfl).notMem_of_mem_left
          hxsk hopen).elim
  · exact Or.inl

/-- On each finite skeleton, Hatcher's stage contains the part of the
subcomplex already present there. -/
theorem subcomplex_inter_skeletonLT_subset_regularNeighborhoodStage
    (A : CWComplex.Subcomplex C) (n : ℕ) :
    (A : Set X) ∩ (Topology.RelCWComplex.skeletonLT C n : Set X) ⊆
      regularNeighborhoodStage C A n := by
  induction n with
  | zero =>
      intro x hx
      have hxsk : x ∈
          (Topology.RelCWComplex.skeletonLT C (0 : ℕ∞) : Set X) := by
        simpa using hx.2
      rw [Topology.CWComplex.skeletonLT_zero_eq_empty] at hxsk
      exact hxsk.elim
  | succ n ih =>
      intro x hx
      rw [regularNeighborhoodStage_succ]
      have hxsk : x ∈ (Topology.RelCWComplex.skeletonLT C
          ((n : ℕ∞) + 1) : Set X) := by
        simpa only [Nat.cast_add, Nat.cast_one] using hx.2
      obtain ⟨m, hmn, i, hxi⟩ :=
        (Topology.CWComplex.mem_skeletonLT_iff (C := C)).mp hxsk
      have hmle : m ≤ n := by
        norm_cast at hmn
        omega
      rcases lt_or_eq_of_le hmle with hmlt | hmeq
      · left
        apply ih
        have hxsmall : x ∈
            (Topology.RelCWComplex.skeletonLT C (m + 1) : Set X) :=
          Topology.RelCWComplex.openCell_subset_skeletonLT (C := C) m i hxi
        exact ⟨hx.1, Topology.RelCWComplex.skeletonLT_mono (C := C) (by
          norm_cast) hxsmall⟩
      · subst m
        right
        have hiA : i ∈ A.I n := by
          by_contra hiA
          exact (A.disjoint_openCell_subcomplex_of_not_mem hiA).notMem_of_mem_left
            hxi hx.1
        obtain ⟨z, hz, rfl⟩ := hxi
        refine Set.mem_iUnion.mpr ⟨i, ⟨z, ⟨hz, ?_⟩, rfl⟩⟩
        split_ifs with houter
        · have hz0 : z ≠ 0 := by
            intro hz0
            subst z
            norm_num at houter
          have hzsphere : NormedSpace.normalize z ∈
              sphere (0 : CellModel n) 1 := by
            rw [mem_sphere, dist_zero_right]
            exact NormedSpace.norm_normalize hz0
          have hfrontier : Topology.CWComplex.map n i (NormedSpace.normalize z) ∈
              Topology.CWComplex.cellFrontier (C := C) n i :=
            ⟨NormedSpace.normalize z, hzsphere, rfl⟩
          exact ih ⟨A.cellFrontier_subset_of_mem hiA hfrontier,
            Topology.CWComplex.cellFrontier_subset_skeletonLT (C := C) n i hfrontier⟩
        · exact hiA

/-- The fixed-radius construction preserves binary intersections at every
finite stage. -/
theorem regularNeighborhoodStage_inter
    (A B : CWComplex.Subcomplex C) (n : ℕ) :
    regularNeighborhoodStage C (Subcomplex.inter A B) n =
      regularNeighborhoodStage C A n ∩ regularNeighborhoodStage C B n := by
  induction n with
  | zero => simp
  | succ n ih =>
      ext x
      constructor
      · intro hx
        have hxsk : x ∈
            (Topology.RelCWComplex.skeletonLT C (n + 1) : Set X) :=
          regularNeighborhoodStage_subset_skeletonLT C (Subcomplex.inter A B) (n + 1) hx
        by_cases hxold : x ∈
            (Topology.RelCWComplex.skeletonLT C n : Set X)
        · have hx' :=
            (mem_regularNeighborhoodStage_succ_iff_of_mem_skeletonLT
              C (Subcomplex.inter A B) n hxold).mp hx
          rw [ih] at hx'
          exact ⟨regularNeighborhoodStage_mono C A n hx'.1,
            regularNeighborhoodStage_mono C B n hx'.2⟩
        · have hxsk' : x ∈ (Topology.RelCWComplex.skeletonLT C
              ((n : ℕ∞) + 1) : Set X) := by
            simpa only [Nat.cast_add, Nat.cast_one] using hxsk
          obtain ⟨m, hmn, i, hxi⟩ :=
            (Topology.CWComplex.mem_skeletonLT_iff (C := C)).mp hxsk'
          have hmle : m ≤ n := by
            norm_cast at hmn
            omega
          have hmeq : m = n := by
            apply le_antisymm hmle
            by_contra hmn'
            have hmlt : m < n := by omega
            have hxsmall : x ∈
                (Topology.RelCWComplex.skeletonLT C (m + 1) : Set X) :=
              Topology.RelCWComplex.openCell_subset_skeletonLT (C := C) m i hxi
            exact hxold (Topology.RelCWComplex.skeletonLT_mono (C := C) (by
              norm_cast) hxsmall)
          subst m
          obtain ⟨z, hz, rfl⟩ := hxi
          have hxrule :=
            (map_mem_regularNeighborhoodStage_succ_iff C
              (Subcomplex.inter A B) n i z hz).mp hx
          constructor
          · apply (map_mem_regularNeighborhoodStage_succ_iff C A n i z hz).mpr
            by_cases houter : (1 / 2 : ℝ) < ‖z‖
            · rw [if_pos houter] at hxrule ⊢
              rw [ih] at hxrule
              exact hxrule.1
            · rw [if_neg houter] at hxrule ⊢
              exact hxrule.1
          · apply (map_mem_regularNeighborhoodStage_succ_iff C B n i z hz).mpr
            by_cases houter : (1 / 2 : ℝ) < ‖z‖
            · rw [if_pos houter] at hxrule ⊢
              rw [ih] at hxrule
              exact hxrule.2
            · rw [if_neg houter] at hxrule ⊢
              exact hxrule.2
      · rintro ⟨hxA, hxB⟩
        have hxsk : x ∈
            (Topology.RelCWComplex.skeletonLT C (n + 1) : Set X) :=
          regularNeighborhoodStage_subset_skeletonLT C A (n + 1) hxA
        by_cases hxold : x ∈
            (Topology.RelCWComplex.skeletonLT C n : Set X)
        · apply regularNeighborhoodStage_mono C (Subcomplex.inter A B) n
          rw [ih]
          exact ⟨
            (mem_regularNeighborhoodStage_succ_iff_of_mem_skeletonLT
              C A n hxold).mp hxA,
            (mem_regularNeighborhoodStage_succ_iff_of_mem_skeletonLT
              C B n hxold).mp hxB⟩
        · have hxsk' : x ∈ (Topology.RelCWComplex.skeletonLT C
              ((n : ℕ∞) + 1) : Set X) := by
            simpa only [Nat.cast_add, Nat.cast_one] using hxsk
          obtain ⟨m, hmn, i, hxi⟩ :=
            (Topology.CWComplex.mem_skeletonLT_iff (C := C)).mp hxsk'
          have hmle : m ≤ n := by
            norm_cast at hmn
            omega
          have hmeq : m = n := by
            apply le_antisymm hmle
            by_contra hmn'
            have hmlt : m < n := by omega
            have hxsmall : x ∈
                (Topology.RelCWComplex.skeletonLT C (m + 1) : Set X) :=
              Topology.RelCWComplex.openCell_subset_skeletonLT (C := C) m i hxi
            exact hxold (Topology.RelCWComplex.skeletonLT_mono (C := C) (by
              norm_cast) hxsmall)
          subst m
          obtain ⟨z, hz, rfl⟩ := hxi
          have hxArule :=
            (map_mem_regularNeighborhoodStage_succ_iff C A n i z hz).mp hxA
          have hxBrule :=
            (map_mem_regularNeighborhoodStage_succ_iff C B n i z hz).mp hxB
          apply (map_mem_regularNeighborhoodStage_succ_iff C
            (Subcomplex.inter A B) n i z hz).mpr
          by_cases houter : (1 / 2 : ℝ) < ‖z‖
          · rw [if_pos houter] at hxArule hxBrule ⊢
            rw [ih]
            exact ⟨hxArule, hxBrule⟩
          · rw [if_neg houter] at hxArule hxBrule ⊢
            exact ⟨hxArule, hxBrule⟩

/-- Radial projection from the fixed outer collar to the preceding
skeleton. -/
def cellBoundaryCollarToSkeleton (n : ℕ)
    (i : Topology.CWComplex.cell C n) :
    C(cellBoundaryCollar n,
      ↑(Topology.RelCWComplex.skeletonLT C n : Set X)) where
  toFun x := skeletonLTStepBoundaryMap C n i (cellBoundaryCollarRetraction n x)
  continuous_toFun := (continuous_skeletonLTStepBoundaryMap C n i).comp
    (cellBoundaryCollarRetraction n).continuous

/-- The pullback of the next neighborhood stage to one closed
characteristic disk. -/
def regularNeighborhoodClosedCellPart
    (A : CWComplex.Subcomplex C) (n : ℕ)
    (i : Topology.CWComplex.cell C n) :
    Set (closedBall (0 : CellModel n) 1) :=
  {z | Topology.CWComplex.map n i z ∈
    regularNeighborhoodStage C A (n + 1)}

private theorem regularNeighborhoodClosedCellPart_eq_univ_of_mem
    (A : CWComplex.Subcomplex C) (n : ℕ)
    (i : Topology.CWComplex.cell C n) (hi : i ∈ A.I n) :
    regularNeighborhoodClosedCellPart C A n i = Set.univ := by
  ext z
  constructor
  · intro _
    trivial
  · intro _
    apply subcomplex_inter_skeletonLT_subset_regularNeighborhoodStage C A (n + 1)
    refine ⟨A.closedCell_subset_of_mem hi ⟨z, z.2, rfl⟩, ?_⟩
    exact Topology.RelCWComplex.closedCell_subset_skeletonLT (C := C) n i
      ⟨z, z.2, rfl⟩

private theorem regularNeighborhoodClosedCellPart_eq_collar_of_not_mem
    (A : CWComplex.Subcomplex C) (n : ℕ)
    (i : Topology.CWComplex.cell C n) (hi : i ∉ A.I n) :
    regularNeighborhoodClosedCellPart C A n i =
      ((↑) : cellBoundaryCollar n → closedBall (0 : CellModel n) 1) ''
        ((cellBoundaryCollarToSkeleton C n i) ⁻¹'
          {x | x.1 ∈ regularNeighborhoodStage C A n}) := by
  ext z
  constructor
  · intro hzstage
    have hzclosed : (z.1 : CellModel n) ∈ closedBall 0 1 := z.2
    have hzsplit : (z.1 : CellModel n) ∈
        ball (0 : CellModel n) 1 ∪ sphere 0 1 := by
      rwa [ball_union_sphere]
    rcases hzsplit with hzball | hzsphere
    · have hzrule :=
          (map_mem_regularNeighborhoodStage_succ_iff C A n i z.1 hzball).mp hzstage
      have houter : (1 / 2 : ℝ) < ‖(z.1 : CellModel n)‖ := by
        by_contra houter
        simp only [if_neg houter, hi] at hzrule
      let c : cellBoundaryCollar n := ⟨z, houter⟩
      refine ⟨c, ?_, rfl⟩
      change Topology.CWComplex.map n i (NormedSpace.normalize (z.1 : CellModel n)) ∈
        regularNeighborhoodStage C A n
      rw [if_pos houter] at hzrule
      exact hzrule
    · have hnorm : ‖(z.1 : CellModel n)‖ = 1 := by
        simpa [mem_sphere, dist_zero_right] using hzsphere
      have houter : (1 / 2 : ℝ) < ‖(z.1 : CellModel n)‖ := by
        rw [hnorm]
        norm_num
      let c : cellBoundaryCollar n := ⟨z, houter⟩
      refine ⟨c, ?_, rfl⟩
      change Topology.CWComplex.map n i (NormedSpace.normalize (z.1 : CellModel n)) ∈
        regularNeighborhoodStage C A n
      rw [NormedSpace.normalize_eq_self_of_norm_eq_one hnorm]
      apply (mem_regularNeighborhoodStage_succ_iff_of_mem_skeletonLT C A n ?_).mp
        hzstage
      exact Topology.CWComplex.cellFrontier_subset_skeletonLT (C := C) n i
        ⟨z.1, hzsphere, rfl⟩
  · rintro ⟨c, hcstage, rfl⟩
    have hcclosed : (c.1.1 : CellModel n) ∈ closedBall 0 1 := c.1.2
    have hcsplit : (c.1.1 : CellModel n) ∈
        ball (0 : CellModel n) 1 ∪ sphere 0 1 := by
      rwa [ball_union_sphere]
    rcases hcsplit with hcball | hcsphere
    · change Topology.CWComplex.map n i c.1.1 ∈
        regularNeighborhoodStage C A (n + 1)
      apply (map_mem_regularNeighborhoodStage_succ_iff C A n i c.1.1 hcball).mpr
      have hcouter : (1 / 2 : ℝ) < ‖(c.1.1 : CellModel n)‖ := c.2
      rw [if_pos hcouter]
      change Topology.CWComplex.map n i (NormedSpace.normalize (c.1.1 : CellModel n)) ∈
        regularNeighborhoodStage C A n at hcstage
      exact hcstage
    · apply regularNeighborhoodStage_mono C A n
      have hnorm : ‖(c.1.1 : CellModel n)‖ = 1 := by
        simpa [mem_sphere, dist_zero_right] using hcsphere
      change Topology.CWComplex.map n i (NormedSpace.normalize (c.1.1 : CellModel n)) ∈
        regularNeighborhoodStage C A n at hcstage
      rw [NormedSpace.normalize_eq_self_of_norm_eq_one hnorm] at hcstage
      exact hcstage

theorem isOpen_regularNeighborhoodClosedCellPart
    (A : CWComplex.Subcomplex C) (n : ℕ)
    (i : Topology.CWComplex.cell C n)
    (hstage : IsOpen
      (((↑) :
        ↑(Topology.RelCWComplex.skeletonLT C n : Set X) → X) ⁻¹'
          regularNeighborhoodStage C A n)) :
    IsOpen (regularNeighborhoodClosedCellPart C A n i) := by
  by_cases hi : i ∈ A.I n
  · rw [regularNeighborhoodClosedCellPart_eq_univ_of_mem C A n i hi]
    exact isOpen_univ
  · rw [regularNeighborhoodClosedCellPart_eq_collar_of_not_mem C A n i hi]
    apply (isOpen_cellBoundaryCollar n).isOpenEmbedding_subtypeVal.isOpenMap
    exact hstage.preimage (cellBoundaryCollarToSkeleton C n i).continuous

/-- Every finite stage is open in the corresponding finite skeleton. -/
theorem isOpen_regularNeighborhoodStage
    (A : CWComplex.Subcomplex C) (n : ℕ) :
    IsOpen
      (((↑) : ↑(Topology.RelCWComplex.skeletonLT C n : Set X) → X) ⁻¹'
        regularNeighborhoodStage C A n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [show (↑(n + 1) : ℕ∞) = (n : ℕ∞) + 1 by norm_num]
      rw [← (skeletonLTStepJointMap_isQuotient C n).isOpen_preimage]
      rw [isOpen_sum_iff]
      constructor
      · have heq :
            Sum.inl ⁻¹'
                ((skeletonLTStepJointMap C n) ⁻¹'
                  (((↑) :
                    ↑(Topology.RelCWComplex.skeletonLT C
                      ((n : ℕ∞) + 1) : Set X) → X) ⁻¹'
                    regularNeighborhoodStage C A (n + 1))) =
              (((↑) :
                ↑(Topology.RelCWComplex.skeletonLT C n : Set X) → X) ⁻¹'
                regularNeighborhoodStage C A n) := by
          ext x
          exact mem_regularNeighborhoodStage_succ_iff_of_mem_skeletonLT C A n x.2
        rw [heq]
        exact ih
      · rw [isOpen_sigma_iff]
        intro i
        change IsOpen (regularNeighborhoodClosedCellPart C A n i)
        exact isOpen_regularNeighborhoodClosedCellPart C A n i ih

/-- Once a skeleton has been reached, later stages do not change its
points. -/
theorem mem_regularNeighborhoodStage_iff_of_mem_skeletonLT_of_le
    (A : CWComplex.Subcomplex C) {n m : ℕ} (hnm : n ≤ m) {x : X}
    (hxsk : x ∈ (Topology.RelCWComplex.skeletonLT C n : Set X)) :
    x ∈ regularNeighborhoodStage C A m ↔
      x ∈ regularNeighborhoodStage C A n := by
  induction m generalizing n with
  | zero =>
      have hn : n = 0 := Nat.eq_zero_of_le_zero hnm
      subst n
      rfl
  | succ m ih =>
      rcases Nat.eq_or_lt_of_le hnm with h | h
      · subst n
        rfl
      · have hnm' : n ≤ m := Nat.le_of_lt_succ h
        have hxskm : x ∈
            (Topology.RelCWComplex.skeletonLT C m : Set X) :=
          Topology.RelCWComplex.skeletonLT_mono (C := C) (by
            norm_cast) hxsk
        exact (mem_regularNeighborhoodStage_succ_iff_of_mem_skeletonLT
          C A m hxskm).trans (ih hnm' hxsk)

/-- The global neighborhood restricts on each finite skeleton to the stage
constructed there. -/
theorem mem_regularNeighborhood_iff_of_mem_skeletonLT
    (A : CWComplex.Subcomplex C) (n : ℕ) {x : X}
    (hxsk : x ∈ (Topology.RelCWComplex.skeletonLT C n : Set X)) :
    x ∈ regularNeighborhood C A ↔
      x ∈ regularNeighborhoodStage C A n := by
  constructor
  · intro hx
    obtain ⟨m, hxm⟩ := Set.mem_iUnion.mp hx
    rcases le_total m n with hmn | hnm
    · exact regularNeighborhoodStage_mono_of_le C A hmn hxm
    · exact (mem_regularNeighborhoodStage_iff_of_mem_skeletonLT_of_le
        C A hnm hxsk).mp hxm
  · intro hx
    exact subset_iUnion (regularNeighborhoodStage C A) n hx

omit [T2Space X] in
theorem regularNeighborhoodStage_subset_regularNeighborhood
    (A : CWComplex.Subcomplex C) (n : ℕ) :
    regularNeighborhoodStage C A n ⊆ regularNeighborhood C A :=
  subset_iUnion (regularNeighborhoodStage C A) n

theorem subcomplex_subset_regularNeighborhood
    (A : CWComplex.Subcomplex C) :
    (A : Set X) ⊆ regularNeighborhood C A := by
  intro x hx
  have hxC : x ∈ C := A.subset_complex hx
  rw [← Topology.CWComplex.iUnion_skeletonLT_eq_complex (C := C)] at hxC
  obtain ⟨n, hxn⟩ := Set.mem_iUnion.mp hxC
  exact regularNeighborhoodStage_subset_regularNeighborhood C A n
    (subcomplex_inter_skeletonLT_subset_regularNeighborhoodStage C A n ⟨hx, hxn⟩)

/-- The canonical inclusion of a subcomplex into its selected regular
neighborhood. -/
def regularNeighborhoodInclusion (A : CWComplex.Subcomplex C) :
    C(↑(A : Set X), ↑(regularNeighborhood C A)) where
  toFun x := ⟨x.1, subcomplex_subset_regularNeighborhood C A x.2⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

private theorem regularNeighborhoodStage_eq_empty_of_subcomplex_eq_empty
    (A : CWComplex.Subcomplex C) (hA : (A : Set X) = ∅) (n : ℕ) :
    regularNeighborhoodStage C A n = ∅ := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [regularNeighborhoodStage_succ, ih, empty_union]
      apply iUnion_eq_empty.mpr
      intro i
      have hi : i ∉ A.I n := by
        intro hi
        have hx : Topology.CWComplex.map n i 0 ∈ (A : Set X) :=
          A.openCell_subset_of_mem hi
            (Topology.CWComplex.map_zero_mem_openCell (C := C) n i)
        rw [hA] at hx
        exact hx
      apply image_eq_empty.mpr
      ext z
      simp [hi]

/-- The construction also handles the empty subcomplex: its selected
neighborhood is empty. -/
theorem regularNeighborhood_eq_empty_of_subcomplex_eq_empty
    (A : CWComplex.Subcomplex C) (hA : (A : Set X) = ∅) :
    regularNeighborhood C A = ∅ := by
  rw [regularNeighborhood]
  apply iUnion_eq_empty.mpr
  exact regularNeighborhoodStage_eq_empty_of_subcomplex_eq_empty C A hA

/-- Using the same radial width for every subcomplex makes regular
neighborhoods preserve intersections on the nose. -/
theorem regularNeighborhood_inter (A B : CWComplex.Subcomplex C) :
    regularNeighborhood C (Subcomplex.inter A B) =
      regularNeighborhood C A ∩ regularNeighborhood C B := by
  ext x
  constructor
  · intro hx
    obtain ⟨n, hxn⟩ := Set.mem_iUnion.mp hx
    rw [regularNeighborhoodStage_inter] at hxn
    exact ⟨Set.mem_iUnion.mpr ⟨n, hxn.1⟩,
      Set.mem_iUnion.mpr ⟨n, hxn.2⟩⟩
  · rintro ⟨hxA, hxB⟩
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hxA
    obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hxB
    let k := max n m
    have hn' : x ∈ regularNeighborhoodStage C A k :=
      regularNeighborhoodStage_mono_of_le C A (le_max_left n m) hn
    have hm' : x ∈ regularNeighborhoodStage C B k :=
      regularNeighborhoodStage_mono_of_le C B (le_max_right n m) hm
    apply Set.mem_iUnion.mpr
    refine ⟨k, ?_⟩
    rw [regularNeighborhoodStage_inter]
    exact ⟨hn', hm'⟩

theorem regularNeighborhood_subset_complex (A : CWComplex.Subcomplex C) :
    regularNeighborhood C A ⊆ C := by
  intro x hx
  obtain ⟨n, hxn⟩ := Set.mem_iUnion.mp hx
  exact (Topology.RelCWComplex.skeletonLT C n).subset_complex
    (regularNeighborhoodStage_subset_skeletonLT C A n hxn)

private theorem isClosed_complex_diff_regularNeighborhood
    (A : CWComplex.Subcomplex C) :
    IsClosed (C \ regularNeighborhood C A) := by
  rw [Topology.CWComplex.closed C (C \ regularNeighborhood C A) sdiff_subset]
  intro n i
  let j : ↑(Topology.CWComplex.closedCell (C := C) n i) →
      ↑(Topology.RelCWComplex.skeletonLT C (n + 1) : Set X) :=
    fun x ↦ ⟨x.1,
      Topology.RelCWComplex.closedCell_subset_skeletonLT (C := C) n i x.2⟩
  have hj : Continuous j := continuous_subtype_val.subtype_mk _
  let V : Set ↑(Topology.RelCWComplex.skeletonLT C (n + 1) : Set X) :=
    ((↑) : ↑(Topology.RelCWComplex.skeletonLT C (n + 1) : Set X) → X) ⁻¹'
      regularNeighborhoodStage C A (n + 1)
  have hV : IsOpen V := isOpen_regularNeighborhoodStage C A (n + 1)
  have hpre : IsClosed (j ⁻¹' V)ᶜ := (hV.preimage hj).isClosed_compl
  have himage : IsClosed
      (((↑) : ↑(Topology.CWComplex.closedCell (C := C) n i) → X) ''
        (j ⁻¹' V)ᶜ) :=
    (Topology.CWComplex.isClosed_closedCell (C := C) (n := n) (i := i))
      |>.isClosedEmbedding_subtypeVal.isClosed_iff_image_isClosed.1 hpre
  have heq :
      (((↑) : ↑(Topology.CWComplex.closedCell (C := C) n i) → X) ''
          (j ⁻¹' V)ᶜ) =
        (C \ regularNeighborhood C A) ∩
          Topology.CWComplex.closedCell (C := C) n i := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hynot : y.1 ∉ regularNeighborhoodStage C A (n + 1) := hy
      refine ⟨⟨Topology.RelCWComplex.closedCell_subset_complex (C := C) n i y.2,
        ?_⟩, y.2⟩
      intro hyN
      exact hynot ((mem_regularNeighborhood_iff_of_mem_skeletonLT C A (n + 1)
        (j y).2).mp hyN)
    · rintro ⟨⟨hxC, hxN⟩, hxcell⟩
      let y : ↑(Topology.CWComplex.closedCell (C := C) n i) := ⟨x, hxcell⟩
      refine ⟨y, ?_, rfl⟩
      change y.1 ∉ regularNeighborhoodStage C A (n + 1)
      intro hystage
      exact hxN ((mem_regularNeighborhood_iff_of_mem_skeletonLT C A (n + 1)
        (j y).2).mpr hystage)
  rwa [← heq]

/-- A regular neighborhood is open in the subspace topology of the ambient
CW complex. -/
theorem isOpen_regularNeighborhood (A : CWComplex.Subcomplex C) :
    IsOpen
      (((↑) : ↑C → X) ⁻¹' regularNeighborhood C A) := by
  rw [← isClosed_compl_iff]
  have heq :
      ((((↑) : ↑C → X) ⁻¹' regularNeighborhood C A)ᶜ) =
        ((↑) : ↑C → X) ⁻¹' (C \ regularNeighborhood C A) := by
    ext x
    simp
  rw [heq]
  exact (isClosed_complex_diff_regularNeighborhood C A).preimage
    continuous_subtype_val

/-- The carrier of a subcomplex lies in the interior of its regular
neighborhood, where interior is taken in the ambient CW complex `C`. -/
theorem subcomplex_subset_interior_regularNeighborhood
    (A : CWComplex.Subcomplex C) :
    (((↑) : ↑C → X) ⁻¹' (A : Set X)) ⊆
      interior (((↑) : ↑C → X) ⁻¹' regularNeighborhood C A) := by
  rw [(isOpen_regularNeighborhood C A).interior_eq]
  intro x hx
  exact subcomplex_subset_regularNeighborhood C A hx

/-- A meet-preserving assignment of open regular neighborhoods to all
subcomplexes of a classical CW complex.  Openness and interior are relative
to the ambient CW complex `C`, as required when `C` is presented as a closed
subset of a larger space. -/
structure RegularNeighborhoodSystem where
  /-- The selected neighborhood of a subcomplex. -/
  neighborhood : CWComplex.Subcomplex C → Set X
  /-- Every selected neighborhood remains inside the ambient CW complex. -/
  neighborhood_subset_complex : ∀ A : CWComplex.Subcomplex C,
    neighborhood A ⊆ C
  /-- Every selected neighborhood is open in the subspace topology on `C`. -/
  isOpen_neighborhood : ∀ A : CWComplex.Subcomplex C,
    IsOpen (((↑) : ↑C → X) ⁻¹' neighborhood A)
  /-- The carrier is contained in its selected neighborhood. -/
  carrier_subset_neighborhood : ∀ A : CWComplex.Subcomplex C,
    (A : Set X) ⊆ neighborhood A
  /-- A subcomplex lies in the interior of its selected neighborhood. -/
  carrier_subset_interior : ∀ A : CWComplex.Subcomplex C,
    (((↑) : ↑C → X) ⁻¹' (A : Set X)) ⊆
      interior (((↑) : ↑C → X) ⁻¹' neighborhood A)
  /-- The common fixed radial width makes the assignment preserve
  intersections exactly. -/
  neighborhood_inter : ∀ A B : CWComplex.Subcomplex C,
    neighborhood (Subcomplex.inter A B) = neighborhood A ∩ neighborhood B

/-- The canonical fixed-width regular-neighborhood system. -/
def regularNeighborhoodSystem : RegularNeighborhoodSystem C where
  neighborhood := regularNeighborhood C
  neighborhood_subset_complex := regularNeighborhood_subset_complex C
  isOpen_neighborhood := isOpen_regularNeighborhood C
  carrier_subset_neighborhood := subcomplex_subset_regularNeighborhood C
  carrier_subset_interior := subcomplex_subset_interior_regularNeighborhood C
  neighborhood_inter := regularNeighborhood_inter C

end Hatcher.ClassicalCW
