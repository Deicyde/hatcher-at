/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Hatcher.Appendix.RegularNeighborhood
import Hatcher.Topology.StrongDeformationRetract
import Mathlib.Topology.CompactOpen

/-!
# Deforming a regular neighborhood onto its subcomplex

This file assembles the radial collar deformations of the cells of a
classical CW complex.  Cell dimension `n` is assigned the interval
`[1/(n+2), 1/(n+1)]`; thus a point is first pushed to the preceding skeleton
and is then handled by the lower-dimensional deformations.  The intervals
accumulate only at zero, where the deformation is the identity on every
fixed closed cell.
-/

noncomputable section

open Metric Set Topology Function
open scoped unitInterval

namespace Hatcher.ClassicalCW

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X]
variable (C : Set X) [CWComplex C]

private abbrev CellModel (n : ℕ) := Fin n → ℝ

/-- The beginning of the time interval assigned to cells of dimension `n`. -/
private def regularNeighborhoodCellStart (n : ℕ) : I :=
  ⟨1 / (n + 2 : ℝ), by
    constructor
    · positivity
    · rw [div_le_iff₀ (by positivity)]
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith⟩

/-- The end of the time interval assigned to cells of dimension `n`. -/
private def regularNeighborhoodCellFinish (n : ℕ) : I :=
  ⟨1 / (n + 1 : ℝ), by
    constructor
    · positivity
    · rw [div_le_iff₀ (by positivity)]
      norm_num⟩

private theorem regularNeighborhoodCellStart_lt_finish (n : ℕ) :
    (regularNeighborhoodCellStart n : ℝ) < regularNeighborhoodCellFinish n := by
  simp only [regularNeighborhoodCellStart, regularNeighborhoodCellFinish]
  exact one_div_lt_one_div_of_lt (by positivity) (by norm_num)

private theorem regularNeighborhoodCellFinish_eq_start_succ (n : ℕ) :
    regularNeighborhoodCellFinish (n + 1) = regularNeighborhoodCellStart n := by
  apply Subtype.ext
  change 1 / ((n + 1 : ℕ) + 1 : ℝ) = 1 / (n + 2 : ℝ)
  congr 1
  push_cast
  ring

/-- Radial collar deformation preserves the radial projection to the cell
boundary. -/
private theorem cellBoundaryCollarRetraction_deformation (n : ℕ)
    (t : I) (x : cellBoundaryCollar n) :
    cellBoundaryCollarRetraction n
        (cellBoundaryCollarDeformation n
          (regularNeighborhoodCellStart n)
          (regularNeighborhoodCellFinish n)
          (regularNeighborhoodCellStart_lt_finish n) (t, x)) =
      cellBoundaryCollarRetraction n x := by
  apply Subtype.ext
  let s := cellBoundaryCollarSchedule
    (regularNeighborhoodCellStart n) (regularNeighborhoodCellFinish n) t
  let v : CellModel n :=
    ((x.1 : closedBall (0 : CellModel n) 1) : CellModel n)
  have hv : 0 < ‖v‖ := by
    change 0 < ‖((x.1 : closedBall (0 : CellModel n) 1) : CellModel n)‖
    exact (by norm_num : (0 : ℝ) < 1 / 2).trans x.2
  have hs0 : 0 ≤ (s : ℝ) := s.2.1
  have hs1 : (s : ℝ) ≤ 1 := s.2.2
  have hfactor : 0 < (1 - (s : ℝ)) + (s : ℝ) * ‖v‖⁻¹ := by
    by_cases hs : (s : ℝ) = 1
    · rw [hs]
      simp [hv]
    · have : (s : ℝ) < 1 := lt_of_le_of_ne hs1 hs
      exact add_pos_of_pos_of_nonneg (sub_pos.mpr this)
        (mul_nonneg hs0 (inv_nonneg.mpr (norm_nonneg v)))
  have hpoint :
      (1 - (s : ℝ)) • v +
          (s : ℝ) • NormedSpace.normalize v =
        ((1 - (s : ℝ)) + (s : ℝ) * ‖v‖⁻¹) • v := by
    rw [NormedSpace.normalize, smul_smul, ← add_smul]
  change NormedSpace.normalize
      ((1 - (s : ℝ)) • v +
        (s : ℝ) • NormedSpace.normalize v) =
    NormedSpace.normalize v
  rw [hpoint, NormedSpace.normalize_smul_of_pos hfactor]

/-! ## Finite-stage deformation data -/

/-- The `n`th neighborhood stage, with its topology inherited from the strict
`n`-skeleton. -/
private abbrev RegularNeighborhoodStageSpace
    (A : CWComplex.Subcomplex C) (n : ℕ) :=
  ↑(((↑) :
      ↑(Topology.RelCWComplex.skeletonLT C n : Set X) → X) ⁻¹'
    regularNeighborhoodStage C A n)

/-- Include one neighborhood stage in its successor. -/
private def regularNeighborhoodStageInclusion
    (A : CWComplex.Subcomplex C) (n : ℕ) :
    C(RegularNeighborhoodStageSpace C A n,
      RegularNeighborhoodStageSpace C A (n + 1)) where
  toFun x :=
    ⟨skeletonLTStepOldMap C n x.1,
      regularNeighborhoodStage_mono C A n x.2⟩
  continuous_toFun :=
    ((continuous_skeletonLTStepOldMap C n).comp continuous_subtype_val).subtype_mk _

/-- The successor-skeleton quotient, restricted to the open neighborhood
stage. -/
private def regularNeighborhoodStageQuotientMap
    (A : CWComplex.Subcomplex C) (n : ℕ) :
    (skeletonLTStepJointMap C n ⁻¹'
      (((↑) :
          ↑(Topology.RelCWComplex.skeletonLT C (n + 1) : Set X) → X) ⁻¹'
        regularNeighborhoodStage C A (n + 1))) →
      RegularNeighborhoodStageSpace C A (n + 1) :=
  ((((↑) :
      ↑(Topology.RelCWComplex.skeletonLT C (n + 1) : Set X) → X) ⁻¹'
    regularNeighborhoodStage C A (n + 1)).restrictPreimage
      (skeletonLTStepJointMap C n))

private theorem regularNeighborhoodStageQuotientMap_isQuotient
    (A : CWComplex.Subcomplex C) (n : ℕ) :
    IsQuotientMap (regularNeighborhoodStageQuotientMap C A n) :=
  (skeletonLTStepJointMap_isQuotient C n).restrictPreimage_isOpen
    (isOpen_regularNeighborhoodStage C A (n + 1))

/-- A subtype of a disjoint sum is the disjoint sum of the two corresponding
preimage subtypes. -/
private def sumPreimageEquiv {P Q : Type*} [TopologicalSpace P]
    [TopologicalSpace Q] (s : Set (P ⊕ Q)) :
    ↑s ≃ (↑(Sum.inl ⁻¹' s) ⊕ ↑(Sum.inr ⁻¹' s)) where
  toFun z := by
    rcases z with ⟨p | q, h⟩
    · exact Sum.inl ⟨p, h⟩
    · exact Sum.inr ⟨q, h⟩
  invFun z := by
    rcases z with p | q
    · exact ⟨Sum.inl p.1, p.2⟩
    · exact ⟨Sum.inr q.1, q.2⟩
  left_inv z := by
    rcases z with ⟨p | q, h⟩ <;> rfl
  right_inv z := by
    rcases z with p | q <;> rfl

private theorem continuous_sumPreimageEquiv_symm
    {P Q : Type*} [TopologicalSpace P] [TopologicalSpace Q]
    (s : Set (P ⊕ Q)) : Continuous (sumPreimageEquiv s).symm := by
  rw [continuous_sum_dom]
  constructor
  · exact (continuous_inl.comp continuous_subtype_val).subtype_mk _
  · exact (continuous_inr.comp continuous_subtype_val).subtype_mk _

private theorem isOpen_preimage_sumPreimageEquiv_iff
    {P Q : Type*} [TopologicalSpace P] [TopologicalSpace Q]
    (s : Set (P ⊕ Q)) (U : Set (↑(Sum.inl ⁻¹' s) ⊕ ↑(Sum.inr ⁻¹' s))) :
    IsOpen ((sumPreimageEquiv s) ⁻¹' U) ↔ IsOpen U := by
  constructor
  · intro hU
    rw [isOpen_sum_iff]
    constructor
    · convert hU.preimage
          ((continuous_sumPreimageEquiv_symm s).comp continuous_inl) using 1
      ext p
      rfl
    · convert hU.preimage
          ((continuous_sumPreimageEquiv_symm s).comp continuous_inr) using 1
      ext q
      rfl
  · intro hU
    obtain ⟨UL, hUL, hpreUL⟩ :=
      IsEmbedding.subtypeVal.isInducing.isOpen_iff.mp
        (isOpen_sum_iff.mp hU).1
    obtain ⟨UR, hUR, hpreUR⟩ :=
      IsEmbedding.subtypeVal.isInducing.isOpen_iff.mp
        (isOpen_sum_iff.mp hU).2
    let V : Set (P ⊕ Q) :=
      Sum.inl '' UL ∪ Sum.inr '' UR
    have hV : IsOpen V :=
      (isOpenMap_inl UL hUL).union (isOpenMap_inr UR hUR)
    have heq : (sumPreimageEquiv s) ⁻¹' U =
        Subtype.val ⁻¹' V := by
      ext z
      rcases z with ⟨p | q, hp⟩
      · change (Sum.inl ⟨p, hp⟩ ∈ U) ↔ Sum.inl p ∈ V
        rw [show Sum.inl p ∈ V ↔ p ∈ UL by simp [V]]
        exact (Set.ext_iff.mp hpreUL ⟨p, hp⟩).symm
      · change (Sum.inr ⟨q, hp⟩ ∈ U) ↔ Sum.inr q ∈ V
        rw [show Sum.inr q ∈ V ↔ q ∈ UR by simp [V]]
        exact (Set.ext_iff.mp hpreUR ⟨q, hp⟩).symm
    rw [heq]
    exact hV.preimage continuous_subtype_val

private def sumPreimageHomeomorph {P Q : Type*} [TopologicalSpace P]
    [TopologicalSpace Q] (s : Set (P ⊕ Q)) :
    ↑s ≃ₜ (↑(Sum.inl ⁻¹' s) ⊕ ↑(Sum.inr ⁻¹' s)) :=
  (sumPreimageEquiv s).toHomeomorph
    (isOpen_preimage_sumPreimageEquiv_iff s)

/-- The analogous decomposition for a dependent sum. -/
private def sigmaPreimageEquiv {J : Type*} {P : J → Type*}
    [∀ j, TopologicalSpace (P j)] (s : Set (Σ j, P j)) :
    ↑s ≃ (Σ j, ↑((Sigma.mk j) ⁻¹' s)) where
  toFun z := ⟨z.1.1, ⟨z.1.2, z.2⟩⟩
  invFun z := ⟨⟨z.1, z.2.1⟩, z.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem continuous_sigmaPreimageEquiv_symm
    {J : Type*} {P : J → Type*} [∀ j, TopologicalSpace (P j)]
    (s : Set (Σ j, P j)) : Continuous (sigmaPreimageEquiv s).symm := by
  apply continuous_sigma
  intro j
  exact (continuous_sigmaMk.comp continuous_subtype_val).subtype_mk _

private theorem isOpen_preimage_sigmaPreimageEquiv_iff
    {J : Type*} {P : J → Type*} [∀ j, TopologicalSpace (P j)]
    (s : Set (Σ j, P j))
    (U : Set (Σ j, ↑((Sigma.mk j) ⁻¹' s))) :
    IsOpen ((sigmaPreimageEquiv s) ⁻¹' U) ↔ IsOpen U := by
  constructor
  · intro hU
    rw [isOpen_sigma_iff]
    intro j
    convert hU.preimage
      ((continuous_sigmaPreimageEquiv_symm s).comp continuous_sigmaMk) using 1
    ext p
    rfl
  · intro hU
    have hopen : ∀ j, IsOpen (Sigma.mk j ⁻¹' U) :=
      isOpen_sigma_iff.mp hU
    choose V hV hpreV using fun j ↦
      IsEmbedding.subtypeVal.isInducing.isOpen_iff.mp (hopen j)
    let W : Set (Σ j, P j) := ⋃ j, Sigma.mk j '' V j
    have hW : IsOpen W := isOpen_iUnion fun j ↦ isOpenMap_sigmaMk _ (hV j)
    have heq : (sigmaPreimageEquiv s) ⁻¹' U =
        Subtype.val ⁻¹' W := by
      ext z
      rcases z with ⟨⟨j, p⟩, hp⟩
      change (⟨j, ⟨p, hp⟩⟩ ∈ U) ↔ ⟨j, p⟩ ∈ W
      rw [show ⟨j, p⟩ ∈ W ↔ p ∈ V j by
        constructor
        · intro h
          obtain ⟨i, hi⟩ := Set.mem_iUnion.mp h
          obtain ⟨x, hx, hxp⟩ := hi
          have hij : i = j := congrArg Sigma.fst hxp
          subst i
          have hxeq : x = p := eq_of_heq (Sigma.mk.inj_iff.mp hxp).2
          rwa [hxeq] at hx
        · intro hpV
          exact Set.mem_iUnion.mpr ⟨j, ⟨p, hpV, rfl⟩⟩]
      exact (Set.ext_iff.mp (hpreV j) ⟨p, hp⟩).symm
    rw [heq]
    exact hW.preimage continuous_subtype_val

private def sigmaPreimageHomeomorph
    {J : Type*} {P : J → Type*} [∀ j, TopologicalSpace (P j)]
    (s : Set (Σ j, P j)) :
    ↑s ≃ₜ (Σ j, ↑((Sigma.mk j) ⁻¹' s)) :=
  (sigmaPreimageEquiv s).toHomeomorph
    (isOpen_preimage_sigmaPreimageEquiv_iff s)

private theorem continuous_prod_sum {P Q Z : Type*}
    [TopologicalSpace P] [TopologicalSpace Q] [TopologicalSpace Z]
    {f : I × (P ⊕ Q) → Z}
    (hP : Continuous fun p : I × P ↦ f (p.1, Sum.inl p.2))
    (hQ : Continuous fun p : I × Q ↦ f (p.1, Sum.inr p.2)) :
    Continuous f := by
  let e : I × (P ⊕ Q) ≃ₜ (I × P) ⊕ (I × Q) :=
    Homeomorph.prodSumDistrib
  apply e.symm.isQuotientMap.continuous_iff.mpr
  rw [continuous_sum_dom]
  exact ⟨hP, hQ⟩

private theorem continuous_prod_sigma {J : Type*} {P : J → Type*}
    {Z : Type*} [∀ j, TopologicalSpace (P j)] [TopologicalSpace Z]
    {f : I × (Σ j, P j) → Z}
    (hf : ∀ j, Continuous fun p : I × P j ↦ f (p.1, ⟨j, p.2⟩)) :
    Continuous f := by
  let paths : (Σ j, P j) → C(I, Z) := fun z ↦
    ⟨fun t ↦ f (t, z), (hf z.1).comp
      (continuous_id.prodMk continuous_const)⟩
  have hpaths : Continuous paths := by
    apply continuous_sigma
    intro j
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous fun p : P j × I ↦ f (p.2, ⟨j, p.1⟩)
    exact (hf j).comp continuous_swap
  have huncurry : Continuous fun p : (Σ j, P j) × I ↦
      paths p.1 p.2 :=
    ContinuousMap.continuous_uncurry_of_continuous ⟨paths, hpaths⟩
  exact (huncurry.comp continuous_swap).congr fun _ ↦ rfl

/-- The part of one closed characteristic disk lying over the successor
neighborhood stage. -/
private abbrev RegularNeighborhoodCellSource
    (A : CWComplex.Subcomplex C) (n : ℕ)
    (i : Topology.CWComplex.cell C n) :=
  ↑(regularNeighborhoodClosedCellPart C A n i)

private theorem regularNeighborhoodCellSource_norm_gt_half_of_not_mem
    (A : CWComplex.Subcomplex C) (n : ℕ)
    (i : Topology.CWComplex.cell C n) (hi : i ∉ A.I n)
    (z : RegularNeighborhoodCellSource C A n i) :
    (1 / 2 : ℝ) < ‖(z.1.1 : CellModel n)‖ := by
  have hzclosed : (z.1.1 : CellModel n) ∈ closedBall 0 1 := z.1.2
  have hzsplit : (z.1.1 : CellModel n) ∈
      ball (0 : CellModel n) 1 ∪ sphere 0 1 := by
    rwa [ball_union_sphere]
  rcases hzsplit with hzball | hzsphere
  · have hzrule := (map_mem_regularNeighborhoodStage_succ_iff
      C A n i z.1.1 hzball).mp z.2
    by_contra houter
    simp only [if_neg houter, hi] at hzrule
  · have hnorm : ‖(z.1.1 : CellModel n)‖ = 1 := by
      simpa [mem_sphere, dist_zero_right] using hzsphere
    rw [hnorm]
    norm_num

private def regularNeighborhoodCellSourceCollar
    (A : CWComplex.Subcomplex C) (n : ℕ)
    (i : Topology.CWComplex.cell C n) (hi : i ∉ A.I n) :
    C(RegularNeighborhoodCellSource C A n i, cellBoundaryCollar n) where
  toFun z :=
    ⟨z.1, regularNeighborhoodCellSource_norm_gt_half_of_not_mem C A n i hi z⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

private theorem regularNeighborhoodCellSource_boundary_mem_stage
    (A : CWComplex.Subcomplex C) (n : ℕ)
    (i : Topology.CWComplex.cell C n) (hi : i ∉ A.I n)
    (z : RegularNeighborhoodCellSource C A n i) :
    (skeletonLTStepBoundaryMap C n i
      (cellBoundaryCollarRetraction n
        (regularNeighborhoodCellSourceCollar C A n i hi z))).1 ∈
      regularNeighborhoodStage C A n := by
  have hzclosed : (z.1.1 : CellModel n) ∈ closedBall 0 1 := z.1.2
  have hzsplit : (z.1.1 : CellModel n) ∈
      ball (0 : CellModel n) 1 ∪ sphere 0 1 := by
    rwa [ball_union_sphere]
  rcases hzsplit with hzball | hzsphere
  · have hzrule := (map_mem_regularNeighborhoodStage_succ_iff
      C A n i z.1.1 hzball).mp z.2
    have houter := regularNeighborhoodCellSource_norm_gt_half_of_not_mem
      C A n i hi z
    rw [if_pos houter] at hzrule
    exact hzrule
  · have hnorm : ‖(z.1.1 : CellModel n)‖ = 1 := by
      simpa [mem_sphere, dist_zero_right] using hzsphere
    change Topology.CWComplex.map n i
      (NormedSpace.normalize (z.1.1 : CellModel n)) ∈
        regularNeighborhoodStage C A n
    rw [NormedSpace.normalize_eq_self_of_norm_eq_one hnorm]
    apply (mem_regularNeighborhoodStage_succ_iff_of_mem_skeletonLT C A n ?_).mp z.2
    exact Topology.CWComplex.cellFrontier_subset_skeletonLT (C := C) n i
      ⟨z.1.1, hzsphere, rfl⟩

private def regularNeighborhoodCellSourceBoundary
    (A : CWComplex.Subcomplex C) (n : ℕ)
    (i : Topology.CWComplex.cell C n) (hi : i ∉ A.I n) :
    C(RegularNeighborhoodCellSource C A n i,
      RegularNeighborhoodStageSpace C A n) where
  toFun z :=
    ⟨skeletonLTStepBoundaryMap C n i
        (cellBoundaryCollarRetraction n
          (regularNeighborhoodCellSourceCollar C A n i hi z)),
      regularNeighborhoodCellSource_boundary_mem_stage C A n i hi z⟩
  continuous_toFun := by
    exact (((continuous_skeletonLTStepBoundaryMap C n i).comp
      ((cellBoundaryCollarRetraction n).continuous.comp
        (regularNeighborhoodCellSourceCollar C A n i hi).continuous)).subtype_mk _)

private theorem map_cellBoundaryCollar_mem_stage_succ
    (A : CWComplex.Subcomplex C) (n : ℕ)
    (i : Topology.CWComplex.cell C n) (hi : i ∉ A.I n)
    (c : cellBoundaryCollar n)
    (hc : (skeletonLTStepBoundaryMap C n i
      (cellBoundaryCollarRetraction n c)).1 ∈
        regularNeighborhoodStage C A n) :
    Topology.CWComplex.map n i c.1.1 ∈
      regularNeighborhoodStage C A (n + 1) := by
  have hcclosed : (c.1.1 : CellModel n) ∈ closedBall 0 1 := c.1.2
  have hcsplit : (c.1.1 : CellModel n) ∈
      ball (0 : CellModel n) 1 ∪ sphere 0 1 := by
    rwa [ball_union_sphere]
  rcases hcsplit with hcball | hcsphere
  · apply (map_mem_regularNeighborhoodStage_succ_iff
      C A n i c.1.1 hcball).mpr
    have hcouter : (1 / 2 : ℝ) < ‖(c.1.1 : CellModel n)‖ := c.2
    rw [if_pos hcouter]
    exact hc
  · apply regularNeighborhoodStage_mono C A n
    have hnorm : ‖(c.1.1 : CellModel n)‖ = 1 := by
      simpa [mem_sphere, dist_zero_right] using hcsphere
    change Topology.CWComplex.map n i
      (NormedSpace.normalize (c.1.1 : CellModel n)) ∈
        regularNeighborhoodStage C A n at hc
    rwa [NormedSpace.normalize_eq_self_of_norm_eq_one hnorm] at hc

/-- Data maintained while the cellwise deformation is assembled over finite
skeleta. -/
private structure RegularNeighborhoodStageDeformation
    (A : CWComplex.Subcomplex C) (n : ℕ) where
  map : C(I × RegularNeighborhoodStageSpace C A n,
    RegularNeighborhoodStageSpace C A n)
  eq_self_of_le : ∀ (t : I),
    (t : ℝ) ≤ regularNeighborhoodCellFinish n →
      ∀ x, map (t, x) = x
  fixed : ∀ (t : I) (x : RegularNeighborhoodStageSpace C A n),
    x.1.1 ∈ (A : Set X) → map (t, x) = x
  endpoint_mem : ∀ x : RegularNeighborhoodStageSpace C A n,
    (map (1, x)).1.1 ∈ (A : Set X)

private def regularNeighborhoodStageDeformationZero
    (A : CWComplex.Subcomplex C) :
    RegularNeighborhoodStageDeformation C A 0 where
  map :=
    ⟨fun p ↦ p.2, continuous_snd⟩
  eq_self_of_le _ _ _ := rfl
  fixed _ _ _ := rfl
  endpoint_mem x := by
    have hx : x.1.1 ∈
        (Topology.RelCWComplex.skeletonLT C (0 : ℕ∞) : Set X) := x.1.2
    rw [Topology.CWComplex.skeletonLT_zero_eq_empty] at hx
    exact hx.elim

private def regularNeighborhoodCellRadialMap
    (A : CWComplex.Subcomplex C) (n : ℕ)
    (i : Topology.CWComplex.cell C n) (hi : i ∉ A.I n) :
    C(I × RegularNeighborhoodCellSource C A n i,
      RegularNeighborhoodStageSpace C A (n + 1)) where
  toFun p := by
    let c := cellBoundaryCollarDeformation n
      (regularNeighborhoodCellStart n)
      (regularNeighborhoodCellFinish n)
      (regularNeighborhoodCellStart_lt_finish n)
      (p.1, regularNeighborhoodCellSourceCollar C A n i hi p.2)
    exact ⟨skeletonLTStepClosedCellMap C n i c.1,
      map_cellBoundaryCollar_mem_stage_succ C A n i hi c (by
        rw [cellBoundaryCollarRetraction_deformation]
        exact regularNeighborhoodCellSource_boundary_mem_stage C A n i hi p.2)⟩
  continuous_toFun := by
    let collar : C(I × RegularNeighborhoodCellSource C A n i,
        I × cellBoundaryCollar n) :=
      ⟨fun p ↦ (p.1, regularNeighborhoodCellSourceCollar C A n i hi p.2),
        continuous_fst.prodMk
          ((regularNeighborhoodCellSourceCollar C A n i hi).continuous.comp
            continuous_snd)⟩
    have hdeform : Continuous fun p :
        I × RegularNeighborhoodCellSource C A n i ↦
        cellBoundaryCollarDeformation n
          (regularNeighborhoodCellStart n)
          (regularNeighborhoodCellFinish n)
          (regularNeighborhoodCellStart_lt_finish n)
          (p.1, regularNeighborhoodCellSourceCollar C A n i hi p.2) := by
      exact (((cellBoundaryCollarDeformation n
        (regularNeighborhoodCellStart n)
        (regularNeighborhoodCellFinish n)
        (regularNeighborhoodCellStart_lt_finish n)).continuous.comp
          collar.continuous)).congr (fun _ ↦ rfl)
    exact ((continuous_skeletonLTStepClosedCellMap C n i).comp
      (continuous_subtype_val.comp hdeform)).subtype_mk _

private def regularNeighborhoodCellLowerMap
    (A : CWComplex.Subcomplex C) (n : ℕ)
    (d : RegularNeighborhoodStageDeformation C A n)
    (i : Topology.CWComplex.cell C n) (hi : i ∉ A.I n) :
    C(I × RegularNeighborhoodCellSource C A n i,
      RegularNeighborhoodStageSpace C A (n + 1)) :=
  (regularNeighborhoodStageInclusion C A n).comp <|
    d.map.comp ⟨fun p ↦
      (p.1, regularNeighborhoodCellSourceBoundary C A n i hi p.2),
      continuous_fst.prodMk
        ((regularNeighborhoodCellSourceBoundary C A n i hi).continuous.comp
          continuous_snd)⟩

private theorem regularNeighborhoodCellLower_eq_radial_at_finish
    (A : CWComplex.Subcomplex C) (n : ℕ)
    (d : RegularNeighborhoodStageDeformation C A n)
    (i : Topology.CWComplex.cell C n) (hi : i ∉ A.I n)
    (z : RegularNeighborhoodCellSource C A n i) :
    regularNeighborhoodCellLowerMap C A n d i hi
        (regularNeighborhoodCellFinish n, z) =
      regularNeighborhoodCellRadialMap C A n i hi
        (regularNeighborhoodCellFinish n, z) := by
  have hd := d.eq_self_of_le (regularNeighborhoodCellFinish n) le_rfl
    (regularNeighborhoodCellSourceBoundary C A n i hi z)
  apply Subtype.ext
  apply Subtype.ext
  change (d.map
      (regularNeighborhoodCellFinish n,
        regularNeighborhoodCellSourceBoundary C A n i hi z)).1.1 =
    Topology.CWComplex.map n i
      ((cellBoundaryCollarDeformation n
        (regularNeighborhoodCellStart n)
        (regularNeighborhoodCellFinish n)
        (regularNeighborhoodCellStart_lt_finish n)
        (regularNeighborhoodCellFinish n,
          regularNeighborhoodCellSourceCollar C A n i hi z)).1.1)
  rw [hd]
  rw [cellBoundaryCollarDeformation_eq_retraction_of_le n
    (regularNeighborhoodCellStart_lt_finish n) le_rfl]
  rfl

private def regularNeighborhoodCellOutsideMap
    (A : CWComplex.Subcomplex C) (n : ℕ)
    (d : RegularNeighborhoodStageDeformation C A n)
    (i : Topology.CWComplex.cell C n) (hi : i ∉ A.I n) :
    C(I × RegularNeighborhoodCellSource C A n i,
      RegularNeighborhoodStageSpace C A (n + 1)) where
  toFun p := if (regularNeighborhoodCellFinish n : ℝ) ≤ p.1 then
      regularNeighborhoodCellLowerMap C A n d i hi p
    else regularNeighborhoodCellRadialMap C A n i hi p
  continuous_toFun := by
    apply Continuous.if_le
      (regularNeighborhoodCellLowerMap C A n d i hi).continuous
      (regularNeighborhoodCellRadialMap C A n i hi).continuous
      continuous_const (continuous_subtype_val.comp continuous_fst)
    rintro ⟨t, z⟩ hp
    have ht : t = regularNeighborhoodCellFinish n := by
      apply Subtype.ext
      exact hp.symm
    subst t
    exact regularNeighborhoodCellLower_eq_radial_at_finish C A n d i hi z

private def regularNeighborhoodCellFixedMap
    (A : CWComplex.Subcomplex C) (n : ℕ)
    (i : Topology.CWComplex.cell C n) :
    C(I × RegularNeighborhoodCellSource C A n i,
      RegularNeighborhoodStageSpace C A (n + 1)) where
  toFun p := ⟨skeletonLTStepClosedCellMap C n i p.2.1, p.2.2⟩
  continuous_toFun :=
    ((continuous_skeletonLTStepClosedCellMap C n i).comp
      (continuous_subtype_val.comp continuous_snd)).subtype_mk _

private def regularNeighborhoodCellMap
    (A : CWComplex.Subcomplex C) (n : ℕ)
    (d : RegularNeighborhoodStageDeformation C A n)
    (i : Topology.CWComplex.cell C n) :
    C(I × RegularNeighborhoodCellSource C A n i,
      RegularNeighborhoodStageSpace C A (n + 1)) := by
  classical
  exact if hi : i ∈ A.I n then regularNeighborhoodCellFixedMap C A n i
    else regularNeighborhoodCellOutsideMap C A n d i hi

private abbrev RegularNeighborhoodStageJointSource
    (A : CWComplex.Subcomplex C) (n : ℕ) :=
  ↑(skeletonLTStepJointMap C n ⁻¹'
    (((↑) :
        ↑(Topology.RelCWComplex.skeletonLT C (n + 1) : Set X) → X) ⁻¹'
      regularNeighborhoodStage C A (n + 1)))

private abbrev RegularNeighborhoodStageOldSource
    (A : CWComplex.Subcomplex C) (n : ℕ) :=
  ↑(Sum.inl ⁻¹'
    (skeletonLTStepJointMap C n ⁻¹'
      (((↑) :
          ↑(Topology.RelCWComplex.skeletonLT C (n + 1) : Set X) → X) ⁻¹'
        regularNeighborhoodStage C A (n + 1))))

private abbrev RegularNeighborhoodStageCellsSource
    (A : CWComplex.Subcomplex C) (n : ℕ) :=
  ↑(Sum.inr ⁻¹'
    (skeletonLTStepJointMap C n ⁻¹'
      (((↑) :
          ↑(Topology.RelCWComplex.skeletonLT C (n + 1) : Set X) → X) ⁻¹'
        regularNeighborhoodStage C A (n + 1))))

private def regularNeighborhoodStageOldSourceToStage
    (A : CWComplex.Subcomplex C) (n : ℕ) :
    C(RegularNeighborhoodStageOldSource C A n,
      RegularNeighborhoodStageSpace C A n) where
  toFun x := ⟨x.1,
    (mem_regularNeighborhoodStage_succ_iff_of_mem_skeletonLT
      C A n x.1.2).mp x.2⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

private def regularNeighborhoodStageOldPreMap
    (A : CWComplex.Subcomplex C) (n : ℕ)
    (d : RegularNeighborhoodStageDeformation C A n) :
    C(I × RegularNeighborhoodStageOldSource C A n,
      RegularNeighborhoodStageSpace C A (n + 1)) :=
  (regularNeighborhoodStageInclusion C A n).comp <|
    d.map.comp ⟨fun p ↦
      (p.1, regularNeighborhoodStageOldSourceToStage C A n p.2),
      continuous_fst.prodMk
        ((regularNeighborhoodStageOldSourceToStage C A n).continuous.comp
          continuous_snd)⟩

private def regularNeighborhoodStageCellsPreMap
    (A : CWComplex.Subcomplex C) (n : ℕ)
    (d : RegularNeighborhoodStageDeformation C A n) :
    C(I × RegularNeighborhoodStageCellsSource C A n,
      RegularNeighborhoodStageSpace C A (n + 1)) where
  toFun p := regularNeighborhoodCellMap C A n d p.2.1.1
    (p.1, ⟨p.2.1.2, p.2.2⟩)
  continuous_toFun := by
    let S : Set (Σ i : Topology.CWComplex.cell C n,
        ↑(closedBall (0 : CellModel n) 1)) :=
      Sum.inr ⁻¹'
        (skeletonLTStepJointMap C n ⁻¹'
          (((↑) :
              ↑(Topology.RelCWComplex.skeletonLT C (n + 1) : Set X) → X) ⁻¹'
            regularNeighborhoodStage C A (n + 1)))
    apply (sigmaPreimageHomeomorph S).symm.isQuotientMap.continuous_lift_prod_right
    apply continuous_prod_sigma
    intro i
    exact (regularNeighborhoodCellMap C A n d i).continuous

private def regularNeighborhoodStagePreMap
    (A : CWComplex.Subcomplex C) (n : ℕ)
    (d : RegularNeighborhoodStageDeformation C A n) :
    C(I × RegularNeighborhoodStageJointSource C A n,
      RegularNeighborhoodStageSpace C A (n + 1)) where
  toFun p := by
    rcases p.2 with ⟨x | z, hz⟩
    · exact regularNeighborhoodStageOldPreMap C A n d
        (p.1, ⟨x, hz⟩)
    · exact regularNeighborhoodStageCellsPreMap C A n d
        (p.1, ⟨z, hz⟩)
  continuous_toFun := by
    let S : Set
        (↑(Topology.RelCWComplex.skeletonLT C n : Set X) ⊕
          (Σ _i : Topology.CWComplex.cell C n,
            ↑(closedBall (0 : CellModel n) 1))) :=
      skeletonLTStepJointMap C n ⁻¹'
        (((↑) :
            ↑(Topology.RelCWComplex.skeletonLT C (n + 1) : Set X) → X) ⁻¹'
          regularNeighborhoodStage C A (n + 1))
    apply (sumPreimageHomeomorph S).symm.isQuotientMap.continuous_lift_prod_right
    apply continuous_prod_sum
    · exact (regularNeighborhoodStageOldPreMap C A n d).continuous
    · exact (regularNeighborhoodStageCellsPreMap C A n d).continuous

private theorem regularNeighborhoodCellSourceCollar_of_boundary
    (A : CWComplex.Subcomplex C) (n : ℕ)
    (i : Topology.CWComplex.cell C n) (hi : i ∉ A.I n)
    (x : sphere (0 : CellModel n) 1)
    (hx : Topology.CWComplex.map n i x ∈
      regularNeighborhoodStage C A (n + 1)) :
    regularNeighborhoodCellSourceCollar C A n i hi
        ⟨⟨x, sphere_subset_closedBall x.2⟩, hx⟩ =
      cellBoundaryCollarInclusion n x := by
  apply Subtype.ext
  apply Subtype.ext
  rfl

private theorem regularNeighborhoodCellMap_boundary
    (A : CWComplex.Subcomplex C) (n : ℕ)
    (d : RegularNeighborhoodStageDeformation C A n)
    (i : Topology.CWComplex.cell C n)
    (t : I) (x : sphere (0 : CellModel n) 1)
    (hx : Topology.CWComplex.map n i x ∈
      regularNeighborhoodStage C A (n + 1)) :
    regularNeighborhoodCellMap C A n d i
        (t, ⟨⟨x, sphere_subset_closedBall x.2⟩, hx⟩) =
      regularNeighborhoodStageInclusion C A n
        (d.map (t, ⟨skeletonLTStepBoundaryMap C n i x,
          (mem_regularNeighborhoodStage_succ_iff_of_mem_skeletonLT C A n
            (skeletonLTStepBoundaryMap C n i x).2).mp hx⟩)) := by
  classical
  by_cases hi : i ∈ A.I n
  · rw [regularNeighborhoodCellMap, dif_pos hi]
    have hA : (skeletonLTStepBoundaryMap C n i x).1 ∈ (A : Set X) :=
      A.cellFrontier_subset_of_mem hi ⟨x, x.2, rfl⟩
    rw [d.fixed t _ hA]
    rfl
  · rw [regularNeighborhoodCellMap, dif_neg hi,
      regularNeighborhoodCellOutsideMap]
    change (if (regularNeighborhoodCellFinish n : ℝ) ≤ t then
        regularNeighborhoodCellLowerMap C A n d i hi
          (t, ⟨⟨x, sphere_subset_closedBall x.2⟩, hx⟩)
      else regularNeighborhoodCellRadialMap C A n i hi
          (t, ⟨⟨x, sphere_subset_closedBall x.2⟩, hx⟩)) = _
    split_ifs with ht
    · change regularNeighborhoodStageInclusion C A n
          (d.map (t, regularNeighborhoodCellSourceBoundary C A n i hi
            ⟨⟨x, sphere_subset_closedBall x.2⟩, hx⟩)) = _
      congr 1
      apply d.map.congr_arg
      apply Prod.ext
      · rfl
      · apply Subtype.ext
        apply Subtype.ext
        change Topology.CWComplex.map n i
            (NormedSpace.normalize (x : CellModel n)) =
          Topology.CWComplex.map n i x
        have hxnorm : ‖(x : CellModel n)‖ = 1 := by
          simpa [mem_sphere, dist_zero_right] using x.2
        rw [NormedSpace.normalize_eq_self_of_norm_eq_one hxnorm]
    · have hd : d.map
          (t, ⟨skeletonLTStepBoundaryMap C n i x,
            (mem_regularNeighborhoodStage_succ_iff_of_mem_skeletonLT C A n
              (skeletonLTStepBoundaryMap C n i x).2).mp hx⟩) =
          ⟨skeletonLTStepBoundaryMap C n i x,
            (mem_regularNeighborhoodStage_succ_iff_of_mem_skeletonLT C A n
              (skeletonLTStepBoundaryMap C n i x).2).mp hx⟩ :=
        d.eq_self_of_le t (le_of_not_ge ht) _
      rw [hd]
      apply Subtype.ext
      apply Subtype.ext
      change Topology.CWComplex.map n i
          ((cellBoundaryCollarDeformation n
            (regularNeighborhoodCellStart n)
            (regularNeighborhoodCellFinish n)
            (regularNeighborhoodCellStart_lt_finish n)
            (t, regularNeighborhoodCellSourceCollar C A n i hi
              ⟨⟨x, sphere_subset_closedBall x.2⟩, hx⟩)).1.1) =
        Topology.CWComplex.map n i x
      rw [regularNeighborhoodCellSourceCollar_of_boundary C A n i hi x hx]
      rw [cellBoundaryCollarDeformation_boundary]
      rfl

private theorem mem_sphere_of_map_mem_skeletonLT_deformation (n : ℕ)
    (i : Topology.RelCWComplex.cell C n) {x : CellModel n}
    (hx : x ∈ closedBall 0 1)
    (hmap : Topology.RelCWComplex.map n i x ∈
      (Topology.RelCWComplex.skeletonLT C n : Set X)) :
    x ∈ sphere 0 1 := by
  rw [← ball_union_sphere] at hx
  rcases hx with hx | hx
  · have hopen : Topology.RelCWComplex.map n i x ∈
        Topology.RelCWComplex.openCell (C := C) n i := ⟨x, hx, rfl⟩
    exact ((Topology.RelCWComplex.disjoint_skeletonLT_openCell (C := C)
      (n := (n : ℕ∞)) (m := n) (j := i) le_rfl).notMem_of_mem_left
        hmap hopen).elim
  · exact hx

private theorem cell_eq_or_map_mem_skeletonLT_deformation (n : ℕ)
    (i k : Topology.RelCWComplex.cell C n) {x y : CellModel n}
    (hx : x ∈ closedBall 0 1) (hy : y ∈ closedBall 0 1)
    (hmap : Topology.RelCWComplex.map n i x =
      Topology.RelCWComplex.map n k y) :
    (i = k ∧ x = y) ∨
      Topology.RelCWComplex.map n i x ∈
        (Topology.RelCWComplex.skeletonLT C n : Set X) := by
  by_cases hik : i = k
  · subst k
    by_cases hxy : x = y
    · exact Or.inl ⟨rfl, hxy⟩
    · right
      by_cases hxs : x ∈ sphere (0 : CellModel n) 1
      · exact Topology.RelCWComplex.cellFrontier_subset_skeletonLT
          (C := C) n i ⟨x, hxs, rfl⟩
      by_cases hys : y ∈ sphere (0 : CellModel n) 1
      · exact Topology.RelCWComplex.cellFrontier_subset_skeletonLT
          (C := C) n i ⟨y, hys, hmap.symm⟩
      have hxb : x ∈ ball (0 : CellModel n) 1 := by
        rw [← ball_union_sphere] at hx
        exact hx.resolve_right hxs
      have hyb : y ∈ ball (0 : CellModel n) 1 := by
        rw [← ball_union_sphere] at hy
        exact hy.resolve_right hys
      have hxy' : x = y := (Topology.RelCWComplex.map n i).injOn
        (by rwa [Topology.RelCWComplex.source_eq])
        (by rwa [Topology.RelCWComplex.source_eq]) hmap
      exact (hxy hxy').elim
  · right
    by_cases hxs : x ∈ sphere (0 : CellModel n) 1
    · exact Topology.RelCWComplex.cellFrontier_subset_skeletonLT
        (C := C) n i ⟨x, hxs, rfl⟩
    by_cases hys : y ∈ sphere (0 : CellModel n) 1
    · have hyold := Topology.RelCWComplex.cellFrontier_subset_skeletonLT
          (C := C) n k ⟨y, hys, rfl⟩
      exact hmap.symm ▸ hyold
    have hxb : x ∈ ball (0 : CellModel n) 1 := by
      rw [← ball_union_sphere] at hx
      exact hx.resolve_right hxs
    have hyb : y ∈ ball (0 : CellModel n) 1 := by
      rw [← ball_union_sphere] at hy
      exact hy.resolve_right hys
    have hopenx : Topology.RelCWComplex.map n i x ∈
        Topology.RelCWComplex.openCell (C := C) n i := ⟨x, hxb, rfl⟩
    have hopeny : Topology.RelCWComplex.map n i x ∈
        Topology.RelCWComplex.openCell (C := C) n k := ⟨y, hyb, hmap.symm⟩
    have hne : (⟨n, i⟩ : Σ m, Topology.RelCWComplex.cell C m) ≠ ⟨n, k⟩ := by
      simpa using hik
    exact ((Topology.RelCWComplex.disjoint_openCell_of_ne (C := C) hne).notMem_of_mem_left
      hopenx hopeny).elim

private theorem regularNeighborhoodStagePreMap_eq_of_quotient_eq
    (A : CWComplex.Subcomplex C) (n : ℕ)
    (d : RegularNeighborhoodStageDeformation C A n) (t : I)
    {a b : RegularNeighborhoodStageJointSource C A n}
    (h : regularNeighborhoodStageQuotientMap C A n a =
      regularNeighborhoodStageQuotientMap C A n b) :
    regularNeighborhoodStagePreMap C A n d (t, a) =
      regularNeighborhoodStagePreMap C A n d (t, b) := by
  rcases a with ⟨x | p, hx⟩
  · rcases b with ⟨y | p, hy⟩
    · have hxy : x = y := Subtype.ext (congrArg
        (fun z : RegularNeighborhoodStageSpace C A (n + 1) ↦ z.1.1) h)
      subst y
      rfl
    · obtain ⟨i, y⟩ := p
      have hxy : x.1 = Topology.CWComplex.map n i y := congrArg
        (fun z : RegularNeighborhoodStageSpace C A (n + 1) ↦ z.1.1) h
      have hymem : Topology.CWComplex.map n i y ∈
          (Topology.RelCWComplex.skeletonLT C n : Set X) := by
        rw [← hxy]
        exact x.2
      have hysphere := mem_sphere_of_map_mem_skeletonLT_deformation
        C n i y.2 hymem
      let ys : sphere (0 : CellModel n) 1 := ⟨y, hysphere⟩
      change regularNeighborhoodStageInclusion C A n
          (d.map (t, regularNeighborhoodStageOldSourceToStage C A n ⟨x, hx⟩)) =
        regularNeighborhoodCellMap C A n d i
          (t, ⟨y, hy⟩)
      rw [regularNeighborhoodCellMap_boundary C A n d i t ys hy]
      congr 1
      apply d.map.congr_arg
      apply Prod.ext
      · rfl
      · apply Subtype.ext
        apply Subtype.ext
        exact hxy
  · obtain ⟨i, x⟩ := p
    rcases b with ⟨y | p, hy⟩
    · have hxy : Topology.CWComplex.map n i x = y.1 := congrArg
        (fun z : RegularNeighborhoodStageSpace C A (n + 1) ↦ z.1.1) h
      have hxmem : Topology.CWComplex.map n i x ∈
          (Topology.RelCWComplex.skeletonLT C n : Set X) := by
        rw [hxy]
        exact y.2
      have hxsphere := mem_sphere_of_map_mem_skeletonLT_deformation
        C n i x.2 hxmem
      let xs : sphere (0 : CellModel n) 1 := ⟨x, hxsphere⟩
      change regularNeighborhoodCellMap C A n d i (t, ⟨x, hx⟩) =
        regularNeighborhoodStageInclusion C A n
          (d.map (t, regularNeighborhoodStageOldSourceToStage C A n ⟨y, hy⟩))
      rw [regularNeighborhoodCellMap_boundary C A n d i t xs hx]
      congr 1
      apply d.map.congr_arg
      apply Prod.ext
      · rfl
      · apply Subtype.ext
        apply Subtype.ext
        exact hxy
    · obtain ⟨k, y⟩ := p
      have hxy : Topology.CWComplex.map n i x =
          Topology.CWComplex.map n k y := congrArg
        (fun z : RegularNeighborhoodStageSpace C A (n + 1) ↦ z.1.1) h
      rcases cell_eq_or_map_mem_skeletonLT_deformation C n i k x.2 y.2 hxy with
        hsame | hxmem
      · obtain ⟨rfl, hxy'⟩ := hsame
        have hsub : x = y := Subtype.ext hxy'
        subst y
        rfl
      · have hxsphere := mem_sphere_of_map_mem_skeletonLT_deformation
          C n i x.2 hxmem
        have hymem : Topology.CWComplex.map n k y ∈
            (Topology.RelCWComplex.skeletonLT C n : Set X) := hxy ▸ hxmem
        have hysphere := mem_sphere_of_map_mem_skeletonLT_deformation
          C n k y.2 hymem
        let xs : sphere (0 : CellModel n) 1 := ⟨x, hxsphere⟩
        let ys : sphere (0 : CellModel n) 1 := ⟨y, hysphere⟩
        change regularNeighborhoodCellMap C A n d i (t, ⟨x, hx⟩) =
          regularNeighborhoodCellMap C A n d k (t, ⟨y, hy⟩)
        rw [regularNeighborhoodCellMap_boundary C A n d i t xs hx,
          regularNeighborhoodCellMap_boundary C A n d k t ys hy]
        congr 1
        apply d.map.congr_arg
        apply Prod.ext
        · rfl
        · apply Subtype.ext
          apply Subtype.ext
          exact hxy

private theorem regularNeighborhoodCellMap_eq_self_of_le_start
    (A : CWComplex.Subcomplex C) (n : ℕ)
    (d : RegularNeighborhoodStageDeformation C A n)
    (i : Topology.CWComplex.cell C n) (t : I)
    (ht : (t : ℝ) ≤ regularNeighborhoodCellStart n)
    (z : RegularNeighborhoodCellSource C A n i) :
    regularNeighborhoodCellMap C A n d i (t, z) =
      ⟨skeletonLTStepClosedCellMap C n i z.1, z.2⟩ := by
  classical
  by_cases hi : i ∈ A.I n
  · rw [regularNeighborhoodCellMap, dif_pos hi]
    rfl
  · rw [regularNeighborhoodCellMap, dif_neg hi,
      regularNeighborhoodCellOutsideMap]
    change (if (regularNeighborhoodCellFinish n : ℝ) ≤ t then
        regularNeighborhoodCellLowerMap C A n d i hi (t, z)
      else regularNeighborhoodCellRadialMap C A n i hi (t, z)) = _
    rw [if_neg (not_le.mpr
      (ht.trans_lt (regularNeighborhoodCellStart_lt_finish n)))]
    apply Subtype.ext
    apply Subtype.ext
    change Topology.CWComplex.map n i
        ((cellBoundaryCollarDeformation n
          (regularNeighborhoodCellStart n)
          (regularNeighborhoodCellFinish n)
          (regularNeighborhoodCellStart_lt_finish n)
          (t, regularNeighborhoodCellSourceCollar C A n i hi z)).1.1) =
      Topology.CWComplex.map n i z.1.1
    rw [cellBoundaryCollarDeformation_eq_self_of_le n
      (regularNeighborhoodCellStart_lt_finish n) ht]
    rfl

private theorem regularNeighborhoodCellMap_fixed_of_mem
    (A : CWComplex.Subcomplex C) (n : ℕ)
    (d : RegularNeighborhoodStageDeformation C A n)
    (i : Topology.CWComplex.cell C n) (t : I)
    (z : RegularNeighborhoodCellSource C A n i)
    (hzA : Topology.CWComplex.map n i z.1.1 ∈ (A : Set X)) :
    regularNeighborhoodCellMap C A n d i (t, z) =
      ⟨skeletonLTStepClosedCellMap C n i z.1, z.2⟩ := by
  classical
  by_cases hi : i ∈ A.I n
  · rw [regularNeighborhoodCellMap, dif_pos hi]
    rfl
  · have hzsphere : (z.1.1 : CellModel n) ∈ sphere 0 1 := by
      have hzclosed : (z.1.1 : CellModel n) ∈ closedBall 0 1 := z.1.2
      have hzsplit : (z.1.1 : CellModel n) ∈
          ball (0 : CellModel n) 1 ∪ sphere 0 1 := by
        rwa [ball_union_sphere]
      rcases hzsplit with hzball | hzsphere
      · have hopen : Topology.CWComplex.map n i z.1.1 ∈
            Topology.CWComplex.openCell (C := C) n i :=
          ⟨z.1.1, hzball, rfl⟩
        exact (A.disjoint_openCell_subcomplex_of_not_mem hi).notMem_of_mem_left
          hopen hzA |>.elim
      · exact hzsphere
    let zs : sphere (0 : CellModel n) 1 := ⟨z.1.1, hzsphere⟩
    rw [regularNeighborhoodCellMap_boundary C A n d i t zs z.2]
    have hboundaryA : (skeletonLTStepBoundaryMap C n i zs).1 ∈
        (A : Set X) := by
      exact hzA
    rw [d.fixed t _ hboundaryA]
    rfl

private theorem regularNeighborhoodCellMap_endpoint_mem
    (A : CWComplex.Subcomplex C) (n : ℕ)
    (d : RegularNeighborhoodStageDeformation C A n)
    (i : Topology.CWComplex.cell C n)
    (z : RegularNeighborhoodCellSource C A n i) :
    (regularNeighborhoodCellMap C A n d i (1, z)).1.1 ∈
      (A : Set X) := by
  classical
  by_cases hi : i ∈ A.I n
  · rw [regularNeighborhoodCellMap, dif_pos hi]
    exact A.closedCell_subset_of_mem hi ⟨z.1.1, z.1.2, rfl⟩
  · rw [regularNeighborhoodCellMap, dif_neg hi,
      regularNeighborhoodCellOutsideMap]
    change (if (regularNeighborhoodCellFinish n : ℝ) ≤ (1 : I) then
        regularNeighborhoodCellLowerMap C A n d i hi (1, z)
      else regularNeighborhoodCellRadialMap C A n i hi (1, z)).1.1 ∈ _
    split_ifs with h
    · exact d.endpoint_mem (regularNeighborhoodCellSourceBoundary C A n i hi z)
    · exact (h (regularNeighborhoodCellFinish n).2.2).elim

private noncomputable def regularNeighborhoodStageMap
    (A : CWComplex.Subcomplex C) (n : ℕ)
    (d : RegularNeighborhoodStageDeformation C A n) :
    I × RegularNeighborhoodStageSpace C A (n + 1) →
      RegularNeighborhoodStageSpace C A (n + 1) := fun p ↦
  regularNeighborhoodStagePreMap C A n d
    (p.1, Function.surjInv
      (regularNeighborhoodStageQuotientMap_isQuotient C A n).surjective p.2)

private theorem regularNeighborhoodStageMap_quotientMap
    (A : CWComplex.Subcomplex C) (n : ℕ)
    (d : RegularNeighborhoodStageDeformation C A n) (t : I)
    (z : RegularNeighborhoodStageJointSource C A n) :
    regularNeighborhoodStageMap C A n d
        (t, regularNeighborhoodStageQuotientMap C A n z) =
      regularNeighborhoodStagePreMap C A n d (t, z) := by
  apply regularNeighborhoodStagePreMap_eq_of_quotient_eq C A n d t
  exact Function.surjInv_eq
    (regularNeighborhoodStageQuotientMap_isQuotient C A n).surjective _

private theorem continuous_regularNeighborhoodStageMap
    (A : CWComplex.Subcomplex C) (n : ℕ)
    (d : RegularNeighborhoodStageDeformation C A n) :
    Continuous (regularNeighborhoodStageMap C A n d) := by
  apply (regularNeighborhoodStageQuotientMap_isQuotient C A n).continuous_lift_prod_right
  apply (regularNeighborhoodStagePreMap C A n d).continuous.congr
  rintro ⟨t, z⟩
  exact (regularNeighborhoodStageMap_quotientMap C A n d t z).symm

private theorem regularNeighborhoodStageMap_old
    (A : CWComplex.Subcomplex C) (n : ℕ)
    (d : RegularNeighborhoodStageDeformation C A n) (t : I)
    (x : RegularNeighborhoodStageSpace C A n) :
    regularNeighborhoodStageMap C A n d
        (t, regularNeighborhoodStageInclusion C A n x) =
      regularNeighborhoodStageInclusion C A n (d.map (t, x)) := by
  let z : RegularNeighborhoodStageJointSource C A n :=
    ⟨Sum.inl x.1, regularNeighborhoodStage_mono C A n x.2⟩
  have hz : regularNeighborhoodStageQuotientMap C A n z =
      regularNeighborhoodStageInclusion C A n x := rfl
  rw [← hz, regularNeighborhoodStageMap_quotientMap]
  rfl

private theorem regularNeighborhoodStageMap_cell
    (A : CWComplex.Subcomplex C) (n : ℕ)
    (d : RegularNeighborhoodStageDeformation C A n) (t : I)
    (i : Topology.CWComplex.cell C n)
    (z : RegularNeighborhoodCellSource C A n i) :
    regularNeighborhoodStageMap C A n d
        (t, ⟨skeletonLTStepClosedCellMap C n i z.1, z.2⟩) =
      regularNeighborhoodCellMap C A n d i (t, z) := by
  let w : RegularNeighborhoodStageJointSource C A n :=
    ⟨Sum.inr ⟨i, z.1⟩, z.2⟩
  have hw : regularNeighborhoodStageQuotientMap C A n w =
      ⟨skeletonLTStepClosedCellMap C n i z.1, z.2⟩ := rfl
  rw [← hw, regularNeighborhoodStageMap_quotientMap]
  rfl

private def regularNeighborhoodStageDeformationSucc
    (A : CWComplex.Subcomplex C) (n : ℕ)
    (d : RegularNeighborhoodStageDeformation C A n) :
    RegularNeighborhoodStageDeformation C A (n + 1) where
  map := ⟨regularNeighborhoodStageMap C A n d,
    continuous_regularNeighborhoodStageMap C A n d⟩
  eq_self_of_le t ht x := by
    obtain ⟨z, rfl⟩ :=
      (regularNeighborhoodStageQuotientMap_isQuotient C A n).surjective x
    change regularNeighborhoodStageMap C A n d
      (t, regularNeighborhoodStageQuotientMap C A n z) =
        regularNeighborhoodStageQuotientMap C A n z
    rw [regularNeighborhoodStageMap_quotientMap]
    rcases z with ⟨y | p, hy⟩
    · change regularNeighborhoodStageInclusion C A n
          (d.map (t, regularNeighborhoodStageOldSourceToStage C A n ⟨y, hy⟩)) =
        ⟨skeletonLTStepOldMap C n y, hy⟩
      have ht' : (t : ℝ) ≤ regularNeighborhoodCellFinish n := by
        exact ht.trans <| by
          rw [regularNeighborhoodCellFinish_eq_start_succ]
          exact (regularNeighborhoodCellStart_lt_finish n).le
      rw [d.eq_self_of_le t ht']
      rfl
    · obtain ⟨i, z⟩ := p
      change regularNeighborhoodCellMap C A n d i (t, ⟨z, hy⟩) =
        ⟨skeletonLTStepClosedCellMap C n i z, hy⟩
      apply regularNeighborhoodCellMap_eq_self_of_le_start C A n d i t
      rwa [← regularNeighborhoodCellFinish_eq_start_succ]
  fixed t x hxA := by
    obtain ⟨z, rfl⟩ :=
      (regularNeighborhoodStageQuotientMap_isQuotient C A n).surjective x
    change regularNeighborhoodStageMap C A n d
      (t, regularNeighborhoodStageQuotientMap C A n z) =
        regularNeighborhoodStageQuotientMap C A n z
    rw [regularNeighborhoodStageMap_quotientMap]
    rcases z with ⟨y | p, hy⟩
    · change regularNeighborhoodStageInclusion C A n
          (d.map (t, regularNeighborhoodStageOldSourceToStage C A n ⟨y, hy⟩)) =
        ⟨skeletonLTStepOldMap C n y, hy⟩
      rw [d.fixed t _ hxA]
      rfl
    · obtain ⟨i, z⟩ := p
      change regularNeighborhoodCellMap C A n d i (t, ⟨z, hy⟩) =
        ⟨skeletonLTStepClosedCellMap C n i z, hy⟩
      exact regularNeighborhoodCellMap_fixed_of_mem C A n d i t ⟨z, hy⟩ hxA
  endpoint_mem x := by
    obtain ⟨z, rfl⟩ :=
      (regularNeighborhoodStageQuotientMap_isQuotient C A n).surjective x
    change (regularNeighborhoodStageMap C A n d
      (1, regularNeighborhoodStageQuotientMap C A n z)).1.1 ∈
        (A : Set X)
    rw [regularNeighborhoodStageMap_quotientMap]
    rcases z with ⟨y | p, hy⟩
    · exact d.endpoint_mem
        (regularNeighborhoodStageOldSourceToStage C A n ⟨y, hy⟩)
    · obtain ⟨i, z⟩ := p
      exact regularNeighborhoodCellMap_endpoint_mem C A n d i ⟨z, hy⟩

private def regularNeighborhoodStageDeformation
    (A : CWComplex.Subcomplex C) :
    (n : ℕ) → RegularNeighborhoodStageDeformation C A n :=
  fun n => Nat.rec
    (motive := fun n => RegularNeighborhoodStageDeformation C A n)
    (regularNeighborhoodStageDeformationZero C A)
    (fun n d => regularNeighborhoodStageDeformationSucc C A n d) n

private theorem regularNeighborhoodStageDeformation_succ_old
    (A : CWComplex.Subcomplex C) (n : ℕ) (t : I)
    (x : RegularNeighborhoodStageSpace C A n) :
    (regularNeighborhoodStageDeformation C A (n + 1)).map
        (t, regularNeighborhoodStageInclusion C A n x) =
      regularNeighborhoodStageInclusion C A n
        ((regularNeighborhoodStageDeformation C A n).map (t, x)) :=
  regularNeighborhoodStageMap_old C A n
    (regularNeighborhoodStageDeformation C A n) t x

private def regularNeighborhoodStageCast
    (A : CWComplex.Subcomplex C) {n m : ℕ} (hnm : n ≤ m) :
    C(RegularNeighborhoodStageSpace C A n,
      RegularNeighborhoodStageSpace C A m) where
  toFun x := ⟨⟨x.1.1,
      Topology.RelCWComplex.skeletonLT_mono (C := C) (by
        exact_mod_cast hnm) x.1.2⟩,
    regularNeighborhoodStage_mono_of_le C A hnm x.2⟩
  continuous_toFun :=
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _

private theorem regularNeighborhoodStageCast_refl
    (A : CWComplex.Subcomplex C) (n : ℕ)
    (x : RegularNeighborhoodStageSpace C A n) :
    regularNeighborhoodStageCast C A (le_refl n) x = x := by
  apply Subtype.ext
  apply Subtype.ext
  rfl

private theorem regularNeighborhoodStageCast_step
    (A : CWComplex.Subcomplex C) {n m : ℕ} (hnm : n ≤ m)
    (x : RegularNeighborhoodStageSpace C A n) :
    regularNeighborhoodStageCast C A (Nat.le.step hnm) x =
      regularNeighborhoodStageInclusion C A m
        (regularNeighborhoodStageCast C A hnm x) := by
  apply Subtype.ext
  apply Subtype.ext
  rfl

private theorem regularNeighborhoodStageDeformation_cast
    (A : CWComplex.Subcomplex C) {n m : ℕ} (hnm : n ≤ m)
    (t : I) (x : RegularNeighborhoodStageSpace C A n) :
    (regularNeighborhoodStageDeformation C A m).map
        (t, regularNeighborhoodStageCast C A hnm x) =
      regularNeighborhoodStageCast C A hnm
        ((regularNeighborhoodStageDeformation C A n).map (t, x)) := by
  induction hnm with
  | refl =>
      rw [regularNeighborhoodStageCast_refl,
        regularNeighborhoodStageCast_refl]
  | @step m hnm ih =>
      rw [regularNeighborhoodStageCast_step C A hnm,
        regularNeighborhoodStageDeformation_succ_old,
        ih, ← regularNeighborhoodStageCast_step C A hnm]

private theorem exists_regularNeighborhoodStage
    (A : CWComplex.Subcomplex C) (x : ↑(regularNeighborhood C A)) :
    ∃ n, x.1 ∈ regularNeighborhoodStage C A n := by
  have hx := x.2
  change x.1 ∈ ⋃ n, regularNeighborhoodStage C A n at hx
  exact Set.mem_iUnion.mp hx

private noncomputable def regularNeighborhoodStageIndex
    (A : CWComplex.Subcomplex C) (x : ↑(regularNeighborhood C A)) : ℕ := by
  classical
  exact Nat.find (exists_regularNeighborhoodStage C A x)

private theorem regularNeighborhoodStageIndex_spec
    (A : CWComplex.Subcomplex C) (x : ↑(regularNeighborhood C A)) :
    x.1 ∈ regularNeighborhoodStage C A
      (regularNeighborhoodStageIndex C A x) := by
  classical
  exact Nat.find_spec (exists_regularNeighborhoodStage C A x)

private def regularNeighborhoodChosenStagePoint
    (A : CWComplex.Subcomplex C) (x : ↑(regularNeighborhood C A)) :
    RegularNeighborhoodStageSpace C A
      (regularNeighborhoodStageIndex C A x) :=
  ⟨⟨x.1, regularNeighborhoodStage_subset_skeletonLT C A
      (regularNeighborhoodStageIndex C A x)
      (regularNeighborhoodStageIndex_spec C A x)⟩,
    regularNeighborhoodStageIndex_spec C A x⟩

private theorem regularNeighborhoodStageIndex_le_of_mem
    (A : CWComplex.Subcomplex C) (x : ↑(regularNeighborhood C A))
    (n : ℕ) (hx : x.1 ∈ regularNeighborhoodStage C A n) :
    regularNeighborhoodStageIndex C A x ≤ n := by
  classical
  exact Nat.find_min' (exists_regularNeighborhoodStage C A x) hx

private def regularNeighborhoodDeformationMap
    (A : CWComplex.Subcomplex C) :
    I × ↑(regularNeighborhood C A) → ↑(regularNeighborhood C A) :=
  fun p ↦
    let n := regularNeighborhoodStageIndex C A p.2
    let y := (regularNeighborhoodStageDeformation C A n).map
      (p.1, regularNeighborhoodChosenStagePoint C A p.2)
    ⟨y.1.1, regularNeighborhoodStage_subset_regularNeighborhood C A n y.2⟩

private theorem regularNeighborhoodDeformationMap_eq_stage
    (A : CWComplex.Subcomplex C) (t : I)
    (x : ↑(regularNeighborhood C A)) (n : ℕ)
    (hxsk : x.1 ∈ (Topology.RelCWComplex.skeletonLT C n : Set X)) :
    regularNeighborhoodDeformationMap C A (t, x) =
      ⟨((regularNeighborhoodStageDeformation C A n).map
        (t, ⟨⟨x.1, hxsk⟩,
          (mem_regularNeighborhood_iff_of_mem_skeletonLT C A n hxsk).mp x.2⟩)).1.1,
        regularNeighborhoodStage_subset_regularNeighborhood C A n
          ((regularNeighborhoodStageDeformation C A n).map
            (t, ⟨⟨x.1, hxsk⟩,
              (mem_regularNeighborhood_iff_of_mem_skeletonLT C A n hxsk).mp x.2⟩)).2⟩ := by
  let k := regularNeighborhoodStageIndex C A x
  have hxstage : x.1 ∈ regularNeighborhoodStage C A n :=
    (mem_regularNeighborhood_iff_of_mem_skeletonLT C A n hxsk).mp x.2
  have hkn : k ≤ n := regularNeighborhoodStageIndex_le_of_mem C A x n hxstage
  have hcast := regularNeighborhoodStageDeformation_cast C A hkn t
    (regularNeighborhoodChosenStagePoint C A x)
  have hinput : regularNeighborhoodStageCast C A hkn
      (regularNeighborhoodChosenStagePoint C A x) =
      ⟨⟨x.1, hxsk⟩, hxstage⟩ := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  rw [hinput] at hcast
  apply Subtype.ext
  change ((regularNeighborhoodStageDeformation C A k).map
      (t, regularNeighborhoodChosenStagePoint C A x)).1.1 =
    ((regularNeighborhoodStageDeformation C A n).map
      (t, ⟨⟨x.1, hxsk⟩, hxstage⟩)).1.1
  exact (congrArg
    (fun z : RegularNeighborhoodStageSpace C A n ↦ z.1.1) hcast).symm

/-! ## The global closed-cell quotient -/

private abbrev ClosedCells (C : Set X) [CWComplex C] :=
  Σ n : ℕ, Σ i : Topology.CWComplex.cell C n,
    ↑(closedBall (0 : CellModel n) 1)

private def closedCellsMap : ClosedCells C → ↑C := fun z ↦
  ⟨Topology.CWComplex.map z.1 z.2.1 z.2.2,
    Topology.RelCWComplex.closedCell_subset_complex
      (C := C) z.1 z.2.1 ⟨z.2.2, z.2.2.2, rfl⟩⟩

private theorem continuous_closedCellsMap : Continuous (closedCellsMap C) := by
  apply continuous_sigma
  intro n
  apply continuous_sigma
  intro i
  exact (Topology.CWComplex.continuousOn n i).restrict.subtype_mk _

private theorem surjective_closedCellsMap : Surjective (closedCellsMap C) := by
  intro x
  let xv : X := x.1
  have hxC : xv ∈ C := x.2
  rw [← Topology.CWComplex.union (C := C)] at hxC
  have hx : x.1 ∈
      ⋃ (n : ℕ) (i : Topology.CWComplex.cell C n),
        Topology.CWComplex.closedCell (C := C) n i := by
    exact hxC
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hn
  obtain ⟨z, hz, hzx⟩ := hi
  exact ⟨⟨n, i, ⟨z, hz⟩⟩, Subtype.ext hzx⟩

private theorem closedCellsMap_isQuotient : IsQuotientMap (closedCellsMap C) := by
  rw [isQuotientMap_iff_isClosed]
  refine ⟨surjective_closedCellsMap C, ?_⟩
  intro T
  constructor
  · intro hT
    exact hT.preimage (continuous_closedCellsMap C)
  · intro hpre
    rw [isClosed_sigma_iff] at hpre
    have hpre' : ∀ (n : ℕ) (i : Topology.CWComplex.cell C n),
        IsClosed {z : ↑(closedBall (0 : CellModel n) 1) |
          closedCellsMap C ⟨n, i, z⟩ ∈ T} := by
      intro n i
      have hn := hpre n
      rw [isClosed_sigma_iff] at hn
      exact hn i
    let B : Set X := ((↑) : ↑C → X) '' T
    have hBsub : B ⊆ C := by
      rintro _ ⟨x, _hxT, rfl⟩
      exact x.2
    have hBclosed : IsClosed B := by
      apply (Topology.CWComplex.closed C B hBsub).mpr
      intro n i
      let S : Set ↑(closedBall (0 : CellModel n) 1) :=
        {z | closedCellsMap C ⟨n, i, z⟩ ∈ T}
      let φ : ↑(closedBall (0 : CellModel n) 1) → X :=
        fun z ↦ Topology.CWComplex.map n i z
      have hSclosed : IsClosed S := hpre' n i
      have hScompact : IsCompact S := hSclosed.isCompact
      have hφcontinuous : Continuous φ :=
        (Topology.CWComplex.continuousOn n i).restrict
      have hφSclosed : IsClosed (φ '' S) :=
        (hScompact.image hφcontinuous).isClosed
      have hφSeq : φ '' S =
          B ∩ Topology.CWComplex.closedCell (C := C) n i := by
        ext x
        constructor
        · rintro ⟨z, hzS, rfl⟩
          refine ⟨⟨closedCellsMap C ⟨n, i, z⟩, hzS, rfl⟩, ?_⟩
          exact ⟨z, z.2, rfl⟩
        · rintro ⟨⟨y, hyT, hyx⟩, z, hz, hzx⟩
          let z' : ↑(closedBall (0 : CellModel n) 1) := ⟨z, hz⟩
          refine ⟨z', ?_, hzx⟩
          change closedCellsMap C ⟨n, i, z'⟩ ∈ T
          have heq : closedCellsMap C ⟨n, i, z'⟩ = y := by
            apply Subtype.ext
            exact hzx.trans hyx.symm
          rwa [heq]
      exact hφSeq ▸ hφSclosed
    have hTeq : T = ((↑) : ↑C → X) ⁻¹' B := by
      ext x
      simp only [B, Set.mem_preimage, Set.mem_image]
      constructor
      · intro hx
        exact ⟨x, hx, rfl⟩
      · rintro ⟨y, hy, hyx⟩
        have : y = x := Subtype.ext hyx
        rwa [← this]
    rw [hTeq]
    exact hBclosed.preimage continuous_subtype_val

private def regularNeighborhoodInComplexHomeomorph
    (A : CWComplex.Subcomplex C) :
    ↑(((↑) : ↑C → X) ⁻¹' regularNeighborhood C A) ≃ₜ
      ↑(regularNeighborhood C A) where
  toFun x := ⟨x.1.1, x.2⟩
  invFun x := ⟨⟨x.1, regularNeighborhood_subset_complex C A x.2⟩, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    (continuous_subtype_val.subtype_mk _).subtype_mk _

private abbrev ClosedCellsNeighborhoodSource
    (A : CWComplex.Subcomplex C) :=
  ↑(closedCellsMap C ⁻¹'
    (((↑) : ↑C → X) ⁻¹' regularNeighborhood C A))

private def closedCellsNeighborhoodMap
    (A : CWComplex.Subcomplex C) :
    ClosedCellsNeighborhoodSource C A → ↑(regularNeighborhood C A) :=
  fun z ↦ ⟨(closedCellsMap C z.1).1, z.2⟩

private theorem closedCellsNeighborhoodMap_isQuotient
    (A : CWComplex.Subcomplex C) :
    IsQuotientMap (closedCellsNeighborhoodMap C A) := by
  let N : Set ↑C :=
    ((↑) : ↑C → X) ⁻¹' regularNeighborhood C A
  have hrestrict : IsQuotientMap (N.restrictPreimage (closedCellsMap C)) :=
    (closedCellsMap_isQuotient C).restrictPreimage_isOpen
      (isOpen_regularNeighborhood C A)
  have hhomeo : IsQuotientMap (regularNeighborhoodInComplexHomeomorph C A) :=
    (regularNeighborhoodInComplexHomeomorph C A).isQuotientMap
  have heq : closedCellsNeighborhoodMap C A =
      (regularNeighborhoodInComplexHomeomorph C A) ∘
        N.restrictPreimage (closedCellsMap C) := by
    funext z
    rfl
  rw [heq]
  exact hhomeo.comp hrestrict

private abbrev GlobalCellSource
    (A : CWComplex.Subcomplex C) (n : ℕ)
    (i : Topology.CWComplex.cell C n) :=
  ↑{z : ↑(closedBall (0 : CellModel n) 1) |
    Topology.CWComplex.map n i z ∈ regularNeighborhood C A}

private def globalCellStageMap
    (A : CWComplex.Subcomplex C) (n : ℕ)
    (i : Topology.CWComplex.cell C n) :
    C(GlobalCellSource C A n i,
      RegularNeighborhoodStageSpace C A (n + 1)) where
  toFun z := ⟨skeletonLTStepClosedCellMap C n i z.1,
    (mem_regularNeighborhood_iff_of_mem_skeletonLT C A (n + 1)
      (skeletonLTStepClosedCellMap C n i z.1).2).mp z.2⟩
  continuous_toFun :=
    ((continuous_skeletonLTStepClosedCellMap C n i).comp
      continuous_subtype_val).subtype_mk _

private def globalCellDeformation
    (A : CWComplex.Subcomplex C) (n : ℕ)
    (i : Topology.CWComplex.cell C n) :
    C(I × GlobalCellSource C A n i,
      ↑(regularNeighborhood C A)) where
  toFun p :=
    let y := (regularNeighborhoodStageDeformation C A (n + 1)).map
      (p.1, globalCellStageMap C A n i p.2)
    ⟨y.1.1,
      regularNeighborhoodStage_subset_regularNeighborhood C A (n + 1) y.2⟩
  continuous_toFun := by
    have hstage : Continuous fun p : I × GlobalCellSource C A n i ↦
        (regularNeighborhoodStageDeformation C A (n + 1)).map
          (p.1, globalCellStageMap C A n i p.2) := by
      exact ((regularNeighborhoodStageDeformation C A (n + 1)).map.continuous.comp
      (continuous_fst.prodMk
        ((globalCellStageMap C A n i).continuous.comp continuous_snd))).congr
          (fun _ ↦ rfl)
    exact ((continuous_subtype_val.comp continuous_subtype_val).comp
      hstage).subtype_mk _

private theorem regularNeighborhoodDeformationMap_cell
    (A : CWComplex.Subcomplex C) (n : ℕ)
    (i : Topology.CWComplex.cell C n) (t : I)
    (z : GlobalCellSource C A n i) :
    regularNeighborhoodDeformationMap C A
        (t, ⟨(skeletonLTStepClosedCellMap C n i z.1).1, z.2⟩) =
      globalCellDeformation C A n i (t, z) := by
  have hxsk : (skeletonLTStepClosedCellMap C n i z.1).1 ∈
      (Topology.RelCWComplex.skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (skeletonLTStepClosedCellMap C n i z.1).2
  exact regularNeighborhoodDeformationMap_eq_stage C A t _ (n + 1) hxsk

private theorem continuous_closedCellsNeighborhoodPreDeformation
    (A : CWComplex.Subcomplex C) :
    Continuous fun p : I × ClosedCellsNeighborhoodSource C A ↦
      regularNeighborhoodDeformationMap C A
        (p.1, closedCellsNeighborhoodMap C A p.2) := by
  let S : Set (ClosedCells C) :=
    closedCellsMap C ⁻¹'
      (((↑) : ↑C → X) ⁻¹' regularNeighborhood C A)
  apply (sigmaPreimageHomeomorph S).symm.isQuotientMap.continuous_lift_prod_right
  apply continuous_prod_sigma
  intro n
  let Sn : Set (Σ i : Topology.CWComplex.cell C n,
      ↑(closedBall (0 : CellModel n) 1)) :=
    (fun z : (Σ i : Topology.CWComplex.cell C n,
        ↑(closedBall (0 : CellModel n) 1)) ↦
      (⟨n, z⟩ : ClosedCells C)) ⁻¹' S
  apply (sigmaPreimageHomeomorph Sn).symm.isQuotientMap.continuous_lift_prod_right
  apply continuous_prod_sigma
  intro i
  apply (globalCellDeformation C A n i).continuous.congr
  rintro ⟨t, z⟩
  exact (regularNeighborhoodDeformationMap_cell C A n i t z).symm

private theorem continuous_regularNeighborhoodDeformationMap
    (A : CWComplex.Subcomplex C) :
    Continuous (regularNeighborhoodDeformationMap C A) := by
  apply (closedCellsNeighborhoodMap_isQuotient C A).continuous_lift_prod_right
  apply (continuous_closedCellsNeighborhoodPreDeformation C A).congr
  rintro ⟨t, z⟩
  rfl

private theorem regularNeighborhoodDeformationMap_zero
    (A : CWComplex.Subcomplex C) (x : ↑(regularNeighborhood C A)) :
    regularNeighborhoodDeformationMap C A (0, x) = x := by
  let n := regularNeighborhoodStageIndex C A x
  have h := (regularNeighborhoodStageDeformation C A n).eq_self_of_le
    0 (regularNeighborhoodCellFinish n).2.1
    (regularNeighborhoodChosenStagePoint C A x)
  apply Subtype.ext
  exact congrArg (fun z : RegularNeighborhoodStageSpace C A n ↦ z.1.1) h

private theorem regularNeighborhoodDeformationMap_fixed
    (A : CWComplex.Subcomplex C) (t : I)
    (x : ↑(regularNeighborhood C A)) (hx : x.1 ∈ (A : Set X)) :
    regularNeighborhoodDeformationMap C A (t, x) = x := by
  let n := regularNeighborhoodStageIndex C A x
  have h := (regularNeighborhoodStageDeformation C A n).fixed t
    (regularNeighborhoodChosenStagePoint C A x) hx
  apply Subtype.ext
  exact congrArg (fun z : RegularNeighborhoodStageSpace C A n ↦ z.1.1) h

private theorem regularNeighborhoodDeformationMap_endpoint_mem
    (A : CWComplex.Subcomplex C) (x : ↑(regularNeighborhood C A)) :
    (regularNeighborhoodDeformationMap C A (1, x)).1 ∈ (A : Set X) := by
  let n := regularNeighborhoodStageIndex C A x
  exact (regularNeighborhoodStageDeformation C A n).endpoint_mem
    (regularNeighborhoodChosenStagePoint C A x)

private def regularNeighborhoodDeformation
    (A : CWComplex.Subcomplex C) :
    C(I × ↑(regularNeighborhood C A), ↑(regularNeighborhood C A)) :=
  ⟨regularNeighborhoodDeformationMap C A,
    continuous_regularNeighborhoodDeformationMap C A⟩

private def regularNeighborhoodRetraction
    (A : CWComplex.Subcomplex C) :
    C(↑(regularNeighborhood C A), ↑(A : Set X)) where
  toFun x := ⟨(regularNeighborhoodDeformationMap C A (1, x)).1,
    regularNeighborhoodDeformationMap_endpoint_mem C A x⟩
  continuous_toFun := by
    exact (continuous_subtype_val.comp
      ((regularNeighborhoodDeformation C A).continuous.comp
        (continuous_const.prodMk continuous_id))).subtype_mk _

private theorem regularNeighborhoodRetraction_inclusion
    (A : CWComplex.Subcomplex C) :
    (regularNeighborhoodRetraction C A).comp
        (regularNeighborhoodInclusion C A) =
      ContinuousMap.id ↑(A : Set X) := by
  ext x
  have h := regularNeighborhoodDeformationMap_fixed C A 1
    (regularNeighborhoodInclusion C A x) x.2
  exact congrArg
    (fun y : ↑(regularNeighborhood C A) ↦ y.1) h

private def regularNeighborhoodHomotopy
    (A : CWComplex.Subcomplex C) :
    (ContinuousMap.id ↑(regularNeighborhood C A)).HomotopyRel
      ((regularNeighborhoodInclusion C A).comp
        (regularNeighborhoodRetraction C A))
      (Set.range (regularNeighborhoodInclusion C A)) where
  toFun := regularNeighborhoodDeformationMap C A
  continuous_toFun := continuous_regularNeighborhoodDeformationMap C A
  map_zero_left := regularNeighborhoodDeformationMap_zero C A
  map_one_left x := by
    apply Subtype.ext
    rfl
  prop' t x hx := by
    obtain ⟨a, rfl⟩ := hx
    exact regularNeighborhoodDeformationMap_fixed C A t
      (regularNeighborhoodInclusion C A a) a.2

/-- **Hatcher, Appendix Proposition A.5.** The canonical fixed-width regular
neighborhood of a classical CW subcomplex strongly deformation retracts onto
the subcomplex.  The construction is uniform for the empty subcomplex, whose
regular neighborhood is empty. -/
def regularNeighborhoodStrongDeformationRetract
    (A : CWComplex.Subcomplex C) :
    Hatcher.StrongDeformationRetract
      (regularNeighborhoodInclusion C A) where
  retract := regularNeighborhoodRetraction C A
  retract_inclusion := regularNeighborhoodRetraction_inclusion C A
  deformation := regularNeighborhoodHomotopy C A

end Hatcher.ClassicalCW
