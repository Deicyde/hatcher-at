/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Hatcher.Singular.DoubleSimplexFundamentalClass
import Hatcher.Singular.DoubleSimplexSwap
import Hatcher.Singular.StandardSimplexDisk
import Hatcher.Sphere.CoordinateSignChanges
import Hatcher.Sphere.HemisphereCharts
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# The ordered double simplex as a sphere

This file identifies the pushout of two ordered standard simplices along their
common boundary with Mathlib's standard sphere, and transports the literal
difference of the two top-dimensional simplices across this homeomorphism.
-/

noncomputable section

open AlgebraicTopology CategoryTheory Limits Metric Set Topology

namespace Hatcher.Simplex

private noncomputable def hemisphereVector (n : ℕ) (positive : Bool)
    (x : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin (n + 1)) :=
  WithLp.toLp 2 <| Fin.lastCases
    (if positive then Real.sqrt (1 - ‖x‖ ^ 2)
      else -Real.sqrt (1 - ‖x‖ ^ 2))
    (fun i ↦ x i)

@[simp]
private theorem hemisphereVector_castSucc (n : ℕ) (positive : Bool)
    (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    hemisphereVector n positive x i.castSucc = x i := by
  simp [hemisphereVector]

@[simp]
private theorem hemisphereVector_last (n : ℕ) (positive : Bool)
    (x : EuclideanSpace ℝ (Fin n)) :
    hemisphereVector n positive x (Fin.last n) =
      if positive then Real.sqrt (1 - ‖x‖ ^ 2)
      else -Real.sqrt (1 - ‖x‖ ^ 2) := by
  simp [hemisphereVector]

private theorem hemisphereVector_norm_sq (n : ℕ) (positive : Bool)
    (x : EuclideanSpace ℝ (Fin n)) (hx : ‖x‖ ≤ 1) :
    ‖hemisphereVector n positive x‖ ^ 2 = 1 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  rw [Fin.sum_univ_castSucc]
  simp only [hemisphereVector_castSucc, hemisphereVector_last]
  rw [← EuclideanSpace.real_norm_sq_eq]
  have hnonneg : 0 ≤ 1 - ‖x‖ ^ 2 := by nlinarith [norm_nonneg x]
  split
  · rw [Real.sq_sqrt hnonneg]
    ring
  · rw [neg_sq, Real.sq_sqrt hnonneg]
    ring

private noncomputable def rawDiskHemispherePoint (n : ℕ) (positive : Bool)
    (x : closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :
    Hatcher.Sphere.RawSphere n :=
  ⟨hemisphereVector n positive x.1, by
    rw [mem_sphere_zero_iff_norm]
    have hx : ‖x.1‖ ≤ 1 := by
      simpa only [mem_closedBall, dist_zero_right] using x.2
    have hsquare := hemisphereVector_norm_sq n positive x.1 hx
    nlinarith [norm_nonneg (hemisphereVector n positive x.1)]⟩

private theorem continuous_rawDiskHemispherePoint (n : ℕ)
    (positive : Bool) :
    Continuous (rawDiskHemispherePoint n positive) := by
  apply Continuous.subtype_mk
  unfold hemisphereVector
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simp only [Fin.lastCases_last]
    cases positive
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact (Real.continuous_sqrt.comp
        ((continuous_const : Continuous (fun _ :
            closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 ↦ (1 : ℝ))).sub
          ((continuous_norm.comp continuous_subtype_val).pow 2))).neg
    · simp only [↓reduceIte]
      exact Real.continuous_sqrt.comp
        ((continuous_const : Continuous (fun _ :
            closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 ↦ (1 : ℝ))).sub
          ((continuous_norm.comp continuous_subtype_val).pow 2))
  · simp only [Fin.lastCases_castSucc]
    exact (PiLp.continuous_apply 2 (fun _ : Fin n ↦ ℝ) j).comp
      continuous_subtype_val

/-- The two closed hemispheres, parametrized by Mathlib's standard disk.
The boolean chooses the sign of the last coordinate. -/
private noncomputable def diskHemispherePoint (n : ℕ) (positive : Bool) :
    ((TopCat.disk.{0} n : TopCat.{0}) : Type) →
      ((TopCat.sphere.{0} n : TopCat.{0}) : Type) :=
  fun x ↦ (Hatcher.Sphere.sphereULiftHomeomorph n).symm
    (rawDiskHemispherePoint n positive x.down)

private theorem continuous_diskHemispherePoint (n : ℕ) (positive : Bool) :
    Continuous (diskHemispherePoint n positive) :=
  (Hatcher.Sphere.sphereULiftHomeomorph n).symm.continuous.comp <|
    (continuous_rawDiskHemispherePoint n positive).comp Homeomorph.ulift.continuous

private noncomputable def diskHemisphereMap (n : ℕ) (positive : Bool) :
    TopCat.disk.{0} n ⟶ TopCat.sphere.{0} n :=
  TopCat.ofHom ⟨diskHemispherePoint n positive,
    continuous_diskHemispherePoint n positive⟩

private theorem hemisphereVector_eq_of_norm_eq_one (n : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) (hx : ‖x‖ = 1) :
    hemisphereVector n true x = hemisphereVector n false x := by
  apply PiLp.ext
  intro i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simp [hemisphereVector, hx]
  · simp [hemisphereVector]

private theorem diskHemisphereMap_boundary (n : ℕ) :
    TopCat.diskBoundaryInclusion.{0} n ≫ diskHemisphereMap n true =
      TopCat.diskBoundaryInclusion.{0} n ≫ diskHemisphereMap n false := by
  ext x
  apply (Hatcher.Sphere.sphereULiftHomeomorph n).injective
  apply Subtype.ext
  exact hemisphereVector_eq_of_norm_eq_one n x.down.1 <| by
    simpa only [mem_sphere_zero_iff_norm] using x.down.2

private noncomputable abbrev diskDouble (n : ℕ) : TopCat.{0} :=
  pushout (TopCat.diskBoundaryInclusion.{0} n)
    (TopCat.diskBoundaryInclusion.{0} n)

private noncomputable def diskDoubleToSphere (n : ℕ) :
    diskDouble n ⟶ TopCat.sphere.{0} n :=
  pushout.desc (diskHemisphereMap n true) (diskHemisphereMap n false)
    (diskHemisphereMap_boundary n)

@[simp]
private theorem diskDoubleToSphere_inl (n : ℕ) :
    pushout.inl (TopCat.diskBoundaryInclusion.{0} n)
          (TopCat.diskBoundaryInclusion.{0} n) ≫
        diskDoubleToSphere n =
      diskHemisphereMap n true := by
  apply pushout.inl_desc

@[simp]
private theorem diskDoubleToSphere_inr (n : ℕ) :
    pushout.inr (TopCat.diskBoundaryInclusion.{0} n)
          (TopCat.diskBoundaryInclusion.{0} n) ≫
        diskDoubleToSphere n =
      diskHemisphereMap n false := by
  apply pushout.inr_desc

private noncomputable def sphereFront (n : ℕ)
    (y : Hatcher.Sphere.RawSphere n) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun i ↦ y.1 i.castSucc

@[simp]
private theorem sphereFront_apply (n : ℕ)
    (y : Hatcher.Sphere.RawSphere n) (i : Fin n) :
    sphereFront n y i = y.1 i.castSucc :=
  rfl

private theorem sphereFront_norm_sq_add_last_sq (n : ℕ)
    (y : Hatcher.Sphere.RawSphere n) :
    ‖sphereFront n y‖ ^ 2 + y.1 (Fin.last n) ^ 2 = 1 := by
  have hy : ‖y.1‖ = 1 := by
    simpa only [mem_sphere_zero_iff_norm] using y.2
  have hsquare : ‖y.1‖ ^ 2 = 1 := by rw [hy]; norm_num
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_castSucc] at hsquare
  rw [EuclideanSpace.real_norm_sq_eq]
  simpa only [sphereFront_apply] using hsquare

private theorem sphereFront_mem_closedBall (n : ℕ)
    (y : Hatcher.Sphere.RawSphere n) :
    sphereFront n y ∈ closedBall
      (0 : EuclideanSpace ℝ (Fin n)) 1 := by
  rw [mem_closedBall, dist_zero_right]
  have h := sphereFront_norm_sq_add_last_sq n y
  nlinarith [norm_nonneg (sphereFront n y),
    sq_nonneg (y.1 (Fin.last n))]

private theorem hemisphereVector_sphereFront_of_last_nonneg (n : ℕ)
    (y : Hatcher.Sphere.RawSphere n) (hy : 0 ≤ y.1 (Fin.last n)) :
    hemisphereVector n true (sphereFront n y) = y.1 := by
  apply PiLp.ext
  intro i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simp only [hemisphereVector_last, ↓reduceIte]
    have hrad : 1 - ‖sphereFront n y‖ ^ 2 =
        y.1 (Fin.last n) ^ 2 := by
      nlinarith [sphereFront_norm_sq_add_last_sq n y]
    rw [hrad, Real.sqrt_sq_eq_abs, abs_of_nonneg hy]
  · simp

private theorem hemisphereVector_sphereFront_of_last_nonpos (n : ℕ)
    (y : Hatcher.Sphere.RawSphere n) (hy : y.1 (Fin.last n) ≤ 0) :
    hemisphereVector n false (sphereFront n y) = y.1 := by
  apply PiLp.ext
  intro i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simp only [hemisphereVector_last, Bool.false_eq_true, ↓reduceIte]
    have hrad : 1 - ‖sphereFront n y‖ ^ 2 =
        y.1 (Fin.last n) ^ 2 := by
      nlinarith [sphereFront_norm_sq_add_last_sq n y]
    rw [hrad, Real.sqrt_sq_eq_abs, abs_of_nonpos hy]
    ring
  · simp

private theorem diskHemispherePoint_injective (n : ℕ) (positive : Bool) :
    Function.Injective (diskHemispherePoint n positive) := by
  intro x y hxy
  have hraw : rawDiskHemispherePoint n positive x.down =
      rawDiskHemispherePoint n positive y.down :=
    (Hatcher.Sphere.sphereULiftHomeomorph n).symm.injective hxy
  have hv : hemisphereVector n positive x.down.1 =
      hemisphereVector n positive y.down.1 :=
    congrArg Subtype.val hraw
  apply ULift.ext
  apply Subtype.ext
  apply PiLp.ext
  intro i
  have hi := congrArg (fun z : EuclideanSpace ℝ (Fin (n + 1)) ↦
    z i.castSucc) hv
  simpa using hi

private theorem diskHemispherePoint_cross (n : ℕ)
    (x y : ((TopCat.disk.{0} n : TopCat.{0}) : Type))
    (hxy : diskHemispherePoint n true x =
      diskHemispherePoint n false y) :
    ∃ a : ((TopCat.diskBoundary.{0} n : TopCat.{0}) : Type),
      TopCat.diskBoundaryInclusion.{0} n a = x ∧
      TopCat.diskBoundaryInclusion.{0} n a = y := by
  have hraw : rawDiskHemispherePoint n true x.down =
      rawDiskHemispherePoint n false y.down :=
    (Hatcher.Sphere.sphereULiftHomeomorph n).symm.injective hxy
  have hv : hemisphereVector n true x.down.1 =
      hemisphereVector n false y.down.1 :=
    congrArg Subtype.val hraw
  have hfront : x.down.1 = y.down.1 := by
    apply PiLp.ext
    intro i
    have hi := congrArg (fun z : EuclideanSpace ℝ (Fin (n + 1)) ↦
      z i.castSucc) hv
    simpa using hi
  have hlast := congrArg (fun z : EuclideanSpace ℝ (Fin (n + 1)) ↦
    z (Fin.last n)) hv
  simp only [hemisphereVector_last, ↓reduceIte, Bool.false_eq_true] at hlast
  rw [← hfront] at hlast
  have hsqrt : Real.sqrt (1 - ‖x.down.1‖ ^ 2) = 0 := by
    nlinarith [Real.sqrt_nonneg (1 - ‖x.down.1‖ ^ 2)]
  have hxle : ‖x.down.1‖ ≤ 1 := by
    simpa only [mem_closedBall, dist_zero_right] using x.down.2
  have hrad : 0 ≤ 1 - ‖x.down.1‖ ^ 2 := by
    nlinarith [norm_nonneg x.down.1]
  have hxnorm : ‖x.down.1‖ = 1 := by
    have hsquare := Real.sq_sqrt hrad
    rw [hsqrt] at hsquare
    nlinarith [norm_nonneg x.down.1]
  let a : ((TopCat.diskBoundary.{0} n : TopCat.{0}) : Type) :=
    ⟨⟨x.down.1, by
      simpa only [mem_sphere_zero_iff_norm] using hxnorm⟩⟩
  refine ⟨a, ?_, ?_⟩
  · apply ULift.ext
    apply Subtype.ext
    rfl
  · apply ULift.ext
    apply Subtype.ext
    exact hfront

private theorem diskDouble_isPushout_underlying (n : ℕ) :
    IsPushout
      ((forget TopCat).map (TopCat.diskBoundaryInclusion.{0} n))
      ((forget TopCat).map (TopCat.diskBoundaryInclusion.{0} n))
      ((forget TopCat).map
        (pushout.inl (TopCat.diskBoundaryInclusion.{0} n)
          (TopCat.diskBoundaryInclusion.{0} n)))
      ((forget TopCat).map
        (pushout.inr (TopCat.diskBoundaryInclusion.{0} n)
          (TopCat.diskBoundaryInclusion.{0} n))) := by
  simpa using IsPushout.of_isColimit_cocone
    (isColimitOfPreserves (forget TopCat)
      (colimit.isColimit (span
        (TopCat.diskBoundaryInclusion.{0} n)
        (TopCat.diskBoundaryInclusion.{0} n))))

private theorem diskDouble_eq_inl_or_inr (n : ℕ) (z : diskDouble n) :
    (∃ x, pushout.inl (TopCat.diskBoundaryInclusion.{0} n)
        (TopCat.diskBoundaryInclusion.{0} n) x = z) ∨
      ∃ y, pushout.inr (TopCat.diskBoundaryInclusion.{0} n)
        (TopCat.diskBoundaryInclusion.{0} n) y = z := by
  simpa using CategoryTheory.Limits.Types.eq_or_eq_of_isPushout
    (diskDouble_isPushout_underlying n) z

private theorem diskDouble_inl_eq_inr_iff (n : ℕ)
    (x y : ((TopCat.disk.{0} n : TopCat.{0}) : Type)) :
    pushout.inl (TopCat.diskBoundaryInclusion.{0} n)
          (TopCat.diskBoundaryInclusion.{0} n) x =
        pushout.inr (TopCat.diskBoundaryInclusion.{0} n)
          (TopCat.diskBoundaryInclusion.{0} n) y ↔
      ∃ a : ((TopCat.diskBoundary.{0} n : TopCat.{0}) : Type),
        TopCat.diskBoundaryInclusion.{0} n a = x ∧
        TopCat.diskBoundaryInclusion.{0} n a = y := by
  have h :=
    CategoryTheory.Limits.Types.pushoutCocone_inl_eq_inr_iff_of_isColimit
      (diskDouble_isPushout_underlying n).isColimit
      (by
        have hinj : Function.Injective
            (TopCat.diskBoundaryInclusion.{0} n) :=
          (TopCat.mono_iff_injective _).mp inferInstance
        simpa using hinj) x y
  exact h

private theorem diskDoubleToSphere_inl_apply (n : ℕ)
    (x : ((TopCat.disk.{0} n : TopCat.{0}) : Type)) :
    diskDoubleToSphere n
        (pushout.inl (TopCat.diskBoundaryInclusion.{0} n)
          (TopCat.diskBoundaryInclusion.{0} n) x) =
      diskHemispherePoint n true x :=
  ConcreteCategory.congr_hom (diskDoubleToSphere_inl n) x

private theorem diskDoubleToSphere_inr_apply (n : ℕ)
    (x : ((TopCat.disk.{0} n : TopCat.{0}) : Type)) :
    diskDoubleToSphere n
        (pushout.inr (TopCat.diskBoundaryInclusion.{0} n)
          (TopCat.diskBoundaryInclusion.{0} n) x) =
      diskHemispherePoint n false x :=
  ConcreteCategory.congr_hom (diskDoubleToSphere_inr n) x

private theorem diskDoubleToSphere_injective (n : ℕ) :
    Function.Injective (diskDoubleToSphere n) := by
  intro z z' hzz'
  obtain (⟨x, rfl⟩ | ⟨y, rfl⟩) := diskDouble_eq_inl_or_inr n z
  · obtain (⟨x', rfl⟩ | ⟨y', rfl⟩) := diskDouble_eq_inl_or_inr n z'
    · apply congrArg (pushout.inl (TopCat.diskBoundaryInclusion.{0} n)
        (TopCat.diskBoundaryInclusion.{0} n))
      apply diskHemispherePoint_injective n true
      simpa only [diskDoubleToSphere_inl_apply] using hzz'
    · apply (diskDouble_inl_eq_inr_iff n x y').2
      apply diskHemispherePoint_cross n x y'
      simpa only [diskDoubleToSphere_inl_apply,
        diskDoubleToSphere_inr_apply] using hzz'
  · obtain (⟨x', rfl⟩ | ⟨y', rfl⟩) := diskDouble_eq_inl_or_inr n z'
    · symm
      apply (diskDouble_inl_eq_inr_iff n x' y).2
      apply diskHemispherePoint_cross n x' y
      simpa only [diskDoubleToSphere_inl_apply,
        diskDoubleToSphere_inr_apply] using hzz'.symm
    · apply congrArg (pushout.inr (TopCat.diskBoundaryInclusion.{0} n)
        (TopCat.diskBoundaryInclusion.{0} n))
      apply diskHemispherePoint_injective n false
      simpa only [diskDoubleToSphere_inr_apply] using hzz'

private theorem diskDoubleToSphere_surjective (n : ℕ) :
    Function.Surjective (diskDoubleToSphere n) := by
  intro y
  let yraw := Hatcher.Sphere.sphereULiftHomeomorph n y
  let x : ((TopCat.disk.{0} n : TopCat.{0}) : Type) :=
    ⟨⟨sphereFront n yraw, sphereFront_mem_closedBall n yraw⟩⟩
  obtain hlast | hlast := le_total 0 (yraw.1 (Fin.last n))
  · refine ⟨pushout.inl (TopCat.diskBoundaryInclusion.{0} n)
      (TopCat.diskBoundaryInclusion.{0} n) x, ?_⟩
    rw [diskDoubleToSphere_inl_apply]
    apply (Hatcher.Sphere.sphereULiftHomeomorph n).injective
    apply Subtype.ext
    exact hemisphereVector_sphereFront_of_last_nonneg n yraw hlast
  · refine ⟨pushout.inr (TopCat.diskBoundaryInclusion.{0} n)
      (TopCat.diskBoundaryInclusion.{0} n) x, ?_⟩
    rw [diskDoubleToSphere_inr_apply]
    apply (Hatcher.Sphere.sphereULiftHomeomorph n).injective
    apply Subtype.ext
    exact hemisphereVector_sphereFront_of_last_nonpos n yraw hlast

private noncomputable def diskDoubleHomeomorphSphere (n : ℕ) :
    ((diskDouble n : TopCat.{0}) : Type) ≃ₜ
      ((TopCat.sphere.{0} n : TopCat.{0}) : Type) := by
  let cover :
      ((TopCat.disk.{0} n : TopCat.{0}) : Type) ⊕
          ((TopCat.disk.{0} n : TopCat.{0}) : Type) →
        ((diskDouble n : TopCat.{0}) : Type) :=
    Sum.elim
      (pushout.inl (TopCat.diskBoundaryInclusion.{0} n)
        (TopCat.diskBoundaryInclusion.{0} n))
      (pushout.inr (TopCat.diskBoundaryInclusion.{0} n)
        (TopCat.diskBoundaryInclusion.{0} n))
  have hcover_continuous : Continuous cover :=
    Continuous.sumElim
      (pushout.inl (TopCat.diskBoundaryInclusion.{0} n)
        (TopCat.diskBoundaryInclusion.{0} n)).hom.continuous
      (pushout.inr (TopCat.diskBoundaryInclusion.{0} n)
        (TopCat.diskBoundaryInclusion.{0} n)).hom.continuous
  have hcover_surjective : Function.Surjective cover := by
    intro z
    obtain (⟨x, rfl⟩ | ⟨y, rfl⟩) := diskDouble_eq_inl_or_inr n z
    · exact ⟨Sum.inl x, rfl⟩
    · exact ⟨Sum.inr y, rfl⟩
  letI : CompactSpace (((diskDouble n : TopCat.{0}) : Type)) :=
    hcover_surjective.compactSpace hcover_continuous
  letI : T2Space (((TopCat.sphere.{0} n : TopCat.{0}) : Type)) := by
    change T2Space (ULift (Metric.sphere
      (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))
    infer_instance
  exact IsHomeomorph.homeomorph (diskDoubleToSphere n) <|
    isHomeomorph_iff_continuous_bijective.2
      ⟨(diskDoubleToSphere n).hom.continuous,
        diskDoubleToSphere_injective n,
        diskDoubleToSphere_surjective n⟩

/-- The ambient component of the standard-simplex-to-disk pair isomorphism. -/
private noncomputable def standardSimplexDiskMap (n : ℕ) :
    TopCat.of (StandardSimplex n) ⟶ TopCat.disk.{0} n :=
  TopPair.Hom.fst (standardSimplexPairIsoDiskPair n).hom

/-- The pair homeomorphism from the ordered simplex and its boundary to the
standard disk and its boundary induces an isomorphism of their doubles. -/
private noncomputable def doubleSimplexIsoDiskDouble (n : ℕ) :
    doubleSimplex n ≅ diskDouble n := by
  let e := standardSimplexPairIsoDiskPair n
  let a : TopCat.of (StandardSimplex n) ⟶ TopCat.disk.{0} n :=
    standardSimplexDiskMap n
  let a_inv : TopCat.disk.{0} n ⟶ TopCat.of (StandardSimplex n) :=
    TopPair.Hom.fst e.inv
  let b : TopCat.of (standardSimplexBoundary n) ⟶
      TopCat.diskBoundary.{0} n := TopPair.Hom.snd e.hom
  let b_inv : TopCat.diskBoundary.{0} n ⟶
      TopCat.of (standardSimplexBoundary n) := TopPair.Hom.snd e.inv
  have hw : standardSimplexBoundaryInclusion n ≫
        a = b ≫ TopCat.diskBoundaryInclusion.{0} n := by
    change (standardSimplexPair n).map ≫ TopPair.Hom.fst e.hom =
      TopPair.Hom.snd e.hom ≫ (standardDiskPair n).map
    exact (TopPair.Hom.w e.hom).symm
  let m := pushout.map
    (standardSimplexBoundaryInclusion n)
    (standardSimplexBoundaryInclusion n)
    (TopCat.diskBoundaryInclusion.{0} n)
    (TopCat.diskBoundaryInclusion.{0} n)
    a a b hw hw
  have hw_inv : TopCat.diskBoundaryInclusion.{0} n ≫
        a_inv = b_inv ≫ standardSimplexBoundaryInclusion n := by
    change (standardDiskPair n).map ≫ TopPair.Hom.fst e.inv =
      TopPair.Hom.snd e.inv ≫ (standardSimplexPair n).map
    exact (TopPair.Hom.w e.inv).symm
  let m_inv := pushout.map
    (TopCat.diskBoundaryInclusion.{0} n)
    (TopCat.diskBoundaryInclusion.{0} n)
    (standardSimplexBoundaryInclusion n)
    (standardSimplexBoundaryInclusion n)
    a_inv a_inv b_inv hw_inv hw_inv
  have hm_inl :
      pushout.inl (standardSimplexBoundaryInclusion n)
            (standardSimplexBoundaryInclusion n) ≫ m =
        a ≫
          pushout.inl (TopCat.diskBoundaryInclusion.{0} n)
            (TopCat.diskBoundaryInclusion.{0} n) := by
    apply pushout.inl_desc
  have hm_inr :
      pushout.inr (standardSimplexBoundaryInclusion n)
            (standardSimplexBoundaryInclusion n) ≫ m =
        a ≫
          pushout.inr (TopCat.diskBoundaryInclusion.{0} n)
            (TopCat.diskBoundaryInclusion.{0} n) := by
    apply pushout.inr_desc
  have hmi_inl :
      pushout.inl (TopCat.diskBoundaryInclusion.{0} n)
            (TopCat.diskBoundaryInclusion.{0} n) ≫ m_inv =
        a_inv ≫
          pushout.inl (standardSimplexBoundaryInclusion n)
            (standardSimplexBoundaryInclusion n) := by
    apply pushout.inl_desc
  have hmi_inr :
      pushout.inr (TopCat.diskBoundaryInclusion.{0} n)
            (TopCat.diskBoundaryInclusion.{0} n) ≫ m_inv =
        a_inv ≫
          pushout.inr (standardSimplexBoundaryInclusion n)
            (standardSimplexBoundaryInclusion n) := by
    apply pushout.inr_desc
  have efst_hom_inv :
      a ≫ a_inv = 𝟙 _ := by
    change TopPair.Hom.fst (e.hom ≫ e.inv) = _
    rw [e.hom_inv_id]
    rfl
  have efst_inv_hom :
      a_inv ≫ a = 𝟙 _ := by
    change TopPair.Hom.fst (e.inv ≫ e.hom) = _
    rw [e.inv_hom_id]
    rfl
  exact
    { hom := m
      inv := m_inv
      hom_inv_id := by
        apply pushout.hom_ext
        · rw [← Category.assoc, hm_inl, Category.assoc, hmi_inl,
            ← Category.assoc, efst_hom_inv, Category.id_comp,
            Category.comp_id]
        · rw [← Category.assoc, hm_inr, Category.assoc, hmi_inr,
            ← Category.assoc, efst_hom_inv, Category.id_comp,
            Category.comp_id]
      inv_hom_id := by
        apply pushout.hom_ext
        · rw [← Category.assoc, hmi_inl, Category.assoc, hm_inl,
            ← Category.assoc, efst_inv_hom, Category.id_comp,
            Category.comp_id]
        · rw [← Category.assoc, hmi_inr, Category.assoc, hm_inr,
            ← Category.assoc, efst_inv_hom, Category.id_comp,
            Category.comp_id] }

/-- **Hatcher, Example 2.23 (page 125).** The ordered double of the standard
`n`-simplex along its boundary is homeomorphic to the standard `n`-sphere.
The construction is valid also for `n = 0`, where it identifies the two
vertices with the two points of `S⁰`. -/
noncomputable def doubleSimplexIsoSphere (n : ℕ) :
    doubleSimplex n ≅ TopCat.sphere.{0} n :=
  (doubleSimplexIsoDiskDouble n).trans <|
    TopCat.isoOfHomeo (diskDoubleHomeomorphSphere n)

/-- The underlying homeomorphism of `doubleSimplexIsoSphere`. -/
noncomputable def doubleSimplexHomeomorphSphere (n : ℕ) :
    ((doubleSimplex n : TopCat.{0}) : Type) ≃ₜ
      ((TopCat.sphere.{0} n : TopCat.{0}) : Type) :=
  TopCat.homeoOfIso (doubleSimplexIsoSphere n)

private theorem diskHemispherePoint_true_reflection (n : ℕ)
    (x : ((TopCat.disk.{0} n : TopCat.{0}) : Type)) :
    (Hatcher.Sphere.coordinateReflectionIso n (Fin.last n)).hom
        (diskHemispherePoint n true x) =
      diskHemispherePoint n false x := by
  apply (Hatcher.Sphere.sphereULiftHomeomorph n).injective
  apply Subtype.ext
  apply PiLp.ext
  intro i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simp [diskHemispherePoint, rawDiskHemispherePoint]
  · simp [diskHemispherePoint, rawDiskHemispherePoint]

private theorem diskHemispherePoint_false_reflection (n : ℕ)
    (x : ((TopCat.disk.{0} n : TopCat.{0}) : Type)) :
    (Hatcher.Sphere.coordinateReflectionIso n (Fin.last n)).hom
        (diskHemispherePoint n false x) =
      diskHemispherePoint n true x := by
  apply (Hatcher.Sphere.sphereULiftHomeomorph n).injective
  apply Subtype.ext
  apply PiLp.ext
  intro i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simp [diskHemispherePoint, rawDiskHemispherePoint]
  · simp [diskHemispherePoint, rawDiskHemispherePoint]

private theorem diskHemisphereMap_true_reflection (n : ℕ) :
    diskHemisphereMap n true ≫
        (Hatcher.Sphere.coordinateReflectionIso n (Fin.last n)).hom =
      diskHemisphereMap n false := by
  ext x
  exact diskHemispherePoint_true_reflection n x

private theorem diskHemisphereMap_false_reflection (n : ℕ) :
    diskHemisphereMap n false ≫
        (Hatcher.Sphere.coordinateReflectionIso n (Fin.last n)).hom =
      diskHemisphereMap n true := by
  ext x
  exact diskHemispherePoint_false_reflection n x

private theorem doubleSimplexFirstInclusion_isoDiskDouble (n : ℕ) :
    doubleSimplexFirstInclusion n ≫ (doubleSimplexIsoDiskDouble n).hom =
      standardSimplexDiskMap n ≫
        pushout.inl (TopCat.diskBoundaryInclusion.{0} n)
          (TopCat.diskBoundaryInclusion.{0} n) := by
  apply pushout.inl_desc

private theorem doubleSimplexSecondInclusion_isoDiskDouble (n : ℕ) :
    doubleSimplexSecondInclusion n ≫ (doubleSimplexIsoDiskDouble n).hom =
      standardSimplexDiskMap n ≫
        pushout.inr (TopCat.diskBoundaryInclusion.{0} n)
          (TopCat.diskBoundaryInclusion.{0} n) := by
  apply pushout.inr_desc

private theorem diskDoubleHomeomorphSphere_hom (n : ℕ) :
    (TopCat.isoOfHomeo (diskDoubleHomeomorphSphere n)).hom =
      diskDoubleToSphere n := by
  rfl

private theorem doubleSimplexFirstInclusion_isoSphere (n : ℕ) :
    doubleSimplexFirstInclusion n ≫ (doubleSimplexIsoSphere n).hom =
      standardSimplexDiskMap n ≫
        diskHemisphereMap n true := by
  change doubleSimplexFirstInclusion n ≫
      ((doubleSimplexIsoDiskDouble n).hom ≫
        (TopCat.isoOfHomeo (diskDoubleHomeomorphSphere n)).hom) = _
  rw [← Category.assoc, doubleSimplexFirstInclusion_isoDiskDouble,
    Category.assoc, diskDoubleHomeomorphSphere_hom,
    diskDoubleToSphere_inl]

private theorem doubleSimplexSecondInclusion_isoSphere (n : ℕ) :
    doubleSimplexSecondInclusion n ≫ (doubleSimplexIsoSphere n).hom =
      standardSimplexDiskMap n ≫
        diskHemisphereMap n false := by
  change doubleSimplexSecondInclusion n ≫
      ((doubleSimplexIsoDiskDouble n).hom ≫
        (TopCat.isoOfHomeo (diskDoubleHomeomorphSphere n)).hom) = _
  rw [← Category.assoc, doubleSimplexSecondInclusion_isoDiskDouble,
    Category.assoc, diskDoubleHomeomorphSphere_hom,
    diskDoubleToSphere_inr]

/-- The explicit last-coordinate reflection agrees with the summand swap under
the ordered double-simplex model of the sphere. -/
private theorem doubleSimplexSwap_isoSphere_aux (n : ℕ) :
    (doubleSimplexSwapIso n).hom ≫ (doubleSimplexIsoSphere n).hom =
      (doubleSimplexIsoSphere n).hom ≫
        (Hatcher.Sphere.coordinateReflectionIso n (Fin.last n)).hom := by
  apply pushout.hom_ext
  · rw [← Category.assoc, doubleSimplexSwapIso_hom,
      doubleSimplexFirstInclusion_swapMap,
      doubleSimplexSecondInclusion_isoSphere,
      ← Category.assoc,
      doubleSimplexFirstInclusion_isoSphere,
      Category.assoc,
      diskHemisphereMap_true_reflection]
  · rw [← Category.assoc, doubleSimplexSwapIso_hom,
      doubleSimplexSecondInclusion_swapMap,
      doubleSimplexFirstInclusion_isoSphere,
      ← Category.assoc,
      doubleSimplexSecondInclusion_isoSphere,
      Category.assoc,
      diskHemisphereMap_false_reflection]

universe v u

variable {C : Type u} [Category.{v} C] [HasCoproducts.{0} C] [Abelian C]

/-- The source-facing orientation class on the standard sphere, obtained by
transporting the literal first-simplex-minus-second-simplex class across
`doubleSimplexIsoSphere`. -/
noncomputable def doubleSimplexSphereFundamentalClass (R : C) (n : ℕ) :
    R ⟶ (Hatcher.Reduced.homologyFunctor R n).obj
      (TopCat.sphere.{0} n) :=
  doubleSimplexFundamentalClass R n ≫
    (Hatcher.Reduced.homologyFunctor R n).map
      (doubleSimplexIsoSphere n).hom

/-- The transported ordered difference class generates reduced homology of
the standard sphere. -/
theorem doubleSimplexSphereFundamentalClass_isIso (R : C) (n : ℕ) :
    IsIso (doubleSimplexSphereFundamentalClass R n) := by
  dsimp only [doubleSimplexSphereFundamentalClass]
  exact IsIso.comp_isIso'
    (doubleSimplexFundamentalClass_isIso R n) (by infer_instance)

/-- Transporting the named sphere class back along the inverse homeomorphism
recovers the literal ordered double-simplex class. -/
theorem doubleSimplexSphereFundamentalClass_map_inv (R : C) (n : ℕ) :
    doubleSimplexSphereFundamentalClass R n ≫
        (Hatcher.Reduced.homologyFunctor R n).map
          (doubleSimplexIsoSphere n).inv =
      doubleSimplexFundamentalClass R n := by
  rw [doubleSimplexSphereFundamentalClass, Category.assoc,
    ← Functor.map_comp]
  simp

/-- The canonically oriented sphere-homology isomorphism determined by the
ordered double-simplex cycle. -/
noncomputable def sphereHomologyIsoFromDoubleSimplex (R : C) (n : ℕ) :
    (Hatcher.Reduced.homologyFunctor R n).obj
        (TopCat.sphere.{0} n) ≅ R := by
  letI : IsIso (doubleSimplexSphereFundamentalClass R n) :=
    doubleSimplexSphereFundamentalClass_isIso R n
  exact (asIso (doubleSimplexSphereFundamentalClass R n)).symm

@[simp]
theorem doubleSimplexSphereFundamentalClass_comp_homologyIso (R : C)
    (n : ℕ) :
    doubleSimplexSphereFundamentalClass R n ≫
        (sphereHomologyIsoFromDoubleSimplex R n).hom =
      𝟙 R := by
  dsimp [sphereHomologyIsoFromDoubleSimplex]
  simp

end Hatcher.Simplex

namespace Hatcher.Sphere

/-- The explicit last-coordinate reflection agrees with the summand swap under
the ordered double-simplex model of the sphere. -/
theorem doubleSimplexSwap_isoSphere (n : ℕ) :
    (Hatcher.Simplex.doubleSimplexSwapIso n).hom ≫
        (Hatcher.Simplex.doubleSimplexIsoSphere n).hom =
      (Hatcher.Simplex.doubleSimplexIsoSphere n).hom ≫
        (coordinateReflectionIso n (Fin.last n)).hom :=
  Hatcher.Simplex.doubleSimplexSwap_isoSphere_aux n

end Hatcher.Sphere


noncomputable section

open AlgebraicTopology CategoryTheory Limits _root_.Topology
open scoped Simplicial

namespace Hatcher.Sphere

universe u

private abbrev sphereLiftCoefficient : AddCommGrpCat.{u} :=
  AddCommGrpCat.of.{u} (ULift.{u} ℤ)

noncomputable def sphereCoordinateUniverseLift (d : ℕ) :
    TopCat.sphere.{0} d ≃ₜ TopCat.sphere.{u} d := by
  change ULift.{0} (Metric.sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) 1) ≃ₜ
    ULift.{u} (Metric.sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) 1)
  exact
    { toFun := fun x => ULift.up x.down
      invFun := fun x => ULift.up x.down
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := continuous_uliftUp.comp continuous_uliftDown
      continuous_invFun := continuous_uliftUp.comp continuous_uliftDown }

noncomputable def sphereSimplexLift (d r : ℕ) :
    (TopCat.toSSet.obj (TopCat.sphere.{0} d)) _⦋r⦌ ≃
      (TopCat.toSSet.obj (TopCat.sphere.{u} d)) _⦋r⦌ :=
  (TopCat.toSSetObjEquiv (TopCat.sphere.{0} d) (.op ⦋r⦌)).trans
    (((Homeomorph.refl (Convexity.StdSimplex ℝ (Fin (r + 1)))).continuousMapCongr
      (sphereCoordinateUniverseLift.{u} d)).trans
        (TopCat.toSSetObjEquiv (TopCat.sphere.{u} d) (.op ⦋r⦌)).symm)

theorem sphereSimplexLift_face (d r : ℕ) (i : Fin (r + 2))
    (s : (TopCat.toSSet.obj (TopCat.sphere.{0} d)) _⦋r + 1⦌) :
    sphereSimplexLift.{u} d r
        ((TopCat.toSSet.obj (TopCat.sphere.{0} d)).δ i s) =
      (TopCat.toSSet.obj (TopCat.sphere.{u} d)).δ i
        (sphereSimplexLift.{u} d (r + 1) s) := by
  apply (TopCat.toSSetObjEquiv (TopCat.sphere.{u} d) (.op ⦋r⦌)).injective
  apply ContinuousMap.ext
  intro x
  rfl

private abbrev sphereLiftOrdinaryComplex (d : ℕ) : ChainComplex AddCommGrpCat.{u} ℕ :=
  (TopCat.toSSet.obj (TopCat.sphere.{u} d)).chainComplex sphereLiftCoefficient.{u}

private abbrev sphereLiftOldOrdinaryComplex (d : ℕ) : ChainComplex AddCommGrpCat.{u} ℕ :=
  (TopCat.toSSet.obj (TopCat.sphere.{0} d)).chainComplex sphereLiftCoefficient.{u}

private noncomputable def sphereLiftXIso (d r : ℕ) :
    (sphereLiftOldOrdinaryComplex.{u} d).X r ≅
      (sphereLiftOrdinaryComplex.{u} d).X r :=
  Sigma.whiskerEquiv (sphereSimplexLift.{u} d r)
    (fun _ => Iso.refl sphereLiftCoefficient.{u})

private theorem sphereLiftXIso_ι (d r : ℕ)
    (s : (TopCat.toSSet.obj (TopCat.sphere.{0} d)) _⦋r⦌) :
    (TopCat.toSSet.obj (TopCat.sphere.{0} d)).ιChainComplex
        (R := sphereLiftCoefficient.{u}) s ≫
        (sphereLiftXIso.{u} d r).hom =
      (TopCat.toSSet.obj (TopCat.sphere.{u} d)).ιChainComplex
        (R := sphereLiftCoefficient.{u}) (sphereSimplexLift.{u} d r s) := by
  simp [sphereLiftXIso, SSet.ιChainComplex, Sigma.whiskerEquiv]

private theorem sphereLiftXIso_d (d r : ℕ) :
    (sphereLiftXIso.{u} d (r + 1)).hom ≫
        (sphereLiftOrdinaryComplex.{u} d).d (r + 1) r =
      (sphereLiftOldOrdinaryComplex.{u} d).d (r + 1) r ≫
        (sphereLiftXIso.{u} d r).hom := by
  let S₀ := TopCat.toSSet.obj (TopCat.sphere.{0} d)
  let S₁ := TopCat.toSSet.obj (TopCat.sphere.{u} d)
  apply SSet.chainComplex_hom_ext
  intro s
  change S₀.ιChainComplex (R := sphereLiftCoefficient.{u}) s ≫
      ((sphereLiftXIso.{u} d (r + 1)).hom ≫ (S₁.chainComplex _).d (r + 1) r) =
    S₀.ιChainComplex s ≫ ((S₀.chainComplex _).d (r + 1) r ≫
      (sphereLiftXIso.{u} d r).hom)
  rw [← Category.assoc, sphereLiftXIso_ι, SSet.ιChainComplex_d]
  rw [← Category.assoc, SSet.ιChainComplex_d]
  simp only [Preadditive.sum_comp, Preadditive.zsmul_comp]
  apply Finset.sum_congr rfl
  intro i _hi
  have hm := sphereLiftXIso_ι.{u} d r
    ((TopCat.toSSet.obj (TopCat.sphere.{0} d)).δ i s)
  have hf := sphereSimplexLift_face.{u} d r i s
  have hterm := hm.trans (congrArg
    (fun t : (TopCat.toSSet.obj (TopCat.sphere.{u} d)) _⦋r⦌ =>
      (TopCat.toSSet.obj (TopCat.sphere.{u} d)).ιChainComplex
        (R := sphereLiftCoefficient.{u}) t) hf)
  exact congrArg
    (fun f : sphereLiftCoefficient.{u} ⟶ (sphereLiftOrdinaryComplex.{u} d).X r =>
      ((-1 : ℤ) ^ i.val) • f) hterm.symm

private theorem sphereLiftAugmentation (d : ℕ) :
    (sphereLiftXIso.{u} d 0).hom ≫
        Hatcher.Reduced.chainAugmentation sphereLiftCoefficient.{u}
          (TopCat.sphere.{u} d) =
      Hatcher.Reduced.chainAugmentation sphereLiftCoefficient.{u}
        (TopCat.sphere.{0} d) := by
  let R : AddCommGrpCat.{u} := sphereLiftCoefficient.{u}
  let ε₀ : (sphereLiftOldOrdinaryComplex.{u} d).X 0 ⟶ R :=
    Hatcher.Reduced.chainAugmentation R (TopCat.sphere.{0} d)
  let ε₁ : (sphereLiftOrdinaryComplex.{u} d).X 0 ⟶ R :=
    Hatcher.Reduced.chainAugmentation R (TopCat.sphere.{u} d)
  change (sphereLiftXIso.{u} d 0).hom ≫ ε₁ = ε₀
  apply SSet.chainComplex_hom_ext
  intro s
  let i₀ : R ⟶ (sphereLiftOldOrdinaryComplex.{u} d).X 0 :=
    (TopCat.toSSet.obj (TopCat.sphere.{0} d)).ιChainComplex s
  let i₁ : R ⟶ (sphereLiftOrdinaryComplex.{u} d).X 0 :=
    (TopCat.toSSet.obj (TopCat.sphere.{u} d)).ιChainComplex
      (sphereSimplexLift.{u} d 0 s)
  have hi : i₀ ≫ (sphereLiftXIso.{u} d 0).hom = i₁ := sphereLiftXIso_ι d 0 s
  change i₀ ≫ ((sphereLiftXIso.{u} d 0).hom ≫ ε₁) = i₀ ≫ ε₀
  calc
    _ = (i₀ ≫ (sphereLiftXIso.{u} d 0).hom) ≫ ε₁ := (Category.assoc _ _ _).symm
    _ = i₁ ≫ ε₁ := congrArg (fun f => f ≫ ε₁) hi
    _ = 𝟙 R := Hatcher.Reduced.ι_chainAugmentation R (TopCat.sphere.{u} d)
      (sphereSimplexLift.{u} d 0 s)
    _ = i₀ ≫ ε₀ := (Hatcher.Reduced.ι_chainAugmentation R (TopCat.sphere.{0} d) s).symm

private abbrev sphereLiftAugmentedComplex (d : ℕ) : ChainComplex AddCommGrpCat.{u} ℕ :=
  (Hatcher.Reduced.augmentedSingularChainComplexFunctor.{u}
    sphereLiftCoefficient.{u}).obj (TopCat.sphere.{u} d)

private abbrev sphereLiftOldAugmentedComplex (d : ℕ) : ChainComplex AddCommGrpCat.{u} ℕ :=
  (Hatcher.Reduced.augmentedSingularChainComplexFunctor.{0}
    sphereLiftCoefficient.{u}).obj (TopCat.sphere.{0} d)

private noncomputable def sphereLiftAugmentedXIso (d : ℕ) :
    ∀ r : ℕ, (sphereLiftOldAugmentedComplex.{u} d).X r ≅
      (sphereLiftAugmentedComplex.{u} d).X r :=
  fun r => match r with
    | 0 => Iso.refl sphereLiftCoefficient.{u}
    | r + 1 => sphereLiftXIso.{u} d r

/-- The actual augmentation-preserving singular-chain universe lift. -/
noncomputable def sphereAugmentedSpaceLiftIso (d : ℕ) :
    (Hatcher.Reduced.augmentedSingularChainComplexFunctor.{0}
      (AddCommGrpCat.of.{u} (ULift.{u} ℤ))).obj (TopCat.sphere.{0} d) ≅
      (Hatcher.Reduced.augmentedSingularChainComplexFunctor.{u}
        (AddCommGrpCat.of.{u} (ULift.{u} ℤ))).obj (TopCat.sphere.{u} d) :=
  HomologicalComplex.Hom.isoOfComponents (sphereLiftAugmentedXIso.{u} d) (by
    intro i j h
    have hij : j + 1 = i := h
    subst i
    cases j with
    | zero =>
        change (sphereLiftXIso.{u} d 0).hom ≫
          Hatcher.Reduced.chainAugmentation sphereLiftCoefficient.{u}
            (TopCat.sphere.{u} d) =
          Hatcher.Reduced.chainAugmentation sphereLiftCoefficient.{u}
            (TopCat.sphere.{0} d) ≫ 𝟙 _
        rw [Category.comp_id]
        exact sphereLiftAugmentation d
    | succ r => exact sphereLiftXIso_d d r)

@[simp]
theorem sphereAugmentedSpaceLiftIso_f_zero (d : ℕ) :
    (sphereAugmentedSpaceLiftIso.{u} d).hom.f 0 =
      𝟙 (AddCommGrpCat.of.{u} (ULift.{u} ℤ)) := rfl

/-- Each actual singular simplex goes to its canonical coordinate lift. -/
theorem sphereAugmentedSpaceLiftIso_ι (d r : ℕ)
    (s : (TopCat.toSSet.obj (TopCat.sphere.{0} d)) _⦋r⦌) :
    (TopCat.toSSet.obj (TopCat.sphere.{0} d)).ιChainComplex
        (R := AddCommGrpCat.of.{u} (ULift.{u} ℤ)) s ≫
        (sphereAugmentedSpaceLiftIso.{u} d).hom.f (r + 1) =
      (TopCat.toSSet.obj (TopCat.sphere.{u} d)).ιChainComplex
        (R := AddCommGrpCat.of.{u} (ULift.{u} ℤ)) (sphereSimplexLift.{u} d r s) :=
  sphereLiftXIso_ι d r s

end Hatcher.Sphere

noncomputable section

namespace Hatcher.Sphere

open AlgebraicTopology CategoryTheory CategoryTheory.Limits
open scoped Simplicial

universe u

private abbrev liftedOrderedSphereCoefficient : AddCommGrpCat.{u} :=
  AddCommGrpCat.of.{u} (ULift.{u} ℤ)

private abbrev liftedOrderedSphereAugmentedComplex (k : ℕ) :
    ChainComplex AddCommGrpCat.{u} ℕ :=
  (Hatcher.Reduced.augmentedSingularChainComplexFunctor.{u}
    liftedOrderedSphereCoefficient.{u}).obj (TopCat.sphere.{u} (k + 1))

private noncomputable def liftedOrderedSphereReducedLiftIso (k : ℕ) :
    (Hatcher.Reduced.homologyFunctor.{0} liftedOrderedSphereCoefficient.{u} (k + 1)).obj
        (TopCat.sphere.{0} (k + 1)) ≅
      (Hatcher.Reduced.homologyFunctor.{u} liftedOrderedSphereCoefficient.{u} (k + 1)).obj
        (TopCat.sphere.{u} (k + 1)) :=
  (HomologicalComplex.homologyFunctor AddCommGrpCat.{u}
    (ComplexShape.down ℕ) (k + 2)).mapIso (sphereAugmentedSpaceLiftIso.{u} (k + 1))

private noncomputable def liftedOrderedSphereChainMap (k : ℕ) :
    (Hatcher.Reduced.augmentedSingularChainComplexFunctor.{0}
      liftedOrderedSphereCoefficient.{u}).obj (Hatcher.Simplex.doubleSimplex (k + 1)) ⟶
        liftedOrderedSphereAugmentedComplex.{u} k :=
  Hatcher.Reduced.augmentedMap liftedOrderedSphereCoefficient.{u}
      (Hatcher.Simplex.doubleSimplexIsoSphere (k + 1)).hom ≫
    (sphereAugmentedSpaceLiftIso.{u} (k + 1)).hom

/-- The actual first ordered double-simplex map, followed by the fixed sphere
model and its canonical coordinate universe lift. -/
noncomputable def liftedOrderedSphereFirstSimplex (k : ℕ) :
    (TopCat.toSSet.obj (TopCat.sphere.{u} (k + 1))) _⦋k + 1⦌ :=
  sphereSimplexLift.{u} (k + 1) (k + 1)
    ((TopCat.toSSet.map (Hatcher.Simplex.doubleSimplexIsoSphere (k + 1)).hom).app
      (.op ⦋k + 1⦌) (Hatcher.Simplex.doubleSimplexFirstSingularSimplex (k + 1)))

/-- The actual second ordered double-simplex map with the same fixed transports. -/
noncomputable def liftedOrderedSphereSecondSimplex (k : ℕ) :
    (TopCat.toSSet.obj (TopCat.sphere.{u} (k + 1))) _⦋k + 1⦌ :=
  sphereSimplexLift.{u} (k + 1) (k + 1)
    ((TopCat.toSSet.map (Hatcher.Simplex.doubleSimplexIsoSphere (k + 1)).hom).app
      (.op ⦋k + 1⦌) (Hatcher.Simplex.doubleSimplexSecondSingularSimplex (k + 1)))

/-- The transported actual ordered cycle, with its coefficient-copy map retained. -/
noncomputable def liftedOrderedSphereCycle (k : ℕ) :
    liftedOrderedSphereCoefficient.{u} ⟶
      (liftedOrderedSphereAugmentedComplex.{u} k).X (k + 2) :=
  Hatcher.Simplex.doubleSimplexFundamentalCycle liftedOrderedSphereCoefficient.{u} (k + 1) ≫
    (liftedOrderedSphereChainMap.{u} k).f (k + 2)

/-- The cycle is literally the first simplex inclusion minus the second. -/
theorem liftedOrderedSphereCycle_eq_difference (k : ℕ) :
    liftedOrderedSphereCycle.{u} k =
      (TopCat.toSSet.obj (TopCat.sphere.{u} (k + 1))).ιChainComplex
          (R := AddCommGrpCat.of.{u} (ULift.{u} ℤ))
          (liftedOrderedSphereFirstSimplex.{u} k) -
        (TopCat.toSSet.obj (TopCat.sphere.{u} (k + 1))).ιChainComplex
          (R := AddCommGrpCat.of.{u} (ULift.{u} ℤ))
          (liftedOrderedSphereSecondSimplex.{u} k) := by
  let R : AddCommGrpCat.{u} := liftedOrderedSphereCoefficient.{u}
  let S : SSet.{0} := TopCat.toSSet.obj (Hatcher.Simplex.doubleSimplex (k + 1))
  let T : SSet.{0} := TopCat.toSSet.obj (TopCat.sphere.{0} (k + 1))
  let U : SSet.{u} := TopCat.toSSet.obj (TopCat.sphere.{u} (k + 1))
  let f : S ⟶ T :=
    TopCat.toSSet.map (Hatcher.Simplex.doubleSimplexIsoSphere (k + 1)).hom
  let Γ := sphereAugmentedSpaceLiftIso.{u} (k + 1)
  let first : S _⦋k + 1⦌ := Hatcher.Simplex.doubleSimplexFirstSingularSimplex (k + 1)
  let second : S _⦋k + 1⦌ := Hatcher.Simplex.doubleSimplexSecondSingularSimplex (k + 1)
  have hfirst : S.ιChainComplex (R := R) first ≫
      (SSet.chainComplexMap f R).f (k + 1) =
    T.ιChainComplex (R := R) (f.app (.op ⦋k + 1⦌) first) :=
    SSet.ι_chainComplexMap_f (X := S) (Y := T) (f := f) (R := R) first
  have hsecond : S.ιChainComplex (R := R) second ≫
      (SSet.chainComplexMap f R).f (k + 1) =
    T.ιChainComplex (R := R) (f.app (.op ⦋k + 1⦌) second) :=
    SSet.ι_chainComplexMap_f (X := S) (Y := T) (f := f) (R := R) second
  have hfirstLift := sphereAugmentedSpaceLiftIso_ι.{u} (k + 1) (k + 1)
    (f.app (.op ⦋k + 1⦌) first)
  have hsecondLift := sphereAugmentedSpaceLiftIso_ι.{u} (k + 1) (k + 1)
    (f.app (.op ⦋k + 1⦌) second)
  change (S.ιChainComplex (R := R) first - S.ιChainComplex (R := R) second) ≫
      ((SSet.chainComplexMap f R).f (k + 1) ≫ Γ.hom.f (k + 2)) =
    U.ιChainComplex (R := R)
        (sphereSimplexLift.{u} (k + 1) (k + 1) (f.app (.op ⦋k + 1⦌) first)) -
      U.ιChainComplex (R := R)
        (sphereSimplexLift.{u} (k + 1) (k + 1) (f.app (.op ⦋k + 1⦌) second))
  rw [Preadditive.sub_comp, ← Category.assoc, hfirst, hfirstLift,
    ← Category.assoc, hsecond, hsecondLift]

/-- Differential compatibility transports the proved ordered cycle equation. -/
theorem liftedOrderedSphereCycle_d (k : ℕ) :
    liftedOrderedSphereCycle.{u} k ≫
        (liftedOrderedSphereAugmentedComplex.{u} k).d (k + 2) (k + 1) = 0 := by
  let R : AddCommGrpCat.{u} := liftedOrderedSphereCoefficient.{u}
  let F := liftedOrderedSphereChainMap.{u} k
  change (Hatcher.Simplex.doubleSimplexFundamentalCycle R (k + 1) ≫
    F.f (k + 2)) ≫ _ = 0
  rw [Category.assoc, F.comm, ← Category.assoc,
    Hatcher.Simplex.doubleSimplexFundamentalCycle_d R (k + 1), zero_comp]

/-- The accepted ordered sphere class transported through the actual augmented
space-universe isomorphism. This definition fixes the orientation. -/
noncomputable def liftedOrderedSphereFundamentalClass (k : ℕ) :
    AddCommGrpCat.of.{u} (ULift.{u} ℤ) ⟶
      (Hatcher.Reduced.homologyFunctor.{u}
        (AddCommGrpCat.of.{u} (ULift.{u} ℤ)) (k + 1)).obj
          (TopCat.sphere.{u} (k + 1)) :=
  Hatcher.Simplex.doubleSimplexSphereFundamentalClass liftedOrderedSphereCoefficient.{u}
      (k + 1) ≫
    (liftedOrderedSphereReducedLiftIso.{u} k).hom

/-- The transported orientation is the class of the exact lifted ordered cycle. -/
theorem liftedOrderedSphereFundamentalClass_eq_cycle (k : ℕ) :
    liftedOrderedSphereFundamentalClass.{u} k =
      (liftedOrderedSphereAugmentedComplex.{u} k).liftCycles
          (liftedOrderedSphereCycle.{u} k) (k + 1) (by simp)
          (liftedOrderedSphereCycle_d.{u} k) ≫
        (liftedOrderedSphereAugmentedComplex.{u} k).homologyπ (k + 2) := by
  let R : AddCommGrpCat.{u} := liftedOrderedSphereCoefficient.{u}
  let K : ChainComplex AddCommGrpCat.{u} ℕ :=
    (Hatcher.Reduced.augmentedSingularChainComplexFunctor.{0} R).obj
      (Hatcher.Simplex.doubleSimplex (k + 1))
  let L : ChainComplex AddCommGrpCat.{u} ℕ := liftedOrderedSphereAugmentedComplex.{u} k
  let F : K ⟶ L := liftedOrderedSphereChainMap.{u} k
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{u}
    (ComplexShape.down ℕ) (k + 2)
  change (Hatcher.Simplex.doubleSimplexFundamentalClass R (k + 1) ≫
    H.map (Hatcher.Reduced.augmentedMap R
      (Hatcher.Simplex.doubleSimplexIsoSphere (k + 1)).hom)) ≫
        H.map (sphereAugmentedSpaceLiftIso.{u} (k + 1)).hom = _
  rw [Category.assoc, ← Functor.map_comp]
  change (K.liftCycles
      (Hatcher.Simplex.doubleSimplexFundamentalCycle R (k + 1))
      (k + 1) (by simp) (Hatcher.Simplex.doubleSimplexFundamentalCycle_d R (k + 1)) ≫
        K.homologyπ (k + 2)) ≫ HomologicalComplex.homologyMap F (k + 2) = _
  rw [Category.assoc,
    HomologicalComplex.homologyπ_naturality (φ := F) (i := k + 2),
    ← Category.assoc]
  have h := HomologicalComplex.liftCycles_comp_cyclesMap
    (φ := F) (i := k + 2)
    (Hatcher.Simplex.doubleSimplexFundamentalCycle R (k + 1))
    (k + 1) (by simp) (Hatcher.Simplex.doubleSimplexFundamentalCycle_d R (k + 1))
  exact congrArg (fun g : R ⟶ L.cycles (k + 2) ↦ g ≫ L.homologyπ (k + 2)) h

/-- The fixed ordered difference class generates reduced sphere homology in
every space universe and every positive sphere dimension. -/
theorem liftedOrderedSphereFundamentalClass_isIso (k : ℕ) :
    IsIso (liftedOrderedSphereFundamentalClass.{u} k) := by
  change IsIso
    (Hatcher.Simplex.doubleSimplexSphereFundamentalClass liftedOrderedSphereCoefficient.{u}
        (k + 1) ≫ (liftedOrderedSphereReducedLiftIso.{u} k).hom)
  exact IsIso.comp_isIso'
    (Hatcher.Simplex.doubleSimplexSphereFundamentalClass_isIso
      liftedOrderedSphereCoefficient.{u} (k + 1)) (by infer_instance)

end Hatcher.Sphere
