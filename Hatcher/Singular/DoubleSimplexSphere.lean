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
theorem _root_.Hatcher.Sphere.doubleSimplexSwap_isoSphere (n : ℕ) :
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
