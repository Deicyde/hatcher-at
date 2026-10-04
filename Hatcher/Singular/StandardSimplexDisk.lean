/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Hatcher.Singular.StandardSimplexBoundaryHorn
import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Geometry.Convex.ConvexSpace.ModuleTopology
import Mathlib.Topology.Category.TopCat.Sphere

/-!
# The standard simplex as a disk

This file identifies the ordered topological standard simplex and its boundary
with Mathlib's standard disk and sphere.  The construction first realizes the
simplex as the convex hull of an affine basis of Euclidean space, then uses
radial gauge rescaling to carry that convex body and its frontier to the unit
closed ball and unit sphere.
-/

noncomputable section

open CategoryTheory Metric Set Topology

namespace Hatcher.Simplex

attribute [local instance] Convexity.ConvexSpace.ofModule
  Convexity.IsModuleConvexSpace.of_module

private abbrev EuclideanModel (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- An affine basis of Euclidean `n`-space indexed by the `n+1` vertices of
the ordered standard simplex. -/
private noncomputable def standardAffineBasis (n : ℕ) :
    AffineBasis (Fin (n + 1)) ℝ (EuclideanModel n) :=
  Classical.choice <| AffineBasis.exists_affineBasis_of_finiteDimensional
    (k := ℝ) (P := EuclideanModel n) (by simp)

/-- The convex-body realization of the standard simplex associated to
`standardAffineBasis`. -/
private def standardSimplexBody (n : ℕ) : Set (EuclideanModel n) :=
  convexHull ℝ (Set.range (standardAffineBasis n))

/-- Barycentric affine realization of the ordered standard simplex. -/
private noncomputable def standardSimplexAffineMap (n : ℕ) :
    StandardSimplex n → EuclideanModel n :=
  Convexity.StdSimplex.affineMapMk (standardAffineBasis n)

private lemma standardSimplexAffineMap_coord (n : ℕ)
    (x : StandardSimplex n) (i : Fin (n + 1)) :
    (standardAffineBasis n).coord i (standardSimplexAffineMap n x) =
      x.weights i := by
  rw [standardSimplexAffineMap,
    Convexity.StdSimplex.affineMapMk_apply_eq_sum_of_fintype]
  rw [← Finset.univ.affineCombination_eq_linear_combination _ _
    x.total_of_fintype]
  exact (standardAffineBasis n).coord_apply_combination_of_mem
    (Finset.mem_univ i) x.total_of_fintype

private lemma standardSimplexAffineMap_mem_body (n : ℕ)
    (x : StandardSimplex n) :
    standardSimplexAffineMap n x ∈ standardSimplexBody n := by
  rw [standardSimplexBody,
    (standardAffineBasis n).convexHull_eq_nonneg_coord]
  intro i
  rw [standardSimplexAffineMap_coord]
  exact x.weights_nonneg i

/-- The barycentric coordinates of a point in the affine simplex, regarded as
a point of the ordered standard simplex. -/
private noncomputable def standardSimplexAffineCoordinates (n : ℕ)
    (x : standardSimplexBody n) : StandardSimplex n where
  weights := Finsupp.equivFunOnFinite.symm
    (fun i ↦ (standardAffineBasis n).coord i x.1)
  nonneg := by
    intro i
    change 0 ≤ (standardAffineBasis n).coord i x.1
    have hx := x.2
    change x.1 ∈ convexHull ℝ (Set.range (standardAffineBasis n)) at hx
    rw [(standardAffineBasis n).convexHull_eq_nonneg_coord] at hx
    exact hx i
  total := by
    rw [Finsupp.equivFunOnFinite_symm_sum]
    exact (standardAffineBasis n).sum_coord_apply_eq_one x.1

@[simp]
private lemma standardSimplexAffineCoordinates_weights (n : ℕ)
    (x : standardSimplexBody n) (i : Fin (n + 1)) :
    (standardSimplexAffineCoordinates n x).weights i =
      (standardAffineBasis n).coord i x.1 := by
  rfl

private lemma standardSimplexAffineCoordinates_left_inv (n : ℕ)
    (x : StandardSimplex n) :
    standardSimplexAffineCoordinates n
        ⟨standardSimplexAffineMap n x,
          standardSimplexAffineMap_mem_body n x⟩ = x := by
  apply Convexity.StdSimplex.weights_inj.mp
  ext i
  rw [standardSimplexAffineCoordinates_weights,
    standardSimplexAffineMap_coord]

private lemma standardSimplexAffineCoordinates_right_inv (n : ℕ)
    (x : standardSimplexBody n) :
    standardSimplexAffineMap n (standardSimplexAffineCoordinates n x) = x.1 := by
  rw [standardSimplexAffineMap,
    Convexity.StdSimplex.affineMapMk_apply_eq_sum_of_fintype]
  simp only [standardSimplexAffineCoordinates_weights]
  exact (standardAffineBasis n).linear_combination_coord_eq_self x.1

private theorem continuous_standardSimplexAffineMap (n : ℕ) :
    Continuous (standardSimplexAffineMap n) := by
  exact Convexity.StdSimplex.continuous_of_affineMap
    (Convexity.StdSimplex.affineMapMk (standardAffineBasis n))

private theorem continuous_standardSimplexAffineCoordinates (n : ℕ) :
    Continuous (standardSimplexAffineCoordinates n) := by
  rw [(Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ
    (Fin (n + 1))).continuous_iff]
  rw [continuous_pi_iff]
  intro i
  change Continuous (fun x : standardSimplexBody n ↦
    (standardAffineBasis n).coord i x.1)
  exact (continuous_barycentric_coord (standardAffineBasis n) i).comp
    continuous_subtype_val

/-- The ordered standard simplex as the convex hull of an affine basis of
Euclidean `n`-space. -/
private noncomputable def standardSimplexAffineHomeomorph (n : ℕ) :
    StandardSimplex n ≃ₜ standardSimplexBody n where
  toFun x := ⟨standardSimplexAffineMap n x,
    standardSimplexAffineMap_mem_body n x⟩
  invFun := standardSimplexAffineCoordinates n
  left_inv := standardSimplexAffineCoordinates_left_inv n
  right_inv := by
    intro x
    apply Subtype.ext
    exact standardSimplexAffineCoordinates_right_inv n x
  continuous_toFun := (continuous_standardSimplexAffineMap n).subtype_mk _
  continuous_invFun := continuous_standardSimplexAffineCoordinates n

private lemma isClosed_standardSimplexBody (n : ℕ) :
    IsClosed (standardSimplexBody n) := by
  exact (Set.finite_range (standardAffineBasis n)).isClosed_convexHull ℝ

private lemma isBounded_standardSimplexBody (n : ℕ) :
    Bornology.IsBounded (standardSimplexBody n) := by
  rw [standardSimplexBody, isBounded_convexHull]
  exact (Set.finite_range (standardAffineBasis n)).isBounded

private lemma interior_standardSimplexBody_nonempty (n : ℕ) :
    (interior (standardSimplexBody n)).Nonempty := by
  exact ⟨Finset.univ.centroid ℝ (standardAffineBasis n),
    (standardAffineBasis n).centroid_mem_interior_convexHull⟩

/-- Gauge rescaling carrying the affine simplex body to the Euclidean unit
closed ball and its frontier to the unit sphere. -/
private noncomputable def standardSimplexGaugeHomeomorph (n : ℕ) :
    EuclideanModel n ≃ₜ EuclideanModel n :=
  Classical.choose <|
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall
      (convex_convexHull ℝ (Set.range (standardAffineBasis n)))
      (interior_standardSimplexBody_nonempty n)
      (isBounded_standardSimplexBody n)

private lemma standardSimplexGaugeHomeomorph_image_body (n : ℕ) :
    standardSimplexGaugeHomeomorph n '' standardSimplexBody n =
      closedBall (0 : EuclideanModel n) 1 := by
  have h := (Classical.choose_spec <|
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall
      (convex_convexHull ℝ (Set.range (standardAffineBasis n)))
      (interior_standardSimplexBody_nonempty n)
      (isBounded_standardSimplexBody n)).2.1
  rw [← (isClosed_standardSimplexBody n).closure_eq]
  simpa [standardSimplexGaugeHomeomorph, standardSimplexBody] using h

private lemma standardSimplexGaugeHomeomorph_image_frontier (n : ℕ) :
    standardSimplexGaugeHomeomorph n '' frontier (standardSimplexBody n) =
      sphere (0 : EuclideanModel n) 1 := by
  exact (Classical.choose_spec <|
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall
      (convex_convexHull ℝ (Set.range (standardAffineBasis n)))
      (interior_standardSimplexBody_nonempty n)
      (isBounded_standardSimplexBody n)).2.2

private lemma standardSimplexAffineMap_mem_frontier_iff (n : ℕ)
    (x : StandardSimplex n) :
    standardSimplexAffineMap n x ∈ frontier (standardSimplexBody n) ↔
      x ∈ standardSimplexBoundary n := by
  rw [frontier, (isClosed_standardSimplexBody n).closure_eq, mem_sdiff]
  rw [standardSimplexBody,
    (standardAffineBasis n).interior_convexHull]
  simp only [mem_ofPred_eq, standardSimplexAffineMap_coord,
    standardSimplexBoundary]
  constructor
  · rintro ⟨_, h⟩
    push Not at h
    obtain ⟨i, hi⟩ := h
    exact ⟨i, le_antisymm hi (x.weights_nonneg i)⟩
  · rintro ⟨i, hi⟩
    refine ⟨standardSimplexAffineMap_mem_body n x, ?_⟩
    intro hall
    have := hall i
    linarith

private lemma standardSimplexGaugeHomeomorph_mem_closedBall_iff (n : ℕ)
    (x : EuclideanModel n) :
    standardSimplexGaugeHomeomorph n x ∈ closedBall 0 1 ↔
      x ∈ standardSimplexBody n := by
  constructor
  · intro hx
    rw [← standardSimplexGaugeHomeomorph_image_body n] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    have hyx : y = x := (standardSimplexGaugeHomeomorph n).injective hxy
    simpa [hyx] using hy
  · intro hx
    rw [← standardSimplexGaugeHomeomorph_image_body n]
    exact ⟨x, hx, rfl⟩

private lemma standardSimplexGaugeHomeomorph_mem_sphere_iff (n : ℕ)
    (x : EuclideanModel n) :
    standardSimplexGaugeHomeomorph n x ∈ sphere 0 1 ↔
      x ∈ frontier (standardSimplexBody n) := by
  constructor
  · intro hx
    rw [← standardSimplexGaugeHomeomorph_image_frontier n] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    have hyx : y = x := (standardSimplexGaugeHomeomorph n).injective hxy
    simpa [hyx] using hy
  · intro hx
    rw [← standardSimplexGaugeHomeomorph_image_frontier n]
    exact ⟨x, hx, rfl⟩

/-- The homeomorphism from the ordered standard simplex to the ordinary unit
closed ball before the universe-lifting convention in `TopCat.disk`. -/
private noncomputable def standardSimplexClosedBallHomeomorph (n : ℕ) :
    StandardSimplex n ≃ₜ closedBall (0 : EuclideanModel n) 1 :=
  (standardSimplexAffineHomeomorph n).trans <|
    (standardSimplexGaugeHomeomorph n).subtype <| fun x ↦
      (standardSimplexGaugeHomeomorph_mem_closedBall_iff n x).symm

private lemma standardSimplexClosedBallHomeomorph_mem_sphere_iff (n : ℕ)
    (x : StandardSimplex n) :
    (standardSimplexClosedBallHomeomorph n x).1 ∈ sphere 0 1 ↔
      x ∈ standardSimplexBoundary n := by
  change standardSimplexGaugeHomeomorph n
      (standardSimplexAffineMap n x) ∈ sphere 0 1 ↔
    x ∈ standardSimplexBoundary n
  rw [
    standardSimplexGaugeHomeomorph_mem_sphere_iff,
    standardSimplexAffineMap_mem_frontier_iff]

/-- The restriction of `standardSimplexClosedBallHomeomorph` to the boundary
and unit sphere.  In dimension zero both source and target are empty. -/
private noncomputable def standardSimplexBoundarySphereHomeomorph (n : ℕ) :
    standardSimplexBoundary n ≃ₜ sphere (0 : EuclideanModel n) 1 where
  toFun x := ⟨(standardSimplexClosedBallHomeomorph n x.1).1,
    (standardSimplexClosedBallHomeomorph_mem_sphere_iff n x.1).2 x.2⟩
  invFun y := ⟨(standardSimplexClosedBallHomeomorph n).symm
      ⟨y.1, Metric.mem_closedBall.2 (le_of_eq y.2)⟩, by
    apply (standardSimplexClosedBallHomeomorph_mem_sphere_iff n _).1
    rw [(standardSimplexClosedBallHomeomorph n).apply_symm_apply]
    exact y.2⟩
  left_inv := by
    intro x
    apply Subtype.ext
    exact (standardSimplexClosedBallHomeomorph n).left_inv x.1
  right_inv := by
    intro y
    apply Subtype.ext
    change ((standardSimplexClosedBallHomeomorph n)
      ((standardSimplexClosedBallHomeomorph n).symm
        ⟨y.1, Metric.mem_closedBall.2 (le_of_eq y.2)⟩)).1 = y.1
    exact congrArg Subtype.val <|
      (standardSimplexClosedBallHomeomorph n).apply_symm_apply
        ⟨y.1, Metric.mem_closedBall.2 (le_of_eq y.2)⟩
  continuous_toFun := by
    exact (continuous_subtype_val.comp
      ((standardSimplexClosedBallHomeomorph n).continuous.comp
        continuous_subtype_val)).subtype_mk _
  continuous_invFun := by
    have hinc : Continuous (fun y : sphere (0 : EuclideanModel n) 1 ↦
        (⟨y.1, Metric.mem_closedBall.2 (le_of_eq y.2)⟩ :
          closedBall (0 : EuclideanModel n) 1)) :=
      continuous_subtype_val.subtype_mk _
    exact ((standardSimplexClosedBallHomeomorph n).symm.continuous.comp hinc).subtype_mk _

/-- Mathlib's standard disk pair `(Dⁿ, ∂Dⁿ)`. -/
def standardDiskPair (n : ℕ) : TopPair.{0} :=
  TopPair.of (TopCat.diskBoundaryInclusion.{0} n)
    (by
      let _ : T2Space ((TopCat.disk.{0} n : TopCat.{0}) : Type) := by
        change T2Space (ULift (closedBall (0 : EuclideanModel n) 1))
        infer_instance
      exact (TopCat.diskBoundaryInclusion.{0} n).hom.continuous.isClosedEmbedding
        ((TopCat.mono_iff_injective _).mp inferInstance) |>.isEmbedding)

/-- The ordered standard simplex pair is isomorphic to Mathlib's standard
disk pair.  The two component homeomorphisms are restrictions of the same
gauge-rescaled affine realization. -/
noncomputable def standardSimplexPairIsoDiskPair (n : ℕ) :
    standardSimplexPair n ≅ standardDiskPair n :=
  MorphismProperty.Arrow.isoMk
    (TopCat.isoOfHomeo <|
      (standardSimplexBoundarySphereHomeomorph n).trans Homeomorph.ulift.symm)
    (TopCat.isoOfHomeo <|
      (standardSimplexClosedBallHomeomorph n).trans Homeomorph.ulift.symm)
    (by
      ext x
      rfl)

end Hatcher.Simplex
