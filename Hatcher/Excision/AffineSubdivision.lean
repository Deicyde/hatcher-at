/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Jack McCarthy, Joël Riou

Parts of the affine-subdivision construction are adapted from Joël Riou's
`excision` development (commit `8b56cd0c8e5f39a7c2f36418c80b298e469596a6`).
-/
import Mathlib.Geometry.Convex.ConvexSpace.Module
import Mathlib.Geometry.Convex.ConvexSpace.Barycenter
import Mathlib.GroupTheory.Perm.Fin

/-!
# Affine barycentric subdivision

This file defines the barycentric subsimplices of an affine simplex, their
iterates, and proves that subdivision is compatible with taking faces.  The
permutation used in the one-step face formula also records the sign needed by
the later chain-level subdivision operator.
-/

noncomputable section

open Convexity

namespace Hatcher.Excision

variable {K : Type*} [Field K] [CharZero K] [LinearOrder K] [IsStrictOrderedRing K]
  {Y : Type*} [ConvexSpace K Y]

/-- Mapping a face barycenter along an injective map of vertex sets gives the
barycenter of the corresponding image face. -/
lemma stdSimplex_map_subBarycenter_of_injective
    {M N : Type*} [DecidableEq N] (S : Finset M) (hS : S.Nonempty)
    (f : M → N) (hf : Function.Injective f) :
    StdSimplex.map f (StdSimplex.subBarycenter (K := K) S hS) =
      StdSimplex.subBarycenter (Finset.image f S) (by simpa) := by
  ext n
  simp only [StdSimplex.weights_map, StdSimplex.weights_subBarycenter,
    Finsupp.coe_finsetSum, Finset.sum_apply]
  by_cases! hn : ∃ (m : M) (hm : m ∈ S), f m = n
  · obtain ⟨m, hm, rfl⟩ := hn
    rw [Finsupp.mapDomain_apply_of_injective hf, Finset.sum_image hf.injOn,
      Finsupp.coe_finsetSum, Finset.sum_apply]
    congr
    ext x
    by_cases hx : m = x
    · subst hx
      simp [Finset.card_image_of_injective S hf]
    · rw [Finsupp.single_eq_of_ne hx, Finsupp.single_eq_of_ne
        (fun h ↦ hx (hf h))]
  · rw [Finsupp.mapDomain_of_not_mem_image_support, Finset.sum_eq_zero]
    · intro x hx
      simp only [Finset.mem_image] at hx
      obtain ⟨x, hx, rfl⟩ := hx
      rw [Finsupp.single_apply_eq_zero]
      intro h
      exact (hn x hx h.symm).elim
    · simp only [Set.mem_image, SetLike.mem_coe, Finsupp.mem_support_iff,
        Finsupp.coe_finsetSum, Finset.sum_apply, ne_eq, not_exists, not_and]
      by_contra!
      obtain ⟨m, hm, rfl⟩ := this
      replace hn : m ∉ S := fun h ↦ by simpa using hn _ h
      apply hm
      rw [Finset.sum_eq_zero]
      intro x hx
      rw [Finsupp.single_apply_eq_zero]
      rintro rfl
      tauto

/-- The image under an affine simplex of the barycenter of a nonempty face. -/
def affineSubBarycenter {M : Type*}
    (f : ConvexSpace.AffineMap K (StdSimplex K M) Y)
    (S : Finset M) (hS : S.Nonempty) : Y :=
  f (StdSimplex.subBarycenter S hS)

@[simp]
lemma affineSubBarycenter_single {M : Type*}
    (f : ConvexSpace.AffineMap K (StdSimplex K M) Y) (m : M) :
    affineSubBarycenter f {m} (by simp) = f (.single m) := by
  simp [affineSubBarycenter]

lemma affineSubBarycenter_comp_of_injective
    {M N : Type*} [DecidableEq M]
    (f : ConvexSpace.AffineMap K (StdSimplex K M) Y)
    (S : Finset N) (hS : S.Nonempty) (g : N → M)
    (hg : Function.Injective g) :
    affineSubBarycenter (f.comp (StdSimplex.affineMap (R := K) g)) S hS =
      affineSubBarycenter f (Finset.image g S) (by simpa) := by
  simp only [affineSubBarycenter, ConvexSpace.AffineMap.coe_comp,
    Function.comp_apply, StdSimplex.coe_affineMap]
  rw [stdSimplex_map_subBarycenter_of_injective S hS g hg]

variable {n : ℕ}

/-- The vertex indexed by `i` in the barycentric subsimplex selected by `σ`.
It is the barycenter of the terminal segment
`{σ i, σ (i + 1), …}` of the corresponding complete flag. -/
def affineSubdivisionVertex
    (f : ConvexSpace.AffineMap K (StdSimplex K (Fin n)) Y)
    (σ : Equiv.Perm (Fin n)) (i : Fin n) : Y :=
  affineSubBarycenter f {x : Fin n | i ≤ σ⁻¹ x} ⟨σ i, by simp⟩

lemma affineSubdivisionVertex_def
    (f : ConvexSpace.AffineMap K (StdSimplex K (Fin n)) Y)
    (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    affineSubdivisionVertex f σ i =
      affineSubBarycenter f {x : Fin n | i ≤ σ⁻¹ x} ⟨σ i, by simp⟩ :=
  rfl

/-- The affine simplex associated to one maximal simplex in the barycentric
subdivision, indexed by a permutation of its vertices. -/
def affineSubdivision
    (f : ConvexSpace.AffineMap K (StdSimplex K (Fin n)) Y)
    (σ : Equiv.Perm (Fin n)) :
    ConvexSpace.AffineMap K (StdSimplex K (Fin n)) Y :=
  StdSimplex.affineMapMk (affineSubdivisionVertex f σ)

/-- The iterated affine subsimplex selected by a sequence of permutations. -/
def affineSubdivisionIter
    (f : ConvexSpace.AffineMap K (StdSimplex K (Fin n)) Y) {k : ℕ}
    (σ : Fin k → Equiv.Perm (Fin n)) :
    ConvexSpace.AffineMap K (StdSimplex K (Fin n)) Y := by
  induction k generalizing f with
  | zero => exact f
  | succ k ih => exact affineSubdivision (ih f (σ ∘ Fin.succ)) (σ 0)

@[simp]
lemma affineSubdivisionIter_zero
    (f : ConvexSpace.AffineMap K (StdSimplex K (Fin n)) Y)
    (σ : Fin 0 → Equiv.Perm (Fin n)) :
    affineSubdivisionIter f σ = f := by
  rfl

lemma affineSubdivisionIter_succ
    (f : ConvexSpace.AffineMap K (StdSimplex K (Fin n)) Y) {k : ℕ}
    (σ : Fin (k + 1) → Equiv.Perm (Fin n)) :
    affineSubdivisionIter f σ =
      affineSubdivision (affineSubdivisionIter f (σ ∘ Fin.succ)) (σ 0) := by
  rfl

lemma affineSubdivisionIter_succ_last
    (f : ConvexSpace.AffineMap K (StdSimplex K (Fin n)) Y) {k : ℕ}
    (σ : Fin (k + 1) → Equiv.Perm (Fin n)) :
    affineSubdivisionIter f σ =
      affineSubdivisionIter (affineSubdivision f (σ (Fin.last _)))
        (σ ∘ Fin.castSucc) := by
  induction k generalizing f with
  | zero => simp [affineSubdivisionIter_succ]
  | succ k ih =>
    rw [affineSubdivisionIter_succ]
    nth_rw 2 [affineSubdivisionIter_succ]
    congr 1
    rw [ih]
    rfl

/-- The face obtained by omitting vertex `i`. -/
def affineFace
    (f : ConvexSpace.AffineMap K (StdSimplex K (Fin (n + 2))) Y)
    (i : Fin (n + 2)) :
    ConvexSpace.AffineMap K (StdSimplex K (Fin (n + 1))) Y :=
  f.comp (StdSimplex.affineMap i.succAbove)

@[simp]
lemma affineFace_single
    (f : ConvexSpace.AffineMap K (StdSimplex K (Fin (n + 2))) Y)
    (i : Fin (n + 2)) (j : Fin (n + 1)) :
    affineFace f i (.single j) = f (.single (i.succAbove j)) := by
  simp [affineFace]

/-- The permutation that inserts the omitted face vertex in front of the
permutation indexing a subdivided face. -/
def affineSubdivisionFacePermutation
    (i : Fin (n + 2)) (σ : Equiv.Perm (Fin (n + 1))) :
    Equiv.Perm (Fin (n + 2)) :=
  Equiv.Perm.decomposeFin'Symm i σ

@[simp]
lemma affineSubdivisionFacePermutation_zero
    (i : Fin (n + 2)) (σ : Equiv.Perm (Fin (n + 1))) :
    affineSubdivisionFacePermutation i σ 0 = i :=
  Equiv.Perm.decomposeFin'Symm_zero i σ

@[simp]
lemma affineSubdivisionFacePermutation_succ
    (i : Fin (n + 2)) (σ : Equiv.Perm (Fin (n + 1))) (j : Fin (n + 1)) :
    affineSubdivisionFacePermutation i σ j.succ = i.succAbove (σ j) :=
  Equiv.Perm.decomposeFin'Symm_succ i σ j

/-- Sign bookkeeping for the permutation appearing in the face formula. -/
@[simp]
lemma affineSubdivisionFacePermutation_sign
    (i : Fin (n + 2)) (σ : Equiv.Perm (Fin (n + 1))) :
    (affineSubdivisionFacePermutation i σ).sign = (-1) ^ i.val * σ.sign :=
  Equiv.Perm.sign_decomposeFin'Symm i σ

/-- A single barycentric subdivision of a face is the zeroth face of the
subsimplex indexed by the inserted permutation. -/
theorem affineSubdivision_face
    (f : ConvexSpace.AffineMap K (StdSimplex K (Fin (n + 2))) Y)
    (i : Fin (n + 2)) (σ : Equiv.Perm (Fin (n + 1))) :
    affineSubdivision (affineFace f i) σ =
      affineFace (affineSubdivision f (affineSubdivisionFacePermutation i σ)) 0 := by
  apply StdSimplex.affineMap_ext
  intro j
  rw [affineFace_single]
  simp only [Fin.zero_succAbove, affineSubdivision,
    StdSimplex.affineMapMk_single, affineSubdivisionVertex_def, affineFace]
  have hfaces :
      Finset.image i.succAbove
          {x : Fin (n + 1) | j ≤ σ⁻¹ x} =
        ({x : Fin (n + 2) |
          j.succ ≤ (affineSubdivisionFacePermutation i σ)⁻¹ x} : Finset _) := by
    ext k
    simp only [Equiv.Perm.coe_inv, Finset.mem_image, Finset.mem_filter,
      Finset.mem_univ, true_and]
    refine ⟨?_, fun h ↦ ?_⟩
    · rintro ⟨k, hk, rfl⟩
      obtain ⟨k, rfl⟩ := σ.surjective k
      simpa [affineSubdivisionFacePermutation] using hk
    · obtain ⟨k, rfl⟩ := (affineSubdivisionFacePermutation i σ).surjective k
      obtain ⟨k, rfl⟩ := k.eq_succ_of_ne_zero (by grind)
      simpa [affineSubdivisionFacePermutation] using h
  rw [affineSubBarycenter_comp_of_injective _ _ ⟨σ j, by simp⟩ _
    Fin.succAbove_right_injective]
  simp only [hfaces]

/-- Every iterated barycentric subdivision of a face occurs as a face of an
iterated barycentric subdivision of the original affine simplex. -/
theorem affineSubdivisionIter_face
    (f : ConvexSpace.AffineMap K (StdSimplex K (Fin (n + 2))) Y)
    (i : Fin (n + 2)) {k : ℕ}
    (σ : Fin k → Equiv.Perm (Fin (n + 1))) :
    ∃ (σ' : Fin k → Equiv.Perm (Fin (n + 2))) (i' : Fin (n + 2)),
      affineSubdivisionIter (affineFace f i) σ =
        affineFace (affineSubdivisionIter f σ') i' := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
    obtain ⟨σ', i', h⟩ :=
      ih (affineSubdivision f
        (affineSubdivisionFacePermutation i (σ (Fin.last k)))) 0
        (σ ∘ Fin.castSucc)
    refine ⟨Fin.lastCases (affineSubdivisionFacePermutation i (σ (Fin.last k))) σ', i', ?_⟩
    rw [affineSubdivisionIter_succ_last, affineSubdivision_face, h,
      affineSubdivisionIter_succ_last, Fin.lastCases_last]
    congr
    aesop

end Hatcher.Excision
