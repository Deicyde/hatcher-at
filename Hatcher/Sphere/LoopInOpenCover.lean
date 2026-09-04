/-
Copyright (c) 2026 Sebastian Kumar. All rights reserved.
SPDX-License-Identifier: Apache-2.0
See `LICENSES/Apache-2.0.txt`.
Authors: Sebastian Kumar

Adapted for this project from Mathlib PR #28246:
https://github.com/leanprover-community/mathlib4/pull/28246
-/
import Mathlib.Topology.Subpath

open Fin Set unitInterval

universe u v

namespace Hatcher

variable {X : Type u} [TopologicalSpace X] {ι : Type v} {c : ι → Set X} {a : X}

local infixr:80 " ≫ₚ " => Path.trans

/-- Pull a loop back along an open cover to obtain a finite subdivision of the unit interval
whose pieces each map into one member of the cover. -/
private theorem exists_partition_unitInterval_of_open_cover (hc₁ : ∀ i, IsOpen (c i))
    (hc₂ : univ ⊆ ⋃ i, c i) (γ : Path a a) : ∃ (n : ℕ) (t : Fin (n + 2) → I),
    t 0 = 0 ∧ t (last (n + 1)) = 1 ∧
      ∀ k : Fin (n + 1), ∃ i, γ '' (uIcc (t k.castSucc) (t k.succ)) ⊆ c i := by
  have ⟨t, ht₀, ht_mono, ⟨n, ht₁⟩, ht_sub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval
      (fun i ↦ IsOpen.preimage (Path.continuous γ) (hc₁ i))
      (fun _ _ ↦ (preimage_iUnion ▸ hc₂ (mem_univ _)))
  use n, t ∘ Fin.toNat
  suffices ∀ k : Fin (n + 1), ∃ i, uIcc (t ↑k) (t (↑k + 1)) ⊆ ⇑γ ⁻¹' c i by
    simpa [ht₀, ht₁]
  intro k
  obtain ⟨i, hi⟩ := ht_sub k
  use i
  rwa [uIcc_of_le (ht_mono (Nat.le_add_right _ _))]

/-- Choose paths from the basepoint to the subdivision points inside adjacent cover sets. -/
private theorem exists_path_range_of_isPathConnected_inter
    (hc₃ : ∀ i j, IsPathConnected (c i ∩ c j)) (ha : ∀ i, a ∈ c i) {n : ℕ}
    (τ : Fin (n + 1) → ι) (p : Fin (n + 2) → X)
    (hτ₁ : ∀ k, p k.castSucc ∈ c (τ k)) (hτ₂ : ∀ k, p k.succ ∈ c (τ k)) :
    ∀ k : Fin n, ∃ g : Path a (p k.succ.castSucc),
      Set.range g ⊆ c (τ k.castSucc) ∩ c (τ k.succ) := by
  intro k
  obtain ⟨γ, hγ⟩ := (hc₃ (τ k.castSucc) (τ k.succ)).joinedIn
    a ⟨ha (τ k.castSucc), ha (τ k.succ)⟩
      (p k.castSucc.succ) ⟨hτ₂ k.castSucc, hτ₁ k.succ⟩
  use γ
  exact range_subset_iff.mpr hγ

/-- Cancelling the connecting paths in a concatenation leaves the original subdivided path. -/
lemma concat_trans_trans_symm {n : ℕ} (p q : Fin (n + 1) → X)
    (F : ∀ k : Fin n, Path (p k.castSucc) (p k.succ))
    (G : ∀ k : Fin (n + 1), Path (q k) (p k)) :
    (Path.concat q (fun k ↦ (G k.castSucc) ≫ₚ (F k) ≫ₚ (G k.succ).symm)).Homotopic
      ((G 0) ≫ₚ (Path.concat p F) ≫ₚ (G (last n)).symm) := by
  induction n with
  | zero =>
    simp only [Path.concat_zero, ← FundamentalGroupoid.fromPath_eq_iff_homotopic]
    aesop_cat
  | succ n hn =>
    have := Path.Homotopic.Quotient.eq.mpr
      (hn (p ∘ castSucc) (q ∘ castSucc) (fun k ↦ F k.castSucc) (fun k ↦ G k.castSucc))
    simp at this
    apply Path.Homotopic.Quotient.exact
    simp only [Path.concat_succ, Function.comp_apply, castSucc_zero, succ_last,
      Nat.succ_eq_add_one, Path.Homotopic.Quotient.mk_trans, this,
      Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.mk_symm]
    grind

/-- Remove endpoint casts around a homotopy after adjoining constant paths. -/
lemma cast_trans_trans_homotopic_of_homotopic_cast {x x₀ x₁ : X}
    {h₀ : x₀ = x} {h₁ : x₁ = x} {p : Path x₀ x₁} {q : Path x x}
    (h : p.Homotopic (q.cast h₀ h₁)) :
    (((Path.refl x).cast rfl h₀) ≫ₚ p ≫ₚ ((Path.refl x).cast h₁ rfl)).Homotopic q := by
  subst_vars
  exact Path.Homotopic.trans
    (Path.Homotopic.trans ⟨Path.Homotopy.reflTrans _⟩ ⟨Path.Homotopy.transRefl _⟩) h

/-- **Hatcher, Lemma 1.15 (page 35).** If `X` is covered by open sets whose pairwise
intersections are path-connected and all contain the basepoint, then every loop at the basepoint
is homotopic to a finite concatenation of loops, each lying in one member of the cover.

This proof is adapted from
[Mathlib PR #28246](https://github.com/leanprover-community/mathlib4/pull/28246). -/
theorem loop_homotopic_prod_of_isOpenCover (hc₁ : ∀ i, IsOpen (c i))
    (hc₂ : univ ⊆ ⋃ i, c i) (hc₃ : ∀ i j, IsPathConnected (c i ∩ c j))
    (ha : ∀ i, a ∈ c i) (γ : Path a a) :
    ∃ (n : ℕ) (D : Fin (n + 1) → Path a a),
      (Path.concat (fun _ ↦ a) D).Homotopic γ ∧
        ∀ k, ∃ i : ι, Set.range (D k) ⊆ c i := by
  obtain ⟨n, t, ht₀, ht₁, ht_range⟩ :=
    exists_partition_unitInterval_of_open_cover hc₁ hc₂ γ
  choose τ hτ using ht_range
  have hpaths := exists_path_range_of_isPathConnected_inter hc₃ ha τ (γ ∘ t)
    (fun k ↦ hτ k (mem_image_of_mem γ left_mem_uIcc))
    (fun k ↦ hτ k (mem_image_of_mem γ right_mem_uIcc))
  choose G hG using hpaths
  let G' := snoc (α := fun k ↦ Path a (γ (t k)))
    (cons (α := fun k ↦ Path a (γ (t k.castSucc)))
      ((Path.refl a).cast rfl (ht₀ ▸ γ.source)) G)
    ((Path.refl a).cast rfl (ht₁ ▸ γ.target))
  have hG'₀ : G' 0 = (Path.refl a).cast rfl (ht₀ ▸ γ.source) :=
    (snoc_apply_zero _ _).trans (cons_zero _ _)
  have hG'₁ : G' (last (n + 1)) = (Path.refl a).cast rfl (ht₁ ▸ γ.target) :=
    snoc_last _ _
  have hG'_range₀ k : range (G' k.castSucc) ⊆ c (τ k) := by
    unfold G'
    rw [snoc_castSucc]
    cases k using Fin.cases with
    | zero =>
      rw [cons_zero, Path.cast_coe, Path.refl_range, singleton_subset_iff]
      exact ha _
    | succ j => exact (subset_inter_iff.mp (hG j)).right
  have hG'_range₁ k : range (G' k.succ) ⊆ c (τ k) := by
    unfold G'
    cases k using Fin.lastCases with
    | cast =>
      rw [succ_castSucc, snoc_castSucc]
      exact (subset_inter_iff.mp (hG _)).left
    | last =>
      rw [succ_last, snoc_last, Path.cast_coe, Path.refl_range, singleton_subset_iff]
      exact ha _
  use n, fun k ↦
    (G' k.castSucc) ≫ₚ (γ.subpath (t k.castSucc) (t k.succ)) ≫ₚ (G' k.succ).symm
  constructor
  · apply Path.Homotopic.trans (concat_trans_trans_symm _ _ _ _)
    rw [hG'₀, hG'₁, ← Path.cast_symm, Path.refl_symm]
    refine cast_trans_trans_homotopic_of_homotopic_cast
      (Path.Homotopic.trans (Path.Homotopic.concat_subpath _ _) ?_)
    rw! (castMode := .all) [ht₀, ht₁, Path.subpath_zero_one]
    rfl
  · intro k
    use τ k
    grind [Path.trans_range, Path.symm_range, union_subset, Path.range_subpath]

end Hatcher
