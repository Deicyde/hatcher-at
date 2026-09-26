/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Jack McCarthy, Joël Riou

Parts of the diameter argument are adapted from Joël Riou's `excision`
development (commit `8b56cd0c8e5f39a7c2f36418c80b298e469596a6`).
-/
import Hatcher.Excision.AffineSubdivision
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.Basic

/-!
# Diameter of affine barycentric subdivisions

This file proves Hatcher's uniform contraction estimate for the simplices in
an iterated barycentric subdivision.
-/

noncomputable section

open Convexity

namespace Hatcher.Excision

lemma self_div_succ_mono (a b : ℝ) (h : a ≤ b) (ha : 0 ≤ a := by positivity) :
    a / (a + 1) ≤ b / (b + 1) := by
  have hrewrite (t : ℝ) (ht : t ≠ -1) : t / (t + 1) = 1 - 1 / (t + 1) := by
    grind
  rw [hrewrite a (by grind), hrewrite b (by grind), sub_le_sub_iff_left]
  exact one_div_le_one_div_of_le (by grind) (by simpa)

lemma finset_nonempty_compl_singleton
    {α : Type*} [Nontrivial α] [Fintype α] [DecidableEq α] (x : α) :
    Finset.Nonempty {x}ᶜ := by
  obtain ⟨y, h⟩ := exists_ne x
  exact ⟨y, by simpa⟩

variable {n : ℕ} {X E : Type*} [ConvexSpace ℝ X] [NormedAddCommGroup E]
  [ConvexSpace ℝ E]

lemma dist_convexComboPair [NormedSpace ℝ E] [IsModuleConvexSpace ℝ E]
    (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t = 1) (a b : E) :
    dist a (convexCombPair s t hs ht hst a b) = t * dist a b := by
  have hcombo : convexCombPair s t hs ht hst a b - a = t • (b - a) := by
    obtain rfl : s = 1 - t := by grind
    simp [smul_sub, sub_smul]
    abel
  simp only [dist_eq_norm', hcombo, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]

/-- The diameter of the range of an affine map into a normed real vector
space. -/
def diam (f : ConvexSpace.AffineMap ℝ X E) : ℝ :=
  Metric.diam (Set.range f)

lemma diam_nonneg (f : ConvexSpace.AffineMap ℝ X E) :
    0 ≤ diam f :=
  Metric.diam_nonneg

variable [NormedSpace ℝ E] [IsModuleConvexSpace ℝ E]

lemma affineRange_convex (f : ConvexSpace.AffineMap ℝ X E) :
    Convex ℝ (Set.range f) := by
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ a b ha hb hab
  exact ⟨convexCombPair a b ha hb hab x y,
    by simp [f.isAffineMap.map_convexCombPair]⟩

variable (s : ConvexSpace.AffineMap ℝ (StdSimplex ℝ (Fin (n + 1))) E)

lemma affineRange_subset_iff_of_convex {F : Set E} (hF : Convex ℝ F) :
    Set.range s ⊆ F ↔ ∀ i, s (.single i) ∈ F := by
  refine ⟨fun h i ↦ h (by simp), fun h ↦ ?_⟩
  rintro _ ⟨x, rfl⟩
  obtain ⟨p, rfl⟩ := StdSimplex.affineMapMk_surjective s
  rw [StdSimplex.affineMapMk_apply_eq_sum_of_fintype]
  refine hF.sum_mem (by simp) ?_ (by simpa using h)
  have hx := x.total
  rwa [Finsupp.sum_fintype _ _ (by simp)] at hx

lemma affineRange_eq_convexHull :
    Set.range s = _root_.convexHull ℝ (Set.range (s ∘ StdSimplex.single)) := by
  refine subset_antisymm ?_ ?_
  · rw [affineRange_subset_iff_of_convex s (convex_convexHull ..)]
    exact fun _ ↦ subset_convexHull _ _ (by simp)
  · rw [(affineRange_convex s).convexHull_subset_iff]
    exact Set.range_comp_subset_range _ _

lemma affineRange_isBounded : Bornology.IsBounded (Set.range s) := by
  rw [affineRange_eq_convexHull s, isBounded_convexHull, ← boundedSpace_induced_iff]
  infer_instance

lemma dist_le_diam {x y : E} (hx : x ∈ Set.range s) (hy : y ∈ Set.range s) :
    dist x y ≤ diam s :=
  Metric.dist_le_diam_of_mem (affineRange_isBounded s) hx hy

lemma exists_diam_eq :
    ∃ i j, diam s = dist (s (.single i)) (s (.single j)) := by
  have hdiam : diam s = Metric.diam (Set.range (s ∘ StdSimplex.single)) := by
    simp [diam, affineRange_eq_convexHull s]
  simp only [hdiam]
  let φ (i j : Fin (n + 1)) : ℝ := dist (s (.single i)) (s (.single j))
  have := φ.uncurry
  let μ := (Finset.univ.image φ.uncurry).max' (by simp)
  have hμ : μ ∈ Finset.univ.image φ.uncurry :=
    (Finset.univ.image φ.uncurry).max'_mem (by simp)
  have hμ' (i j : Fin (n + 1)) : φ i j ≤ μ :=
    (Finset.univ.image φ.uncurry).le_max' _ (by simp)
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Prod.exists,
    Function.uncurry_apply_pair] at hμ
  obtain ⟨i, j, h⟩ := hμ
  refine ⟨i, j, le_antisymm ?_ ?_⟩
  · refine Metric.diam_le_of_forall_dist_le (by positivity) ?_
    rintro _ ⟨i', rfl⟩ _ ⟨j', rfl⟩
    exact le_of_le_of_eq (hμ' i' j') h.symm
  · exact Metric.dist_le_diam_of_mem
      (Metric.isBounded_range_iff.2 ⟨μ, hμ'⟩) (by simp) (by simp)

lemma diam_comp_le {d : ℕ}
    (t : ConvexSpace.AffineMap ℝ (StdSimplex ℝ (Fin (d + 1)))
      (StdSimplex ℝ (Fin (n + 1)))) :
    diam (s.comp t) ≤ diam s :=
  Metric.diam_mono (Set.range_comp_subset_range t s) (affineRange_isBounded s)

lemma dist_barycenter_single_eq
    (s : ConvexSpace.AffineMap ℝ (StdSimplex ℝ (Fin (n + 2))) E)
    (i : Fin (n + 2)) :
    dist (affineSubBarycenter s .univ (by simp)) (s (.single i)) =
      (n + 1) / (n + 2) *
        dist (affineSubBarycenter s {i}ᶜ (finset_nonempty_compl_singleton i))
          (s (.single i)) := by
  have hcenter :
      affineSubBarycenter s .univ (by simp) =
        convexCombPair (R := ℝ) (1 / (n + 2)) ((n + 1) / (n + 2))
          (by positivity) (by positivity) (by grind) (s (.single i))
          (affineSubBarycenter s {i}ᶜ (finset_nonempty_compl_singleton i)) := by
    dsimp [affineSubBarycenter]
    rw [← s.isAffineMap.map_convexCombPair]
    congr 1
    ext j
    by_cases hj : j = i
    · subst hj
      have hsum : ∑ c ∈ {j}ᶜ, Finsupp.single c (n + 1 : ℝ)⁻¹ j = 0 :=
        Finset.sum_eq_zero (fun k hk ↦ Finsupp.single_eq_of_ne' (by simpa using hk))
      simp [StdSimplex.weights_barycenter_apply,
        StdSimplex.subBarycenter_weights_apply_eq_zero]
    · have h₁ :
          ∑ c ∈ {i}ᶜ, (Finsupp.single c (n + 1 : ℝ)⁻¹) j =
            (n + 1 : ℝ)⁻¹ := by
        rw [Finset.sum_eq_single j (by aesop) (by aesop), Finsupp.single_eq_same]
      have h₂ :
          (n + 1 : ℝ) / (n + 2) * (n + 1 : ℝ)⁻¹ = (n + 2 : ℝ)⁻¹ := by
        grind
      simp [Finsupp.single_eq_of_ne hj, StdSimplex.weights_subBarycenter,
        Finset.card_compl, h₁, h₂]
  rw [dist_comm, hcenter, dist_convexComboPair, dist_comm]

lemma dist_barycenter_single_le (i : Fin (n + 1)) :
    dist (affineSubBarycenter s .univ (by simp)) (s (.single i)) ≤
      n / (n + 1) * diam s := by
  obtain _ | n := n
  · fin_cases i
    simp [diam, affineSubBarycenter]
  · rw [dist_barycenter_single_eq s i]
    exact mul_le_mul (by grind)
      (dist_le_diam s ⟨_, rfl⟩ (by simp)) (by simp) (by positivity)

lemma dist_barycenter_le (e : E) (he : e ∈ Set.range s) :
    dist (affineSubBarycenter s .univ (by simp)) e ≤
      n / (n + 1) * diam s := by
  rw [affineRange_eq_convexHull s] at he
  obtain ⟨_, ⟨i, rfl⟩, h⟩ :=
    convexHull_exists_dist_ge he (affineSubBarycenter s .univ (by simp))
  rw [dist_comm]
  refine h.trans ?_
  rw [dist_comm]
  simpa using dist_barycenter_single_le s i

lemma dist_subBarycenter_le
    (t : Finset (Fin (n + 1))) (ht : t.Nonempty)
    (y : StdSimplex ℝ (Fin (n + 1)))
    (hy : ∀ (i : Fin (n + 1)), i ∉ t → y.weights i = 0) :
    dist (affineSubBarycenter s t ht) (s y) ≤
      n / (n + 1) * diam s := by
  obtain ⟨d, hdn, ⟨e⟩⟩ :
      ∃ (d : ℕ), d ≤ n ∧ Nonempty (t ≃ Fin (d + 1)) := by
    generalize hd : t.card = d
    obtain _ | d := d
    · grind
    · refine ⟨d, ?_, ?_⟩
      · simpa [hd] using Finset.card_le_card t.subset_univ
      · rw [← hd]
        exact ⟨Finset.equivFin _⟩
  let φ : Fin (d + 1) → Fin (n + 1) := Subtype.val ∘ e.symm
  have hφ : Function.Injective φ := Subtype.val_injective.comp e.symm.injective
  have hφ' : Finset.image φ .univ = t := by
    ext a
    simp only [Finset.mem_image, Finset.mem_univ, Function.comp_apply, true_and, φ]
    exact ⟨by grind, fun ha ↦ ⟨e ⟨a, ha⟩, by simp⟩⟩
  have hsub := affineSubBarycenter_comp_of_injective s .univ (by simp) φ hφ
  simp only [hφ'] at hsub
  rw [← hsub]
  refine (dist_barycenter_le (s.comp (StdSimplex.affineMap φ)) (s y) ?_).trans
    (mul_le_mul (self_div_succ_mono d n (by simpa)) (diam_comp_le s _)
      (diam_nonneg _) (by positivity))
  have hy' : y ∈ Set.range (StdSimplex.map φ) := by
    rw [StdSimplex.mem_range_map_iff]
    exact fun i hi ↦ hy i (by
      rw [← hφ']
      simpa [Set.mem_range] using hi)
  obtain ⟨x, hx⟩ := hy'
  refine ⟨x, ?_⟩
  simp only [ConvexSpace.AffineMap.coe_comp, Function.comp_apply,
    StdSimplex.coe_affineMap, hx]

/-- One barycentric subdivision contracts the diameter of an affine
`n`-simplex by the factor `n / (n + 1)`. -/
theorem affineSubdivision_diameter_le
    (σ : Equiv.Perm (Fin (n + 1))) :
    diam (affineSubdivision s σ) ≤ n / (n + 1) * diam s := by
  suffices ∀ (i j : Fin (n + 1)), i ≤ j →
      dist (affineSubdivisionVertex s σ i) (affineSubdivisionVertex s σ j) ≤
        n / (n + 1) * diam s by
    obtain ⟨i, j, h⟩ := exists_diam_eq (affineSubdivision s σ)
    rw [h]
    simp only [affineSubdivision, StdSimplex.affineMapMk_single]
    obtain hij | hij := le_total i j
    · exact this _ _ hij
    · rw [dist_comm]
      exact this _ _ hij
  intro i j hij
  simp only [affineSubdivisionVertex_def]
  refine dist_subBarycenter_le s _ _ _ (fun k hk ↦
    StdSimplex.subBarycenter_weights_apply_eq_zero _ _ _ ?_)
  simp only [Equiv.Perm.coe_inv, Finset.mem_filter, Finset.mem_univ,
    true_and, not_le] at hk ⊢
  exact lt_of_lt_of_le hk hij

/-- Every `k`-fold barycentric subsimplex contracts diameter uniformly by
the factor `(n / (n + 1)) ^ k`. -/
theorem affineSubdivisionIter_diameter_le
    {k : ℕ} (σ : Fin k → Equiv.Perm (Fin (n + 1))) :
    diam (affineSubdivisionIter s σ) ≤
      (n / (n + 1)) ^ k * diam s := by
  induction k with
  | zero => simp
  | succ k ih =>
    nth_rw 2 [add_comm k 1]
    rw [affineSubdivisionIter_succ, pow_add, pow_one, mul_assoc]
    exact (affineSubdivision_diameter_le _ _).trans
      (mul_le_mul_of_nonneg_left (ih _) (by positivity))

end Hatcher.Excision
