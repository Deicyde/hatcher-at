/-
Copyright (c) 2026 Sebastian Kumar. All rights reserved.
SPDX-License-Identifier: Apache-2.0
See `LICENSES/Apache-2.0.txt`.
Authors: Sebastian Kumar

Adapted for this project from Mathlib PR #28246:
https://github.com/leanprover-community/mathlib4/pull/28246
-/
import Hatcher.Sphere.LoopInOpenCover
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Geometry.Manifold.Instances.Sphere

open Fin Function Path Set unitInterval
open scoped EuclideanSpace

namespace Hatcher.Sphere

local notation "𝕊" => fun (n : ℕ) ↦
  Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1

variable {n : ℕ}

private theorem partialEquiv_image_source_minus_singleton_eq {α β : Type*}
    (e : PartialEquiv α β) {a : α} (h : a ∈ e.source) :
    e '' (e.source \ {a}) = e.target \ {e a} := by
  rw [image_sdiff_of_injOn, PartialEquiv.image_source_eq_target, image_singleton]
  · exact e.injOn
  · exact singleton_subset_iff.mpr h

private theorem partialEquiv_symm_image_target_minus_singleton_eq {α β : Type*}
    (e : PartialEquiv α β) {b : β} (h : b ∈ e.target) :
    e.symm '' (e.target \ {b}) = e.source \ {e.symm b} :=
  partialEquiv_image_source_minus_singleton_eq e.symm h

private instance sphereNonempty : Nonempty (𝕊 n) :=
  Nonempty.to_subtype (NormedSpace.sphere_nonempty.mpr (by norm_num))

private instance sphereInfinite : Infinite (𝕊 (n + 1)) := by
  rw [← infinite_univ_iff]
  have v : 𝕊 (n + 1) := Nonempty.some inferInstance
  apply Infinite.of_image (stereographic' (n + 1) v)
  rw [image_univ]
  apply Infinite.mono
    (PartialEquiv.target_subset_range (stereographic' (n + 1) v).toPartialEquiv)
  rw [stereographic'_target]
  exact infinite_univ

private instance spherePathConnected (n : ℕ) : PathConnectedSpace (𝕊 (n + 1)) := by
  rw [← isPathConnected_iff_pathConnectedSpace]
  apply isPathConnected_sphere
  · rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
    exact Nat.one_lt_ofNat
  · exact zero_le_one' ℝ

/-- The sphere minus one point is contractible by stereographic projection. -/
private instance sphereComplSingletonContractible (v : 𝕊 n) :
    ContractibleSpace ({v}ᶜ : Set (𝕊 n)) := by
  let proj := stereographic' n v
  have : ContractibleSpace proj.target := by
    rw [stereographic'_target]
    exact Homeomorph.contractibleSpace
      (Homeomorph.Set.univ (EuclideanSpace ℝ (Fin n)))
  convert Homeomorph.contractibleSpace proj.toHomeomorphSourceTarget <;>
    exact (stereographic'_source v).symm

private theorem isPathConnected_compl_singleton (v : 𝕊 (n + 1)) :
    IsPathConnected ({v}ᶜ) := by
  rw [isPathConnected_iff_pathConnectedSpace]
  infer_instance

private lemma stereographic'_symm_zero (v : 𝕊 n) :
    (stereographic' n v).toPartialEquiv.symm 0 = -v := by
  ext
  simp [stereographic', stereographic, stereoInvFun]

/-- The sphere minus two antipodal points is path-connected in dimension at least two. -/
private theorem isPathConnected_compl_singleton_inter_neg (v : 𝕊 (n + 2)) :
    IsPathConnected ({v}ᶜ ∩ {-v}ᶜ) := by
  let proj := stereographic' (n + 2) v
  have himage : proj.toPartialEquiv.symm '' (proj.target \ {0}) = {v}ᶜ ∩ {-v}ᶜ := by
    rw [partialEquiv_symm_image_target_minus_singleton_eq,
      stereographic'_source, stereographic'_symm_zero, sdiff_eq]
    rw [stereographic'_target]
    exact mem_univ 0
  rw [← himage]
  apply IsPathConnected.image'
  · rw [stereographic'_target, ← compl_eq_univ_sdiff]
    exact isPathConnected_compl_singleton_of_one_lt_rank
      (by
        rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
        exact Nat.one_lt_ofNat) 0
  · exact ContinuousOn.mono proj.continuousOn_invFun sdiff_subset

/-- The two-set cover of the sphere by complements of antipodal points. -/
private abbrev cover (v : 𝕊 n) : Fin 2 → Set (𝕊 n) :=
  cases {v}ᶜ (fun _ ↦ {-v}ᶜ)

private lemma cover_isOpen (v : 𝕊 n) : ∀ i, IsOpen (cover v i) := by
  apply cases <;> simp

private lemma cover_iUnion (v : 𝕊 n) : univ ⊆ ⋃ i, cover v i := by
  intro s _
  rcases eq_or_ne s v with rfl | h
  · rw [mem_iUnion]
    use 1
    change s ∈ ({-s}ᶜ : Set (𝕊 n))
    rw [mem_compl_iff, mem_singleton_iff, ← Ne, ← Subtype.coe_ne_coe, coe_neg_sphere]
    intro hv
    apply ne_zero_of_mem_unit_sphere s
    ext k
    rw [PiLp.zero_apply, ← CharZero.eq_neg_self_iff, ← PiLp.neg_apply, ← hv]
  · rw [mem_iUnion]
    use 0
    exact h

private lemma cover_inter_isPathConnected (v : 𝕊 (n + 2)) :
    ∀ i j, IsPathConnected (cover v i ∩ cover v j) := by
  apply cases
  · apply cases
    · simp only [cases_zero, inter_self]
      exact isPathConnected_compl_singleton v
    · intro _
      simp only [cases_zero, cases_succ]
      exact isPathConnected_compl_singleton_inter_neg v
  · intro _
    apply cases
    · simp only [cases_succ, cases_zero, inter_comm]
      exact isPathConnected_compl_singleton_inter_neg v
    · intro _
      simp only [cases_succ, inter_self]
      exact isPathConnected_compl_singleton (-v)

private lemma exists_cover_containing (x : 𝕊 (n + 1)) :
    ∃ v, ∀ i : Fin 2, x ∈ cover v i := by
  obtain ⟨v, hv⟩ := Infinite.exists_notMem_finset {x, -x}
  use v
  apply cases
  · simp only [cases_zero, mem_compl_singleton_iff]
    intro h
    apply hv
    rw [Finset.mem_insert]
    exact Or.inl h.symm
  · simp only [cases_succ, mem_compl_singleton_iff]
    intro _ h
    apply hv
    rw [Finset.mem_insert, Finset.mem_singleton, h]
    exact Or.inr (neg_neg v).symm

/-- A loop in the sphere that misses a point is nullhomotopic. -/
private theorem homotopic_refl_of_not_surjective {v : 𝕊 n} (γ : Path v v)
    (h : ¬Surjective γ) : γ.Homotopic (Path.refl v) := by
  unfold Surjective at h
  push Not at h
  obtain ⟨w, hw⟩ := h
  let wCompl : Set (𝕊 n) := {w}ᶜ
  let v' : wCompl := ⟨v, by
    rw [mem_compl_singleton_iff]
    convert hw 0
    exact γ.source.symm⟩
  let f : I → γ ⁻¹' {w}ᶜ := fun x ↦ ⟨x, hw x⟩
  let γ' : Path v' v' :=
    { toFun := γ.restrictPreimage {w}ᶜ ∘ f
      source' := by rw [comp_apply, ContinuousMap.restrictPreimage_apply]; ext; simp [f, v']
      target' := by rw [comp_apply, ContinuousMap.restrictPreimage_apply]; ext; simp [f, v'] }
  have hs : SimplyConnectedSpace wCompl := inferInstance
  let incl : C(wCompl, 𝕊 n) := ⟨Subtype.val, continuous_subtype_val⟩
  exact Path.Homotopic.map
    ((simply_connected_iff_loops_nullhomotopic.mp hs).right v' γ') incl

/-- **Hatcher, Proposition 1.14 (page 35).** The Euclidean `(n + 2)`-sphere is
simply connected. The proof follows Hatcher's two-chart open-cover argument and is adapted from
[Mathlib PR #28246](https://github.com/leanprover-community/mathlib4/pull/28246). -/
theorem simplyConnectedSpace (n : ℕ) : SimplyConnectedSpace (𝕊 (n + 2)) := by
  rw [simply_connected_iff_loops_nullhomotopic]
  constructor
  · infer_instance
  · intro x p
    obtain ⟨v, hv⟩ := exists_cover_containing x
    obtain ⟨m, D, hDp, hDr⟩ := Hatcher.loop_homotopic_prod_of_isOpenCover
      (cover_isOpen v) (cover_iUnion v) (cover_inter_isPathConnected v) hv p
    apply Path.Homotopic.trans hDp.symm
    rw [← Path.concat_refl]
    apply Path.Homotopic.concat_hcomp
    intro k
    obtain ⟨i, hi⟩ := hDr k
    fin_cases i
    · simp only [zero_eta, cases_zero] at hi
      apply homotopic_refl_of_not_surjective
      exact fun h ↦ hi (h v) rfl
    · have hone : (1 : Fin 2) = succ 0 := rfl
      simp only [mk_one, hone, cases_succ] at hi
      apply homotopic_refl_of_not_surjective
      exact fun h ↦ hi (h (-v)) rfl

instance (n : ℕ) : SimplyConnectedSpace (𝕊 (n + 2)) := simplyConnectedSpace n

end Hatcher.Sphere
