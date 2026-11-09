/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Hatcher.Topology.StrongDeformationRetract
import Hatcher.Appendix.RegularNeighborhoodDeformation
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.Topology.Category.TopPair

/-!
# Good pairs

This file packages Hatcher's definition of a good topological pair.  A good
pair consists of a nonempty closed subspace which is a strong deformation
retract of a neighborhood in the ambient space.
-/

noncomputable section

open CategoryTheory Set Topology

namespace Hatcher.Relative

universe u

/-- The map from the subspace of a topological pair into a set containing its
image. -/
def goodPairNeighborhoodInclusion (P : TopPair.{u}) (V : Set P.fst)
    (hV : Set.range P.map ⊆ V) : C(P.snd, V) where
  toFun a := ⟨P.map a, hV ⟨a, rfl⟩⟩
  continuous_toFun := P.map.hom.continuous.subtype_mk _

/-- The induced inclusion into a neighborhood is a topological embedding. -/
theorem goodPairNeighborhoodInclusion_isEmbedding (P : TopPair.{u})
    (V : Set P.fst) (hV : Set.range P.map ⊆ V) :
    IsEmbedding (goodPairNeighborhoodInclusion P V hV) :=
  P.isEmbedding_map.codRestrict V (fun a ↦ hV ⟨a, rfl⟩)

/-- Chosen witness data that a topological pair is good in Hatcher's sense. -/
structure GoodPairData (P : TopPair.{u}) where
  /-- The subspace is nonempty. -/
  nonempty : Nonempty P.snd
  /-- The image of the subspace is closed in the ambient space. -/
  isClosed_range : IsClosed (Set.range P.map)
  /-- A neighborhood of the embedded subspace. It need not itself be open. -/
  V : Set P.fst
  /-- The chosen set contains the embedded subspace in its interior. -/
  range_subset_interior : Set.range P.map ⊆ interior V
  /-- The chosen neighborhood strongly deformation retracts onto the embedded
  subspace. -/
  strongDeformationRetract :
    Hatcher.StrongDeformationRetract
      (goodPairNeighborhoodInclusion P V
        (range_subset_interior.trans interior_subset))

/-- A topological pair is good when it admits Hatcher's witness data. -/
def IsGoodPair (P : TopPair.{u}) : Prop :=
  Nonempty (GoodPairData P)

/-- The object property of being a good topological pair. -/
def goodPairProperty : ObjectProperty TopPair.{u} :=
  IsGoodPair

/-- The full subcategory of good topological pairs. Its morphisms are ordinary
morphisms of topological pairs and do not preserve chosen witness data. -/
abbrev GoodPair : Type (u + 1) :=
  goodPairProperty.FullSubcategory

/-- The inclusion of good pairs into all topological pairs. -/
abbrev goodPairForget : GoodPair.{u} ⥤ TopPair.{u} :=
  goodPairProperty.ι

end Hatcher.Relative

namespace Hatcher.ClassicalCW

universe u

/-- A nonempty classical CW subcomplex is a good pair with its ambient
complex. The witness uses the actual fixed-width regular neighborhood and
its completed strong deformation retraction. -/
theorem subcomplex_isGoodPair
    {X : Type u} [TopologicalSpace X] [T2Space X]
    (C : Set X) [CWComplex C] (A : CWComplex.Subcomplex C)
    (hA : (A : Set X).Nonempty) :
    Hatcher.Relative.IsGoodPair
      (TopPair.of
        (TopCat.ofHom (ContinuousMap.inclusion A.subset_complex))
        (IsEmbedding.inclusion A.subset_complex)) := by
  let P : TopPair.{u} := TopPair.of
    (TopCat.ofHom (ContinuousMap.inclusion A.subset_complex))
    (IsEmbedding.inclusion A.subset_complex)
  let V : Set ↑C :=
    ((↑) : ↑C → X) ⁻¹' regularNeighborhood C A
  have hrange : Set.range P.map =
      ((↑) : ↑C → X) ⁻¹' (A : Set X) := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact a.2
    · intro hx
      exact ⟨⟨x.1, hx⟩, Subtype.ext rfl⟩
  have hinterior : Set.range P.map ⊆ interior V := by
    rw [hrange]
    exact subcomplex_subset_interior_regularNeighborhood C A
  let i : C(↑(A : Set X), V) :=
    Hatcher.Relative.goodPairNeighborhoodInclusion P V
      (hinterior.trans interior_subset)
  let e : V ≃ₜ ↑(regularNeighborhood C A) :=
    { toFun := fun x ↦ ⟨x.1.1, x.2⟩
      invFun := fun x ↦
        ⟨⟨x.1, regularNeighborhood_subset_complex C A x.2⟩, x.2⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl
      continuous_toFun :=
        (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
      continuous_invFun :=
        (continuous_subtype_val.subtype_mk _).subtype_mk _ }
  have he : ∀ a : ↑(A : Set X),
      e (i a) = regularNeighborhoodInclusion C A a := by
    intro a
    rfl
  let sdr := regularNeighborhoodStrongDeformationRetract C A
  let transported : Hatcher.StrongDeformationRetract i :=
    { retract :=
        ⟨fun x ↦ sdr.retract (e x),
          sdr.retract.continuous.comp e.continuous⟩
      retract_inclusion := by
        apply ContinuousMap.ext
        intro a
        change sdr.retract (e (i a)) = a
        rw [he]
        have h := DFunLike.congr_fun sdr.retract_inclusion a
        change sdr.retract (regularNeighborhoodInclusion C A a) = a at h
        exact h
      deformation :=
        { toFun := fun p ↦ e.symm (sdr.deformation (p.1, e p.2))
          continuous_toFun := e.symm.continuous.comp
            (sdr.deformation.continuous.comp
              (continuous_fst.prodMk (e.continuous.comp continuous_snd)))
          map_zero_left := by
            intro x
            change e.symm (sdr.deformation (0, e x)) = x
            rw [sdr.deformation.apply_zero]
            exact e.symm_apply_apply x
          map_one_left := by
            intro x
            change e.symm (sdr.deformation (1, e x)) =
              i (sdr.retract (e x))
            rw [sdr.deformation.apply_one]
            simp only [ContinuousMap.comp_apply]
            apply e.injective
            rw [e.apply_symm_apply]
            exact (he (sdr.retract (e x))).symm
          prop' := by
            intro t x hx
            rcases hx with ⟨a, rfl⟩
            change e.symm (sdr.deformation (t, e (i a))) = i a
            apply e.injective
            rw [e.apply_symm_apply, he]
            exact sdr.deformation.eq_fst t ⟨a, rfl⟩ } }
  change Nonempty (Hatcher.Relative.GoodPairData P)
  refine ⟨{ nonempty := hA.coe_sort
            isClosed_range := ?_
            V := V
            range_subset_interior := hinterior
            strongDeformationRetract := transported }⟩
  rw [hrange]
  exact A.closed.preimage continuous_subtype_val

end Hatcher.ClassicalCW
