/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Hatcher.Singular.LocalHomology

/-!
# Deleted pairs and open neighborhoods

The relative homology of `(X, X \ F)` can be computed inside any open
neighborhood of a closed set `F`.  The canonical map is factored through the
actual source of binary-cover excision.  For a singleton deletion, a canonical
source-pair isomorphism recovers the established local-homology map.
-/

noncomputable section

open AlgebraicTopology CategoryTheory Limits Set Topology

namespace Hatcher.Relative

universe w v u

/-- The topological pair `(X, X \ F)`. -/
def deletedPair (X : TopCat.{w}) (F : Set X) : TopPair.{w} :=
  TopPair.ofSubset Fᶜ

/-- The pair inside `W` obtained by deleting the preimage of `F`. -/
def deletedPairWithin {X : TopCat.{w}} (F W : Set X) : TopPair.{w} :=
  TopPair.ofSubset (X := TopCat.of W)
    ((fun z : W ↦ (z : X)) ⁻¹' Fᶜ : Set W)

private def deletedPairWithinSubspaceInclusion
    {X : TopCat.{w}} (F W : Set X) :
    C((deletedPairWithin F W).snd, (deletedPair X F).snd) where
  toFun z := ⟨z.1.1, z.2⟩
  continuous_toFun :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

/-- The canonical inclusion from the deleted pair inside `W` to the deleted
pair in the ambient space. -/
def deletedPairOpenNeighborhoodPairHom
    {X : TopCat.{w}} (F W : Set X) :
    deletedPairWithin F W ⟶ deletedPair X F :=
  TopPair.ofHom
    (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)
    (TopCat.ofHom (deletedPairWithinSubspaceInclusion F W))
    (by ext z; rfl)

@[simp]
theorem deletedPairOpenNeighborhoodPairHom_fst_apply
    {X : TopCat.{w}} (F W : Set X) (z : W) :
    TopPair.Hom.fst (deletedPairOpenNeighborhoodPairHom F W) z = z.1 :=
  rfl

@[simp]
theorem deletedPairOpenNeighborhoodPairHom_snd_apply_coe
    {X : TopCat.{w}} (F W : Set X) (z : (deletedPairWithin F W).snd) :
    (TopPair.Hom.snd (deletedPairOpenNeighborhoodPairHom F W) z).1 =
      z.1.1 := by
  rfl

/-- The map on relative homology induced by including the deleted pair inside
`W` into the ambient deleted pair. -/
noncomputable def deletedPairOpenNeighborhoodMap
    {X : TopCat.{w}} (F W : Set X)
    {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    [CategoryWithHomology C] (R : C) (n : ℕ) :
    (homologyFunctor R n).obj (deletedPairWithin F W) ⟶
      (homologyFunctor R n).obj (deletedPair X F) :=
  (homologyFunctor R n).map (deletedPairOpenNeighborhoodPairHom F W)

private noncomputable def deletedPairWithinSubspaceHomeomorph
    {X : TopCat.{w}} (F W : Set X) :
    (deletedPairWithin F W).snd ≃ₜ (Fᶜ ∩ W : Set X) :=
  { toEquiv :=
      { toFun := fun z ↦ ⟨z.1.1, z.2, z.1.2⟩
        invFun := fun z ↦ ⟨⟨z.1, z.2.2⟩, z.2.1⟩
        left_inv := by
          intro z
          apply Subtype.ext
          rfl
        right_inv := by
          intro z
          apply Subtype.ext
          rfl }
    continuous_toFun :=
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
    continuous_invFun :=
      (continuous_subtype_val.subtype_mk _).subtype_mk _ }

/-- The binary-cover source pair `(W, Fᶜ ∩ W)`. -/
abbrev deletedPairWithinCoverPair
    {X : TopCat.{w}} (F W : Set X) : TopPair.{w} :=
  TopPair.of
    (TopCat.ofHom
      (ContinuousMap.inclusion
        (Set.inter_subset_right : Fᶜ ∩ W ⊆ W)))
    (IsEmbedding.inclusion
      (Set.inter_subset_right : Fᶜ ∩ W ⊆ W))

/-- The deleted pair inside `W` is canonically isomorphic to the source pair
used by binary-cover excision. -/
noncomputable def deletedPairWithinCoverIso
    {X : TopCat.{w}} (F W : Set X) :
    deletedPairWithin F W ≅ deletedPairWithinCoverPair F W :=
  MorphismProperty.Arrow.isoMk
    (TopCat.isoOfHomeo (deletedPairWithinSubspaceHomeomorph F W))
    (Iso.refl (TopCat.of W))
    (by ext z; rfl)

/-- If `F` is closed, lies in the open set `W`, then `Fᶜ` and `W` form an
interior cover of the ambient space. -/
theorem deletedPairCoverCondition
    {X : TopCat.{w}} (F W : Set X) (hF : IsClosed F) (hW : IsOpen W)
    (hFW : F ⊆ W) : Hatcher.Excision.CoverCondition Fᶜ W where
  union_interior := by
    rw [hF.isOpen_compl.interior_eq, hW.interior_eq]
    ext z
    simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_univ, iff_true]
    by_cases hz : z ∈ F
    · exact Or.inr (hFW hz)
    · exact Or.inl hz

/-- The cover-source isomorphism followed by binary-cover inclusion is the
canonical deleted-pair neighborhood map. -/
@[reassoc]
theorem deletedPairWithinCoverIso_hom_comp
    {X : TopCat.{w}} (F W : Set X) (hF : IsClosed F) (hW : IsOpen W)
    (hFW : F ⊆ W) :
    (deletedPairWithinCoverIso F W).hom ≫
        Hatcher.Excision.coverPairHom
          (deletedPairCoverCondition F W hF hW hFW) =
      deletedPairOpenNeighborhoodPairHom F W := by
  apply MorphismProperty.Arrow.Hom.ext
  · ext z
    apply Subtype.ext
    rfl
  · ext z
    rfl

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasCoproducts.{w} C] [CategoryWithHomology C]

/-- If `F` is closed and contained in an open set `W`, inclusion of the
deleted pair inside `W` induces an isomorphism on relative homology. -/
theorem deletedPairOpenNeighborhoodMap_isIso
    {X : TopCat.{w}} (F W : Set X) (hF : IsClosed F) (hW : IsOpen W)
    (hFW : F ⊆ W) (R : C) (n : ℕ) :
    IsIso (deletedPairOpenNeighborhoodMap F W R n) := by
  change IsIso ((homologyFunctor R n).map
    (deletedPairOpenNeighborhoodPairHom F W))
  rw [← deletedPairWithinCoverIso_hom_comp F W hF hW hFW]
  change IsIso ((homologyFunctor R n).map
    ((deletedPairWithinCoverIso F W).hom ≫
      Hatcher.Excision.coverPairHom
        (deletedPairCoverCondition F W hF hW hFW)))
  rw [Functor.map_comp]
  apply IsIso.comp_isIso'
  · exact ((homologyFunctor R n).mapIso
      (deletedPairWithinCoverIso F W)).isIso_hom
  · exact Hatcher.Excision.coverHomologyMap_isIso
      (deletedPairCoverCondition F W hF hW hFW) R n

/-- In a `T1Space`, the deleted-pair comparison is an isomorphism for every
finite deleted set contained in an open neighborhood. -/
theorem deletedPairOpenNeighborhoodMap_isIso_of_finite
    {X : TopCat.{w}} [T1Space X] (F W : Set X) (hF : F.Finite)
    (hW : IsOpen W) (hFW : F ⊆ W) (R : C) (n : ℕ) :
    IsIso (deletedPairOpenNeighborhoodMap F W R n) :=
  deletedPairOpenNeighborhoodMap_isIso F W hF.isClosed hW hFW R n

private noncomputable def puncturedPairToDeletedPairWithinHomeomorph
    {X : TopCat.{w}} (x : X) (W : Set X) (hx : x ∈ W) :
    (puncturedPair (TopCat.of W) ⟨x, hx⟩).snd ≃ₜ
      (deletedPairWithin ({x} : Set X) W).snd :=
  { toEquiv :=
      { toFun := fun z ↦ ⟨z.1, by
          simp only [Set.mem_preimage, Set.mem_compl_iff,
            Set.mem_singleton_iff]
          intro hzx
          have hz : z.1 ≠ (⟨x, hx⟩ : W) := by
            simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using z.2
          exact hz (Subtype.ext hzx)⟩
        invFun := fun z ↦ ⟨z.1, by
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
          intro hzx
          have hval := congrArg Subtype.val hzx
          exact z.2 hval⟩
        left_inv := by
          intro z
          apply Subtype.ext
          rfl
        right_inv := by
          intro z
          apply Subtype.ext
          rfl }
    continuous_toFun := continuous_subtype_val.subtype_mk _
    continuous_invFun := continuous_subtype_val.subtype_mk _ }

/-- The canonical source-pair isomorphism from the punctured pair of `W` to
the deleted pair within `W` for a singleton deletion. -/
noncomputable def puncturedPairIsoDeletedPairWithinSingleton
    {X : TopCat.{w}} (x : X) (W : Set X) (hx : x ∈ W) :
    puncturedPair (TopCat.of W) ⟨x, hx⟩ ≅
      deletedPairWithin ({x} : Set X) W :=
  MorphismProperty.Arrow.isoMk
    (TopCat.isoOfHomeo
      (puncturedPairToDeletedPairWithinHomeomorph x W hx))
    (Iso.refl (TopCat.of W))
    (by ext z; rfl)

/-- The singleton source isomorphism followed by the deleted-pair map is the
completed punctured-neighborhood pair map. -/
@[reassoc]
theorem puncturedPairIsoDeletedPairWithinSingleton_hom_comp
    {X : TopCat.{w}} (x : X) (W : Set X) (hx : x ∈ W) :
    (puncturedPairIsoDeletedPairWithinSingleton x W hx).hom ≫
        deletedPairOpenNeighborhoodPairHom ({x} : Set X) W =
      localHomologyOpenNeighborhoodPairHom x W hx := by
  apply MorphismProperty.Arrow.Hom.ext
  · ext z
    apply Subtype.ext
    change z.1.1 = z.1.1
    rfl
  · ext z
    change z.1 = z.1
    rfl

/-- The homology isomorphism induced by the singleton source-pair
isomorphism. -/
noncomputable def puncturedPairHomologyIsoDeletedPairWithinSingleton
    {X : TopCat.{w}} (x : X) (W : Set X) (hx : x ∈ W)
    (R : C) (n : ℕ) :
    (homologyFunctor R n).obj
        (puncturedPair (TopCat.of W) ⟨x, hx⟩) ≅
      (homologyFunctor R n).obj
        (deletedPairWithin ({x} : Set X) W) :=
  (homologyFunctor R n).mapIso
    (puncturedPairIsoDeletedPairWithinSingleton x W hx)

/-- At homology level, the singleton source isomorphism followed by the
deleted-pair neighborhood map is the completed local-homology comparison. -/
@[reassoc]
theorem puncturedPairHomologyIsoDeletedPairWithinSingleton_hom_comp
    {X : TopCat.{w}} (x : X) (W : Set X) (hx : x ∈ W)
    (R : C) (n : ℕ) :
    (puncturedPairHomologyIsoDeletedPairWithinSingleton x W hx R n).hom ≫
        deletedPairOpenNeighborhoodMap ({x} : Set X) W R n =
      localHomologyOpenNeighborhoodMap x W hx R n := by
  change (homologyFunctor R n).map
      (puncturedPairIsoDeletedPairWithinSingleton x W hx).hom ≫
        (homologyFunctor R n).map
          (deletedPairOpenNeighborhoodPairHom ({x} : Set X) W) =
      (homologyFunctor R n).map
        (localHomologyOpenNeighborhoodPairHom x W hx)
  rw [← Functor.map_comp,
    puncturedPairIsoDeletedPairWithinSingleton_hom_comp]
  rfl

end Hatcher.Relative
