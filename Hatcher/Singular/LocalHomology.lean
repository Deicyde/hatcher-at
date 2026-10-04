/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Hatcher.Excision.BinaryCover

/-!
# Local homology

This file defines the punctured pair `(X, X \ {x})` and proves that its
relative homology can be computed in any open neighborhood of `x`.  It also
packages the pair and homology isomorphisms induced by a homeomorphism that
carries one distinguished point to another.
-/

noncomputable section

open AlgebraicTopology CategoryTheory Limits Set Topology

namespace Hatcher.Relative

universe w v u

/-- The punctured topological pair `(X, X \ {x})`. -/
def puncturedPair (X : TopCat.{w}) (x : X) : TopPair.{w} :=
  TopPair.ofSubset ({x}ᶜ : Set X)

private def puncturedNeighborhoodInclusion
    {X : TopCat.{w}} (x : X) (U : Set X) (hx : x ∈ U) :
    C(({⟨x, hx⟩}ᶜ : Set U), ({x}ᶜ : Set X)) where
  toFun z := ⟨z.1.1, by
    have hz : z.1 ≠ (⟨x, hx⟩ : U) := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using z.2
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using
      (fun h : z.1.1 = x ↦ hz (Subtype.ext h))⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp continuous_subtype_val

/-- The canonical map from the punctured pair of a neighborhood `U` of `x`
to the punctured pair of the ambient space. -/
def localHomologyOpenNeighborhoodPairHom
    {X : TopCat.{w}} (x : X) (U : Set X) (hx : x ∈ U) :
    puncturedPair (TopCat.of U) ⟨x, hx⟩ ⟶ puncturedPair X x :=
  TopPair.ofHom
    (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)
    (TopCat.ofHom (puncturedNeighborhoodInclusion x U hx))
    (by ext z; rfl)

@[simp]
lemma localHomologyOpenNeighborhoodPairHom_fst_apply
    {X : TopCat.{w}} (x : X) (U : Set X) (hx : x ∈ U) (z : U) :
    TopPair.Hom.fst (localHomologyOpenNeighborhoodPairHom x U hx) z = z.1 :=
  rfl

/-- The map on local homology induced by including an open neighborhood in
the ambient space. -/
noncomputable def localHomologyOpenNeighborhoodMap
    {X : TopCat.{w}} (x : X) (U : Set X) (hx : x ∈ U)
    {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    [CategoryWithHomology C] (R : C) (n : ℕ) :
    (homologyFunctor R n).obj
        (puncturedPair (TopCat.of U) ⟨x, hx⟩) ⟶
      (homologyFunctor R n).obj (puncturedPair X x) :=
  (homologyFunctor R n).map (localHomologyOpenNeighborhoodPairHom x U hx)

private noncomputable def localPunctureHomeomorph
    {X : TopCat.{w}} (x : X) (U : Set X) (hx : x ∈ U) :
    (({⟨x, hx⟩}ᶜ : Set U)) ≃ₜ (({x}ᶜ ∩ U : Set X)) := by
  let f : (({⟨x, hx⟩}ᶜ : Set U)) → (({x}ᶜ ∩ U : Set X)) :=
    fun z ↦ ⟨z.1.1, by
      constructor
      · have hz : z.1 ≠ (⟨x, hx⟩ : U) := by
          simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using z.2
        simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using
          (fun h : z.1.1 = x ↦ hz (Subtype.ext h))
      · exact z.1.2⟩
  let g : (({x}ᶜ ∩ U : Set X)) → (({⟨x, hx⟩}ᶜ : Set U)) :=
    fun z ↦ ⟨⟨z.1, z.2.2⟩, by
      have hz : z.1 ≠ x := by
        simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using z.2.1
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using
        (fun h : (⟨z.1, z.2.2⟩ : U) = ⟨x, hx⟩ ↦
          hz (congrArg Subtype.val h))⟩
  exact
    { toEquiv :=
        { toFun := f
          invFun := g
          left_inv := by
            intro z
            apply Subtype.ext
            rfl
          right_inv := by
            intro z
            apply Subtype.ext
            rfl }
      continuous_toFun := by
        dsimp [f]
        exact (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := by
        dsimp [g]
        exact (continuous_subtype_val.subtype_mk _).subtype_mk _ }

private abbrev localExcisionPair
    {X : TopCat.{w}} (x : X) (U : Set X) : TopPair.{w} :=
  TopPair.of
    (TopCat.ofHom
      (ContinuousMap.inclusion
        (Set.inter_subset_right : ({x}ᶜ : Set X) ∩ U ⊆ U)))
    (IsEmbedding.inclusion
      (Set.inter_subset_right : ({x}ᶜ : Set X) ∩ U ⊆ U))

/-- The punctured pair of `U` is canonically isomorphic to the source pair
used by binary-cover excision for the cover `X \ {x}` and `U`. -/
private noncomputable def localPuncturedPairExcisionIso
    {X : TopCat.{w}} (x : X) (U : Set X) (hx : x ∈ U) :
    puncturedPair (TopCat.of U) ⟨x, hx⟩ ≅ localExcisionPair x U :=
  MorphismProperty.Arrow.isoMk
    (TopCat.isoOfHomeo (localPunctureHomeomorph x U hx))
    (Iso.refl _)
    (by ext z; rfl)

private theorem localHomologyCoverCondition
    {X : TopCat.{w}} (x : X) (U : Set X) (hx : x ∈ U)
    (hU : IsOpen U) (hclosed : IsClosed ({x} : Set X)) :
    Hatcher.Excision.CoverCondition ({x}ᶜ : Set X) U where
  union_interior := by
    rw [hclosed.isOpen_compl.interior_eq, hU.interior_eq]
    ext z
    simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_singleton_iff,
      Set.mem_univ, iff_true]
    by_cases hz : z = x
    · exact Or.inr (hz.symm ▸ hx)
    · exact Or.inl hz

private lemma localPuncturedPairExcisionIso_hom_comp
    {X : TopCat.{w}} (x : X) (U : Set X) (hx : x ∈ U)
    (hU : IsOpen U) (hclosed : IsClosed ({x} : Set X)) :
    (localPuncturedPairExcisionIso x U hx).hom ≫
        Hatcher.Excision.coverPairHom
          (localHomologyCoverCondition x U hx hU hclosed) =
      localHomologyOpenNeighborhoodPairHom x U hx := by
  apply MorphismProperty.Arrow.Hom.ext
  · ext z
    rfl
  · ext z
    rfl

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasCoproducts.{w} C] [CategoryWithHomology C]

/-- **Hatcher, local homology after Theorem 2.26 (page 126).** If `U` is an
open neighborhood of `x` and `{x}` is closed, the canonical inclusion
`(U, U \ {x}) ⟶ (X, X \ {x})` induces an isomorphism on relative homology
in every degree. -/
theorem localHomologyOpenNeighborhoodMap_isIso
    {X : TopCat.{w}} (x : X) (U : Set X) (hx : x ∈ U)
    (hU : IsOpen U) (hclosed : IsClosed ({x} : Set X))
    (R : C) (n : ℕ) :
    IsIso (localHomologyOpenNeighborhoodMap x U hx R n) := by
  change IsIso ((homologyFunctor R n).map
    (localHomologyOpenNeighborhoodPairHom x U hx))
  rw [← localPuncturedPairExcisionIso_hom_comp x U hx hU hclosed]
  dsimp only [puncturedPair]
  rw [Functor.map_comp]
  apply IsIso.comp_isIso'
  · exact ((homologyFunctor R n).mapIso
      (localPuncturedPairExcisionIso x U hx)).isIso_hom
  · exact Hatcher.Excision.coverHomologyMap_isIso
      (localHomologyCoverCondition x U hx hU hclosed) R n

/-- In a `T1Space`, local homology can be computed in every open
neighborhood, since singletons are closed. -/
theorem localHomologyOpenNeighborhoodMap_isIso_of_t1
    {X : TopCat.{w}} [T1Space X] (x : X) (U : Set X) (hx : x ∈ U)
    (hU : IsOpen U) (R : C) (n : ℕ) :
    IsIso (localHomologyOpenNeighborhoodMap x U hx R n) :=
  localHomologyOpenNeighborhoodMap_isIso x U hx hU isClosed_singleton R n

/-- A homeomorphism carrying `x` to `y` induces an isomorphism of punctured
pairs. -/
noncomputable def puncturedPairIso
    {X Y : TopCat.{w}} {x : X} {y : Y}
    (e : X ≃ₜ Y) (hxy : e x = y) :
    puncturedPair X x ≅ puncturedPair Y y :=
  MorphismProperty.Arrow.isoMk
    (TopCat.isoOfHomeo (e.subtype fun z ↦ by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      rw [← hxy]
      exact e.injective.ne_iff.symm))
    (TopCat.isoOfHomeo e)
    (by ext z; rfl)

/-- The isomorphism on local homology induced by a homeomorphism carrying
`x` to `y`. -/
noncomputable def puncturedPairHomologyIso
    {X Y : TopCat.{w}} {x : X} {y : Y}
    (e : X ≃ₜ Y) (hxy : e x = y) (R : C) (n : ℕ) :
    (homologyFunctor R n).obj (puncturedPair X x) ≅
      (homologyFunctor R n).obj (puncturedPair Y y) :=
  (homologyFunctor R n).mapIso (puncturedPairIso e hxy)

end Hatcher.Relative
