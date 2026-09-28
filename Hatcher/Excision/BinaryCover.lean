/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Joël Riou, Jack McCarthy

This file adapts the binary-cover excision argument from `joelriou/excision`
at commit `8b56cd0c8e5f39a7c2f36418c80b298e469596a6` to the Mathlib version pinned
by this project.
-/

import Hatcher.Singular.Relative
import Hatcher.Excision.Devissage
import Hatcher.Excision.SmallChainEquivalence

/-!
# Binary-cover excision on relative singular chains

For subsets whose interiors cover a space, the canonical inclusion of pairs
`(B, A ∩ B) → (X, A)` induces a chain-homotopy equivalence on relative
singular chains.
-/

noncomputable section

open AlgebraicTopology CategoryTheory Limits HomologicalComplex Simplicial
  Opposite Topology

namespace Hatcher.Excision

universe w v u

variable {X : TopCat.{w}} (A B : Set X)

/-- The interiors of `A` and `B` cover the ambient space. -/
structure CoverCondition : Prop where
  union_interior : interior A ∪ interior B = Set.univ

namespace CoverCondition

variable {A B}

private lemma smallSimplicesCondition (h : CoverCondition A B) :
    SmallSimplicesCondition (Bool.rec A B) where
  iUnion_interior := by
    rw [← h.union_interior]
    aesop

end CoverCondition

variable {A B}

/-- The canonical inclusion of topological pairs `(B, A ∩ B) → (X, A)`.
The map does not depend on the proof that the interiors cover `X`. -/
def coverPairHom (_ : CoverCondition A B) :
    TopPair.of
        (TopCat.ofHom
          (ContinuousMap.inclusion (Set.inter_subset_right : A ∩ B ⊆ B)))
        (IsEmbedding.inclusion (Set.inter_subset_right : A ∩ B ⊆ B)) ⟶
      TopPair.ofSubset A :=
  TopPair.ofHom
    (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)
    (TopCat.ofHom
      (ContinuousMap.inclusion (Set.inter_subset_left : A ∩ B ⊆ A)))
    rfl

private lemma mono_toSSetMap_of_injective {Y Z : TopCat.{w}}
    (f : Y ⟶ Z) (hf : Function.Injective f) :
    Mono (TopCat.toSSet.map f) := by
  rw [NatTrans.mono_iff_mono_app]
  intro ⟨⟨n⟩⟩
  rw [CategoryTheory.mono_iff_injective]
  intro x y hxy
  apply (TopCat.toSSetObjEquiv _ _).injective
  ext t
  exact hf
    (DFunLike.congr_fun
      ((TopCat.toSSetObjEquiv Z (op ⦋n⦌)).congr_arg hxy) t)

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasCoproducts.{w} C]

/-- **Hatcher, Theorem 2.20 (binary-cover chain-level form).** The canonical
relative-chain map induced by `(B, A ∩ B) → (X, A)` is a chain-homotopy
equivalence whenever the interiors of `A` and `B` cover `X`. -/
theorem coverChainMap_homotopyEquivalence
    (h : CoverCondition A B) (R : C) :
    HomologicalComplex.homotopyEquivalences _ _
      ((Hatcher.Relative.chainComplexFunctor R).map (coverPairHom h)) := by
  change HomologicalComplex.homotopyEquivalences _ _
    (SSetPair.chainComplexMap
      (Hatcher.Relative.singularPairFunctor.map (coverPairHom h)) R)
  rw [relativeChainMap_homotopyEquivalence_iff
    (Z := smallSubcomplex (Bool.rec A B))]
  · exact smallChainInclusion_homotopyEquivalences
      (CoverCondition.smallSimplicesCondition h) R
  · exact smallSubcomplex_bool _
  · apply mono_toSSetMap_of_injective
    intro x y hxy
    exact Subtype.ext_iff.2 hxy
  · exact smallSubcomplexOfSet_inter A B

/-- **Hatcher, Theorem 2.20 (binary-cover homology form).** The canonical map
on relative homology induced by `(B, A ∩ B) → (X, A)` is an isomorphism
whenever the interiors of `A` and `B` cover `X`. -/
instance coverHomologyMap_isIso [CategoryWithHomology C]
    (h : CoverCondition A B) (R : C) (n : ℕ) :
    IsIso ((Hatcher.Relative.homologyFunctor R n).map (coverPairHom h)) := by
  change IsIso (HomologicalComplex.homologyMap
    ((Hatcher.Relative.chainComplexFunctor R).map (coverPairHom h)) n)
  obtain ⟨e, he⟩ := coverChainMap_homotopyEquivalence h R
  rw [← he]
  exact (e.toHomologyIso n).isIso_hom

variable (A Z : Set X)

/-- The canonical inclusion of topological pairs
`(X \ Z, A \ Z) → (X, A)`. This map does not depend on a proof of the
excision hypothesis. -/
def deletedSubsetPairHom :
    TopPair.of
        (TopCat.ofHom
          (ContinuousMap.inclusion
            (Set.inter_subset_right : A \ Z ⊆ Zᶜ)))
        (IsEmbedding.inclusion
          (Set.inter_subset_right : A \ Z ⊆ Zᶜ)) ⟶
      TopPair.ofSubset A :=
  TopPair.ofHom
    (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)
    (TopCat.ofHom
      (ContinuousMap.inclusion
        (Set.inter_subset_left : A \ Z ⊆ A)))
    rfl

/-- The deleted-subset pair map is definitionally the binary-cover pair map
for the complement of the deleted subset. Here `A \ Z` is `A ∩ Zᶜ`. -/
lemma deletedSubsetPairHom_eq_coverPairHom
    (h : CoverCondition A Zᶜ) :
    deletedSubsetPairHom A Z = coverPairHom h := rfl

/-- If the closure of `Z` lies in the interior of `A`, then the interiors of
`A` and `Zᶜ` cover the ambient space. This uses
`interior (Zᶜ) = (closure Z)ᶜ`. -/
theorem deletedSubsetCoverCondition
    (h : closure Z ⊆ interior A) :
    CoverCondition A Zᶜ where
  union_interior := by
    ext x
    simp only [Set.mem_union, Set.mem_univ, iff_true, interior_compl,
      Set.mem_compl_iff]
    by_cases hx : x ∈ interior A
    · exact Or.inl hx
    · exact Or.inr (fun hxZ ↦ hx (h hxZ))

/-- **Hatcher, Theorem 2.20 (deleted-subset homology form).** If the closure
of `Z` lies in the interior of `A`, then the canonical inclusion
`(X \ Z, A \ Z) → (X, A)` induces an isomorphism on relative homology. -/
theorem deletedSubsetHomologyMap_isIso_of_closure_subset_interior
    [CategoryWithHomology C] (h : closure Z ⊆ interior A)
    (R : C) (n : ℕ) :
    IsIso ((Hatcher.Relative.homologyFunctor R n).map
      (deletedSubsetPairHom A Z)) := by
  rw [deletedSubsetPairHom_eq_coverPairHom A Z
    (deletedSubsetCoverCondition A Z h)]
  infer_instance

/-- The `IsIso` instance for deleted-subset excision. The excision hypothesis
is packaged as a `Fact` because the canonical map itself is proof-independent. -/
instance deletedSubsetHomologyMap_isIso [CategoryWithHomology C]
    [h : Fact (closure Z ⊆ interior A)] (R : C) (n : ℕ) :
    IsIso ((Hatcher.Relative.homologyFunctor R n).map
      (deletedSubsetPairHom A Z)) :=
  deletedSubsetHomologyMap_isIso_of_closure_subset_interior A Z h.out R n

end Hatcher.Excision
