/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Hatcher.Appendix.SubcomplexNeighborhoodCover
import Hatcher.Excision.BinaryCover
import Hatcher.Singular.Homology
import Hatcher.Singular.RelativeIsomorphism

/-!
# Excision for a union of CW subcomplexes

Compatible regular neighborhoods reduce excision for two CW subcomplexes to
binary-cover excision.  The comparison is made through the actual inclusions
of the subcomplex carriers, so the resulting isomorphism is induced by the
canonical map of pairs `(B, A ∩ B) ⟶ (C, A)`.  No nonemptiness assumption is
used; in particular the argument includes disjoint subcomplexes.
-/

noncomputable section

open AlgebraicTopology CategoryTheory Limits Set Topology

namespace Hatcher.ClassicalCW

universe u v w

variable {X : Type u} [TopologicalSpace X] [T2Space X]
variable (C : Set X) [CWComplex C]

/-- The topological pair consisting of a classical CW complex and one of its
subcomplexes, represented by the literal subcomplex carrier. -/
def subcomplexPair (A : CWComplex.Subcomplex C) : TopPair.{u} :=
  TopPair.of
    (TopCat.ofHom
      (ContinuousMap.inclusion A.subset_complex))
    (IsEmbedding.inclusion A.subset_complex)

/-- The source pair `(B, A ∩ B)` in CW-subcomplex excision. -/
def subcomplexExcisionSourcePair
    (A B : CWComplex.Subcomplex C) : TopPair.{u} :=
  TopPair.of
    (TopCat.ofHom
      (ContinuousMap.inclusion
        (show (Subcomplex.inter A B : Set X) ⊆ (B : Set X) by
          intro x hx
          exact hx.2)))
    (IsEmbedding.inclusion
      (show (Subcomplex.inter A B : Set X) ⊆ (B : Set X) by
        intro x hx
        exact hx.2))

/-- The canonical inclusion of pairs `(B, A ∩ B) ⟶ (C, A)` for two
subcomplexes of a classical CW complex. -/
def subcomplexExcisionPairHom
    (A B : CWComplex.Subcomplex C) :
    subcomplexExcisionSourcePair C A B ⟶ subcomplexPair C A :=
  TopPair.ofHom
    (TopCat.ofHom (ContinuousMap.inclusion B.subset_complex))
    (TopCat.ofHom
      (ContinuousMap.inclusion
        (show (Subcomplex.inter A B : Set X) ⊆ (A : Set X) by
          intro x hx
          exact hx.1)))
    (by ext x; rfl)

private abbrev leftNeighborhood (A : CWComplex.Subcomplex C) : Set X :=
  regularNeighborhood C A

private abbrev neighborhoodInComplex (A : CWComplex.Subcomplex C) : Set ↑C :=
  ((↑) : ↑C → X) ⁻¹' regularNeighborhood C A

/-- The literal-neighborhood source pair
`(N(B), N(A) ∩ N(B))`. -/
private def neighborhoodSourcePair
    (A B : CWComplex.Subcomplex C) : TopPair.{u} :=
  TopPair.of
    (TopCat.ofHom
      (ContinuousMap.inclusion
        (Set.inter_subset_right :
          leftNeighborhood C A ∩ leftNeighborhood C B ⊆
            leftNeighborhood C B)))
    (IsEmbedding.inclusion
      (Set.inter_subset_right :
        leftNeighborhood C A ∩ leftNeighborhood C B ⊆
          leftNeighborhood C B))

/-- The literal-neighborhood target pair `(C, N(A))`. -/
private def neighborhoodTargetPair
    (A : CWComplex.Subcomplex C) : TopPair.{u} :=
  TopPair.of
    (TopCat.ofHom
      (ContinuousMap.inclusion
        (regularNeighborhood_subset_complex C A)))
    (IsEmbedding.inclusion
      (regularNeighborhood_subset_complex C A))

/-- Include `(B, A ∩ B)` into
`(N(B), N(A) ∩ N(B))`. -/
private def subcomplexToNeighborhoodSourceHom
    (A B : CWComplex.Subcomplex C) :
    subcomplexExcisionSourcePair C A B ⟶ neighborhoodSourcePair C A B :=
  TopPair.ofHom
    (TopCat.ofHom (regularNeighborhoodInclusion C B))
    (TopCat.ofHom
      (regularNeighborhoodIntersectionInclusion C A B))
    (by ext x; rfl)

/-- Enlarge the subspace in `(C,A)` to its regular neighborhood. -/
private def subcomplexToNeighborhoodTargetHom
    (A : CWComplex.Subcomplex C) :
    subcomplexPair C A ⟶ neighborhoodTargetPair C A :=
  TopPair.ofHom
    (𝟙 (TopCat.of ↑C))
    (TopCat.ofHom (regularNeighborhoodInclusion C A))
    (by ext x; rfl)

/-- A subset of the ambient model which lies in `C` is homeomorphic to its
relative-subtype presentation inside `C`. -/
private def subtypeHomeomorphRelative
    (S : Set X) (hS : S ⊆ C) :
    ↑S ≃ₜ ↑(((↑) : ↑C → X) ⁻¹' S) where
  toFun x := ⟨⟨x.1, hS x.2⟩, x.2⟩
  invFun x := ⟨x.1.1, x.2⟩
  left_inv x := by ext; rfl
  right_inv x := by ext; rfl
  continuous_toFun :=
    (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

private abbrev excisionNeighborhoodSourcePair
    (A B : CWComplex.Subcomplex C) : TopPair.{u} :=
  TopPair.of
    (TopCat.ofHom
      (ContinuousMap.inclusion
        (Set.inter_subset_right :
          neighborhoodInComplex C A ∩ neighborhoodInComplex C B ⊆
            neighborhoodInComplex C B)))
    (IsEmbedding.inclusion
      (Set.inter_subset_right :
        neighborhoodInComplex C A ∩ neighborhoodInComplex C B ⊆
          neighborhoodInComplex C B))

private abbrev excisionNeighborhoodTargetPair
    (A : CWComplex.Subcomplex C) : TopPair.{u} :=
  TopPair.ofSubset (X := TopCat.of ↑C) (neighborhoodInComplex C A)

/-- The direct and relative-subtype presentations of the neighborhood source
pair are canonically isomorphic. -/
private noncomputable def neighborhoodSourceIso
    (A B : CWComplex.Subcomplex C) :
    neighborhoodSourcePair C A B ≅
      excisionNeighborhoodSourcePair C A B :=
  MorphismProperty.Arrow.isoMk
    (TopCat.isoOfHomeo
      (subtypeHomeomorphRelative C
        (leftNeighborhood C A ∩ leftNeighborhood C B)
        (fun _ hx ↦ regularNeighborhood_subset_complex C A hx.1)))
    (TopCat.isoOfHomeo
      (subtypeHomeomorphRelative C (leftNeighborhood C B)
        (regularNeighborhood_subset_complex C B)))
    (by ext x; rfl)

/-- The direct and relative-subtype presentations of the neighborhood target
pair are canonically isomorphic. -/
private noncomputable def neighborhoodTargetIso
    (A : CWComplex.Subcomplex C) :
    neighborhoodTargetPair C A ≅ excisionNeighborhoodTargetPair C A :=
  MorphismProperty.Arrow.isoMk
    (TopCat.isoOfHomeo
      (subtypeHomeomorphRelative C (leftNeighborhood C A)
        (regularNeighborhood_subset_complex C A)))
    (Iso.refl _)
    (by ext x; rfl)

/-- Compatible regular neighborhoods form the binary interior cover consumed
by excision. -/
private theorem neighborhoodCoverCondition
    (A B : CWComplex.Subcomplex C)
    (h : SubcomplexNeighborhoodCover C A B) :
    Hatcher.Excision.CoverCondition (X := TopCat.of ↑C)
      (neighborhoodInComplex C A) (neighborhoodInComplex C B) where
  union_interior := by
    rw [h.isOpen_leftNeighborhood.interior_eq,
      h.isOpen_rightNeighborhood.interior_eq]
    apply Set.eq_univ_of_forall
    intro x
    have hx : x.1 ∈
        regularNeighborhood C A ∪ regularNeighborhood C B := by
      rw [h.neighborhood_union_eq]
      exact x.2
    exact hx

/-- Binary-cover excision, conjugated back to the literal regular-neighborhood
pair presentations. -/
private noncomputable def neighborhoodExcisionPairHom
    (A B : CWComplex.Subcomplex C)
    (h : SubcomplexNeighborhoodCover C A B) :
    neighborhoodSourcePair C A B ⟶ neighborhoodTargetPair C A :=
  (neighborhoodSourceIso C A B).hom ≫
    Hatcher.Excision.coverPairHom (neighborhoodCoverCondition C A B h) ≫
    (neighborhoodTargetIso C A).inv

/-- The neighborhood comparison is the actual canonical pair map after both
ends are included in their regular neighborhoods. -/
private theorem subcomplexExcisionPairHom_factorization
    (A B : CWComplex.Subcomplex C)
    (h : SubcomplexNeighborhoodCover C A B) :
    subcomplexToNeighborhoodSourceHom C A B ≫
        neighborhoodExcisionPairHom C A B h =
      subcomplexExcisionPairHom C A B ≫
        subcomplexToNeighborhoodTargetHom C A := by
  apply MorphismProperty.Arrow.Hom.ext
  · ext x
    apply Subtype.ext
    rfl
  · ext x
    apply Subtype.ext
    rfl

private theorem subcomplexToNeighborhoodSourceHom_homologyMap_isIso
    (A B : CWComplex.Subcomplex C)
    (h : SubcomplexNeighborhoodCover C A B)
    {𝒜 : Type w} [Category.{v} 𝒜] [HasCoproducts.{u} 𝒜]
    [Abelian 𝒜] (R : 𝒜) (n : ℕ) :
    IsIso ((Hatcher.Relative.homologyFunctor R n).map
      (subcomplexToNeighborhoodSourceHom C A B)) := by
  apply Hatcher.Relative.homologyMap_isIso_of_components
  · intro k
    change IsIso (((singularHomologyFunctor 𝒜 k).obj R).map
      (TopCat.ofHom (regularNeighborhoodIntersectionInclusion C A B)))
    exact (Hatcher.Singular.homologyIsoOfHomotopyEquiv
      h.intersectionRetract.some.toHomotopyEquiv.symm R k).isIso_hom
  · intro k
    change IsIso (((singularHomologyFunctor 𝒜 k).obj R).map
      (TopCat.ofHom (regularNeighborhoodInclusion C B)))
    exact (Hatcher.Singular.homologyIsoOfHomotopyEquiv
      h.rightRetract.some.toHomotopyEquiv.symm R k).isIso_hom

private theorem subcomplexToNeighborhoodTargetHom_homologyMap_isIso
    (A B : CWComplex.Subcomplex C)
    (h : SubcomplexNeighborhoodCover C A B)
    {𝒜 : Type w} [Category.{v} 𝒜] [HasCoproducts.{u} 𝒜]
    [Abelian 𝒜] (R : 𝒜) (n : ℕ) :
    IsIso ((Hatcher.Relative.homologyFunctor R n).map
      (subcomplexToNeighborhoodTargetHom C A)) := by
  apply Hatcher.Relative.homologyMap_isIso_of_components
  · intro k
    change IsIso (((singularHomologyFunctor 𝒜 k).obj R).map
      (TopCat.ofHom (regularNeighborhoodInclusion C A)))
    exact (Hatcher.Singular.homologyIsoOfHomotopyEquiv
      h.leftRetract.some.toHomotopyEquiv.symm R k).isIso_hom
  · intro k
    change IsIso (((singularHomologyFunctor 𝒜 k).obj R).map
      (𝟙 (TopCat.of ↑C)))
    infer_instance

private theorem neighborhoodExcisionPairHom_homologyMap_isIso
    (A B : CWComplex.Subcomplex C)
    (h : SubcomplexNeighborhoodCover C A B)
    {𝒜 : Type w} [Category.{v} 𝒜] [HasCoproducts.{u} 𝒜]
    [Abelian 𝒜] (R : 𝒜) (n : ℕ) :
    IsIso ((Hatcher.Relative.homologyFunctor R n).map
      (neighborhoodExcisionPairHom C A B h)) := by
  rw [neighborhoodExcisionPairHom, Functor.map_comp, Functor.map_comp]
  apply IsIso.comp_isIso'
  · exact ((Hatcher.Relative.homologyFunctor R n).mapIso
      (neighborhoodSourceIso C A B)).isIso_hom
  · apply IsIso.comp_isIso'
    · exact Hatcher.Excision.coverHomologyMap_isIso
        (neighborhoodCoverCondition C A B h) R n
    · exact ((Hatcher.Relative.homologyFunctor R n).mapIso
        (neighborhoodTargetIso C A).symm).isIso_hom

/-- **Hatcher, Corollary 2.24 (page 126).** If a classical CW complex is
the union of subcomplexes `A` and `B`, then the canonical inclusion
`(B, A ∩ B) ⟶ (C, A)` induces an isomorphism on relative singular
homology in every degree.  The statement includes `A ∩ B = ∅`. -/
theorem subcomplexExcision_homologyMap_isIso
    (A B : CWComplex.Subcomplex C)
    (hcover : (A : Set X) ∪ (B : Set X) = C)
    {𝒜 : Type w} [Category.{v} 𝒜] [HasCoproducts.{u} 𝒜]
    [Abelian 𝒜] (R : 𝒜) (n : ℕ) :
    IsIso ((Hatcher.Relative.homologyFunctor R n).map
      (subcomplexExcisionPairHom C A B)) := by
  let h := subcomplexNeighborhoodCover C A B hcover
  have hsource : IsIso ((Hatcher.Relative.homologyFunctor R n).map
      (subcomplexToNeighborhoodSourceHom C A B)) :=
    subcomplexToNeighborhoodSourceHom_homologyMap_isIso C A B h R n
  have hexcision : IsIso ((Hatcher.Relative.homologyFunctor R n).map
      (neighborhoodExcisionPairHom C A B h)) :=
    neighborhoodExcisionPairHom_homologyMap_isIso C A B h R n
  have htarget : IsIso ((Hatcher.Relative.homologyFunctor R n).map
      (subcomplexToNeighborhoodTargetHom C A)) :=
    subcomplexToNeighborhoodTargetHom_homologyMap_isIso C A B h R n
  have hneighborhood : IsIso
      (((Hatcher.Relative.homologyFunctor R n).map
          (subcomplexToNeighborhoodSourceHom C A B)) ≫
        (Hatcher.Relative.homologyFunctor R n).map
          (neighborhoodExcisionPairHom C A B h)) :=
    IsIso.comp_isIso' hsource hexcision
  have hfactorization :
      (Hatcher.Relative.homologyFunctor R n).map
          (subcomplexExcisionPairHom C A B) ≫
        (Hatcher.Relative.homologyFunctor R n).map
          (subcomplexToNeighborhoodTargetHom C A) =
      (Hatcher.Relative.homologyFunctor R n).map
          (subcomplexToNeighborhoodSourceHom C A B) ≫
        (Hatcher.Relative.homologyFunctor R n).map
          (neighborhoodExcisionPairHom C A B h) := by
    rw [← Functor.map_comp,
      ← subcomplexExcisionPairHom_factorization C A B h,
      Functor.map_comp]
  exact @IsIso.of_isIso_fac_right 𝒜 _ _ _ _
    ((Hatcher.Relative.homologyFunctor R n).map
      (subcomplexToNeighborhoodTargetHom C A))
    ((Hatcher.Relative.homologyFunctor R n).map
      (subcomplexExcisionPairHom C A B))
    ((Hatcher.Relative.homologyFunctor R n).map
        (subcomplexToNeighborhoodSourceHom C A B) ≫
      (Hatcher.Relative.homologyFunctor R n).map
        (neighborhoodExcisionPairHom C A B h))
    htarget hneighborhood hfactorization

end Hatcher.ClassicalCW
