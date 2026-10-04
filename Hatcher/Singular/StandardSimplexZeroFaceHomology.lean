/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Hatcher.Excision.BinaryCover
import Hatcher.Singular.GoodPairPointQuotientNaturality
import Hatcher.Singular.StandardSimplexGoodPairs
import Hatcher.Singular.StandardSimplexZeroFaceQuotient

/-!
# Relative homology of the zero face

This file proves the second comparison in Hatcher's Example 2.23.  The zero
face induces an isomorphism from the relative homology of a standard simplex
and its boundary to that of the successor boundary and its zero horn.
-/

noncomputable section

open AlgebraicTopology CategoryTheory Limits Set Topology

namespace Hatcher.Simplex

private def zeroHornInOneBoundary : Set (standardSimplexBoundary 1) :=
  {x | x.1 ∈ standardSimplexZeroHorn 0}

private def zeroFaceInOneBoundary : Set (standardSimplexBoundary 1) :=
  {x | x.1 ∈ standardSimplexZeroFaceSet 0}

private theorem zeroHornInOneBoundary_disjoint_zeroFaceInOneBoundary :
    Disjoint zeroHornInOneBoundary zeroFaceInOneBoundary := by
  rw [Set.disjoint_left]
  intro x hxHorn hxFace
  change x.1 ∈ standardSimplexZeroHorn 0 at hxHorn
  change x.1 ∈ standardSimplexZeroFaceSet 0 at hxFace
  obtain ⟨i, hi0, hi⟩ := hxHorn
  have hi1 : i = 1 := by
    fin_cases i
    · exact (hi0 rfl).elim
    · rfl
  have hweight0 : x.1.weights 0 = 0 := hxFace
  have hweight1 : x.1.weights 1 = 0 := by simpa [hi1] using hi
  have hsumZero : ∑ j : Fin 2, x.1.weights j = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    fin_cases j
    · exact hweight0
    · exact hweight1
  linarith [x.1.total_of_fintype, hsumZero]

private theorem zeroHornInOneBoundary_union_zeroFaceInOneBoundary :
    zeroHornInOneBoundary ∪ zeroFaceInOneBoundary = Set.univ := by
  ext x
  simp only [Set.mem_union, Set.mem_univ, iff_true]
  have hx := (Set.ext_iff.mp
    (standardSimplexBoundary_succ_eq_zeroFace_union_zeroHorn 0) x.1).mp x.2
  exact hx.elim Or.inr Or.inl

private theorem isClosed_zeroHornInOneBoundary :
    IsClosed zeroHornInOneBoundary :=
  (isClosed_standardSimplexZeroHorn 0).preimage continuous_subtype_val

private theorem isClosed_zeroFaceInOneBoundary :
    IsClosed zeroFaceInOneBoundary :=
  (isClosed_standardSimplexZeroFaceSet 0).preimage continuous_subtype_val

private theorem isOpen_zeroHornInOneBoundary :
    IsOpen zeroHornInOneBoundary := by
  have hcompl : zeroFaceInOneBoundaryᶜ = zeroHornInOneBoundary := by
    ext x
    constructor
    · intro hx
      have hu : x ∈ zeroHornInOneBoundary ∪ zeroFaceInOneBoundary := by
        rw [zeroHornInOneBoundary_union_zeroFaceInOneBoundary]
        trivial
      exact hu.resolve_right hx
    · intro hxHorn hxFace
      exact (Set.disjoint_left.mp
        zeroHornInOneBoundary_disjoint_zeroFaceInOneBoundary)
          hxHorn hxFace
  rw [← hcompl]
  exact isClosed_zeroFaceInOneBoundary.isOpen_compl

private theorem isOpen_zeroFaceInOneBoundary :
    IsOpen zeroFaceInOneBoundary := by
  have hcompl : zeroHornInOneBoundaryᶜ = zeroFaceInOneBoundary := by
    ext x
    constructor
    · intro hx
      have hu : x ∈ zeroHornInOneBoundary ∪ zeroFaceInOneBoundary := by
        rw [zeroHornInOneBoundary_union_zeroFaceInOneBoundary]
        trivial
      exact hu.resolve_left hx
    · intro hxFace hxHorn
      exact (Set.disjoint_left.mp
        zeroHornInOneBoundary_disjoint_zeroFaceInOneBoundary)
          hxHorn hxFace
  rw [← hcompl]
  exact isClosed_zeroHornInOneBoundary.isOpen_compl

private theorem zeroFaceCoverCondition :
    Hatcher.Excision.CoverCondition
      (X := TopCat.of (standardSimplexBoundary 1))
      zeroHornInOneBoundary zeroFaceInOneBoundary where
  union_interior := by
    rw [isOpen_zeroHornInOneBoundary.interior_eq,
      isOpen_zeroFaceInOneBoundary.interior_eq,
      zeroHornInOneBoundary_union_zeroFaceInOneBoundary]

private abbrev zeroFaceCoverPair : TopPair.{0} :=
  TopPair.of
    (TopCat.ofHom
      (ContinuousMap.inclusion
        (Set.inter_subset_right :
          zeroHornInOneBoundary ∩ zeroFaceInOneBoundary ⊆
            zeroFaceInOneBoundary)))
    (IsEmbedding.inclusion
      (Set.inter_subset_right :
        zeroHornInOneBoundary ∩ zeroFaceInOneBoundary ⊆
          zeroFaceInOneBoundary))

private theorem standardSimplexBoundary_zero_false
    (x : standardSimplexBoundary 0) : False := by
  obtain ⟨i, hi⟩ := x.2
  fin_cases i
  have hsumZero : ∑ j : Fin 1, x.1.weights j = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    fin_cases j
    exact hi
  linarith [x.1.total_of_fintype, hsumZero]

private theorem zeroHornFaceIntersection_false
    (x : (zeroHornInOneBoundary ∩ zeroFaceInOneBoundary :
      Set (standardSimplexBoundary 1))) : False :=
  (Set.disjoint_left.mp zeroHornInOneBoundary_disjoint_zeroFaceInOneBoundary)
    x.2.1 x.2.2

private noncomputable def zeroBoundaryIntersectionHomeomorph :
    standardSimplexBoundary 0 ≃ₜ
      (zeroHornInOneBoundary ∩ zeroFaceInOneBoundary :
        Set (standardSimplexBoundary 1)) := by
  letI : IsEmpty (standardSimplexBoundary 0) :=
    ⟨standardSimplexBoundary_zero_false⟩
  letI : IsEmpty
      (zeroHornInOneBoundary ∩ zeroFaceInOneBoundary :
        Set (standardSimplexBoundary 1)) :=
    ⟨zeroHornFaceIntersection_false⟩
  exact
    { toEquiv := Equiv.equivOfIsEmpty _ _
      continuous_toFun := by
        rw [continuous_iff_continuousAt]
        intro x
        exact (standardSimplexBoundary_zero_false x).elim
      continuous_invFun := by
        rw [continuous_iff_continuousAt]
        intro x
        exact (zeroHornFaceIntersection_false x).elim }

private noncomputable def zeroFaceBoundaryHomeomorph :
    StandardSimplex 0 ≃ₜ zeroFaceInOneBoundary where
  toEquiv :=
    { toFun := fun x ↦
        ⟨standardSimplexZeroFaceToBoundary 0 x,
          standardSimplexZeroFace_weights_zero 0 x⟩
      invFun := fun y ↦
        (standardSimplexZeroFaceHomeomorph 0).symm ⟨y.1.1, y.2⟩
      left_inv := fun x ↦ standardSimplexZeroFaceHomeomorph_symm_apply 0 x
      right_inv := by
        intro y
        apply Subtype.ext
        apply Subtype.ext
        change standardSimplexZeroFace 0
            ((standardSimplexZeroFaceHomeomorph 0).symm ⟨y.1.1, y.2⟩) =
          y.1.1
        exact congrArg Subtype.val
          ((standardSimplexZeroFaceHomeomorph 0).apply_symm_apply
            ⟨y.1.1, y.2⟩) }
  continuous_toFun :=
    (standardSimplexZeroFaceToBoundary 0).continuous.subtype_mk _
  continuous_invFun :=
    (standardSimplexZeroFaceHomeomorph 0).symm.continuous.comp
      ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)

private noncomputable def zeroFaceSourcePairIso :
    standardSimplexPair 0 ≅ zeroFaceCoverPair :=
  MorphismProperty.Arrow.isoMk
    (TopCat.isoOfHomeo zeroBoundaryIntersectionHomeomorph)
    (TopCat.isoOfHomeo zeroFaceBoundaryHomeomorph)
    (by
      ext x
      exact (standardSimplexBoundary_zero_false x).elim)

private noncomputable def zeroHornBoundaryHomeomorph :
    zeroHornInOneBoundary ≃ₜ standardSimplexZeroHorn 0 where
  toEquiv :=
    { toFun := fun x ↦ ⟨x.1.1, x.2⟩
      invFun := fun x ↦
        ⟨⟨x.1, standardSimplexZeroHorn_subset_boundary 0 x.2⟩, x.2⟩
      left_inv := by
        intro x
        rfl
      right_inv := by
        intro x
        rfl }
  continuous_toFun :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    (continuous_subtype_val.subtype_mk _).subtype_mk _

private noncomputable def zeroFaceTargetPairIso :
    TopPair.ofSubset
        (X := TopCat.of (standardSimplexBoundary 1))
        zeroHornInOneBoundary ≅
      Hatcher.Relative.TopTriple.pairAB.obj
        (standardSimplexBoundaryHornTriple 0) :=
  MorphismProperty.Arrow.isoMk
    (TopCat.isoOfHomeo zeroHornBoundaryHomeomorph)
    (Iso.refl _)
    (by ext x; rfl)

private theorem zeroFacePairHom_zero_factorization :
    (zeroFaceSourcePairIso).hom ≫
        Hatcher.Excision.coverPairHom zeroFaceCoverCondition ≫
        (zeroFaceTargetPairIso).hom =
      standardSimplexZeroFacePairHom 0 := by
  apply MorphismProperty.Arrow.Hom.ext
  · ext x
    exact (standardSimplexBoundary_zero_false x).elim
  · ext x
    rfl

universe v u

variable {C : Type u} [Category.{v} C] [HasCoproducts.{0} C] [Abelian C]

/-- **Hatcher, Example 2.23 (page 125).** The canonical zero-face map
`(Δ[n], ∂Δ[n]) ⟶ (∂Δ[n+1], Λ⁰[n+1])` induces an isomorphism on
relative homology in every degree. -/
theorem zeroFacePair_homologyMap_isIso (R : C) (n k : ℕ) :
    IsIso ((Hatcher.Relative.homologyFunctor R k).map
      (standardSimplexZeroFacePairHom n)) := by
  cases n with
  | zero =>
      rw [← zeroFacePairHom_zero_factorization]
      rw [Functor.map_comp, Functor.map_comp]
      apply IsIso.comp_isIso'
      · exact ((Hatcher.Relative.homologyFunctor R k).mapIso
          zeroFaceSourcePairIso).isIso_hom
      · apply IsIso.comp_isIso'
        · exact Hatcher.Excision.coverHomologyMap_isIso
            zeroFaceCoverCondition R k
        · exact ((Hatcher.Relative.homologyFunctor R k).mapIso
            zeroFaceTargetPairIso).isIso_hom
  | succ n =>
      let P : Hatcher.Relative.GoodPair.{0} :=
        ⟨standardSimplexPair (n + 1),
          ⟨standardSimplexBoundaryGoodPairData n⟩⟩
      let Q : Hatcher.Relative.GoodPair.{0} :=
        ⟨Hatcher.Relative.TopTriple.pairAB.obj
            (standardSimplexBoundaryHornTriple (n + 1)),
          ⟨boundaryZeroHornGoodPairData (n + 1)⟩⟩
      let f : P ⟶ Q := ObjectProperty.homMk
        (standardSimplexZeroFacePairHom (n + 1))
      let F := Hatcher.Relative.goodPairRelativeHomologyFunctor R k
      let G := Hatcher.Relative.goodPairReducedPointQuotientHomologyFunctor R k
      let η := (Hatcher.Relative.goodPairPointQuotientRelativeHomologyNatIso
        R k).hom
      have hSquare :
          F.map f ≫ η.app Q = η.app P ≫ G.map f :=
        η.naturality f
      have hG : IsIso (G.map f) := by
        change IsIso ((Hatcher.Reduced.homologyFunctor R k).map
          (Hatcher.Relative.pointQuotientMap
            (standardSimplexZeroFacePairHom (n + 1))))
        rw [← zeroFacePointQuotientIso_hom (n + 1)]
        exact ((Hatcher.Reduced.homologyFunctor R k).mapIso
          (zeroFacePointQuotientIso (n + 1))).isIso_hom
      have hf : IsIso (F.map f) := @IsIso.of_isIso_fac_right C _ _ _ _ _ _ _
        (inferInstance : IsIso (η.app Q))
        (IsIso.comp_isIso'
          (inferInstance : IsIso (η.app P))
          hG)
        hSquare
      simpa [F, f, P, Q,
        Hatcher.Relative.goodPairRelativeHomologyFunctor] using hf

end Hatcher.Simplex
