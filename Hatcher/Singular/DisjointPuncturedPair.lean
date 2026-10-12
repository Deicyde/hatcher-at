/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Hatcher.Singular.DeletedPair
import Hatcher.Singular.SigmaPair
import Hatcher.Topology.DisjointOpenUnion
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Disjoint punctured pairs

The sigma pair of pairwise-disjoint punctured neighborhoods is canonically
isomorphic to their union with the ambient range of the chosen centers
deleted.  The construction requires no separation hypothesis on the ambient
space.
-/

noncomputable section

open CategoryTheory Function Set Topology

namespace Hatcher.Relative

universe u v

variable {ι : Type u} {X : Type (max u v)} [TopologicalSpace X]

/-- The sigma pair of the punctured pairs `(U i, U i \ {x i})`. -/
abbrev sigmaPuncturedPair (U : ι → Set X) (x : ι → X)
    (hx : ∀ i, x i ∈ U i) : TopPair.{max u v} :=
  sigmaPair fun i ↦
    puncturedPair (TopCat.of (U i) : TopCat.{max u v}) ⟨x i, hx i⟩

/-- The union pair with the ambient range of the chosen centers deleted. -/
def deletedUnionPair (U : ι → Set X) (x : ι → X) :
    TopPair.{max u v} :=
  deletedPairWithin
    (X := (TopCat.of X : TopCat.{max u v}))
    (Set.range x) (⋃ i, U i)

private theorem sigmaPuncturedMap_not_mem_range
    (U : ι → Set X) (hU : Pairwise (Disjoint on U))
    (hUopen : ∀ i, IsOpen (U i)) (x : ι → X) (hx : ∀ i, x i ∈ U i)
    (z : (sigmaPuncturedPair U x hx).snd) :
    ((Hatcher.Topology.sigmaSubtypeHomeomorphUnion U hU hUopen
      ((sigmaPuncturedPair U x hx).map z) : ⋃ i, U i) : X) ∉
      Set.range x := by
  rintro ⟨j, hj⟩
  rcases z with ⟨i, z⟩
  have hout :
      ((Hatcher.Topology.sigmaSubtypeHomeomorphUnion U hU hUopen
        ((sigmaPuncturedPair U x hx).map ⟨i, z⟩) : ⋃ i, U i) : X) =
        z.1.1 := by
    rfl
  have hzxj : z.1.1 = x j := (hj.trans hout).symm
  by_cases hij : i = j
  · subst j
    have hz : z.1 ≠ (⟨x i, hx i⟩ : U i) := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using z.2
    exact hz (Subtype.ext hzxj)
  · have hd : Disjoint (U i) (U j) := hU hij
    exact (Set.disjoint_left.1 hd z.1.2) (hzxj.symm ▸ hx j)

private def sigmaPuncturedToUnion
    (U : ι → Set X) (hU : Pairwise (Disjoint on U))
    (hUopen : ∀ i, IsOpen (U i)) (x : ι → X) (hx : ∀ i, x i ∈ U i) :
    (sigmaPuncturedPair U x hx).snd → (⋃ i, U i) :=
  fun z ↦ Hatcher.Topology.sigmaSubtypeHomeomorphUnion U hU hUopen
    ((sigmaPuncturedPair U x hx).map z)

private noncomputable def sigmaPuncturedToDeletedUnion
    (U : ι → Set X) (hU : Pairwise (Disjoint on U))
    (hUopen : ∀ i, IsOpen (U i)) (x : ι → X) (hx : ∀ i, x i ∈ U i) :
    C((sigmaPuncturedPair U x hx).snd, (deletedUnionPair U x).snd) where
  toFun z :=
    ⟨sigmaPuncturedToUnion U hU hUopen x hx z,
      sigmaPuncturedMap_not_mem_range U hU hUopen x hx z⟩
  continuous_toFun :=
    ((Hatcher.Topology.sigmaSubtypeHomeomorphUnion U hU hUopen).continuous.comp
      (sigmaPuncturedPair U x hx).map.hom.continuous).subtype_mk _

private theorem sigmaPuncturedToDeletedUnion_isEmbedding
    (U : ι → Set X) (hU : Pairwise (Disjoint on U))
    (hUopen : ∀ i, IsOpen (U i)) (x : ι → X) (hx : ∀ i, x i ∈ U i) :
    IsEmbedding (sigmaPuncturedToDeletedUnion U hU hUopen x hx) := by
  change IsEmbedding (Set.codRestrict
    (sigmaPuncturedToUnion U hU hUopen x hx)
    ((fun z : ⋃ i, U i ↦ (z : X)) ⁻¹' (Set.range x)ᶜ) _)
  exact ((Hatcher.Topology.sigmaSubtypeHomeomorphUnion U hU hUopen).isEmbedding.comp
    (TopPair.isEmbedding_map (sigmaPuncturedPair U x hx))).codRestrict _ _

private theorem sigmaPuncturedToDeletedUnion_surjective
    (U : ι → Set X) (hU : Pairwise (Disjoint on U))
    (hUopen : ∀ i, IsOpen (U i)) (x : ι → X) (hx : ∀ i, x i ∈ U i) :
    Function.Surjective (sigmaPuncturedToDeletedUnion U hU hUopen x hx) := by
  intro z
  let s := (Hatcher.Topology.sigmaSubtypeHomeomorphUnion U hU hUopen).symm z.1
  have hs := Homeomorph.apply_symm_apply
    (Hatcher.Topology.sigmaSubtypeHomeomorphUnion U hU hUopen) z.1
  have ha : s.2 ≠ (⟨x s.1, hx s.1⟩ : U s.1) := by
    intro has
    have hzrange : (z.1.1 : X) ∈ Set.range x := by
      refine ⟨s.1, ?_⟩
      calc
        x s.1 = s.2.1 := congrArg Subtype.val has.symm
        _ = (Hatcher.Topology.sigmaSubtypeHomeomorphUnion U hU hUopen s).1 := rfl
        _ = z.1.1 := congrArg Subtype.val hs
    exact z.2 hzrange
  let a' : ({⟨x s.1, hx s.1⟩}ᶜ : Set (U s.1)) := ⟨s.2, by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using ha⟩
  refine ⟨⟨s.1, a'⟩, ?_⟩
  apply Subtype.ext
  change Hatcher.Topology.sigmaSubtypeHomeomorphUnion U hU hUopen s = z.1
  exact hs

/-- The subspace of the punctured sigma pair is homeomorphic to the union
with the ambient range of the chosen centers deleted. -/
noncomputable def sigmaPuncturedSubspaceHomeomorphDeletedUnion
    (U : ι → Set X) (hU : Pairwise (Disjoint on U))
    (hUopen : ∀ i, IsOpen (U i)) (x : ι → X) (hx : ∀ i, x i ∈ U i) :
    (sigmaPuncturedPair U x hx).snd ≃ₜ (deletedUnionPair U x).snd :=
  Topology.IsEmbedding.toHomeomorphOfSurjective
    (sigmaPuncturedToDeletedUnion_isEmbedding U hU hUopen x hx)
    (sigmaPuncturedToDeletedUnion_surjective U hU hUopen x hx)

@[simp]
theorem sigmaPuncturedSubspaceHomeomorphDeletedUnion_apply_coe
    (U : ι → Set X) (hU : Pairwise (Disjoint on U))
    (hUopen : ∀ i, IsOpen (U i)) (x : ι → X) (hx : ∀ i, x i ∈ U i)
    (z : (sigmaPuncturedPair U x hx).snd) :
    ((sigmaPuncturedSubspaceHomeomorphDeletedUnion
      U hU hUopen x hx z).1 : ⋃ i, U i) =
      Hatcher.Topology.sigmaSubtypeHomeomorphUnion U hU hUopen
        ((sigmaPuncturedPair U x hx).map z) :=
  rfl

/-- The sigma pair of disjoint punctured neighborhoods is canonically
isomorphic to their union with the range of centers deleted. -/
noncomputable def sigmaPuncturedPairIsoDeletedUnion
    (U : ι → Set X) (hU : Pairwise (Disjoint on U))
    (hUopen : ∀ i, IsOpen (U i)) (x : ι → X) (hx : ∀ i, x i ∈ U i) :
    sigmaPuncturedPair U x hx ≅ deletedUnionPair U x :=
  MorphismProperty.Arrow.isoMk
    (TopCat.isoOfHomeo
      (sigmaPuncturedSubspaceHomeomorphDeletedUnion U hU hUopen x hx))
    (TopCat.isoOfHomeo
      (Hatcher.Topology.sigmaSubtypeHomeomorphUnion U hU hUopen))
    (by ext z; rfl)

@[simp]
theorem sigmaPuncturedPairIsoDeletedUnion_hom_fst
    (U : ι → Set X) (hU : Pairwise (Disjoint on U))
    (hUopen : ∀ i, IsOpen (U i)) (x : ι → X) (hx : ∀ i, x i ∈ U i) :
    TopPair.Hom.fst
        (sigmaPuncturedPairIsoDeletedUnion U hU hUopen x hx).hom =
      (TopCat.isoOfHomeo
        (Hatcher.Topology.sigmaSubtypeHomeomorphUnion U hU hUopen)).hom :=
  rfl

@[simp]
theorem sigmaPuncturedPairIsoDeletedUnion_hom_fst_apply
    (U : ι → Set X) (hU : Pairwise (Disjoint on U))
    (hUopen : ∀ i, IsOpen (U i)) (x : ι → X) (hx : ∀ i, x i ∈ U i)
    (z : Σ i, U i) :
    TopPair.Hom.fst
        (sigmaPuncturedPairIsoDeletedUnion U hU hUopen x hx).hom z =
      Hatcher.Topology.sigmaSubtypeHomeomorphUnion U hU hUopen z :=
  rfl

private noncomputable def puncturedNeighborhoodDeletedUnionSubspaceMap
    (U : ι → Set X) (hU : Pairwise (Disjoint on U))
    (hUopen : ∀ i, IsOpen (U i)) (x : ι → X) (hx : ∀ i, x i ∈ U i)
    (i : ι) :
    C((puncturedPair (TopCat.of (U i) : TopCat.{max u v})
        ⟨x i, hx i⟩).snd, (deletedUnionPair U x).snd) where
  toFun z := sigmaPuncturedSubspaceHomeomorphDeletedUnion
    U hU hUopen x hx ⟨i, z⟩
  continuous_toFun :=
    (sigmaPuncturedSubspaceHomeomorphDeletedUnion U hU hUopen x hx).continuous.comp
      continuous_sigmaMk

/-- The direct inclusion of one punctured neighborhood into the deleted union
pair. -/
noncomputable def puncturedNeighborhoodDeletedUnionPairHom
    (U : ι → Set X) (hU : Pairwise (Disjoint on U))
    (hUopen : ∀ i, IsOpen (U i)) (x : ι → X) (hx : ∀ i, x i ∈ U i)
    (i : ι) :
    puncturedPair (TopCat.of (U i) : TopCat.{max u v}) ⟨x i, hx i⟩ ⟶
      deletedUnionPair U x :=
  TopPair.ofHom
    (TopCat.ofHom (ContinuousMap.inclusion (Set.subset_iUnion U i)))
    (TopCat.ofHom
      (puncturedNeighborhoodDeletedUnionSubspaceMap U hU hUopen x hx i))
    (by ext z; rfl)

@[simp]
theorem puncturedNeighborhoodDeletedUnionPairHom_fst_apply
    (U : ι → Set X) (hU : Pairwise (Disjoint on U))
    (hUopen : ∀ i, IsOpen (U i)) (x : ι → X) (hx : ∀ i, x i ∈ U i)
    (i : ι) (z : U i) :
    TopPair.Hom.fst
        (puncturedNeighborhoodDeletedUnionPairHom U hU hUopen x hx i) z =
      ⟨z.1, Set.mem_iUnion.2 ⟨i, z.2⟩⟩ :=
  rfl

@[simp]
theorem puncturedNeighborhoodDeletedUnionPairHom_snd_apply_coe
    (U : ι → Set X) (hU : Pairwise (Disjoint on U))
    (hUopen : ∀ i, IsOpen (U i)) (x : ι → X) (hx : ∀ i, x i ∈ U i)
    (i : ι)
    (z : (puncturedPair (TopCat.of (U i) : TopCat.{max u v})
      ⟨x i, hx i⟩).snd) :
    ((TopPair.Hom.snd
      (puncturedNeighborhoodDeletedUnionPairHom
        U hU hUopen x hx i) z).1 : ⋃ i, U i).1 = z.1.1 := by
  rfl

/-- Each canonical sigma summand followed by the pair isomorphism is the
ordinary direct inclusion into the deleted union pair. -/
@[reassoc]
theorem sigmaPairι_comp_sigmaPuncturedPairIsoDeletedUnion_hom
    (U : ι → Set X) (hU : Pairwise (Disjoint on U))
    (hUopen : ∀ i, IsOpen (U i)) (x : ι → X) (hx : ∀ i, x i ∈ U i)
    (i : ι) :
    sigmaPairι (fun j ↦
        puncturedPair (TopCat.of (U j) : TopCat.{max u v}) ⟨x j, hx j⟩) i ≫
        (sigmaPuncturedPairIsoDeletedUnion U hU hUopen x hx).hom =
      puncturedNeighborhoodDeletedUnionPairHom U hU hUopen x hx i := by
  apply MorphismProperty.Arrow.Hom.ext
  · ext z
    apply Subtype.ext
    rfl
  · ext z
    rfl

end Hatcher.Relative
