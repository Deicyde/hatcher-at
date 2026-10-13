/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Hatcher.Singular.DisjointPuncturedPair
import Hatcher.Sphere.FiniteFiberNeighborhoods
import Mathlib.Algebra.Category.Grp.AB

/-!
# Excision for a finite puncture set

The sigma pair of chosen punctured neighborhoods of a finite sphere-map fiber
maps canonically to the sphere pair obtained by deleting the whole fiber.  The
map is the disjoint-union pair isomorphism followed by deleted-pair excision,
so it induces an isomorphism on relative integral homology in every degree.
-/

noncomputable section

open AlgebraicTopology CategoryTheory Function Set Topology

namespace Hatcher.Sphere

private noncomputable def deletedUnionFiberSubspaceHomeomorph {n : ℕ}
    {f : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n}
    {y : TopCat.sphere.{0} n} (D : FiniteFiberNeighborhoods f y) :
    (Hatcher.Relative.deletedUnionPair D.U (fun i ↦ i.1)).snd ≃ₜ
      (Hatcher.Relative.deletedPairWithin (fiber f y) D.union).snd :=
  { toEquiv :=
      { toFun := fun z ↦ ⟨⟨z.1.1, by
          simpa only [FiniteFiberNeighborhoods.union] using z.1.2⟩, by
          change z.1.1 ∈ (fiber f y)ᶜ
          simpa only [Set.mem_preimage, Set.mem_compl_iff,
            Subtype.range_val] using z.2⟩
        invFun := fun z ↦ ⟨⟨z.1.1, by
          simpa only [FiniteFiberNeighborhoods.union] using z.1.2⟩, by
          change z.1.1 ∈ (Set.range fun j : fiber f y ↦ j.1)ᶜ
          simpa only [Set.mem_preimage, Set.mem_compl_iff,
            Subtype.range_val] using z.2⟩
        left_inv := by
          intro z
          apply Subtype.ext
          apply Subtype.ext
          rfl
        right_inv := by
          intro z
          apply Subtype.ext
          apply Subtype.ext
          rfl }
    continuous_toFun :=
      ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _
    continuous_invFun :=
      ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _ }

private noncomputable def finitePunctureSubspaceHomeomorph {n : ℕ}
    {f : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n}
    {y : TopCat.sphere.{0} n} (D : FiniteFiberNeighborhoods f y) :
    (Hatcher.Relative.sigmaPuncturedPair D.U
      (fun i ↦ i.1) D.center_mem).snd ≃ₜ
      (Hatcher.Relative.deletedPairWithin (fiber f y) D.union).snd :=
  (Hatcher.Relative.sigmaPuncturedSubspaceHomeomorphDeletedUnion
      D.U D.pairwiseDisjoint_U D.isOpen_U (fun i ↦ i.1)
        D.center_mem).trans
    (deletedUnionFiberSubspaceHomeomorph D)

/-- The finite-family specialization of the disjoint punctured-pair
isomorphism, with target literally the deleted fiber inside the chosen open
union. -/
noncomputable def finitePunctureSigmaPairIsoDeletedUnion {n : ℕ}
    {f : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n}
    {y : TopCat.sphere.{0} n} (D : FiniteFiberNeighborhoods f y) :
    Hatcher.Relative.sigmaPuncturedPair D.U (fun i ↦ i.1) D.center_mem ≅
      Hatcher.Relative.deletedPairWithin (fiber f y) D.union :=
  MorphismProperty.Arrow.isoMk
    (TopCat.isoOfHomeo (finitePunctureSubspaceHomeomorph D))
    (TopCat.isoOfHomeo
      (Hatcher.Topology.sigmaSubtypeHomeomorphUnion
        D.U D.pairwiseDisjoint_U D.isOpen_U))
    (by ext z; rfl)

/-- The disjoint-union comparison followed by inclusion into the sphere with
the whole fiber deleted. -/
noncomputable def finitePuncturePairHom {n : ℕ}
    {f : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n}
    {y : TopCat.sphere.{0} n} (D : FiniteFiberNeighborhoods f y) :
    Hatcher.Relative.sigmaPuncturedPair D.U (fun i ↦ i.1) D.center_mem ⟶
      Hatcher.Relative.deletedPair (TopCat.sphere.{0} n) (fiber f y) :=
  (finitePunctureSigmaPairIsoDeletedUnion D).hom ≫
    Hatcher.Relative.deletedPairOpenNeighborhoodPairHom
      (fiber f y) D.union

/-- The direct inclusion of one chosen punctured neighborhood into the sphere
pair obtained by deleting the full fiber. -/
noncomputable def finitePunctureNeighborhoodPairHom {n : ℕ}
    {f : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n}
    {y : TopCat.sphere.{0} n} (D : FiniteFiberNeighborhoods f y)
    (i : fiber f y) :
    Hatcher.Relative.puncturedPair (TopCat.of (D.U i))
        ⟨i.1, D.center_mem i⟩ ⟶
      Hatcher.Relative.deletedPair (TopCat.sphere.{0} n) (fiber f y) :=
  Hatcher.Relative.sigmaPairι (fun j ↦
      Hatcher.Relative.puncturedPair (TopCat.of (D.U j))
        ⟨j.1, D.center_mem j⟩) i ≫
    finitePuncturePairHom D

@[simp]
theorem finitePunctureNeighborhoodPairHom_fst_apply {n : ℕ}
    {f : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n}
    {y : TopCat.sphere.{0} n} (D : FiniteFiberNeighborhoods f y)
    (i : fiber f y) (z : D.U i) :
    TopPair.Hom.fst (finitePunctureNeighborhoodPairHom D i) z = z.1 := by
  change z.1 = z.1
  rfl

@[simp]
theorem finitePunctureNeighborhoodPairHom_snd_apply_coe {n : ℕ}
    {f : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n}
    {y : TopCat.sphere.{0} n} (D : FiniteFiberNeighborhoods f y)
    (i : fiber f y)
    (z : (Hatcher.Relative.puncturedPair (TopCat.of (D.U i))
      ⟨i.1, D.center_mem i⟩).snd) :
    (TopPair.Hom.snd
      (finitePunctureNeighborhoodPairHom D i) z).1 = z.1.1 := by
  change z.1.1 = z.1.1
  rfl

/-- Each sigma summand followed by the finite-puncture comparison is the
direct inclusion of that local punctured pair. -/
@[reassoc]
theorem sigmaPairι_comp_finitePuncturePairHom {n : ℕ}
    {f : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n}
    {y : TopCat.sphere.{0} n} (D : FiniteFiberNeighborhoods f y)
    (i : fiber f y) :
    Hatcher.Relative.sigmaPairι (fun j ↦
        Hatcher.Relative.puncturedPair (TopCat.of (D.U j))
          ⟨j.1, D.center_mem j⟩) i ≫
        finitePuncturePairHom D =
      finitePunctureNeighborhoodPairHom D i := by
  rfl

/-- **Hatcher, Proposition 2.30 (printed page 136), excision step.** The
canonical map from the disjoint local punctured pairs to the sphere with the
full finite fiber deleted induces an isomorphism on relative integral homology
in every degree. -/
theorem finitePuncturePairHom_homology_isIso {n : ℕ}
    {f : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n}
    {y : TopCat.sphere.{0} n} (D : FiniteFiberNeighborhoods f y)
    (hfinite : (fiber f y).Finite) (k : ℕ) :
    IsIso ((Hatcher.Relative.homologyFunctor (AddCommGrpCat.of ℤ) k).map
      (finitePuncturePairHom D)) := by
  let _ : T2Space (TopCat.sphere.{0} n) :=
    (sphereULiftHomeomorph n).symm.t2Space
  change IsIso ((Hatcher.Relative.homologyFunctor
      (AddCommGrpCat.of ℤ) k).map
    ((finitePunctureSigmaPairIsoDeletedUnion D).hom ≫
      Hatcher.Relative.deletedPairOpenNeighborhoodPairHom
        (fiber f y) D.union))
  rw [Functor.map_comp]
  apply IsIso.comp_isIso'
  · exact ((Hatcher.Relative.homologyFunctor
      (AddCommGrpCat.of ℤ) k).mapIso
        (finitePunctureSigmaPairIsoDeletedUnion D)).isIso_hom
  · change IsIso (Hatcher.Relative.deletedPairOpenNeighborhoodMap
      (fiber f y) D.union (AddCommGrpCat.of ℤ) k)
    exact Hatcher.Relative.deletedPairOpenNeighborhoodMap_isIso_of_finite
      (fiber f y) D.union hfinite D.isOpen_union D.fiber_subset_union
        (AddCommGrpCat.of ℤ) k

end Hatcher.Sphere
