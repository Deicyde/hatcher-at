/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Hatcher.Singular.DisjointPuncturedPair
import Hatcher.Singular.SigmaRelativeHomology
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

/-!
## The canonical finite-puncture homology coproduct
-/

open CategoryTheory.Limits

/-- **Hatcher, Proposition 2.30 (printed page 136), direct-sum step.**
The canonical sigma-pair homology comparison followed by finite-puncture
excision identifies the coproduct of the local groups with the deleted-fiber
relative group in every degree, including an empty fiber. -/
noncomputable def finitePunctureHomologyIso {n : ℕ}
    {f : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n}
    {y : TopCat.sphere.{0} n} (D : FiniteFiberNeighborhoods f y)
    (hfinite : (fiber f y).Finite) (k : ℕ) :
    (∐ fun i : fiber f y ↦
      (Hatcher.Relative.homologyFunctor (AddCommGrpCat.of ℤ) k).obj
        (Hatcher.Relative.puncturedPair (TopCat.of (D.U i))
          ⟨i.1, D.center_mem i⟩)) ≅
      (Hatcher.Relative.homologyFunctor (AddCommGrpCat.of ℤ) k).obj
        (Hatcher.Relative.deletedPair (TopCat.sphere.{0} n) (fiber f y)) := by
  letI : IsIso ((Hatcher.Relative.homologyFunctor (AddCommGrpCat.of ℤ) k).map
      (finitePuncturePairHom D)) :=
    finitePuncturePairHom_homology_isIso D hfinite k
  exact Hatcher.Relative.relativeIntegralHomologySigmaPairIso
      (fun i : fiber f y ↦
        Hatcher.Relative.puncturedPair (TopCat.of (D.U i))
          ⟨i.1, D.center_mem i⟩) k ≪≫
    asIso ((Hatcher.Relative.homologyFunctor (AddCommGrpCat.of ℤ) k).map
      (finitePuncturePairHom D))

/-- Each coproduct summand is carried by the actual inclusion of its local
punctured pair into the sphere with the full fiber deleted. -/
@[reassoc (attr := simp)]
theorem ι_finitePunctureHomologyIso_hom {n : ℕ}
    {f : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n}
    {y : TopCat.sphere.{0} n} (D : FiniteFiberNeighborhoods f y)
    (hfinite : (fiber f y).Finite) (k : ℕ) (i : fiber f y) :
    Sigma.ι (fun j : fiber f y ↦
        (Hatcher.Relative.homologyFunctor (AddCommGrpCat.of ℤ) k).obj
          (Hatcher.Relative.puncturedPair (TopCat.of (D.U j))
            ⟨j.1, D.center_mem j⟩)) i ≫
        (finitePunctureHomologyIso D hfinite k).hom =
      (Hatcher.Relative.homologyFunctor (AddCommGrpCat.of ℤ) k).map
        (finitePunctureNeighborhoodPairHom D i) := by
  dsimp only [finitePunctureHomologyIso, Iso.trans_hom, asIso_hom,
    Hatcher.Relative.relativeIntegralHomologySigmaPairIso]
  rw [← Category.assoc,
    Hatcher.Relative.ι_relativeHomologySigmaPairIso_hom]
  rw [← Functor.map_comp, sigmaPairι_comp_finitePuncturePairHom]

/-- The inverse finite-puncture comparison followed by a finite-biproduct
projection. All indexing instances are installed from the finiteness proof. -/
noncomputable def finitePunctureHomologyProjection {n : ℕ}
    {f : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n}
    {y : TopCat.sphere.{0} n} (D : FiniteFiberNeighborhoods f y)
    (hfinite : (fiber f y).Finite) (k : ℕ) (i : fiber f y) :
    (Hatcher.Relative.homologyFunctor (AddCommGrpCat.of ℤ) k).obj
        (Hatcher.Relative.deletedPair (TopCat.sphere.{0} n) (fiber f y)) ⟶
      (Hatcher.Relative.homologyFunctor (AddCommGrpCat.of ℤ) k).obj
        (Hatcher.Relative.puncturedPair (TopCat.of (D.U i))
          ⟨i.1, D.center_mem i⟩) := by
  classical
  letI : Fintype (fiber f y) := finiteFiberFintype hfinite
  let H (j : fiber f y) :=
    (Hatcher.Relative.homologyFunctor (AddCommGrpCat.of ℤ) k).obj
      (Hatcher.Relative.puncturedPair (TopCat.of (D.U j))
        ⟨j.1, D.center_mem j⟩)
  exact (finitePunctureHomologyIso D hfinite k).inv ≫
    (biproduct.isoCoproduct H).inv ≫ biproduct.π H i

/-- Morphisms into finite-puncture homology are determined by all their local
components. The empty component family is handled by the same biproduct
universal property. -/
theorem finitePunctureHomology_hom_ext {n : ℕ}
    {f : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n}
    {y : TopCat.sphere.{0} n} (D : FiniteFiberNeighborhoods f y)
    (hfinite : (fiber f y).Finite) (k : ℕ) {A : AddCommGrpCat}
    {a b : A ⟶ (Hatcher.Relative.homologyFunctor (AddCommGrpCat.of ℤ) k).obj
      (Hatcher.Relative.deletedPair (TopCat.sphere.{0} n) (fiber f y))}
    (h : ∀ i : fiber f y,
      a ≫ finitePunctureHomologyProjection D hfinite k i =
        b ≫ finitePunctureHomologyProjection D hfinite k i) : a = b := by
  classical
  let : Fintype (fiber f y) := finiteFiberFintype hfinite
  let H (j : fiber f y) :=
    (Hatcher.Relative.homologyFunctor (AddCommGrpCat.of ℤ) k).obj
      (Hatcher.Relative.puncturedPair (TopCat.of (D.U j))
        ⟨j.1, D.center_mem j⟩)
  apply (cancel_mono (finitePunctureHomologyIso D hfinite k).inv).1
  apply (cancel_mono (biproduct.isoCoproduct H).inv).1
  apply biproduct.hom_ext
  intro i
  simpa only [H, finitePunctureHomologyProjection, Category.assoc] using h i

end Hatcher.Sphere
