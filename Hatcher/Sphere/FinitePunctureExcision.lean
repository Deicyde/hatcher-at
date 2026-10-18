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

/-!
## The geometric projections and their matrix
-/

/-- Inclusion of complements defines the projection from the deleted-fiber
pair to the sphere pair punctured at a single fiber point. -/
noncomputable def finitePunctureProjectionPairHom {n : ℕ}
    {f : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n}
    {y : TopCat.sphere.{0} n} (x : fiber f y) :
    Hatcher.Relative.deletedPair (TopCat.sphere.{0} n) (fiber f y) ⟶
      Hatcher.Relative.puncturedPair (TopCat.sphere.{0} n) x.1 :=
  TopPair.ofHom (𝟙 _) (TopCat.ofHom (ContinuousMap.inclusion
    (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr x.2))))
    (by ext z; rfl)

@[simp]
theorem finitePunctureProjectionPairHom_fst {n : ℕ}
    {f : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n}
    {y : TopCat.sphere.{0} n} (x : fiber f y) :
    TopPair.Hom.fst (finitePunctureProjectionPairHom x) = 𝟙 _ := rfl

@[simp]
theorem finitePunctureProjectionPairHom_snd_apply_coe {n : ℕ}
    {f : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n}
    {y : TopCat.sphere.{0} n} (x : fiber f y)
    (z : (Hatcher.Relative.deletedPair
      (TopCat.sphere.{0} n) (fiber f y)).snd) :
    (TopPair.Hom.snd (finitePunctureProjectionPairHom x) z).1 = z.1 := rfl

/-- Hatcher's geometric projection on relative integral homology, induced by
the actual inclusion of complements. -/
noncomputable def finitePunctureProjectionMap {n : ℕ}
    {f : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n}
    {y : TopCat.sphere.{0} n} (x : fiber f y) (k : ℕ) :
    (Hatcher.Relative.homologyFunctor (AddCommGrpCat.of ℤ) k).obj
        (Hatcher.Relative.deletedPair (TopCat.sphere.{0} n) (fiber f y)) ⟶
      (Hatcher.Relative.homologyFunctor (AddCommGrpCat.of ℤ) k).obj
        (Hatcher.Relative.puncturedPair (TopCat.sphere.{0} n) x.1) :=
  (Hatcher.Relative.homologyFunctor (AddCommGrpCat.of ℤ) k).map
    (finitePunctureProjectionPairHom x)

/-- The diagonal triangle commutes already in topological pairs. -/
@[reassoc]
theorem finitePunctureNeighborhoodPairHom_comp_projectionPairHom {n : ℕ}
    {f : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n}
    {y : TopCat.sphere.{0} n} (D : FiniteFiberNeighborhoods f y)
    (x : fiber f y) :
    finitePunctureNeighborhoodPairHom D x ≫ finitePunctureProjectionPairHom x =
      Hatcher.Relative.localHomologyOpenNeighborhoodPairHom
        x.1 (D.U x) (D.center_mem x) := by
  apply MorphismProperty.Arrow.Hom.ext
  · ext z
    rfl
  · ext z
    rfl

/-- The local neighborhood followed by the geometric projection gives the
open-neighborhood local-homology map. -/
@[reassoc]
theorem finitePunctureProjectionMap_comp_neighborhood_self {n : ℕ}
    {f : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n}
    {y : TopCat.sphere.{0} n} (D : FiniteFiberNeighborhoods f y)
    (x : fiber f y) (k : ℕ) :
    (Hatcher.Relative.homologyFunctor (AddCommGrpCat.of ℤ) k).map
        (finitePunctureNeighborhoodPairHom D x) ≫
        finitePunctureProjectionMap x k =
      Hatcher.Relative.localHomologyOpenNeighborhoodMap
        x.1 (D.U x) (D.center_mem x) (AddCommGrpCat.of ℤ) k := by
  rw [finitePunctureProjectionMap, ← Functor.map_comp,
    finitePunctureNeighborhoodPairHom_comp_projectionPairHom]
  rfl

/-- A different disjoint neighborhood lies in the target complement, so its
composite induces the zero map on relative homology. -/
@[reassoc]
theorem finitePunctureProjectionMap_comp_neighborhood_of_ne {n : ℕ}
    {f : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n}
    {y : TopCat.sphere.{0} n} (D : FiniteFiberNeighborhoods f y)
    (x z : fiber f y) (k : ℕ) (hzx : z ≠ x) :
    (Hatcher.Relative.homologyFunctor (AddCommGrpCat.of ℤ) k).map
        (finitePunctureNeighborhoodPairHom D z) ≫
        finitePunctureProjectionMap x k = 0 := by
  have hmiss : D.U z ⊆ ({x.1}ᶜ : Set (TopCat.sphere.{0} n)) := by
    intro t ht
    change t ≠ x.1
    intro h
    exact (Set.disjoint_left.1 (D.pairwiseDisjoint_U hzx))
      (h ▸ ht) (D.center_mem x)
  let g : (Hatcher.Relative.puncturedPair (TopCat.of (D.U z))
      ⟨z.1, D.center_mem z⟩).fst ⟶
      (Hatcher.Relative.puncturedPair (TopCat.sphere.{0} n) x.1).snd :=
    TopCat.ofHom (ContinuousMap.inclusion hmiss)
  rw [finitePunctureProjectionMap, ← Functor.map_comp]
  exact Hatcher.Relative.homologyFunctor_map_eq_zero_of_factors_through_subspace
    (finitePunctureNeighborhoodPairHom D z ≫ finitePunctureProjectionPairHom x)
    g (by ext t; rfl) (AddCommGrpCat.of ℤ) k

section ProjectionMatrix

open scoped Classical

variable {n : ℕ}
  {f : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n}
  {y : TopCat.sphere.{0} n}
  (D : FiniteFiberNeighborhoods f y)
  (hfinite : (fiber f y).Finite) (k : ℕ)

/-- The diagonal component is the actual open-neighborhood inclusion. -/
@[reassoc]
theorem finitePunctureProjection_comp_summand_self (x : fiber f y) :
    Sigma.ι (fun j : fiber f y ↦
        (Hatcher.Relative.homologyFunctor (AddCommGrpCat.of ℤ) k).obj
          (Hatcher.Relative.puncturedPair (TopCat.of (D.U j))
            ⟨j.1, D.center_mem j⟩)) x ≫
        (finitePunctureHomologyIso D hfinite k).hom ≫
        finitePunctureProjectionMap x k =
      Hatcher.Relative.localHomologyOpenNeighborhoodMap
        x.1 (D.U x) (D.center_mem x) (AddCommGrpCat.of ℤ) k := by
  rw [ι_finitePunctureHomologyIso_hom_assoc]
  exact finitePunctureProjectionMap_comp_neighborhood_self D x k

/-- Every off-diagonal component vanishes. -/
@[reassoc]
theorem finitePunctureProjection_comp_summand_of_ne
    (x z : fiber f y) (hzx : z ≠ x) :
    Sigma.ι (fun j : fiber f y ↦
        (Hatcher.Relative.homologyFunctor (AddCommGrpCat.of ℤ) k).obj
          (Hatcher.Relative.puncturedPair (TopCat.of (D.U j))
            ⟨j.1, D.center_mem j⟩)) z ≫
        (finitePunctureHomologyIso D hfinite k).hom ≫
        finitePunctureProjectionMap x k = 0 := by
  rw [ι_finitePunctureHomologyIso_hom_assoc]
  exact finitePunctureProjectionMap_comp_neighborhood_of_ne D x z k hzx

/-- **Hatcher, Proposition 2.30 (printed page 136), projection step.**
Under the canonical finite-puncture comparison, Hatcher's geometric
projections have the diagonal matrix. Equality of indices transports the
source local group before applying its neighborhood inclusion. -/
@[reassoc]
theorem finitePunctureProjection_comp_summand (x z : fiber f y) :
    Sigma.ι (fun j : fiber f y ↦
        (Hatcher.Relative.homologyFunctor (AddCommGrpCat.of ℤ) k).obj
          (Hatcher.Relative.puncturedPair (TopCat.of (D.U j))
            ⟨j.1, D.center_mem j⟩)) z ≫
        (finitePunctureHomologyIso D hfinite k).hom ≫
        finitePunctureProjectionMap x k =
      if h : z = x then
        eqToHom (congrArg (fun j : fiber f y ↦
          (Hatcher.Relative.homologyFunctor (AddCommGrpCat.of ℤ) k).obj
            (Hatcher.Relative.puncturedPair (TopCat.of (D.U j))
              ⟨j.1, D.center_mem j⟩)) h) ≫
          Hatcher.Relative.localHomologyOpenNeighborhoodMap
            x.1 (D.U x) (D.center_mem x) (AddCommGrpCat.of ℤ) k
      else 0 := by
  by_cases h : z = x
  · subst z
    simpa only [dite_eq_left (rfl : x = x),
      eqToHom_refl, Category.id_comp] using
      finitePunctureProjection_comp_summand_self D hfinite k x
  · simpa only [dite_eq_right h] using
      finitePunctureProjection_comp_summand_of_ne D hfinite k x z h

/-- The geometric projection is the canonical coproduct coordinate followed
by the local-neighborhood inclusion. -/
@[reassoc]
theorem finitePunctureProjectionMap_eq_sigma_projection (x : fiber f y) :
    finitePunctureProjectionMap x k =
      (finitePunctureHomologyIso D hfinite k).inv ≫
        Sigma.π (fun j : fiber f y ↦
          (Hatcher.Relative.homologyFunctor (AddCommGrpCat.of ℤ) k).obj
            (Hatcher.Relative.puncturedPair (TopCat.of (D.U j))
              ⟨j.1, D.center_mem j⟩)) x ≫
        Hatcher.Relative.localHomologyOpenNeighborhoodMap
          x.1 (D.U x) (D.center_mem x) (AddCommGrpCat.of ℤ) k := by
  apply (cancel_epi (finitePunctureHomologyIso D hfinite k).hom).1
  simp only [Iso.hom_inv_id_assoc]
  apply Sigma.hom_ext
  intro z
  by_cases h : z = x
  · subst z
    simpa only [Category.assoc, Sigma.ι_π_eq_id_assoc,
      Category.id_comp] using
      finitePunctureProjection_comp_summand_self D hfinite k x
  · simpa only [Category.assoc, Sigma.ι_π_of_ne_assoc _ h,
      zero_comp] using
      finitePunctureProjection_comp_summand_of_ne D hfinite k x z h

/-- The chosen finite-biproduct coordinate is exactly the canonical
coproduct coordinate. -/
@[reassoc]
theorem finitePunctureHomologyProjection_eq_sigma_projection
    (x : fiber f y) :
    finitePunctureHomologyProjection D hfinite k x =
      (finitePunctureHomologyIso D hfinite k).inv ≫
        Sigma.π (fun j : fiber f y ↦
          (Hatcher.Relative.homologyFunctor (AddCommGrpCat.of ℤ) k).obj
            (Hatcher.Relative.puncturedPair (TopCat.of (D.U j))
              ⟨j.1, D.center_mem j⟩)) x := by
  classical
  let : Fintype (fiber f y) := finiteFiberFintype hfinite
  let H (j : fiber f y) :=
    (Hatcher.Relative.homologyFunctor (AddCommGrpCat.of ℤ) k).obj
      (Hatcher.Relative.puncturedPair (TopCat.of (D.U j))
        ⟨j.1, D.center_mem j⟩)
  have hπ : (biproduct.isoCoproduct H).inv ≫ biproduct.π H x = Sigma.π H x := by
    apply Sigma.hom_ext
    intro z
    rw [biproduct.isoCoproduct_inv, Sigma.ι_comp_desc_assoc]
    by_cases h : z = x
    · subst z
      rw [biproduct.ι_π_self, Sigma.ι_π_eq_id]
    · rw [biproduct.ι_π_ne H h, Sigma.ι_π_of_ne H h]
  change
    (finitePunctureHomologyIso D hfinite k).inv ≫
        (biproduct.isoCoproduct H).inv ≫ biproduct.π H x =
      (finitePunctureHomologyIso D hfinite k).inv ≫ Sigma.π H x
  rw [hπ]

/-- The geometric map factors through the existing abstract finite-biproduct
coordinate and the local-neighborhood inclusion. -/
@[reassoc]
theorem finitePunctureProjectionMap_eq_homologyProjection_comp
    (x : fiber f y) :
    finitePunctureProjectionMap x k =
      finitePunctureHomologyProjection D hfinite k x ≫
        Hatcher.Relative.localHomologyOpenNeighborhoodMap
          x.1 (D.U x) (D.center_mem x) (AddCommGrpCat.of ℤ) k := by
  rw [finitePunctureHomologyProjection_eq_sigma_projection, Category.assoc]
  exact finitePunctureProjectionMap_eq_sigma_projection D hfinite k x

/-- The finite-biproduct formula installs its finite indexing instance
internally from the finiteness proof. -/
theorem finitePunctureProjectionMap_eq_biproduct_projection
    (x : fiber f y) :
    letI : Fintype (fiber f y) := finiteFiberFintype hfinite
    finitePunctureProjectionMap x k =
      (finitePunctureHomologyIso D hfinite k).inv ≫
        (biproduct.isoCoproduct (fun j : fiber f y ↦
          (Hatcher.Relative.homologyFunctor (AddCommGrpCat.of ℤ) k).obj
            (Hatcher.Relative.puncturedPair (TopCat.of (D.U j))
              ⟨j.1, D.center_mem j⟩))).inv ≫
        biproduct.π (fun j : fiber f y ↦
          (Hatcher.Relative.homologyFunctor (AddCommGrpCat.of ℤ) k).obj
            (Hatcher.Relative.puncturedPair (TopCat.of (D.U j))
              ⟨j.1, D.center_mem j⟩)) x ≫
        Hatcher.Relative.localHomologyOpenNeighborhoodMap
          x.1 (D.U x) (D.center_mem x) (AddCommGrpCat.of ℤ) k := by
  classical
  let : Fintype (fiber f y) := finiteFiberFintype hfinite
  simpa only [finitePunctureHomologyProjection, Category.assoc] using
    finitePunctureProjectionMap_eq_homologyProjection_comp D hfinite k x

/-- Normalize the geometric projection by the inverse open-neighborhood
local-homology map. Finiteness is not needed for this definition. -/
noncomputable def finitePunctureNormalizedProjection (x : fiber f y) :
    (Hatcher.Relative.homologyFunctor (AddCommGrpCat.of ℤ) k).obj
        (Hatcher.Relative.deletedPair (TopCat.sphere.{0} n) (fiber f y)) ⟶
      (Hatcher.Relative.homologyFunctor (AddCommGrpCat.of ℤ) k).obj
        (Hatcher.Relative.puncturedPair (TopCat.of (D.U x))
          ⟨x.1, D.center_mem x⟩) := by
  letI : T2Space (TopCat.sphere.{0} n) :=
    (sphereULiftHomeomorph n).symm.t2Space
  letI : IsIso (Hatcher.Relative.localHomologyOpenNeighborhoodMap
      x.1 (D.U x) (D.center_mem x) (AddCommGrpCat.of ℤ) k) :=
    Hatcher.Relative.localHomologyOpenNeighborhoodMap_isIso_of_t1
      x.1 (D.U x) (D.center_mem x) (D.isOpen_U x) (AddCommGrpCat.of ℤ) k
  exact finitePunctureProjectionMap x k ≫
    inv (Hatcher.Relative.localHomologyOpenNeighborhoodMap
      x.1 (D.U x) (D.center_mem x) (AddCommGrpCat.of ℤ) k)

/-- Normalization identifies the geometric and abstract coordinates exactly. -/
@[reassoc]
theorem finitePunctureNormalizedProjection_eq_homologyProjection
    (x : fiber f y) :
    finitePunctureNormalizedProjection D k x =
      finitePunctureHomologyProjection D hfinite k x := by
  let : T2Space (TopCat.sphere.{0} n) :=
    (sphereULiftHomeomorph n).symm.t2Space
  let : IsIso (Hatcher.Relative.localHomologyOpenNeighborhoodMap
      x.1 (D.U x) (D.center_mem x) (AddCommGrpCat.of ℤ) k) :=
    Hatcher.Relative.localHomologyOpenNeighborhoodMap_isIso_of_t1
      x.1 (D.U x) (D.center_mem x) (D.isOpen_U x) (AddCommGrpCat.of ℤ) k
  rw [finitePunctureNormalizedProjection,
    finitePunctureProjectionMap_eq_homologyProjection_comp D hfinite k x]
  simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id]

/-- The normalized projection is the inverse finite-puncture comparison
followed by the canonical coproduct coordinate. -/
@[reassoc]
theorem finitePunctureNormalizedProjection_eq_sigma_projection
    (x : fiber f y) :
    finitePunctureNormalizedProjection D k x =
      (finitePunctureHomologyIso D hfinite k).inv ≫
        Sigma.π (fun j : fiber f y ↦
          (Hatcher.Relative.homologyFunctor (AddCommGrpCat.of ℤ) k).obj
            (Hatcher.Relative.puncturedPair (TopCat.of (D.U j))
              ⟨j.1, D.center_mem j⟩)) x := by
  rw [finitePunctureNormalizedProjection_eq_homologyProjection D hfinite k x,
    finitePunctureHomologyProjection_eq_sigma_projection D hfinite k x]

end ProjectionMatrix

end Hatcher.Sphere
