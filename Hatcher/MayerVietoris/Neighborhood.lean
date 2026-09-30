/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Hatcher.MayerVietoris.Sequence
import Hatcher.Singular.Homology
import Hatcher.Topology.StrongDeformationRetract

/-!
# Mayer--Vietoris for neighborhood deformation retracts

This file transports the ordinary binary-cover Mayer--Vietoris sequence from
neighborhoods to strong deformation retracts, while retaining the maps induced
by the actual inclusions of the original subspaces.
-/

noncomputable section

open AlgebraicTopology CategoryTheory Limits Topology

attribute [local instance] preservesBinaryBiproduct_of_preservesBiproduct

namespace Hatcher.MayerVietoris

universe w v u

variable {X : TopCat.{w}}

/-- The canonical continuous map associated to an inclusion of subspaces. -/
def inclusionOfSubset {A B : Set X} (h : A ⊆ B) :
    C(A, B) :=
  ContinuousMap.inclusion h

variable {C : Type u} [Category.{v} C] [Abelian C]
  [HasCoproducts.{w} C]

local instance neighborhoodHasFiniteCoproducts : HasFiniteCoproducts C :=
  hasFiniteCoproducts_of_hasCoproducts C

local instance neighborhoodHasBinaryBiproducts : HasBinaryBiproducts C :=
  HasBinaryBiproducts.of_hasBinaryCoproducts

/-- The singular-homology map induced by an inclusion of subspaces. -/
noncomputable def homologyMapOfSubset {A B : Set X} (h : A ⊆ B)
    (R : C) (n : ℕ) :
    (Hatcher.Excision.singularChains (TopCat.of A) R).homology n ⟶
      (Hatcher.Excision.singularChains (TopCat.of B) R).homology n :=
  HomologicalComplex.homologyMap
    (Hatcher.Excision.singularChainMap
      (TopCat.ofHom (inclusionOfSubset h)) R) n

/-- The singular-homology map induced by the canonical inclusion of a
subspace into its ambient space. -/
noncomputable def homologyMapToAmbient (A : Set X) (R : C) (n : ℕ) :
    (Hatcher.Excision.singularChains (TopCat.of A) R).homology n ⟶
      (Hatcher.Excision.singularChains X R).homology n :=
  HomologicalComplex.homologyMap
    (Hatcher.Excision.singularChainMap
      (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩) R) n

/-- Inclusions of two subspaces induce an inclusion of their intersections. -/
theorem intersectionSubset {A B U V : Set X} (hA : A ⊆ U) (hB : B ⊆ V) :
    A ∩ B ⊆ U ∩ V :=
  fun _ hx ↦ ⟨hA hx.1, hB hx.2⟩

@[reassoc]
theorem homologyMapOfSubset_comp {A B D : Set X}
    (hAB : A ⊆ B) (hBD : B ⊆ D) (R : C) (n : ℕ) :
    homologyMapOfSubset hAB R n ≫ homologyMapOfSubset hBD R n =
      homologyMapOfSubset (hAB.trans hBD) R n := by
  rw [homologyMapOfSubset, homologyMapOfSubset,
    homologyMapOfSubset, ← HomologicalComplex.homologyMap_comp]
  dsimp only [Hatcher.Excision.singularChainMap]
  rw [← Functor.map_comp]
  congr 1

@[reassoc]
theorem homologyMapOfSubset_comp_toAmbient {A B : Set X}
    (hAB : A ⊆ B) (R : C) (n : ℕ) :
    homologyMapOfSubset hAB R n ≫ homologyMapToAmbient B R n =
      homologyMapToAmbient A R n := by
  rw [homologyMapOfSubset, homologyMapToAmbient,
    homologyMapToAmbient, ← HomologicalComplex.homologyMap_comp]
  dsimp only [Hatcher.Excision.singularChainMap]
  rw [← Functor.map_comp]
  congr 1

/- The explicit transparency settings below let rewriting see through the
definitionally equal presentations of singular homology used by Mathlib's
functor API and by the Mayer--Vietoris chain-complex API. -/

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the signed intersection map under inclusions of both
subspaces. -/
@[reassoc]
theorem homologyMapOfSubset_comp_intersectionMap
    {A B U V : Set X} (hA : A ⊆ U) (hB : B ⊆ V)
    (R : C) (n : ℕ) :
    homologyMapOfSubset (intersectionSubset hA hB) R n ≫
        intersectionMap U V R n =
      intersectionMap A B R n ≫
        biprod.map (homologyMapOfSubset hA R n)
          (homologyMapOfSubset hB R n) := by
  apply biprod.hom_ext
  · rw [Category.assoc]
    rw [Category.assoc, biprod.map_fst]
    rw [intersectionMap, biprod.lift_fst]
    rw [intersectionMap, biprod.lift_fst_assoc]
    change
      homologyMapOfSubset (intersectionSubset hA hB) R n ≫
          homologyMapOfSubset Set.inter_subset_left R n =
        homologyMapOfSubset Set.inter_subset_left R n ≫
          homologyMapOfSubset hA R n
    rw [homologyMapOfSubset_comp, homologyMapOfSubset_comp]
  · rw [Category.assoc]
    rw [Category.assoc, biprod.map_snd]
    rw [intersectionMap, biprod.lift_snd]
    rw [intersectionMap, biprod.lift_snd_assoc]
    simp only [Preadditive.comp_neg, Preadditive.neg_comp]
    congr 1
    change
      homologyMapOfSubset (intersectionSubset hA hB) R n ≫
          homologyMapOfSubset Set.inter_subset_right R n =
        homologyMapOfSubset Set.inter_subset_right R n ≫
          homologyMapOfSubset hB R n
    rw [homologyMapOfSubset_comp, homologyMapOfSubset_comp]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the addition map under inclusions of both subspaces. -/
@[reassoc]
theorem biprodMap_comp_unionMap
    {A B U V : Set X} (hA : A ⊆ U) (hB : B ⊆ V)
    (R : C) (n : ℕ) :
    biprod.map (homologyMapOfSubset hA R n)
          (homologyMapOfSubset hB R n) ≫
        unionMap U V R n =
      unionMap A B R n := by
  apply biprod.hom_ext'
  · rw [biprod.inl_map_assoc]
    rw [unionMap, biprod.inl_desc]
    rw [unionMap, biprod.inl_desc]
    change homologyMapOfSubset hA R n ≫
        homologyMapToAmbient U R n = homologyMapToAmbient A R n
    exact homologyMapOfSubset_comp_toAmbient hA R n
  · rw [biprod.inr_map_assoc]
    rw [unionMap, biprod.inr_desc]
    rw [unionMap, biprod.inr_desc]
    change homologyMapOfSubset hB R n ≫
        homologyMapToAmbient V R n = homologyMapToAmbient B R n
    exact homologyMapOfSubset_comp_toAmbient hB R n

/-- A cover by subspaces which strongly deformation retract from an
interior cover by neighborhoods. -/
structure NeighborhoodCover (A B : Set X) where
  /-- A neighborhood of `A`. -/
  U : Set X
  /-- A neighborhood of `B`. -/
  V : Set X
  /-- The original subspaces cover the ambient space. -/
  union_eq_univ : A ∪ B = Set.univ
  /-- `A` lies in the interior of its neighborhood. -/
  left_subset_interior : A ⊆ interior U
  /-- `B` lies in the interior of its neighborhood. -/
  right_subset_interior : B ⊆ interior V
  /-- The neighborhood `U` strongly deformation retracts onto `A` along the
  canonical subtype inclusion. -/
  leftRetract : Hatcher.StrongDeformationRetract
    (inclusionOfSubset (left_subset_interior.trans interior_subset))
  /-- The neighborhood `V` strongly deformation retracts onto `B` along the
  canonical subtype inclusion. -/
  rightRetract : Hatcher.StrongDeformationRetract
    (inclusionOfSubset (right_subset_interior.trans interior_subset))
  /-- The neighborhood intersection strongly deformation retracts onto the
  original intersection along the canonical subtype inclusion. -/
  intersectionRetract : Hatcher.StrongDeformationRetract
    (inclusionOfSubset
      (intersectionSubset
        (left_subset_interior.trans interior_subset)
        (right_subset_interior.trans interior_subset)))

namespace NeighborhoodCover

variable {A B : Set X} (h : NeighborhoodCover A B)

/-- The canonical inclusion `A → U`. -/
def leftInclusion : C(A, h.U) :=
  inclusionOfSubset (h.left_subset_interior.trans interior_subset)

/-- The canonical inclusion `B → V`. -/
def rightInclusion : C(B, h.V) :=
  inclusionOfSubset (h.right_subset_interior.trans interior_subset)

/-- The canonical inclusion `A ∩ B → U ∩ V`. -/
def intersectionInclusion : C(↑(A ∩ B), ↑(h.U ∩ h.V)) :=
  inclusionOfSubset
    (intersectionSubset
      (h.left_subset_interior.trans interior_subset)
      (h.right_subset_interior.trans interior_subset))

/-- The neighborhoods form an interior cover. -/
theorem coverCondition : Hatcher.Excision.CoverCondition h.U h.V where
  union_interior := by
    ext x
    simp only [Set.mem_union, Set.mem_univ, iff_true]
    have hx : x ∈ A ∪ B := by
      rw [h.union_eq_univ]
      exact Set.mem_univ x
    rcases hx with hx | hx
    · exact Or.inl (h.left_subset_interior hx)
    · exact Or.inr (h.right_subset_interior hx)

/-- The homology isomorphism induced by the actual inclusion `A → U`. -/
noncomputable def leftHomologyIso (R : C) (n : ℕ) :
    (Hatcher.Excision.singularChains (TopCat.of A) R).homology n ≅
      (Hatcher.Excision.singularChains (TopCat.of h.U) R).homology n :=
  Hatcher.Singular.homologyIsoOfHomotopyEquiv
    h.leftRetract.toHomotopyEquiv.symm R n

/-- The homology isomorphism induced by the actual inclusion `B → V`. -/
noncomputable def rightHomologyIso (R : C) (n : ℕ) :
    (Hatcher.Excision.singularChains (TopCat.of B) R).homology n ≅
      (Hatcher.Excision.singularChains (TopCat.of h.V) R).homology n :=
  Hatcher.Singular.homologyIsoOfHomotopyEquiv
    h.rightRetract.toHomotopyEquiv.symm R n

/-- The homology isomorphism induced by the actual inclusion
`A ∩ B → U ∩ V`. -/
noncomputable def intersectionHomologyIso (R : C) (n : ℕ) :
    (Hatcher.Excision.singularChains (TopCat.of ↑(A ∩ B)) R).homology n ≅
      (Hatcher.Excision.singularChains (TopCat.of ↑(h.U ∩ h.V)) R).homology n :=
  Hatcher.Singular.homologyIsoOfHomotopyEquiv
    h.intersectionRetract.toHomotopyEquiv.symm R n

@[simp]
theorem leftHomologyIso_hom (R : C) (n : ℕ) :
    (h.leftHomologyIso R n).hom =
      homologyMapOfSubset
        (h.left_subset_interior.trans interior_subset) R n :=
  rfl

@[simp]
theorem rightHomologyIso_hom (R : C) (n : ℕ) :
    (h.rightHomologyIso R n).hom =
      homologyMapOfSubset
        (h.right_subset_interior.trans interior_subset) R n :=
  rfl

@[simp]
theorem intersectionHomologyIso_hom (R : C) (n : ℕ) :
    (h.intersectionHomologyIso R n).hom =
      homologyMapOfSubset
        (intersectionSubset
          (h.left_subset_interior.trans interior_subset)
          (h.right_subset_interior.trans interior_subset)) R n :=
  rfl

end NeighborhoodCover

/-- The connecting morphism for a neighborhood-retract cover, transported
from the interior-cover connecting morphism. -/
noncomputable def neighborhoodConnecting {A B : Set X}
    (h : NeighborhoodCover A B) (R : C) (n m : ℕ)
    (hnm : m + 1 = n) :
    (Hatcher.Excision.singularChains X R).homology n ⟶
      (Hatcher.Excision.singularChains (TopCat.of ↑(A ∩ B)) R).homology m :=
  connecting h.coverCondition R n m hnm ≫
    (h.intersectionHomologyIso R m).inv

/-- Six consecutive terms in the ordinary Mayer--Vietoris sequence for
subspaces which strongly deformation retract from an interior cover by
neighborhoods. -/
noncomputable def neighborhoodSequence {A B : Set X}
    (h : NeighborhoodCover A B) (R : C) (n m : ℕ)
    (hnm : m + 1 = n) : ComposableArrows C 5 :=
  ComposableArrows.mk₅
    (intersectionMap A B R n)
    (unionMap A B R n)
    (neighborhoodConnecting h R n m hnm)
    (intersectionMap A B R m)
    (unionMap A B R m)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def neighborhoodSequenceIso {A B : Set X}
    (h : NeighborhoodCover A B) (R : C) (n m : ℕ)
    (hnm : m + 1 = n) :
    neighborhoodSequence h R n m hnm ≅
      sequence h.coverCondition R n m hnm :=
  ComposableArrows.isoMk₅
    (h.intersectionHomologyIso R n)
    (biprod.mapIso (h.leftHomologyIso R n) (h.rightHomologyIso R n))
    (Iso.refl _)
    (h.intersectionHomologyIso R m)
    (biprod.mapIso (h.leftHomologyIso R m) (h.rightHomologyIso R m))
    (Iso.refl _)
    (by
      change
        intersectionMap A B R n ≫
            biprod.map
              (homologyMapOfSubset
                (h.left_subset_interior.trans interior_subset) R n)
              (homologyMapOfSubset
                (h.right_subset_interior.trans interior_subset) R n) =
          homologyMapOfSubset
              (intersectionSubset
                (h.left_subset_interior.trans interior_subset)
                (h.right_subset_interior.trans interior_subset)) R n ≫
            intersectionMap h.U h.V R n
      exact (homologyMapOfSubset_comp_intersectionMap
          (h.left_subset_interior.trans interior_subset)
          (h.right_subset_interior.trans interior_subset) R n).symm)
    (by
      simpa [neighborhoodSequence, sequence] using
        (biprodMap_comp_unionMap
          (h.left_subset_interior.trans interior_subset)
          (h.right_subset_interior.trans interior_subset) R n).symm)
    (by
      simp [neighborhoodSequence, sequence, neighborhoodConnecting]
      rw [← h.intersectionHomologyIso_hom R m]
      rw [Iso.inv_hom_id, Category.comp_id])
    (by
      change
        intersectionMap A B R m ≫
            biprod.map
              (homologyMapOfSubset
                (h.left_subset_interior.trans interior_subset) R m)
              (homologyMapOfSubset
                (h.right_subset_interior.trans interior_subset) R m) =
          homologyMapOfSubset
              (intersectionSubset
                (h.left_subset_interior.trans interior_subset)
                (h.right_subset_interior.trans interior_subset)) R m ≫
            intersectionMap h.U h.V R m
      exact (homologyMapOfSubset_comp_intersectionMap
          (h.left_subset_interior.trans interior_subset)
          (h.right_subset_interior.trans interior_subset) R m).symm)
    (by
      simpa [neighborhoodSequence, sequence] using
        (biprodMap_comp_unionMap
          (h.left_subset_interior.trans interior_subset)
          (h.right_subset_interior.trans interior_subset) R m).symm)

/-- **Hatcher, §2.2, page 150.** Every adjacent-degree six-term window in
the ordinary Mayer--Vietoris sequence for a neighborhood deformation-retract
cover is exact. The first and second maps are induced by the actual
inclusions of `A ∩ B`, `A`, and `B`. -/
theorem neighborhoodSequence_exact {A B : Set X}
    (h : NeighborhoodCover A B) (R : C) (n m : ℕ)
    (hnm : m + 1 = n) :
    (neighborhoodSequence h R n m hnm).Exact := by
  apply ComposableArrows.exact_of_iso
    (neighborhoodSequenceIso h R n m hnm).symm
  exact sequence_exact h.coverCondition R n m hnm

/-- The degree-zero addition map for a neighborhood deformation-retract cover
is an epimorphism. -/
theorem neighborhoodUnionMap_zero_epi {A B : Set X}
    (h : NeighborhoodCover A B) (R : C) :
    Epi (unionMap A B R 0) := by
  rw [← biprodMap_comp_unionMap
    (h.left_subset_interior.trans interior_subset)
    (h.right_subset_interior.trans interior_subset) R 0]
  change Epi
    ((biprod.mapIso (h.leftHomologyIso R 0)
      (h.rightHomologyIso R 0)).hom ≫ unionMap h.U h.V R 0)
  exact epi_comp'
    (inferInstance : Epi
      (biprod.mapIso (h.leftHomologyIso R 0)
        (h.rightHomologyIso R 0)).hom)
    (unionMap_zero_epi h.coverCondition R)

end Hatcher.MayerVietoris
