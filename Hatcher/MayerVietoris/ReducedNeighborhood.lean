/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Hatcher.MayerVietoris.Neighborhood
import Hatcher.MayerVietoris.ReducedSequence

/-!
# Reduced Mayer--Vietoris for neighborhood deformation retracts

This file transports the reduced binary-cover Mayer--Vietoris sequence from
neighborhoods to strong deformation retracts.  Its displayed maps remain the
maps induced by the actual inclusions of the original subspaces.
-/

noncomputable section

open AlgebraicTopology CategoryTheory Limits ZeroObject Topology

attribute [local instance] preservesBinaryBiproduct_of_preservesBiproduct

namespace Hatcher.MayerVietoris

universe w v u

variable {X : TopCat.{w}}
variable {C : Type u} [Category.{v} C] [Abelian C]
  [HasCoproducts.{w} C]

local instance reducedNeighborhoodHasFiniteCoproducts :
    HasFiniteCoproducts C :=
  hasFiniteCoproducts_of_hasCoproducts C

local instance reducedNeighborhoodHasBinaryBiproducts :
    HasBinaryBiproducts C :=
  HasBinaryBiproducts.of_hasBinaryCoproducts

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the signed reduced intersection map under inclusions of
both subspaces. -/
@[reassoc]
theorem reducedHomologyMapOfSubset_comp_reducedIntersectionMap
    {A B U V : Set X} (hA : A ⊆ U) (hB : B ⊆ V)
    (R : C) (n : ℕ) :
    reducedHomologyMapOfSubset (intersectionSubset hA hB) R n ≫
        reducedIntersectionMap U V R n =
      reducedIntersectionMap A B R n ≫
        biprod.map (reducedHomologyMapOfSubset hA R n)
          (reducedHomologyMapOfSubset hB R n) := by
  apply biprod.hom_ext
  · rw [Category.assoc]
    rw [Category.assoc, biprod.map_fst]
    rw [reducedIntersectionMap_eq, biprod.lift_fst]
    rw [reducedIntersectionMap_eq, biprod.lift_fst_assoc]
    rw [reducedHomologyMapOfSubset_comp,
      reducedHomologyMapOfSubset_comp]
  · rw [Category.assoc]
    rw [Category.assoc, biprod.map_snd]
    rw [reducedIntersectionMap_eq, biprod.lift_snd]
    rw [reducedIntersectionMap_eq, biprod.lift_snd_assoc]
    simp only [Preadditive.comp_neg, Preadditive.neg_comp]
    congr 1
    rw [reducedHomologyMapOfSubset_comp,
      reducedHomologyMapOfSubset_comp]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the reduced codiagonal map under inclusions of both
subspaces. -/
@[reassoc]
theorem biprodMap_comp_reducedUnionMap
    {A B U V : Set X} (hA : A ⊆ U) (hB : B ⊆ V)
    (R : C) (n : ℕ) :
    biprod.map (reducedHomologyMapOfSubset hA R n)
          (reducedHomologyMapOfSubset hB R n) ≫
        reducedUnionMap U V R n =
      reducedUnionMap A B R n := by
  apply biprod.hom_ext'
  · rw [biprod.inl_map_assoc]
    rw [reducedUnionMap_eq, biprod.inl_desc]
    rw [reducedUnionMap_eq, biprod.inl_desc]
    exact reducedHomologyMapOfSubset_comp_toAmbient hA R n
  · rw [biprod.inr_map_assoc]
    rw [reducedUnionMap_eq, biprod.inr_desc]
    rw [reducedUnionMap_eq, biprod.inr_desc]
    exact reducedHomologyMapOfSubset_comp_toAmbient hB R n

namespace NeighborhoodCover

variable {A B : Set X} (h : NeighborhoodCover A B)

/-- The reduced-homology isomorphism induced by the actual inclusion
`A → U`. -/
noncomputable def leftReducedHomologyIso (R : C) (n : ℕ) :
    (Hatcher.Reduced.homologyFunctor R n).obj (TopCat.of A) ≅
      (Hatcher.Reduced.homologyFunctor R n).obj (TopCat.of h.U) :=
  Hatcher.Reduced.homologyIsoOfHomotopyEquiv
    h.leftRetract.toHomotopyEquiv.symm R n

/-- The reduced-homology isomorphism induced by the actual inclusion
`B → V`. -/
noncomputable def rightReducedHomologyIso (R : C) (n : ℕ) :
    (Hatcher.Reduced.homologyFunctor R n).obj (TopCat.of B) ≅
      (Hatcher.Reduced.homologyFunctor R n).obj (TopCat.of h.V) :=
  Hatcher.Reduced.homologyIsoOfHomotopyEquiv
    h.rightRetract.toHomotopyEquiv.symm R n

/-- The reduced-homology isomorphism induced by the actual inclusion
`A ∩ B → U ∩ V`. -/
noncomputable def intersectionReducedHomologyIso (R : C) (n : ℕ) :
    (Hatcher.Reduced.homologyFunctor R n).obj (TopCat.of ↥(A ∩ B)) ≅
      (Hatcher.Reduced.homologyFunctor R n).obj
        (TopCat.of ↥(h.U ∩ h.V)) :=
  Hatcher.Reduced.homologyIsoOfHomotopyEquiv
    h.intersectionRetract.toHomotopyEquiv.symm R n

@[simp]
theorem leftReducedHomologyIso_hom (R : C) (n : ℕ) :
    (h.leftReducedHomologyIso R n).hom =
      reducedHomologyMapOfSubset
        (h.left_subset_interior.trans interior_subset) R n :=
  rfl

@[simp]
theorem rightReducedHomologyIso_hom (R : C) (n : ℕ) :
    (h.rightReducedHomologyIso R n).hom =
      reducedHomologyMapOfSubset
        (h.right_subset_interior.trans interior_subset) R n :=
  rfl

@[simp]
theorem intersectionReducedHomologyIso_hom (R : C) (n : ℕ) :
    (h.intersectionReducedHomologyIso R n).hom =
      reducedHomologyMapOfSubset
        (intersectionSubset
          (h.left_subset_interior.trans interior_subset)
          (h.right_subset_interior.trans interior_subset)) R n :=
  rfl

end NeighborhoodCover

/-- The reduced connecting morphism for a neighborhood-retract cover,
transported from the interior-cover connecting morphism. -/
noncomputable def reducedNeighborhoodConnecting {A B : Set X}
    (h : NeighborhoodCover A B) (R : C) (n m : ℕ)
    (hnm : m + 1 = n) :
    (Hatcher.Reduced.homologyFunctor R n).obj X ⟶
      (Hatcher.Reduced.homologyFunctor R m).obj (TopCat.of ↥(A ∩ B)) :=
  reducedConnecting h.coverCondition R n m hnm ≫
    (h.intersectionReducedHomologyIso R m).inv

/-- Six consecutive terms in the reduced Mayer--Vietoris sequence for
subspaces which strongly deformation retract from an interior cover. -/
noncomputable def reducedNeighborhoodSequence {A B : Set X}
    (h : NeighborhoodCover A B) (R : C) (n m : ℕ)
    (hnm : m + 1 = n) : ComposableArrows C 5 :=
  ComposableArrows.mk₅
    (reducedIntersectionMap A B R n)
    (reducedUnionMap A B R n)
    (reducedNeighborhoodConnecting h R n m hnm)
    (reducedIntersectionMap A B R m)
    (reducedUnionMap A B R m)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def reducedNeighborhoodSequenceIso {A B : Set X}
    (h : NeighborhoodCover A B) (R : C) (n m : ℕ)
    (hnm : m + 1 = n) :
    reducedNeighborhoodSequence h R n m hnm ≅
      reducedSequence h.coverCondition R n m hnm :=
  ComposableArrows.isoMk₅
    (h.intersectionReducedHomologyIso R n)
    (biprod.mapIso (h.leftReducedHomologyIso R n)
      (h.rightReducedHomologyIso R n))
    (Iso.refl _)
    (h.intersectionReducedHomologyIso R m)
    (biprod.mapIso (h.leftReducedHomologyIso R m)
      (h.rightReducedHomologyIso R m))
    (Iso.refl _)
    (by
      change
        reducedIntersectionMap A B R n ≫
            biprod.map
              (reducedHomologyMapOfSubset
                (h.left_subset_interior.trans interior_subset) R n)
              (reducedHomologyMapOfSubset
                (h.right_subset_interior.trans interior_subset) R n) =
          reducedHomologyMapOfSubset
              (intersectionSubset
                (h.left_subset_interior.trans interior_subset)
                (h.right_subset_interior.trans interior_subset)) R n ≫
            reducedIntersectionMap h.U h.V R n
      exact (reducedHomologyMapOfSubset_comp_reducedIntersectionMap
        (h.left_subset_interior.trans interior_subset)
        (h.right_subset_interior.trans interior_subset) R n).symm)
    (by
      simpa [reducedNeighborhoodSequence, reducedSequence] using
        (biprodMap_comp_reducedUnionMap
          (h.left_subset_interior.trans interior_subset)
          (h.right_subset_interior.trans interior_subset) R n).symm)
    (by
      simp [reducedNeighborhoodSequence, reducedSequence]
      rw [reducedNeighborhoodConnecting, Category.assoc]
      rw [← h.intersectionReducedHomologyIso_hom R m]
      rw [Iso.inv_hom_id, Category.comp_id])
    (by
      change
        reducedIntersectionMap A B R m ≫
            biprod.map
              (reducedHomologyMapOfSubset
                (h.left_subset_interior.trans interior_subset) R m)
              (reducedHomologyMapOfSubset
                (h.right_subset_interior.trans interior_subset) R m) =
          reducedHomologyMapOfSubset
              (intersectionSubset
                (h.left_subset_interior.trans interior_subset)
                (h.right_subset_interior.trans interior_subset)) R m ≫
            reducedIntersectionMap h.U h.V R m
      exact (reducedHomologyMapOfSubset_comp_reducedIntersectionMap
        (h.left_subset_interior.trans interior_subset)
        (h.right_subset_interior.trans interior_subset) R m).symm)
    (by
      simpa [reducedNeighborhoodSequence, reducedSequence] using
        (biprodMap_comp_reducedUnionMap
          (h.left_subset_interior.trans interior_subset)
          (h.right_subset_interior.trans interior_subset) R m).symm)

/-- Every adjacent-degree six-term window in the reduced
Mayer--Vietoris sequence for a neighborhood deformation-retract cover is
exact. -/
theorem reducedNeighborhoodSequence_exact {A B : Set X}
    (h : NeighborhoodCover A B) (R : C) (n m : ℕ)
    (hnm : m + 1 = n) :
    (reducedNeighborhoodSequence h R n m hnm).Exact := by
  apply ComposableArrows.exact_of_iso
    (reducedNeighborhoodSequenceIso h R n m hnm).symm
  exact reducedSequence_exact h.coverCondition R n m hnm

/-- The terminal degree-zero reduced Mayer--Vietoris sequence for a
neighborhood deformation-retract cover. -/
noncomputable def reducedNeighborhoodZeroSequence {A B : Set X}
    (_h : NeighborhoodCover A B) (R : C) : ComposableArrows C 3 :=
  ComposableArrows.mk₃
    (reducedIntersectionMap A B R 0)
    (reducedUnionMap A B R 0)
    (0 : (Hatcher.Reduced.homologyFunctor R 0).obj X ⟶ (0 : C))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def reducedNeighborhoodZeroSequenceIso
    {A B : Set X} (h : NeighborhoodCover A B) (R : C) :
    reducedNeighborhoodZeroSequence h R ≅
      reducedZeroSequence h.U h.V R :=
  ComposableArrows.isoMk₃
    (h.intersectionReducedHomologyIso R 0)
    (biprod.mapIso (h.leftReducedHomologyIso R 0)
      (h.rightReducedHomologyIso R 0))
    (Iso.refl _)
    (Iso.refl _)
    (by
      change
        reducedIntersectionMap A B R 0 ≫
            biprod.map
              (reducedHomologyMapOfSubset
                (h.left_subset_interior.trans interior_subset) R 0)
              (reducedHomologyMapOfSubset
                (h.right_subset_interior.trans interior_subset) R 0) =
          reducedHomologyMapOfSubset
              (intersectionSubset
                (h.left_subset_interior.trans interior_subset)
                (h.right_subset_interior.trans interior_subset)) R 0 ≫
            reducedIntersectionMap h.U h.V R 0
      exact (reducedHomologyMapOfSubset_comp_reducedIntersectionMap
        (h.left_subset_interior.trans interior_subset)
        (h.right_subset_interior.trans interior_subset) R 0).symm)
    (by
      simpa [reducedNeighborhoodZeroSequence, reducedZeroSequence] using
        (biprodMap_comp_reducedUnionMap
          (h.left_subset_interior.trans interior_subset)
          (h.right_subset_interior.trans interior_subset) R 0).symm)
    (by simp [reducedNeighborhoodZeroSequence, reducedZeroSequence])

/-- If the original intersection is nonempty, the terminal sequence
`H̃₀(A ∩ B) ⟶ H̃₀(A) ⊞ H̃₀(B) ⟶ H̃₀(X) ⟶ 0`
for a neighborhood deformation-retract cover is exact. -/
theorem reducedNeighborhoodZeroSequence_exact {A B : Set X}
    (h : NeighborhoodCover A B) (R : C)
    (hAB : Nonempty ↑(A ∩ B)) :
    (reducedNeighborhoodZeroSequence h R).Exact := by
  apply ComposableArrows.exact_of_iso
    (reducedNeighborhoodZeroSequenceIso h R).symm
  exact reducedZeroSequence_exact h.coverCondition R
    (Nonempty.map h.intersectionInclusion hAB)

/-- **Hatcher, §2.2 (page 150).** The reduced Mayer--Vietoris sequence
for a neighborhood deformation-retract cover is exact in every adjacent
degree window and, when the original intersection is nonempty, at its
terminal degree-zero end.  The displayed maps are induced by the actual
subspace inclusions. -/
theorem reducedNeighborhoodLongExact {A B : Set X}
    (h : NeighborhoodCover A B) (R : C)
    (hAB : Nonempty ↑(A ∩ B)) :
    (∀ (n m : ℕ) (hnm : m + 1 = n),
      (reducedNeighborhoodSequence h R n m hnm).Exact) ∧
      (reducedNeighborhoodZeroSequence h R).Exact := by
  exact ⟨fun n m hnm ↦
    reducedNeighborhoodSequence_exact h R n m hnm,
    reducedNeighborhoodZeroSequence_exact h R hAB⟩

end Hatcher.MayerVietoris
