/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Hatcher.Appendix.RegularNeighborhoodDeformation

/-!
# Compatible neighborhoods for a cover by CW subcomplexes

The common fixed-width regular-neighborhood construction turns a cover of a
classical CW complex by two subcomplexes into a compatible neighborhood cover.
Besides the two deformation retractions, this file retains the literal
intersection of the two neighborhoods as the target of the intersection
deformation retraction.  This includes the case of disjoint subcomplexes: the
common neighborhood is then empty.
-/

noncomputable section

open Set Topology

namespace Hatcher.ClassicalCW

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X]
variable (C : Set X) [CWComplex C]

/-- The canonical inclusion of the intersection of two subcomplexes into the
literal intersection of their fixed-width regular neighborhoods. -/
def regularNeighborhoodIntersectionInclusion
    (A B : CWComplex.Subcomplex C) :
    C(↑(Subcomplex.inter A B : Set X),
      ↑(regularNeighborhood C A ∩ regularNeighborhood C B)) where
  toFun x := ⟨x.1,
    subcomplex_subset_regularNeighborhood C A x.2.1,
    subcomplex_subset_regularNeighborhood C B x.2.2⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

/-- Transport a strong deformation retract across a homeomorphism of its
ambient target while keeping the retract fixed. -/
private def strongDeformationRetractOfTargetHomeomorph
    {A Y Z : Type u}
    [TopologicalSpace A] [TopologicalSpace Y] [TopologicalSpace Z]
    (i : C(A, Y)) (j : C(A, Z)) (h : Y ≃ₜ Z)
    (square : ∀ a, h (i a) = j a)
    (sdr : Hatcher.StrongDeformationRetract j) :
    Hatcher.StrongDeformationRetract i where
  retract :=
    ⟨fun y ↦ sdr.retract (h y),
      sdr.retract.continuous.comp h.continuous⟩
  retract_inclusion := by
    ext a
    change sdr.retract (h (i a)) = a
    rw [square]
    have hs := congrArg (fun g : C(A, A) ↦ g a)
      sdr.retract_inclusion
    simpa only [ContinuousMap.comp_apply, ContinuousMap.id_apply]
      using hs
  deformation := {
    toFun := fun p ↦ h.symm (sdr.deformation (p.1, h p.2))
    continuous_toFun := h.symm.continuous.comp
      (sdr.deformation.continuous.comp
        (continuous_fst.prodMk (h.continuous.comp continuous_snd)))
    map_zero_left := by
      intro y
      change h.symm (sdr.deformation (0, h y)) = y
      rw [sdr.deformation.apply_zero]
      exact h.symm_apply_apply y
    map_one_left := by
      intro y
      change h.symm (sdr.deformation (1, h y)) =
        i (sdr.retract (h y))
      rw [sdr.deformation.apply_one]
      simp only [ContinuousMap.comp_apply]
      apply h.injective
      rw [h.apply_symm_apply, square]
    prop' := by
      intro t y hy
      rcases hy with ⟨a, rfl⟩
      change h.symm (sdr.deformation (t, h (i a))) = i a
      apply h.injective
      rw [h.apply_symm_apply, square]
      exact sdr.deformation.eq_fst t ⟨a, rfl⟩ }

/-- The exact intersection law transports the regular-neighborhood
deformation onto the literal intersection of the two neighborhoods. -/
def regularNeighborhoodIntersectionStrongDeformationRetract
    (A B : CWComplex.Subcomplex C) :
    Hatcher.StrongDeformationRetract
      (regularNeighborhoodIntersectionInclusion C A B) :=
  strongDeformationRetractOfTargetHomeomorph
    (regularNeighborhoodIntersectionInclusion C A B)
    (regularNeighborhoodInclusion C (Subcomplex.inter A B))
    (Homeomorph.setCongr (regularNeighborhood_inter C A B).symm)
    (fun _ ↦ by
      apply Subtype.ext
      rfl)
    (regularNeighborhoodStrongDeformationRetract C
      (Subcomplex.inter A B))

/-- The topology-only data supplied by compatible regular neighborhoods of
two subcomplexes covering a classical CW complex. -/
structure SubcomplexNeighborhoodCover
    (A B : CWComplex.Subcomplex C) : Prop where
  /-- The two original subcomplexes cover the ambient CW complex. -/
  carrier_union_eq : (A : Set X) ∪ (B : Set X) = C
  /-- The left regular neighborhood remains in the ambient CW complex. -/
  leftNeighborhood_subset_complex : regularNeighborhood C A ⊆ C
  /-- The right regular neighborhood remains in the ambient CW complex. -/
  rightNeighborhood_subset_complex : regularNeighborhood C B ⊆ C
  /-- The two regular neighborhoods cover exactly the ambient CW complex. -/
  neighborhood_union_eq :
    regularNeighborhood C A ∪ regularNeighborhood C B = C
  /-- The left neighborhood is open relative to the ambient CW complex. -/
  isOpen_leftNeighborhood :
    IsOpen (((↑) : ↑C → X) ⁻¹' regularNeighborhood C A)
  /-- The right neighborhood is open relative to the ambient CW complex. -/
  isOpen_rightNeighborhood :
    IsOpen (((↑) : ↑C → X) ⁻¹' regularNeighborhood C B)
  /-- The left carrier lies in the relative interior of its neighborhood. -/
  leftCarrier_subset_interior :
    (((↑) : ↑C → X) ⁻¹' (A : Set X)) ⊆
      interior (((↑) : ↑C → X) ⁻¹' regularNeighborhood C A)
  /-- The right carrier lies in the relative interior of its neighborhood. -/
  rightCarrier_subset_interior :
    (((↑) : ↑C → X) ⁻¹' (B : Set X)) ⊆
      interior (((↑) : ↑C → X) ⁻¹' regularNeighborhood C B)
  /-- The left neighborhood strongly deformation retracts onto its carrier. -/
  leftRetract : Nonempty (Hatcher.StrongDeformationRetract
    (regularNeighborhoodInclusion C A))
  /-- The right neighborhood strongly deformation retracts onto its carrier. -/
  rightRetract : Nonempty (Hatcher.StrongDeformationRetract
    (regularNeighborhoodInclusion C B))
  /-- The literal neighborhood intersection is the regular neighborhood of
  the subcomplex intersection. -/
  intersection_eq :
    regularNeighborhood C A ∩ regularNeighborhood C B =
      regularNeighborhood C (Subcomplex.inter A B)
  /-- The literal neighborhood intersection strongly deformation retracts
  onto the subcomplex intersection. -/
  intersectionRetract : Nonempty (Hatcher.StrongDeformationRetract
    (regularNeighborhoodIntersectionInclusion C A B))
  /-- If the two subcomplexes are disjoint, their common regular neighborhood
  is empty as well. -/
  intersection_eq_empty_of_carrier_inter_eq_empty :
    (A : Set X) ∩ (B : Set X) = ∅ →
      regularNeighborhood C A ∩ regularNeighborhood C B = ∅

/-- **Hatcher, Appendix Proposition A.5 and the following intersection
observation.** Two subcomplexes covering a classical CW complex have
compatible fixed-width regular neighborhoods, including when their
intersection is empty. -/
theorem subcomplexNeighborhoodCover
    (A B : CWComplex.Subcomplex C)
    (hcover : (A : Set X) ∪ (B : Set X) = C) :
    SubcomplexNeighborhoodCover C A B := by
  let N := regularNeighborhoodSystem C
  refine {
    carrier_union_eq := hcover
    leftNeighborhood_subset_complex := N.neighborhood_subset_complex A
    rightNeighborhood_subset_complex := N.neighborhood_subset_complex B
    neighborhood_union_eq := ?_
    isOpen_leftNeighborhood := N.isOpen_neighborhood A
    isOpen_rightNeighborhood := N.isOpen_neighborhood B
    leftCarrier_subset_interior := N.carrier_subset_interior A
    rightCarrier_subset_interior := N.carrier_subset_interior B
    leftRetract := ⟨regularNeighborhoodStrongDeformationRetract C A⟩
    rightRetract := ⟨regularNeighborhoodStrongDeformationRetract C B⟩
    intersection_eq := (N.neighborhood_inter A B).symm
    intersectionRetract := ?_
    intersection_eq_empty_of_carrier_inter_eq_empty := ?_ }
  · apply Set.Subset.antisymm
    · exact union_subset
        (N.neighborhood_subset_complex A)
        (N.neighborhood_subset_complex B)
    · intro x hxC
      have hx : x ∈ (A : Set X) ∪ (B : Set X) := by
        rw [hcover]
        exact hxC
      rcases hx with hxA | hxB
      · exact Or.inl (N.carrier_subset_neighborhood A hxA)
      · exact Or.inr (N.carrier_subset_neighborhood B hxB)
  · exact ⟨regularNeighborhoodIntersectionStrongDeformationRetract C A B⟩
  · intro hinter
    rw [← regularNeighborhood_inter C A B]
    apply regularNeighborhood_eq_empty_of_subcomplex_eq_empty C
      (Subcomplex.inter A B)
    simpa only [Subcomplex.coe_inter] using hinter

end Hatcher.ClassicalCW
