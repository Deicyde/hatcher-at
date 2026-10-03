/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Hatcher.Singular.GoodPairNeighborhoodQuotient
import Mathlib.Topology.CompactOpen

/-!
# Contraction of point-quotient neighborhoods

The chosen strong deformation retraction of a good-pair neighborhood descends
through its restricted point-quotient projection.  This contracts the quotient
neighborhood onto the collapsed point without assuming that the original
neighborhood is open.
-/

noncomputable section

open CategoryTheory Set Topology
open scoped unitInterval

namespace Hatcher.Relative

universe w

namespace GoodPairData

variable {P : TopPair.{w}}

private abbrev neighborhoodInclusion (h : GoodPairData P) :=
  goodPairNeighborhoodInclusion P h.V
    (h.range_subset_interior.trans interior_subset)

private lemma neighborhoodProjection_inclusion (h : GoodPairData P)
    (a : P.snd) :
    h.pointQuotientNeighborhoodProjection (neighborhoodInclusion h a) =
      h.pointQuotientNeighborhoodInclusion PUnit.unit := by
  apply Subtype.ext
  change pointQuotientProjection P (P.map a) = pointQuotientPoint P
  have ha : P.map a ∈ pointQuotientProjection P ⁻¹'
      ({pointQuotientPoint P} : Set (pointQuotient P)) := by
    rw [pointQuotientProjection_preimage_point]
    exact Set.mem_range_self a
  simpa only [Set.mem_preimage, Set.mem_singleton_iff] using ha

private lemma deformation_fixed_of_mem_range (h : GoodPairData P)
    (t : unitInterval) (x : h.V) (hx : x.1 ∈ Set.range P.map) :
    h.strongDeformationRetract.deformation (t, x) = x := by
  obtain ⟨a, ha⟩ := hx
  apply h.strongDeformationRetract.deformation.eq_fst
  refine ⟨a, ?_⟩
  apply Subtype.ext
  exact ha

private lemma deformation_projection_eq_of_projection_eq
    (h : GoodPairData P) (t : unitInterval) {x y : h.V}
    (hxy : h.pointQuotientNeighborhoodProjection x =
      h.pointQuotientNeighborhoodProjection y) :
    h.pointQuotientNeighborhoodProjection
        (h.strongDeformationRetract.deformation (t, x)) =
      h.pointQuotientNeighborhoodProjection
        (h.strongDeformationRetract.deformation (t, y)) := by
  let _ : Nonempty P.snd := h.nonempty
  have hxy' : pointQuotientProjection P x.1 =
      pointQuotientProjection P y.1 := by
    simpa only [pointQuotientNeighborhoodProjection_apply] using
      congrArg Subtype.val hxy
  by_cases hxA : x.1 ∈ Set.range P.map
  · have hxpoint : pointQuotientProjection P x.1 =
        pointQuotientPoint P := by
      have hxpre : x.1 ∈ pointQuotientProjection P ⁻¹'
          ({pointQuotientPoint P} : Set (pointQuotient P)) := by
        rw [pointQuotientProjection_preimage_point]
        exact hxA
      simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hxpre
    have hypoint : pointQuotientProjection P y.1 =
        pointQuotientPoint P := hxy'.symm.trans hxpoint
    have hyA : y.1 ∈ Set.range P.map := by
      rw [← pointQuotientProjection_preimage_point P]
      simpa only [Set.mem_preimage, Set.mem_singleton_iff]
    rw [deformation_fixed_of_mem_range h t x hxA,
      deformation_fixed_of_mem_range h t y hyA]
    exact hxy
  · have hyA : y.1 ∉ Set.range P.map := by
      intro hyA
      have hypoint : pointQuotientProjection P y.1 =
          pointQuotientPoint P := by
        have hypre : y.1 ∈ pointQuotientProjection P ⁻¹'
            ({pointQuotientPoint P} : Set (pointQuotient P)) := by
          rw [pointQuotientProjection_preimage_point]
          exact hyA
        simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hypre
      apply hxA
      rw [← pointQuotientProjection_preimage_point P]
      simpa only [Set.mem_preimage, Set.mem_singleton_iff] using
        hxy'.trans hypoint
    let e := pointQuotientComplementHomeomorph P h.isClosed_range
    have he : e ⟨x.1, hxA⟩ = e ⟨y.1, hyA⟩ := by
      apply Subtype.ext
      change
        (pointQuotientComplementHomeomorph P h.isClosed_range
          ⟨x.1, hxA⟩).1 =
        (pointQuotientComplementHomeomorph P h.isClosed_range
          ⟨y.1, hyA⟩).1
      rw [pointQuotientComplementHomeomorph_apply,
        pointQuotientComplementHomeomorph_apply]
      exact hxy'
    have hxy_val : x.1 = y.1 :=
      congrArg
        (fun z : ((Set.range P.map)ᶜ : Set P.fst) ↦ z.1)
        (e.injective he)
    have hxy_subtype : x = y := Subtype.ext hxy_val
    subst y
    rfl

private noncomputable def pointQuotientNeighborhoodSection
    (h : GoodPairData P) : h.pointQuotientNeighborhood → h.V :=
  fun y ↦ Classical.choose
    (h.pointQuotientNeighborhoodProjection_surjective y)

private lemma pointQuotientNeighborhoodSection_spec (h : GoodPairData P)
    (y : h.pointQuotientNeighborhood) :
    h.pointQuotientNeighborhoodProjection
        (pointQuotientNeighborhoodSection h y) = y :=
  Classical.choose_spec
    (h.pointQuotientNeighborhoodProjection_surjective y)

private noncomputable def pointQuotientNeighborhoodDeformationMap
    (h : GoodPairData P) :
    unitInterval × h.pointQuotientNeighborhood →
      h.pointQuotientNeighborhood :=
  fun z ↦ h.pointQuotientNeighborhoodProjection
    (h.strongDeformationRetract.deformation
      (z.1, pointQuotientNeighborhoodSection h z.2))

private lemma pointQuotientNeighborhoodDeformationMap_comp_projection
    (h : GoodPairData P) (z : unitInterval × h.V) :
    pointQuotientNeighborhoodDeformationMap h
        (z.1, h.pointQuotientNeighborhoodProjection z.2) =
      h.pointQuotientNeighborhoodProjection
        (h.strongDeformationRetract.deformation z) := by
  apply deformation_projection_eq_of_projection_eq h z.1
  exact pointQuotientNeighborhoodSection_spec h _

private theorem continuous_pointQuotientNeighborhoodDeformationMap
    (h : GoodPairData P) :
    Continuous (pointQuotientNeighborhoodDeformationMap h) := by
  apply h.pointQuotientNeighborhoodProjection_isQuotientMap.continuous_lift_prod_right
  have heq :
      (fun z : unitInterval × h.V ↦
        pointQuotientNeighborhoodDeformationMap h
          (z.1, h.pointQuotientNeighborhoodProjection z.2)) =
      (fun z : unitInterval × h.V ↦
        h.pointQuotientNeighborhoodProjection
          (h.strongDeformationRetract.deformation z)) := by
    funext z
    exact pointQuotientNeighborhoodDeformationMap_comp_projection h z
  rw [heq]
  exact h.pointQuotientNeighborhoodProjection.continuous.comp
    h.strongDeformationRetract.deformation.continuous

private noncomputable def pointQuotientNeighborhoodDeformation
    (h : GoodPairData P) :
    (ContinuousMap.id h.pointQuotientNeighborhood).HomotopyRel
      (h.pointQuotientNeighborhoodInclusion.hom.comp
        (ContinuousMap.const h.pointQuotientNeighborhood PUnit.unit))
      (Set.range h.pointQuotientNeighborhoodInclusion.hom) where
  toHomotopy :=
    { toFun := pointQuotientNeighborhoodDeformationMap h
      continuous_toFun :=
        continuous_pointQuotientNeighborhoodDeformationMap h
      map_zero_left := by
        intro y
        change h.pointQuotientNeighborhoodProjection
            (h.strongDeformationRetract.deformation
              (0, pointQuotientNeighborhoodSection h y)) = y
        rw [h.strongDeformationRetract.deformation.apply_zero]
        exact pointQuotientNeighborhoodSection_spec h y
      map_one_left := by
        intro y
        change h.pointQuotientNeighborhoodProjection
            (h.strongDeformationRetract.deformation
              (1, pointQuotientNeighborhoodSection h y)) =
          h.pointQuotientNeighborhoodInclusion PUnit.unit
        rw [h.strongDeformationRetract.deformation.apply_one]
        exact neighborhoodProjection_inclusion h
          (h.strongDeformationRetract.retract
            (pointQuotientNeighborhoodSection h y)) }
  prop' := by
    intro t y hy
    obtain ⟨u, rfl⟩ := hy
    cases u
    let a : P.snd := Classical.choice h.nonempty
    let x : h.V := neighborhoodInclusion h a
    have hxproj : h.pointQuotientNeighborhoodProjection x =
        h.pointQuotientNeighborhoodInclusion PUnit.unit :=
      neighborhoodProjection_inclusion h a
    change pointQuotientNeighborhoodDeformationMap h
        (t, h.pointQuotientNeighborhoodInclusion PUnit.unit) =
      h.pointQuotientNeighborhoodInclusion PUnit.unit
    rw [← hxproj]
    calc
      pointQuotientNeighborhoodDeformationMap h
          (t, h.pointQuotientNeighborhoodProjection x) =
          h.pointQuotientNeighborhoodProjection
            (h.strongDeformationRetract.deformation (t, x)) :=
        pointQuotientNeighborhoodDeformationMap_comp_projection h (t, x)
      _ = h.pointQuotientNeighborhoodProjection x := by
        rw [deformation_fixed_of_mem_range h t x (Set.mem_range_self a)]

/-- The chosen deformation retraction of a good-pair neighborhood descends to
a strong deformation retraction of its point quotient onto the collapsed
point. -/
noncomputable def pointQuotientNeighborhoodStrongDeformationRetract
    (h : GoodPairData P) :
    Hatcher.StrongDeformationRetract
      h.pointQuotientNeighborhoodInclusion.hom where
  retract := ContinuousMap.const h.pointQuotientNeighborhood PUnit.unit
  retract_inclusion := by ext
  deformation := pointQuotientNeighborhoodDeformation h

/-- The homotopy equivalence induced by contracting a good-pair quotient
neighborhood onto its collapsed point. -/
noncomputable def pointQuotientNeighborhoodHomotopyEquiv
    (h : GoodPairData P) :
    ContinuousMap.HomotopyEquiv PUnit h.pointQuotientNeighborhood :=
  h.pointQuotientNeighborhoodStrongDeformationRetract.toHomotopyEquiv.symm

@[simp]
lemma pointQuotientNeighborhoodHomotopyEquiv_toFun
    (h : GoodPairData P) :
    h.pointQuotientNeighborhoodHomotopyEquiv.toFun =
      h.pointQuotientNeighborhoodInclusion.hom := rfl

end GoodPairData

end Hatcher.Relative
