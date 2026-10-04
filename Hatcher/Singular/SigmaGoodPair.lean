/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Hatcher.Singular.GoodPair
import Hatcher.Singular.SigmaPointedPair
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Good pairs and topological coproducts

This file assembles pointwise good-pair witnesses for pointed spaces into a
good-pair witness for their topological coproduct.  No compatibility data is
required of maps: the construction only combines the chosen neighborhoods and
their strong deformation retractions fiberwise.
-/

noncomputable section

open CategoryTheory Set Topology
open scoped unitInterval

namespace Hatcher.Relative

universe u v

variable {ι : Type u} {X : ι → TopCat.{max u v}}
  (x₀ : ∀ i, X i)

private abbrev SigmaPointedSubspace :=
  Σ _ : ι, PUnit.{max u v + 1}

private def pointedNeighborhoodInclusion (i : ι) (V : Set (X i))
    (h : x₀ i ∈ V) : C(PUnit.{max u v + 1}, V) where
  toFun _ := ⟨x₀ i, h⟩
  continuous_toFun := continuous_const

private structure PointedGoodPairWitness (i : ι) where
  V : Set (X i)
  isClosed_point : IsClosed ({x₀ i} : Set (X i))
  basepoint_mem_interior : x₀ i ∈ interior V
  strongDeformationRetract :
    Hatcher.StrongDeformationRetract
      (pointedNeighborhoodInclusion x₀ i V
        (interior_subset basepoint_mem_interior))

private def pointedGoodPairWitnessOfData (i : ι)
    (d : GoodPairData (pointedPair (X i) (x₀ i))) :
    PointedGoodPairWitness x₀ i where
  V := d.V
  isClosed_point := by
    have hd := d.isClosed_range
    change IsClosed
      (Set.range (fun _ : PUnit.{max u v + 1} ↦ x₀ i)) at hd
    simpa only [Set.range_const] using hd
  basepoint_mem_interior :=
    d.range_subset_interior ⟨PUnit.unit, rfl⟩
  strongDeformationRetract := by
    have hd := d.strongDeformationRetract
    change Hatcher.StrongDeformationRetract
      (pointedNeighborhoodInclusion x₀ i d.V
        (interior_subset
          (d.range_subset_interior ⟨PUnit.unit, rfl⟩))) at hd
    exact hd

private def sigmaGoodPairNeighborhood
    (d : ∀ i, PointedGoodPairWitness x₀ i) : Set (Σ i, X i) :=
  {z | z.2 ∈ (d z.1).V}

private def sigmaGoodPairNeighborhoodEquiv
    (d : ∀ i, PointedGoodPairWitness x₀ i) :
    (Σ i, (d i).V) ≃ sigmaGoodPairNeighborhood x₀ d where
  toFun z := ⟨⟨z.1, z.2.1⟩, z.2.2⟩
  invFun z := ⟨z.1.1, ⟨z.1.2, z.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

private lemma sigmaGoodPairNeighborhoodEquiv_continuous
    (d : ∀ i, PointedGoodPairWitness x₀ i) :
    Continuous (sigmaGoodPairNeighborhoodEquiv x₀ d) := by
  apply continuous_sigma
  intro i
  exact ((continuous_sigmaMk (i := i)).comp
    (continuous_subtype_val : Continuous
      ((↑) : (d i).V → X i))).subtype_mk _

private lemma sigmaGoodPairNeighborhoodEquiv_isOpenMap
    (d : ∀ i, PointedGoodPairWitness x₀ i) :
    IsOpenMap (sigmaGoodPairNeighborhoodEquiv x₀ d) := by
  rw [isOpenMap_sigma]
  intro i
  apply Topology.IsOpenEmbedding.isOpenMap
  refine ⟨?_, ?_⟩
  · change Topology.IsEmbedding
      (Set.codRestrict (Sigma.mk i ∘ Subtype.val)
        (sigmaGoodPairNeighborhood x₀ d) (fun z ↦ z.2))
    exact ((Topology.IsEmbedding.sigmaMk (i := i)).comp
      Topology.IsEmbedding.subtypeVal).codRestrict _ _
  · have hOpen : IsOpen
        ((fun z : sigmaGoodPairNeighborhood x₀ d ↦ (z.1 : Σ i, X i)) ⁻¹'
          Set.range (Sigma.mk i)) :=
      isOpen_range_sigmaMk.preimage continuous_subtype_val
    convert hOpen using 1
    ext z
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨a.1, congrArg Subtype.val ha⟩
    · rintro ⟨a, ha⟩
      have haV : a ∈ (d i).V := by
        change (⟨i, a⟩ : Σ i, X i).2 ∈
          (d (⟨i, a⟩ : Σ i, X i).1).V
        rw [ha]
        exact z.2
      exact ⟨⟨a, haV⟩, Subtype.ext ha⟩

private def sigmaGoodPairNeighborhoodHomeomorph
    (d : ∀ i, PointedGoodPairWitness x₀ i) :
    (Σ i, (d i).V) ≃ₜ sigmaGoodPairNeighborhood x₀ d :=
  (sigmaGoodPairNeighborhoodEquiv x₀ d).toHomeomorphOfContinuousOpen
    (sigmaGoodPairNeighborhoodEquiv_continuous x₀ d)
    (sigmaGoodPairNeighborhoodEquiv_isOpenMap x₀ d)

private def sigmaFiberNeighborhoodInclusion
    (d : ∀ i, PointedGoodPairWitness x₀ i) (i : ι) :
    C(PUnit.{max u v + 1}, (d i).V) :=
  pointedNeighborhoodInclusion x₀ i (d i).V
    (interior_subset (d i).basepoint_mem_interior)

private def sigmaNeighborhoodInclusion
    (d : ∀ i, PointedGoodPairWitness x₀ i) :
    C(SigmaPointedSubspace (ι := ι), Σ i, (d i).V) where
  toFun z := ⟨z.1, sigmaFiberNeighborhoodInclusion x₀ d z.1 z.2⟩
  continuous_toFun := by
    rw [continuous_sigma_iff]
    intro i
    exact continuous_sigmaMk.comp
      (sigmaFiberNeighborhoodInclusion x₀ d i).continuous

private def sigmaNeighborhoodRetraction
    (d : ∀ i, PointedGoodPairWitness x₀ i) :
    C((Σ i, (d i).V), SigmaPointedSubspace (ι := ι)) where
  toFun z := ⟨z.1, (d z.1).strongDeformationRetract.retract z.2⟩
  continuous_toFun := by
    rw [continuous_sigma_iff]
    intro i
    exact continuous_sigmaMk.comp
      (d i).strongDeformationRetract.retract.continuous

private lemma sigmaNeighborhoodRetraction_inclusion
    (d : ∀ i, PointedGoodPairWitness x₀ i) :
    (sigmaNeighborhoodRetraction x₀ d).comp
        (sigmaNeighborhoodInclusion x₀ d) =
      ContinuousMap.id (SigmaPointedSubspace (ι := ι)) := by
  apply ContinuousMap.ext
  rintro ⟨i, a⟩
  change (⟨i, _⟩ : SigmaPointedSubspace (ι := ι)) = ⟨i, a⟩
  apply Sigma.mk.inj_iff.mpr
  refine ⟨rfl, heq_of_eq ?_⟩
  change (d i).strongDeformationRetract.retract
    (sigmaFiberNeighborhoodInclusion x₀ d i a) = a
  exact ContinuousMap.congr_fun
    (d i).strongDeformationRetract.retract_inclusion a

private def sigmaNeighborhoodDeformation
    (d : ∀ i, PointedGoodPairWitness x₀ i) :
    (ContinuousMap.id (Σ i, (d i).V)).HomotopyRel
      ((sigmaNeighborhoodInclusion x₀ d).comp
        (sigmaNeighborhoodRetraction x₀ d))
      (Set.range (sigmaNeighborhoodInclusion x₀ d)) where
  toFun p :=
    ⟨p.2.1, (d p.2.1).strongDeformationRetract.deformation
      (p.1, p.2.2)⟩
  continuous_toFun := by
    let e : unitInterval × (Σ i, (d i).V) ≃ₜ
        Σ i, (d i).V × unitInterval :=
      (Homeomorph.prodComm _ _).trans
        (Homeomorph.sigmaProdDistrib :
          ((Σ i, (d i).V) × unitInterval) ≃ₜ
            Σ i, (d i).V × unitInterval)
    have hContinuous : Continuous
        (fun q : Σ i, (d i).V × unitInterval ↦
          (⟨q.1, (d q.1).strongDeformationRetract.deformation
            (q.2.2, q.2.1)⟩ : Σ i, (d i).V)) := by
      apply continuous_sigma
      intro i
      exact continuous_sigmaMk.comp
        ((d i).strongDeformationRetract.deformation.continuous.comp
          (continuous_snd.prodMk continuous_fst))
    exact hContinuous.comp e.continuous
  map_zero_left z := by
    rcases z with ⟨i, z⟩
    change (⟨i, _⟩ : Σ i, (d i).V) = ⟨i, z⟩
    apply Sigma.mk.inj_iff.mpr
    exact ⟨rfl, heq_of_eq
      ((d i).strongDeformationRetract.deformation.map_zero_left z)⟩
  map_one_left z := by
    rcases z with ⟨i, z⟩
    change (⟨i, _⟩ : Σ i, (d i).V) =
      (⟨i, _⟩ : Σ i, (d i).V)
    apply Sigma.mk.inj_iff.mpr
    exact ⟨rfl, heq_of_eq
      ((d i).strongDeformationRetract.deformation.map_one_left z)⟩
  prop' t z hz := by
    obtain ⟨a, rfl⟩ := hz
    rcases a with ⟨i, a⟩
    change (⟨i, _⟩ : Σ i, (d i).V) =
      (⟨i, _⟩ : Σ i, (d i).V)
    apply Sigma.mk.inj_iff.mpr
    exact ⟨rfl, heq_of_eq
      ((d i).strongDeformationRetract.deformation.prop t _ ⟨a, rfl⟩)⟩

private def sigmaNeighborhoodStrongDeformationRetract
    (d : ∀ i, PointedGoodPairWitness x₀ i) :
    Hatcher.StrongDeformationRetract (sigmaNeighborhoodInclusion x₀ d) where
  retract := sigmaNeighborhoodRetraction x₀ d
  retract_inclusion := sigmaNeighborhoodRetraction_inclusion x₀ d
  deformation := sigmaNeighborhoodDeformation x₀ d

private lemma sigmaGoodPair_range_subset_neighborhood
    (d : ∀ i, PointedGoodPairWitness x₀ i) :
    Set.range (sigmaPointedPair x₀).map ⊆
      sigmaGoodPairNeighborhood x₀ d := by
  rintro _ ⟨⟨i, a⟩, rfl⟩
  change x₀ i ∈ (d i).V
  exact interior_subset (d i).basepoint_mem_interior

private def sigmaGoodPairInclusion
    (d : ∀ i, PointedGoodPairWitness x₀ i) :
    C((sigmaPointedPair x₀).snd, sigmaGoodPairNeighborhood x₀ d) :=
  goodPairNeighborhoodInclusion _ _
    (sigmaGoodPair_range_subset_neighborhood x₀ d)

private lemma sigmaGoodPairHomeomorph_inclusion
    (d : ∀ i, PointedGoodPairWitness x₀ i)
    (a : (sigmaPointedPair x₀).snd) :
    sigmaGoodPairNeighborhoodHomeomorph x₀ d
        (sigmaNeighborhoodInclusion x₀ d a) =
      sigmaGoodPairInclusion x₀ d a := by
  apply Subtype.ext
  rfl

private lemma sigmaGoodPairHomeomorph_symm_inclusion
    (d : ∀ i, PointedGoodPairWitness x₀ i)
    (a : (sigmaPointedPair x₀).snd) :
    (sigmaGoodPairNeighborhoodHomeomorph x₀ d).symm
        (sigmaGoodPairInclusion x₀ d a) =
      sigmaNeighborhoodInclusion x₀ d a := by
  rw [← sigmaGoodPairHomeomorph_inclusion x₀ d]
  exact (sigmaGoodPairNeighborhoodHomeomorph x₀ d).symm_apply_apply _

private def sigmaGoodPairRetraction
    (d : ∀ i, PointedGoodPairWitness x₀ i) :
    C(sigmaGoodPairNeighborhood x₀ d,
      SigmaPointedSubspace (ι := ι)) :=
  (sigmaNeighborhoodRetraction x₀ d).comp
    { toFun := (sigmaGoodPairNeighborhoodHomeomorph x₀ d).symm
      continuous_toFun :=
        (sigmaGoodPairNeighborhoodHomeomorph x₀ d).symm.continuous }

private lemma sigmaGoodPairRetraction_inclusion
    (d : ∀ i, PointedGoodPairWitness x₀ i) :
    (sigmaGoodPairRetraction x₀ d).comp
        (sigmaGoodPairInclusion x₀ d) =
      ContinuousMap.id (SigmaPointedSubspace (ι := ι)) := by
  apply ContinuousMap.ext
  intro a
  change sigmaNeighborhoodRetraction x₀ d
      ((sigmaGoodPairNeighborhoodHomeomorph x₀ d).symm
        (sigmaGoodPairInclusion x₀ d a)) = a
  rw [sigmaGoodPairHomeomorph_symm_inclusion]
  exact ContinuousMap.congr_fun
    (sigmaNeighborhoodRetraction_inclusion x₀ d) a

private def sigmaGoodPairDeformation
    (d : ∀ i, PointedGoodPairWitness x₀ i) :
    (ContinuousMap.id (sigmaGoodPairNeighborhood x₀ d)).HomotopyRel
      ((sigmaGoodPairInclusion x₀ d).comp
        (sigmaGoodPairRetraction x₀ d))
      (Set.range (sigmaGoodPairInclusion x₀ d)) where
  toFun p := sigmaGoodPairNeighborhoodHomeomorph x₀ d
    (sigmaNeighborhoodDeformation x₀ d
      (p.1, (sigmaGoodPairNeighborhoodHomeomorph x₀ d).symm p.2))
  continuous_toFun :=
    (sigmaGoodPairNeighborhoodHomeomorph x₀ d).continuous.comp
      ((sigmaNeighborhoodDeformation x₀ d).continuous.comp
        (continuous_fst.prodMk
          ((sigmaGoodPairNeighborhoodHomeomorph x₀ d).symm.continuous.comp
            continuous_snd)))
  map_zero_left z := by
    change sigmaGoodPairNeighborhoodHomeomorph x₀ d
      (sigmaNeighborhoodDeformation x₀ d
        (0, (sigmaGoodPairNeighborhoodHomeomorph x₀ d).symm z)) = z
    calc
      _ = sigmaGoodPairNeighborhoodHomeomorph x₀ d
          ((sigmaGoodPairNeighborhoodHomeomorph x₀ d).symm z) :=
        congrArg (sigmaGoodPairNeighborhoodHomeomorph x₀ d)
          ((sigmaNeighborhoodDeformation x₀ d).map_zero_left _)
      _ = z :=
        (sigmaGoodPairNeighborhoodHomeomorph x₀ d).apply_symm_apply z
  map_one_left z := by
    change sigmaGoodPairNeighborhoodHomeomorph x₀ d
      (sigmaNeighborhoodDeformation x₀ d
        (1, (sigmaGoodPairNeighborhoodHomeomorph x₀ d).symm z)) =
      sigmaGoodPairInclusion x₀ d
        (sigmaNeighborhoodRetraction x₀ d
          ((sigmaGoodPairNeighborhoodHomeomorph x₀ d).symm z))
    calc
      _ = sigmaGoodPairNeighborhoodHomeomorph x₀ d
          (sigmaNeighborhoodInclusion x₀ d
            (sigmaNeighborhoodRetraction x₀ d
              ((sigmaGoodPairNeighborhoodHomeomorph x₀ d).symm z))) :=
        congrArg (sigmaGoodPairNeighborhoodHomeomorph x₀ d)
          ((sigmaNeighborhoodDeformation x₀ d).map_one_left _)
      _ = _ := sigmaGoodPairHomeomorph_inclusion x₀ d _
  prop' t z hz := by
    obtain ⟨a, rfl⟩ := hz
    change sigmaGoodPairNeighborhoodHomeomorph x₀ d
      (sigmaNeighborhoodDeformation x₀ d
        (t, (sigmaGoodPairNeighborhoodHomeomorph x₀ d).symm
          (sigmaGoodPairInclusion x₀ d a))) =
      sigmaGoodPairInclusion x₀ d a
    calc
      _ = sigmaGoodPairNeighborhoodHomeomorph x₀ d
          (sigmaNeighborhoodDeformation x₀ d
            (t, sigmaNeighborhoodInclusion x₀ d a)) := by
        rw [sigmaGoodPairHomeomorph_symm_inclusion]
      _ = sigmaGoodPairNeighborhoodHomeomorph x₀ d
          (sigmaNeighborhoodInclusion x₀ d a) :=
        congrArg (sigmaGoodPairNeighborhoodHomeomorph x₀ d)
          ((sigmaNeighborhoodDeformation x₀ d).prop t _ ⟨a, rfl⟩)
      _ = _ := sigmaGoodPairHomeomorph_inclusion x₀ d a

private def sigmaGoodPairStrongDeformationRetract
    (d : ∀ i, PointedGoodPairWitness x₀ i) :
    Hatcher.StrongDeformationRetract (sigmaGoodPairInclusion x₀ d) where
  retract := sigmaGoodPairRetraction x₀ d
  retract_inclusion := sigmaGoodPairRetraction_inclusion x₀ d
  deformation := sigmaGoodPairDeformation x₀ d

private lemma sigmaGoodPair_isClosed_range
    (d : ∀ i, PointedGoodPairWitness x₀ i) :
    IsClosed (Set.range (sigmaPointedPair x₀).map) := by
  change IsClosed (Set.range (fun z : Σ _ : ι, PUnit =>
    (⟨z.1, x₀ z.1⟩ : Σ i, X i)))
  rw [isClosed_sigma_iff]
  intro i
  rw [show Sigma.mk i ⁻¹'
      Set.range (fun z : Σ _ : ι, PUnit ↦
        (⟨z.1, x₀ z.1⟩ : Σ i, X i)) = ({x₀ i} : Set (X i)) by
    ext x
    simp only [Set.mem_preimage, Set.mem_range, Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨j, a⟩, hj⟩
      have hji : j = i := congrArg Sigma.fst hj
      subst j
      exact (eq_of_heq (Sigma.mk.inj_iff.mp hj).2).symm
    · intro hx
      exact ⟨⟨i, PUnit.unit⟩,
        Sigma.ext rfl (heq_of_eq hx.symm)⟩]
  exact (d i).isClosed_point

private lemma sigmaGoodPair_range_subset_interior
    (d : ∀ i, PointedGoodPairWitness x₀ i) :
    Set.range (sigmaPointedPair x₀).map ⊆
      interior (sigmaGoodPairNeighborhood x₀ d) := by
  rintro _ ⟨⟨i, a⟩, rfl⟩
  have hi : x₀ i ∈ interior (d i).V :=
    (d i).basepoint_mem_interior
  have hInterior :
      Sigma.mk i ⁻¹' interior (sigmaGoodPairNeighborhood x₀ d) =
        interior (Sigma.mk i ⁻¹' sigmaGoodPairNeighborhood x₀ d) :=
    (isOpenMap_sigmaMk (i := i)).preimage_interior_eq_interior_preimage
      (continuous_sigmaMk (i := i)) _
  change Sigma.mk i (x₀ i) ∈ interior (sigmaGoodPairNeighborhood x₀ d)
  change x₀ i ∈ Sigma.mk i ⁻¹'
    interior (sigmaGoodPairNeighborhood x₀ d)
  rw [hInterior]
  rw [show Sigma.mk i ⁻¹' sigmaGoodPairNeighborhood x₀ d = (d i).V by
    ext x
    rfl]
  exact hi

private def sigmaPointedPairGoodPairData [Nonempty ι]
    (d : ∀ i, PointedGoodPairWitness x₀ i) :
    GoodPairData (sigmaPointedPair x₀) where
  nonempty := by
    let i : ι := Classical.choice inferInstance
    exact ⟨⟨i, PUnit.unit⟩⟩
  isClosed_range := sigmaGoodPair_isClosed_range x₀ d
  V := sigmaGoodPairNeighborhood x₀ d
  range_subset_interior := sigmaGoodPair_range_subset_interior x₀ d
  strongDeformationRetract := sigmaGoodPairStrongDeformationRetract x₀ d

/-- A nonempty topological coproduct of pointed good pairs is a good pair. -/
theorem sigmaPointedPair_isGoodPair [Nonempty ι]
    (h : ∀ i, IsGoodPair (pointedPair (X i) (x₀ i))) :
    IsGoodPair (sigmaPointedPair x₀) := by
  let d : ∀ i, PointedGoodPairWitness x₀ i := fun i ↦
    pointedGoodPairWitnessOfData x₀ i (Classical.choice (h i))
  exact ⟨sigmaPointedPairGoodPairData x₀ d⟩

end Hatcher.Relative
