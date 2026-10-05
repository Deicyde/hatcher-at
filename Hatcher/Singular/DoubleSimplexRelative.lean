/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Hatcher.Singular.DoubleSimplexCycle
import Hatcher.Singular.GoodPairPointQuotientNaturality
import Hatcher.Singular.StandardSimplexGoodPairs
import Hatcher.Singular.StandardSimplexZeroFaceHomology
import Mathlib.CategoryTheory.Limits.Types.Pushouts
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Relative homology of the ordered double simplex

This file packages the second simplex in the ordered double simplex as a
topological pair.  In positive dimension a collar of the common boundary,
glued to the whole second simplex, makes this a good pair.  Collapsing the
second simplex recovers the point quotient of the first simplex by its
boundary.  The resulting naturality square proves that the canonical first
simplex map is an isomorphism on relative homology.
-/

noncomputable section

open AlgebraicTopology CategoryTheory Limits Set Topology
open scoped unitInterval

namespace Hatcher.Simplex

/-- Folding the two copies of the standard simplex back onto one copy. -/
noncomputable def doubleSimplexFold (n : ℕ) :
    doubleSimplex n ⟶ TopCat.of (StandardSimplex n) :=
  pushout.desc (𝟙 _) (𝟙 _) (by simp)

@[simp]
theorem doubleSimplexFirstInclusion_fold (n : ℕ) :
    doubleSimplexFirstInclusion n ≫ doubleSimplexFold n = 𝟙 _ := by
  apply pushout.inl_desc

@[simp]
theorem doubleSimplexSecondInclusion_fold (n : ℕ) :
    doubleSimplexSecondInclusion n ≫ doubleSimplexFold n = 𝟙 _ := by
  apply pushout.inr_desc

/-- Each canonical simplex inclusion into the double simplex is an embedding.
The fold map is a continuous left inverse. -/
theorem doubleSimplexFirstInclusion_isEmbedding (n : ℕ) :
    IsEmbedding (doubleSimplexFirstInclusion n) := by
  apply Function.LeftInverse.isEmbedding
    (f := doubleSimplexFold n) (g := doubleSimplexFirstInclusion n)
  · intro x
    exact ConcreteCategory.congr_hom (doubleSimplexFirstInclusion_fold n) x
  · exact (doubleSimplexFold n).hom.continuous
  · exact (doubleSimplexFirstInclusion n).hom.continuous

/-- Each canonical simplex inclusion into the double simplex is an embedding.
The fold map is a continuous left inverse. -/
theorem doubleSimplexSecondInclusion_isEmbedding (n : ℕ) :
    IsEmbedding (doubleSimplexSecondInclusion n) := by
  apply Function.LeftInverse.isEmbedding
    (f := doubleSimplexFold n) (g := doubleSimplexSecondInclusion n)
  · intro x
    exact ConcreteCategory.congr_hom (doubleSimplexSecondInclusion_fold n) x
  · exact (doubleSimplexFold n).hom.continuous
  · exact (doubleSimplexSecondInclusion n).hom.continuous

/-- The ordered double simplex, relative to its second canonical simplex. -/
noncomputable abbrev doubleSimplexSecondPair (n : ℕ) : TopPair.{0} :=
  TopPair.of (doubleSimplexSecondInclusion n)
    (doubleSimplexSecondInclusion_isEmbedding n)

/-- The canonical map of pairs from the first simplex and its boundary to the
double simplex relative to the second simplex. -/
noncomputable def doubleSimplexFirstPairHom (n : ℕ) :
    standardSimplexPair n ⟶ doubleSimplexSecondPair n :=
  TopPair.ofHom (doubleSimplexFirstInclusion n)
    (standardSimplexBoundaryInclusion n) (by
      exact pushout.condition
        (f := standardSimplexBoundaryInclusion n)
        (g := standardSimplexBoundaryInclusion n) |>.symm)

private theorem doubleSimplexPointQuotientOuterIsPushout (n : ℕ) :
    IsPushout
      (standardSimplexPair n).map
      (Hatcher.Relative.pointQuotientCollapse (standardSimplexPair n))
      ((doubleSimplexFirstInclusion n) ≫
        Hatcher.Relative.pointQuotientProjection
          (doubleSimplexSecondPair n))
      (Hatcher.Relative.pointQuotientPointInclusion
        (doubleSimplexSecondPair n)) := by
  change IsPushout
    (standardSimplexBoundaryInclusion n)
    (Hatcher.Relative.pointQuotientCollapse (standardSimplexPair n))
    (doubleSimplexFirstInclusion n ≫
      Hatcher.Relative.pointQuotientProjection (doubleSimplexSecondPair n))
    (Hatcher.Relative.pointQuotientPointInclusion (doubleSimplexSecondPair n))
  have h₁ := IsPushout.of_hasPushout
    (standardSimplexBoundaryInclusion n)
    (standardSimplexBoundaryInclusion n)
  have h₂ := IsPushout.of_hasPushout
    (doubleSimplexSecondPair n).map
    (Hatcher.Relative.pointQuotientCollapse (doubleSimplexSecondPair n))
  have h := h₁.paste_vert h₂
  have hc :
      standardSimplexBoundaryInclusion n ≫
          Hatcher.Relative.pointQuotientCollapse
            (doubleSimplexSecondPair n) =
        Hatcher.Relative.pointQuotientCollapse (standardSimplexPair n) :=
    TopCat.isTerminalPUnit.hom_ext _ _
  rw [hc] at h
  simpa only [Hatcher.Relative.pointQuotientProjection,
    Hatcher.Relative.pointQuotientPointInclusion,
    Hatcher.Relative.pointQuotient] using h

/-- Collapsing the second simplex in the double simplex gives the same pointed
quotient as collapsing the boundary of the first simplex.  The forward map is
the map induced by the canonical map of pairs. -/
noncomputable def doubleSimplexFirstPointQuotientIso (n : ℕ) :
    Hatcher.Relative.pointQuotient (standardSimplexPair n) ≅
      Hatcher.Relative.pointQuotient (doubleSimplexSecondPair n) :=
  (IsPushout.of_hasPushout
      (standardSimplexPair n).map
      (Hatcher.Relative.pointQuotientCollapse (standardSimplexPair n))).isoIsPushout
    _ _ (doubleSimplexPointQuotientOuterIsPushout n)

@[simp]
theorem doubleSimplexFirstPointQuotientIso_hom (n : ℕ) :
    (doubleSimplexFirstPointQuotientIso n).hom =
      Hatcher.Relative.pointQuotientMap
        (doubleSimplexFirstPairHom n) := by
  unfold doubleSimplexFirstPointQuotientIso
  apply (IsPushout.of_hasPushout
    (standardSimplexPair n).map
    (Hatcher.Relative.pointQuotientCollapse (standardSimplexPair n))).hom_ext
  · rw [IsPushout.inl_isoIsPushout_hom]
    exact (Hatcher.Relative.pointQuotientProjection_naturality
      (doubleSimplexFirstPairHom n)).symm
  · rw [IsPushout.inr_isoIsPushout_hom]
    exact (Hatcher.Relative.pointQuotientPointInclusion_naturality
      (doubleSimplexFirstPairHom n)).symm

/-! ## A collar of the second simplex -/

private abbrev positiveBoundaryData (n : ℕ) :=
  standardSimplexBoundaryGoodPairData n

private abbrev positiveBoundaryNeighborhood (n : ℕ) :
    Set (StandardSimplex (n + 1)) :=
  (positiveBoundaryData n).V

private theorem isOpen_positiveBoundaryNeighborhood (n : ℕ) :
    IsOpen (positiveBoundaryNeighborhood n) := by
  change IsOpen (standardSimplexBoundaryNeighborhood n)
  unfold standardSimplexBoundaryNeighborhood
  apply isOpen_lt
  · fun_prop
  · exact continuous_const

private def boundaryToPositiveNeighborhood (n : ℕ) :
    TopCat.of (standardSimplexBoundary (n + 1)) ⟶
      TopCat.of (positiveBoundaryNeighborhood n) :=
  TopCat.ofHom <|
    Hatcher.Relative.goodPairNeighborhoodInclusion
      (standardSimplexPair (n + 1))
      (positiveBoundaryNeighborhood n)
      ((positiveBoundaryData n).range_subset_interior.trans interior_subset)

private def positiveNeighborhoodToSimplex (n : ℕ) :
    TopCat.of (positiveBoundaryNeighborhood n) ⟶
      TopCat.of (StandardSimplex (n + 1)) :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

private theorem boundaryToPositiveNeighborhood_comp (n : ℕ) :
    boundaryToPositiveNeighborhood n ≫ positiveNeighborhoodToSimplex n =
      standardSimplexBoundaryInclusion (n + 1) := by
  rfl

/-- The collar neighborhood before identifying it with an open subspace of
the double simplex: glue the boundary neighborhood in the first simplex to
the whole second simplex along their common boundary. -/
private noncomputable abbrev doubleSimplexSecondNeighborhood (n : ℕ) :
    TopCat.{0} :=
  pushout (boundaryToPositiveNeighborhood n)
    (standardSimplexBoundaryInclusion (n + 1))

private noncomputable abbrev doubleSimplexSecondNeighborhoodInl (n : ℕ) :
    TopCat.of (positiveBoundaryNeighborhood n) ⟶
      doubleSimplexSecondNeighborhood n :=
  pushout.inl (boundaryToPositiveNeighborhood n)
    (standardSimplexBoundaryInclusion (n + 1))

private noncomputable abbrev doubleSimplexSecondNeighborhoodInr (n : ℕ) :
    TopCat.of (StandardSimplex (n + 1)) ⟶
      doubleSimplexSecondNeighborhood n :=
  pushout.inr (boundaryToPositiveNeighborhood n)
    (standardSimplexBoundaryInclusion (n + 1))

/-- The glued collar maps to the double simplex by the first inclusion on its
boundary-neighborhood part and by the second inclusion on its whole-simplex
part. -/
private noncomputable def doubleSimplexSecondNeighborhoodMap (n : ℕ) :
    doubleSimplexSecondNeighborhood n ⟶ doubleSimplex (n + 1) :=
  pushout.desc
    (positiveNeighborhoodToSimplex n ≫
      doubleSimplexFirstInclusion (n + 1))
    (doubleSimplexSecondInclusion (n + 1)) (by
      rw [← Category.assoc, boundaryToPositiveNeighborhood_comp]
      exact pushout.condition)

@[simp]
private theorem doubleSimplexSecondNeighborhoodInl_map (n : ℕ) :
    doubleSimplexSecondNeighborhoodInl n ≫
        doubleSimplexSecondNeighborhoodMap n =
      positiveNeighborhoodToSimplex n ≫
        doubleSimplexFirstInclusion (n + 1) := by
  apply pushout.inl_desc

@[simp]
private theorem doubleSimplexSecondNeighborhoodInr_map (n : ℕ) :
    doubleSimplexSecondNeighborhoodInr n ≫
        doubleSimplexSecondNeighborhoodMap n =
      doubleSimplexSecondInclusion (n + 1) := by
  apply pushout.inr_desc

private theorem doubleSimplexSecondNeighborhoodMap_inl_apply
    (n : ℕ) (v : positiveBoundaryNeighborhood n) :
    doubleSimplexSecondNeighborhoodMap n
        (doubleSimplexSecondNeighborhoodInl n v) =
      doubleSimplexFirstInclusion (n + 1) v.1 :=
  ConcreteCategory.congr_hom (doubleSimplexSecondNeighborhoodInl_map n) v

private theorem doubleSimplexSecondNeighborhoodMap_inr_apply
    (n : ℕ) (b : StandardSimplex (n + 1)) :
    doubleSimplexSecondNeighborhoodMap n
        (doubleSimplexSecondNeighborhoodInr n b) =
      doubleSimplexSecondInclusion (n + 1) b :=
  ConcreteCategory.congr_hom (doubleSimplexSecondNeighborhoodInr_map n) b

private theorem doubleSimplex_isPushout_underlying (n : ℕ) :
    IsPushout
      ((forget TopCat).map (standardSimplexBoundaryInclusion n))
      ((forget TopCat).map (standardSimplexBoundaryInclusion n))
      ((forget TopCat).map (doubleSimplexFirstInclusion n))
      ((forget TopCat).map (doubleSimplexSecondInclusion n)) := by
  simpa using IsPushout.of_isColimit_cocone
    (isColimitOfPreserves (forget TopCat)
      (colimit.isColimit (span
        (standardSimplexBoundaryInclusion n)
        (standardSimplexBoundaryInclusion n))))

private theorem doubleSimplexSecondNeighborhood_isPushout_underlying (n : ℕ) :
    IsPushout
      ((forget TopCat).map (boundaryToPositiveNeighborhood n))
      ((forget TopCat).map (standardSimplexBoundaryInclusion (n + 1)))
      ((forget TopCat).map (doubleSimplexSecondNeighborhoodInl n))
      ((forget TopCat).map (doubleSimplexSecondNeighborhoodInr n)) := by
  simpa using IsPushout.of_isColimit_cocone
    (isColimitOfPreserves (forget TopCat)
      (colimit.isColimit (span
        (boundaryToPositiveNeighborhood n)
        (standardSimplexBoundaryInclusion (n + 1)))))

private theorem doubleSimplexSecondNeighborhood_eq_or_eq' (n : ℕ)
    (z : doubleSimplexSecondNeighborhood n) :
    (∃ v, doubleSimplexSecondNeighborhoodInl n v = z) ∨
      ∃ b, doubleSimplexSecondNeighborhoodInr n b = z ∧
        b ∉ Set.range (standardSimplexBoundaryInclusion (n + 1)) := by
  obtain (⟨v, hv⟩ | ⟨b, hb, hbrange⟩) :=
    CategoryTheory.Limits.Types.eq_or_eq_of_isPushout'
      (doubleSimplexSecondNeighborhood_isPushout_underlying n) z
  · left
    refine ⟨v, ?_⟩
    change doubleSimplexSecondNeighborhoodInl n v = z at hv
    exact hv
  · right
    refine ⟨b, ?_, ?_⟩
    · change doubleSimplexSecondNeighborhoodInr n b = z at hb
      exact hb
    · change b ∉ Set.range (standardSimplexBoundaryInclusion (n + 1)) at hbrange
      exact hbrange

private theorem doubleSimplexSecondNeighborhood_eq_or_eq (n : ℕ)
    (z : doubleSimplexSecondNeighborhood n) :
    (∃ v, doubleSimplexSecondNeighborhoodInl n v = z) ∨
      ∃ b, doubleSimplexSecondNeighborhoodInr n b = z := by
  obtain (⟨v, hv⟩ | ⟨b, hb, _⟩) :=
    doubleSimplexSecondNeighborhood_eq_or_eq' n z
  · exact Or.inl ⟨v, hv⟩
  · exact Or.inr ⟨b, hb⟩

private theorem doubleSimplex_inl_eq_inr_iff (n : ℕ)
    (x y : StandardSimplex n) :
    doubleSimplexFirstInclusion n x = doubleSimplexSecondInclusion n y ↔
      ∃ a : standardSimplexBoundary n,
        standardSimplexBoundaryInclusion n a = x ∧
        standardSimplexBoundaryInclusion n a = y := by
  have h :=
    CategoryTheory.Limits.Types.pushoutCocone_inl_eq_inr_iff_of_isColimit
      (doubleSimplex_isPushout_underlying n).isColimit
      Topology.IsEmbedding.subtypeVal.injective x y
  change
    ((forget TopCat).map (doubleSimplexFirstInclusion n)) x =
        ((forget TopCat).map (doubleSimplexSecondInclusion n)) y ↔ _ at h
  exact h

private theorem doubleSimplexSecondNeighborhoodMap_injective (n : ℕ) :
    Function.Injective (doubleSimplexSecondNeighborhoodMap n) := by
  intro z z' hzz'
  obtain (⟨v, rfl⟩ | ⟨b, rfl, hb⟩) :=
    doubleSimplexSecondNeighborhood_eq_or_eq' n z
  · obtain (⟨v', rfl⟩ | ⟨b', rfl, hb'⟩) :=
      doubleSimplexSecondNeighborhood_eq_or_eq' n z'
    · apply congrArg (doubleSimplexSecondNeighborhoodInl n)
      apply Subtype.ext
      apply (doubleSimplexFirstInclusion_isEmbedding (n + 1)).injective
      rw [doubleSimplexSecondNeighborhoodMap_inl_apply,
        doubleSimplexSecondNeighborhoodMap_inl_apply] at hzz'
      exact hzz'
    · exfalso
      have hcross :
          doubleSimplexFirstInclusion (n + 1) v.1 =
            doubleSimplexSecondInclusion (n + 1) b' := by
        rw [doubleSimplexSecondNeighborhoodMap_inl_apply,
          doubleSimplexSecondNeighborhoodMap_inr_apply] at hzz'
        exact hzz'
      obtain ⟨a, _, ha⟩ :=
        (doubleSimplex_inl_eq_inr_iff (n + 1) v.1 b').mp hcross
      exact hb' ⟨a, ha⟩
  · obtain (⟨v', rfl⟩ | ⟨b', rfl, hb'⟩) :=
      doubleSimplexSecondNeighborhood_eq_or_eq' n z'
    · exfalso
      have hcross :
          doubleSimplexFirstInclusion (n + 1) v'.1 =
            doubleSimplexSecondInclusion (n + 1) b := by
        rw [doubleSimplexSecondNeighborhoodMap_inl_apply,
          doubleSimplexSecondNeighborhoodMap_inr_apply] at hzz'
        exact hzz'.symm
      obtain ⟨a, _, ha⟩ :=
        (doubleSimplex_inl_eq_inr_iff (n + 1) v'.1 b).mp hcross
      exact hb ⟨a, ha⟩
    · apply congrArg (doubleSimplexSecondNeighborhoodInr n)
      apply (doubleSimplexSecondInclusion_isEmbedding (n + 1)).injective
      rw [doubleSimplexSecondNeighborhoodMap_inr_apply,
        doubleSimplexSecondNeighborhoodMap_inr_apply] at hzz'
      exact hzz'

private theorem doubleSimplexFirstInclusion_preimage_neighborhoodImage
    (n : ℕ) (U : Set (doubleSimplexSecondNeighborhood n)) :
    doubleSimplexFirstInclusion (n + 1) ⁻¹'
        (doubleSimplexSecondNeighborhoodMap n '' U) =
      positiveNeighborhoodToSimplex n ''
        (doubleSimplexSecondNeighborhoodInl n ⁻¹' U) := by
  ext x
  constructor
  · rintro ⟨z, hzU, hz⟩
    obtain (⟨v, rfl⟩ | ⟨b, rfl, hb⟩) :=
      doubleSimplexSecondNeighborhood_eq_or_eq' n z
    · have hxv : x = v.1 := by
        apply (doubleSimplexFirstInclusion_isEmbedding (n + 1)).injective
        rw [doubleSimplexSecondNeighborhoodMap_inl_apply] at hz
        exact hz.symm
      refine ⟨v, hzU, ?_⟩
      exact hxv.symm
    · have hcross :
          doubleSimplexFirstInclusion (n + 1) x =
            doubleSimplexSecondInclusion (n + 1) b := by
        rw [doubleSimplexSecondNeighborhoodMap_inr_apply] at hz
        exact hz.symm
      obtain ⟨a, _, ha⟩ :=
        (doubleSimplex_inl_eq_inr_iff (n + 1) x b).mp hcross
      exact (hb ⟨a, ha⟩).elim
  · rintro ⟨v, hvU, rfl⟩
    refine ⟨doubleSimplexSecondNeighborhoodInl n v, hvU, ?_⟩
    exact ConcreteCategory.congr_hom
      (doubleSimplexSecondNeighborhoodInl_map n) v

private theorem doubleSimplexSecondInclusion_preimage_neighborhoodImage
    (n : ℕ) (U : Set (doubleSimplexSecondNeighborhood n)) :
    doubleSimplexSecondInclusion (n + 1) ⁻¹'
        (doubleSimplexSecondNeighborhoodMap n '' U) =
      doubleSimplexSecondNeighborhoodInr n ⁻¹' U := by
  ext b
  constructor
  · rintro ⟨z, hzU, hz⟩
    have hj : doubleSimplexSecondNeighborhoodMap n
          (doubleSimplexSecondNeighborhoodInr n b) =
        doubleSimplexSecondNeighborhoodMap n z := by
      rw [doubleSimplexSecondNeighborhoodMap_inr_apply]
      exact hz.symm
    have hz' := doubleSimplexSecondNeighborhoodMap_injective n hj
    change doubleSimplexSecondNeighborhoodInr n b ∈ U
    rw [hz']
    exact hzU
  · intro hbU
    refine ⟨doubleSimplexSecondNeighborhoodInr n b, hbU, ?_⟩
    exact ConcreteCategory.congr_hom
      (doubleSimplexSecondNeighborhoodInr_map n) b

private theorem doubleSimplexSecondNeighborhoodMap_isOpenMap (n : ℕ) :
    IsOpenMap (doubleSimplexSecondNeighborhoodMap n) := by
  intro U hU
  have hleft : IsOpen
      (doubleSimplexFirstInclusion (n + 1) ⁻¹'
        (doubleSimplexSecondNeighborhoodMap n '' U)) := by
    rw [doubleSimplexFirstInclusion_preimage_neighborhoodImage]
    exact (isOpen_positiveBoundaryNeighborhood n).isOpenMap_subtype_val _
      (hU.preimage (doubleSimplexSecondNeighborhoodInl n).hom.continuous)
  have hright : IsOpen
      (doubleSimplexSecondInclusion (n + 1) ⁻¹'
        (doubleSimplexSecondNeighborhoodMap n '' U)) := by
    rw [doubleSimplexSecondInclusion_preimage_neighborhoodImage]
    exact hU.preimage (doubleSimplexSecondNeighborhoodInr n).hom.continuous
  let hD := IsPushout.of_hasPushout
    (standardSimplexBoundaryInclusion (n + 1))
    (standardSimplexBoundaryInclusion (n + 1))
  apply (TopCat.isOpen_iff_of_isColimit hD.cocone hD.isColimit _).2
  intro j
  rcases j with _ | j
  · change IsOpen
      ((standardSimplexBoundaryInclusion (n + 1) ≫
        doubleSimplexFirstInclusion (n + 1)) ⁻¹'
          (doubleSimplexSecondNeighborhoodMap n '' U))
    exact hleft.preimage
      (standardSimplexBoundaryInclusion (n + 1)).hom.continuous
  · rcases j with _ | _
    · exact hleft
    · exact hright

private theorem doubleSimplexSecondNeighborhoodMap_isOpenEmbedding (n : ℕ) :
    IsOpenEmbedding (doubleSimplexSecondNeighborhoodMap n) :=
  IsOpenEmbedding.of_continuous_injective_isOpenMap
    (doubleSimplexSecondNeighborhoodMap n).hom.continuous
    (doubleSimplexSecondNeighborhoodMap_injective n)
    (doubleSimplexSecondNeighborhoodMap_isOpenMap n)

private noncomputable def doubleSimplexSecondNeighborhoodHomeomorph (n : ℕ) :
    doubleSimplexSecondNeighborhood n ≃ₜ
      Set.range (doubleSimplexSecondNeighborhoodMap n) :=
  (doubleSimplexSecondNeighborhoodMap_isOpenEmbedding n).isEmbedding.toHomeomorph

private abbrev positiveBoundaryStrongDeformationRetract (n : ℕ) :=
  (positiveBoundaryData n).strongDeformationRetract

private abbrev positiveBoundaryRetract (n : ℕ) :
    C(positiveBoundaryNeighborhood n, standardSimplexBoundary (n + 1)) :=
  (positiveBoundaryStrongDeformationRetract n).retract

private def positiveBoundaryNeighborhoodRetraction (n : ℕ) :
    C(positiveBoundaryNeighborhood n, StandardSimplex (n + 1)) :=
  (standardSimplexBoundaryInclusion (n + 1)).hom.comp
    (positiveBoundaryRetract n)

private theorem positiveBoundaryNeighborhoodRetraction_condition (n : ℕ) :
    boundaryToPositiveNeighborhood n ≫
        TopCat.ofHom (positiveBoundaryNeighborhoodRetraction n) =
      standardSimplexBoundaryInclusion (n + 1) := by
  apply ConcreteCategory.hom_ext
  intro a
  exact congrArg Subtype.val <|
    ContinuousMap.congr_fun
      (positiveBoundaryStrongDeformationRetract n).retract_inclusion a

private noncomputable def doubleSimplexSecondNeighborhoodRetraction (n : ℕ) :
    doubleSimplexSecondNeighborhood n ⟶
      TopCat.of (StandardSimplex (n + 1)) :=
  pushout.desc
    (TopCat.ofHom (positiveBoundaryNeighborhoodRetraction n))
    (𝟙 _) (positiveBoundaryNeighborhoodRetraction_condition n)

@[simp]
private theorem doubleSimplexSecondNeighborhoodInl_retraction (n : ℕ) :
    doubleSimplexSecondNeighborhoodInl n ≫
        doubleSimplexSecondNeighborhoodRetraction n =
      TopCat.ofHom (positiveBoundaryNeighborhoodRetraction n) := by
  apply pushout.inl_desc

@[simp]
private theorem doubleSimplexSecondNeighborhoodInr_retraction (n : ℕ) :
    doubleSimplexSecondNeighborhoodInr n ≫
        doubleSimplexSecondNeighborhoodRetraction n = 𝟙 _ := by
  apply pushout.inr_desc

private def positiveBoundaryDeformationAt (n : ℕ) (t : unitInterval) :
    C(positiveBoundaryNeighborhood n, positiveBoundaryNeighborhood n) where
  toFun v := (positiveBoundaryStrongDeformationRetract n).deformation (t, v)
  continuous_toFun :=
    (positiveBoundaryStrongDeformationRetract n).deformation.continuous.comp
      (continuous_const.prodMk continuous_id)

private theorem positiveBoundaryDeformationAt_zero (n : ℕ) :
    TopCat.ofHom (positiveBoundaryDeformationAt n 0) = 𝟙 _ := by
  apply ConcreteCategory.hom_ext
  intro v
  exact (positiveBoundaryStrongDeformationRetract n).deformation.map_zero_left v

private theorem positiveBoundaryDeformationAt_one (n : ℕ) :
    TopCat.ofHom (positiveBoundaryDeformationAt n 1) =
      TopCat.ofHom (positiveBoundaryRetract n) ≫
        boundaryToPositiveNeighborhood n := by
  apply ConcreteCategory.hom_ext
  intro v
  exact (positiveBoundaryStrongDeformationRetract n).deformation.map_one_left v

private noncomputable def doubleSimplexSecondNeighborhoodDeformationAt
    (n : ℕ) (t : unitInterval) :
    doubleSimplexSecondNeighborhood n ⟶ doubleSimplexSecondNeighborhood n :=
  pushout.desc
    (TopCat.ofHom (positiveBoundaryDeformationAt n t) ≫
      doubleSimplexSecondNeighborhoodInl n)
    (doubleSimplexSecondNeighborhoodInr n) (by
      ext a
      change doubleSimplexSecondNeighborhoodInl n
          ((positiveBoundaryStrongDeformationRetract n).deformation
            (t, boundaryToPositiveNeighborhood n a)) =
        doubleSimplexSecondNeighborhoodInr n
          (standardSimplexBoundaryInclusion (n + 1) a)
      rw [show (positiveBoundaryStrongDeformationRetract n).deformation
          (t, boundaryToPositiveNeighborhood n a) =
          boundaryToPositiveNeighborhood n a from
        (positiveBoundaryStrongDeformationRetract n).deformation.prop
          t _ ⟨a, rfl⟩]
      exact ConcreteCategory.congr_hom pushout.condition a)

@[simp]
private theorem doubleSimplexSecondNeighborhoodDeformationAt_inl
    (n : ℕ) (t : unitInterval) (v : positiveBoundaryNeighborhood n) :
    doubleSimplexSecondNeighborhoodDeformationAt n t
        (doubleSimplexSecondNeighborhoodInl n v) =
      doubleSimplexSecondNeighborhoodInl n
        ((positiveBoundaryStrongDeformationRetract n).deformation (t, v)) := by
  change (doubleSimplexSecondNeighborhoodInl n ≫
      doubleSimplexSecondNeighborhoodDeformationAt n t) v = _
  unfold doubleSimplexSecondNeighborhoodDeformationAt
  rw [pushout.inl_desc]
  rfl

@[simp]
private theorem doubleSimplexSecondNeighborhoodDeformationAt_inr
    (n : ℕ) (t : unitInterval) (b : StandardSimplex (n + 1)) :
    doubleSimplexSecondNeighborhoodDeformationAt n t
        (doubleSimplexSecondNeighborhoodInr n b) =
      doubleSimplexSecondNeighborhoodInr n b := by
  change (doubleSimplexSecondNeighborhoodInr n ≫
      doubleSimplexSecondNeighborhoodDeformationAt n t) b = _
  unfold doubleSimplexSecondNeighborhoodDeformationAt
  rw [pushout.inr_desc]

private def doubleSimplexSecondNeighborhoodCoproductMap (n : ℕ) :
    positiveBoundaryNeighborhood n ⊕ StandardSimplex (n + 1) →
      doubleSimplexSecondNeighborhood n :=
  Sum.elim (doubleSimplexSecondNeighborhoodInl n)
    (doubleSimplexSecondNeighborhoodInr n)

private theorem doubleSimplexSecondNeighborhood_isOpen_iff (n : ℕ)
    (U : Set (doubleSimplexSecondNeighborhood n)) :
    IsOpen U ↔
      IsOpen (doubleSimplexSecondNeighborhoodInl n ⁻¹' U) ∧
      IsOpen (doubleSimplexSecondNeighborhoodInr n ⁻¹' U) := by
  constructor
  · intro hU
    exact ⟨hU.preimage (doubleSimplexSecondNeighborhoodInl n).hom.continuous,
      hU.preimage (doubleSimplexSecondNeighborhoodInr n).hom.continuous⟩
  · rintro ⟨hleft, hright⟩
    let hN := IsPushout.of_hasPushout
      (boundaryToPositiveNeighborhood n)
      (standardSimplexBoundaryInclusion (n + 1))
    apply (TopCat.isOpen_iff_of_isColimit hN.cocone hN.isColimit U).2
    intro j
    rcases j with _ | j
    · change IsOpen
        ((boundaryToPositiveNeighborhood n ≫
          doubleSimplexSecondNeighborhoodInl n) ⁻¹' U)
      exact hleft.preimage (boundaryToPositiveNeighborhood n).hom.continuous
    · rcases j with _ | _
      · exact hleft
      · exact hright

private theorem doubleSimplexSecondNeighborhoodCoproductMap_isQuotientMap
    (n : ℕ) :
    IsQuotientMap (doubleSimplexSecondNeighborhoodCoproductMap n) := by
  refine ⟨?_, ?_⟩
  · apply IsCoinducing.of_isOpen_preimage_iff_isOpen
    intro U
    rw [isOpen_sum_iff]
    change
      (IsOpen (doubleSimplexSecondNeighborhoodInl n ⁻¹' U) ∧
        IsOpen (doubleSimplexSecondNeighborhoodInr n ⁻¹' U)) ↔ IsOpen U
    exact (doubleSimplexSecondNeighborhood_isOpen_iff n U).symm
  · intro z
    obtain (⟨v, rfl⟩ | ⟨b, rfl⟩) :=
      doubleSimplexSecondNeighborhood_eq_or_eq n z
    · exact ⟨Sum.inl v, rfl⟩
    · exact ⟨Sum.inr b, rfl⟩

private theorem continuous_doubleSimplexSecondNeighborhoodDeformation (n : ℕ) :
    Continuous (fun p : unitInterval × doubleSimplexSecondNeighborhood n ↦
      doubleSimplexSecondNeighborhoodDeformationAt n p.1 p.2) := by
  apply (doubleSimplexSecondNeighborhoodCoproductMap_isQuotientMap n).continuous_lift_prod_right
  let e : unitInterval ×
        (positiveBoundaryNeighborhood n ⊕ StandardSimplex (n + 1)) ≃ₜ
      (unitInterval × positiveBoundaryNeighborhood n) ⊕
        (unitInterval × StandardSimplex (n + 1)) :=
    Homeomorph.prodSumDistrib
  have hleft : Continuous
      (fun p : unitInterval × positiveBoundaryNeighborhood n ↦
        doubleSimplexSecondNeighborhoodInl n
          ((positiveBoundaryStrongDeformationRetract n).deformation p)) :=
    (doubleSimplexSecondNeighborhoodInl n).hom.continuous.comp
      (positiveBoundaryStrongDeformationRetract n).deformation.continuous
  have hright : Continuous
      (fun p : unitInterval × StandardSimplex (n + 1) ↦
        doubleSimplexSecondNeighborhoodInr n p.2) :=
    (doubleSimplexSecondNeighborhoodInr n).hom.continuous.comp continuous_snd
  have h := (hleft.sumElim hright).comp e.continuous
  convert h using 1
  ext p
  rcases p with ⟨t, v | b⟩
  · change doubleSimplexSecondNeighborhoodDeformationAt n t
        (doubleSimplexSecondNeighborhoodInl n v) =
      Sum.elim _ _ (e (t, Sum.inl v))
    rw [show e (t, Sum.inl v) = Sum.inl (t, v) by rfl]
    exact doubleSimplexSecondNeighborhoodDeformationAt_inl n t v
  · change doubleSimplexSecondNeighborhoodDeformationAt n t
        (doubleSimplexSecondNeighborhoodInr n b) =
      Sum.elim _ _ (e (t, Sum.inr b))
    rw [show e (t, Sum.inr b) = Sum.inr (t, b) by rfl]
    exact doubleSimplexSecondNeighborhoodDeformationAt_inr n t b

private theorem doubleSimplexSecondNeighborhoodDeformationAt_zero (n : ℕ) :
    doubleSimplexSecondNeighborhoodDeformationAt n 0 = 𝟙 _ := by
  apply (IsPushout.of_hasPushout
    (boundaryToPositiveNeighborhood n)
    (standardSimplexBoundaryInclusion (n + 1))).hom_ext
  · unfold doubleSimplexSecondNeighborhoodDeformationAt
    rw [pushout.inl_desc, positiveBoundaryDeformationAt_zero]
    simp
  · unfold doubleSimplexSecondNeighborhoodDeformationAt
    rw [pushout.inr_desc]
    simp

private theorem doubleSimplexSecondNeighborhoodDeformationAt_one (n : ℕ) :
    doubleSimplexSecondNeighborhoodDeformationAt n 1 =
      doubleSimplexSecondNeighborhoodRetraction n ≫
        doubleSimplexSecondNeighborhoodInr n := by
  apply (IsPushout.of_hasPushout
    (boundaryToPositiveNeighborhood n)
    (standardSimplexBoundaryInclusion (n + 1))).hom_ext
  · unfold doubleSimplexSecondNeighborhoodDeformationAt
    rw [pushout.inl_desc, positiveBoundaryDeformationAt_one,
      Category.assoc, pushout.condition]
    ext v
    change doubleSimplexSecondNeighborhoodInr n
        (standardSimplexBoundaryInclusion (n + 1)
          (positiveBoundaryRetract n v)) =
      doubleSimplexSecondNeighborhoodInr n
        (doubleSimplexSecondNeighborhoodRetraction n
          (doubleSimplexSecondNeighborhoodInl n v))
    rw [show doubleSimplexSecondNeighborhoodRetraction n
        (doubleSimplexSecondNeighborhoodInl n v) =
        standardSimplexBoundaryInclusion (n + 1)
          (positiveBoundaryRetract n v) from
      ConcreteCategory.congr_hom
        (doubleSimplexSecondNeighborhoodInl_retraction n) v]
  · unfold doubleSimplexSecondNeighborhoodDeformationAt
    rw [pushout.inr_desc, ← Category.assoc,
      doubleSimplexSecondNeighborhoodInr_retraction]
    simp

private def doubleSimplexSecondNeighborhoodDeformation (n : ℕ) :
    (ContinuousMap.id (doubleSimplexSecondNeighborhood n)).HomotopyRel
      ((doubleSimplexSecondNeighborhoodInr n).hom.comp
        (doubleSimplexSecondNeighborhoodRetraction n).hom)
      (Set.range (doubleSimplexSecondNeighborhoodInr n)) where
  toFun p := doubleSimplexSecondNeighborhoodDeformationAt n p.1 p.2
  continuous_toFun := continuous_doubleSimplexSecondNeighborhoodDeformation n
  map_zero_left z :=
    ConcreteCategory.congr_hom
      (doubleSimplexSecondNeighborhoodDeformationAt_zero n) z
  map_one_left z :=
    ConcreteCategory.congr_hom
      (doubleSimplexSecondNeighborhoodDeformationAt_one n) z
  prop' t z hz := by
    obtain ⟨b, rfl⟩ := hz
    exact doubleSimplexSecondNeighborhoodDeformationAt_inr n t b

private noncomputable def doubleSimplexSecondNeighborhoodStrongDeformationRetract
    (n : ℕ) :
    Hatcher.StrongDeformationRetract
      (doubleSimplexSecondNeighborhoodInr n).hom where
  retract := (doubleSimplexSecondNeighborhoodRetraction n).hom
  retract_inclusion := by
    apply ContinuousMap.ext
    intro b
    exact ConcreteCategory.congr_hom
      (doubleSimplexSecondNeighborhoodInr_retraction n) b
  deformation := doubleSimplexSecondNeighborhoodDeformation n

private abbrev doubleSimplexSecondNeighborhoodSet (n : ℕ) :
    Set (doubleSimplex (n + 1)) :=
  Set.range (doubleSimplexSecondNeighborhoodMap n)

private theorem isOpen_doubleSimplexSecondNeighborhoodSet (n : ℕ) :
    IsOpen (doubleSimplexSecondNeighborhoodSet n) :=
  (doubleSimplexSecondNeighborhoodMap_isOpenEmbedding n).isOpen_range

private theorem doubleSimplexSecondRange_subset_neighborhood (n : ℕ) :
    Set.range (doubleSimplexSecondPair (n + 1)).map ⊆
      doubleSimplexSecondNeighborhoodSet n := by
  rintro _ ⟨b, rfl⟩
  refine ⟨doubleSimplexSecondNeighborhoodInr n b, ?_⟩
  exact ConcreteCategory.congr_hom
    (doubleSimplexSecondNeighborhoodInr_map n) b

private abbrev doubleSimplexSecondGoodPairInclusion (n : ℕ) :
    C(StandardSimplex (n + 1), doubleSimplexSecondNeighborhoodSet n) :=
  Hatcher.Relative.goodPairNeighborhoodInclusion
    (doubleSimplexSecondPair (n + 1))
    (doubleSimplexSecondNeighborhoodSet n)
    (doubleSimplexSecondRange_subset_neighborhood n)

private theorem doubleSimplexSecondNeighborhoodHomeomorph_inr
    (n : ℕ) (b : StandardSimplex (n + 1)) :
    doubleSimplexSecondNeighborhoodHomeomorph n
        (doubleSimplexSecondNeighborhoodInr n b) =
      doubleSimplexSecondGoodPairInclusion n b := by
  apply Subtype.ext
  exact ConcreteCategory.congr_hom
    (doubleSimplexSecondNeighborhoodInr_map n) b

private theorem doubleSimplexSecondNeighborhoodHomeomorph_symm_inclusion
    (n : ℕ) (b : StandardSimplex (n + 1)) :
    (doubleSimplexSecondNeighborhoodHomeomorph n).symm
        (doubleSimplexSecondGoodPairInclusion n b) =
      doubleSimplexSecondNeighborhoodInr n b := by
  rw [← doubleSimplexSecondNeighborhoodHomeomorph_inr]
  exact (doubleSimplexSecondNeighborhoodHomeomorph n).symm_apply_apply _

private abbrev doubleSimplexSecondGoodPairRetraction (n : ℕ) :
    C(doubleSimplexSecondNeighborhoodSet n, StandardSimplex (n + 1)) :=
  (doubleSimplexSecondNeighborhoodRetraction n).hom.comp
    { toFun := (doubleSimplexSecondNeighborhoodHomeomorph n).symm
      continuous_toFun :=
        (doubleSimplexSecondNeighborhoodHomeomorph n).symm.continuous }

private theorem doubleSimplexSecondGoodPairRetraction_inclusion (n : ℕ) :
    (doubleSimplexSecondGoodPairRetraction n).comp
        (doubleSimplexSecondGoodPairInclusion n) =
      ContinuousMap.id (StandardSimplex (n + 1)) := by
  apply ContinuousMap.ext
  intro b
  change doubleSimplexSecondNeighborhoodRetraction n
      ((doubleSimplexSecondNeighborhoodHomeomorph n).symm
        (doubleSimplexSecondGoodPairInclusion n b)) = b
  rw [doubleSimplexSecondNeighborhoodHomeomorph_symm_inclusion]
  exact ConcreteCategory.congr_hom
    (doubleSimplexSecondNeighborhoodInr_retraction n) b

private def doubleSimplexSecondGoodPairDeformation (n : ℕ) :
    (ContinuousMap.id (doubleSimplexSecondNeighborhoodSet n)).HomotopyRel
      ((doubleSimplexSecondGoodPairInclusion n).comp
        (doubleSimplexSecondGoodPairRetraction n))
      (Set.range (doubleSimplexSecondGoodPairInclusion n)) where
  toFun p := doubleSimplexSecondNeighborhoodHomeomorph n
    (doubleSimplexSecondNeighborhoodDeformation n
      (p.1, (doubleSimplexSecondNeighborhoodHomeomorph n).symm p.2))
  continuous_toFun :=
    (doubleSimplexSecondNeighborhoodHomeomorph n).continuous.comp
      ((doubleSimplexSecondNeighborhoodDeformation n).continuous.comp
        (continuous_fst.prodMk
          ((doubleSimplexSecondNeighborhoodHomeomorph n).symm.continuous.comp
            continuous_snd)))
  map_zero_left z := by
    change doubleSimplexSecondNeighborhoodHomeomorph n
      (doubleSimplexSecondNeighborhoodDeformation n
        (0, (doubleSimplexSecondNeighborhoodHomeomorph n).symm z)) = z
    calc
      _ = doubleSimplexSecondNeighborhoodHomeomorph n
          ((doubleSimplexSecondNeighborhoodHomeomorph n).symm z) :=
        congrArg (doubleSimplexSecondNeighborhoodHomeomorph n)
          ((doubleSimplexSecondNeighborhoodDeformation n).map_zero_left _)
      _ = z := (doubleSimplexSecondNeighborhoodHomeomorph n).apply_symm_apply z
  map_one_left z := by
    change doubleSimplexSecondNeighborhoodHomeomorph n
      (doubleSimplexSecondNeighborhoodDeformation n
        (1, (doubleSimplexSecondNeighborhoodHomeomorph n).symm z)) =
      doubleSimplexSecondGoodPairInclusion n
        (doubleSimplexSecondNeighborhoodRetraction n
          ((doubleSimplexSecondNeighborhoodHomeomorph n).symm z))
    calc
      _ = doubleSimplexSecondNeighborhoodHomeomorph n
          (doubleSimplexSecondNeighborhoodInr n
            (doubleSimplexSecondNeighborhoodRetraction n
              ((doubleSimplexSecondNeighborhoodHomeomorph n).symm z))) :=
        congrArg (doubleSimplexSecondNeighborhoodHomeomorph n)
          ((doubleSimplexSecondNeighborhoodDeformation n).map_one_left _)
      _ = _ := doubleSimplexSecondNeighborhoodHomeomorph_inr n _
  prop' t z hz := by
    obtain ⟨b, rfl⟩ := hz
    change doubleSimplexSecondNeighborhoodHomeomorph n
      (doubleSimplexSecondNeighborhoodDeformation n
        (t, (doubleSimplexSecondNeighborhoodHomeomorph n).symm
          (doubleSimplexSecondGoodPairInclusion n b))) =
      doubleSimplexSecondGoodPairInclusion n b
    rw [doubleSimplexSecondNeighborhoodHomeomorph_symm_inclusion]
    calc
      _ = doubleSimplexSecondNeighborhoodHomeomorph n
          (doubleSimplexSecondNeighborhoodInr n b) :=
        congrArg (doubleSimplexSecondNeighborhoodHomeomorph n)
          ((doubleSimplexSecondNeighborhoodDeformation n).prop t _ ⟨b, rfl⟩)
      _ = _ := doubleSimplexSecondNeighborhoodHomeomorph_inr n b

private def doubleSimplexSecondGoodPairStrongDeformationRetract (n : ℕ) :
    Hatcher.StrongDeformationRetract
      (doubleSimplexSecondGoodPairInclusion n) where
  retract := doubleSimplexSecondGoodPairRetraction n
  retract_inclusion := doubleSimplexSecondGoodPairRetraction_inclusion n
  deformation := doubleSimplexSecondGoodPairDeformation n

private theorem doubleSimplexFirstInclusion_preimage_secondRange (n : ℕ) :
    doubleSimplexFirstInclusion n ⁻¹'
        Set.range (doubleSimplexSecondInclusion n) =
      Set.range (standardSimplexBoundaryInclusion n) := by
  ext x
  constructor
  · rintro ⟨b, hxb⟩
    obtain ⟨a, ha, _⟩ :=
      (doubleSimplex_inl_eq_inr_iff n x b).mp hxb.symm
    exact ⟨a, ha⟩
  · rintro ⟨a, rfl⟩
    refine ⟨standardSimplexBoundaryInclusion n a, ?_⟩
    exact (ConcreteCategory.congr_hom pushout.condition a).symm

private theorem doubleSimplexSecondInclusion_preimage_secondRange (n : ℕ) :
    doubleSimplexSecondInclusion n ⁻¹'
        Set.range (doubleSimplexSecondInclusion n) = Set.univ := by
  ext b
  simp

private theorem standardSimplexBoundaryRange_isClosed (n : ℕ) :
    IsClosed (standardSimplexBoundary (n + 1)) := by
  have h := (positiveBoundaryData n).isClosed_range
  change IsClosed (Set.range (fun a : standardSimplexBoundary (n + 1) ↦
    (a : StandardSimplex (n + 1)))) at h
  simpa using h

private theorem doubleSimplexSecondPair_isClosed_range (n : ℕ) :
    IsClosed (Set.range (doubleSimplexSecondPair (n + 1)).map) := by
  change IsClosed (Set.range (doubleSimplexSecondInclusion (n + 1)))
  let hD := IsPushout.of_hasPushout
    (standardSimplexBoundaryInclusion (n + 1))
    (standardSimplexBoundaryInclusion (n + 1))
  apply (TopCat.isClosed_iff_of_isColimit hD.cocone hD.isColimit _).2
  intro j
  rcases j with _ | j
  · dsimp [hD]
    change IsClosed
      ((standardSimplexBoundaryInclusion (n + 1) ≫
        doubleSimplexFirstInclusion (n + 1)) ⁻¹'
          Set.range (doubleSimplexSecondInclusion (n + 1)))
    convert isClosed_univ using 1
    ext a
    simp only [Set.mem_preimage, Set.mem_range, Set.mem_univ, iff_true]
    refine ⟨standardSimplexBoundaryInclusion (n + 1) a, ?_⟩
    exact (ConcreteCategory.congr_hom pushout.condition a).symm
  · rcases j with _ | _
    · dsimp [hD]
      change IsClosed
        (doubleSimplexFirstInclusion (n + 1) ⁻¹'
          Set.range (doubleSimplexSecondInclusion (n + 1)))
      rw [doubleSimplexFirstInclusion_preimage_secondRange]
      rw [show Set.range (standardSimplexBoundaryInclusion (n + 1)) =
          standardSimplexBoundary (n + 1) by
        ext x
        constructor
        · rintro ⟨a, rfl⟩
          exact a.2
        · intro hx
          exact ⟨⟨x, hx⟩, rfl⟩]
      exact standardSimplexBoundaryRange_isClosed n
    · dsimp [hD]
      change IsClosed
        (doubleSimplexSecondInclusion (n + 1) ⁻¹'
          Set.range (doubleSimplexSecondInclusion (n + 1)))
      rw [doubleSimplexSecondInclusion_preimage_secondRange]
      exact isClosed_univ

/-- The second simplex in a positive-dimensional ordered double simplex is a
good pair.  Its chosen neighborhood is the whole second simplex together with
the standard collar of the common boundary in the first simplex. -/
noncomputable def doubleSimplexSecondGoodPairData (n : ℕ) :
    Hatcher.Relative.GoodPairData (doubleSimplexSecondPair (n + 1)) where
  nonempty := ⟨Convexity.StdSimplex.single (R := ℝ) (0 : Fin (n + 2))⟩
  isClosed_range := doubleSimplexSecondPair_isClosed_range n
  V := doubleSimplexSecondNeighborhoodSet n
  range_subset_interior := by
    change Set.range (doubleSimplexSecondInclusion (n + 1)) ⊆
      interior (doubleSimplexSecondNeighborhoodSet n)
    rw [(isOpen_doubleSimplexSecondNeighborhoodSet n).interior_eq]
    exact doubleSimplexSecondRange_subset_neighborhood n
  strongDeformationRetract :=
    doubleSimplexSecondGoodPairStrongDeformationRetract n

/-! ## The zero-dimensional pair -/

private theorem standardSimplexBoundary_zero_false
    (a : standardSimplexBoundary 0) : False := by
  obtain ⟨i, hi⟩ := a.2
  fin_cases i
  have htotal := a.1.total_of_fintype
  have hi' : a.1.weights (0 : Fin 1) = 0 := hi
  rw [Fin.sum_univ_one, hi'] at htotal
  norm_num at htotal

private theorem standardSimplex_zero_subsingleton
    (x y : StandardSimplex 0) : x = y := by
  apply Convexity.StdSimplex.ext
  apply Finsupp.ext
  intro i
  fin_cases i
  have hx := x.total_of_fintype
  have hy := y.total_of_fintype
  rw [Fin.sum_univ_one] at hx hy
  exact hx.trans hy.symm

private theorem standardSimplexZeroHorn_zero_subsingleton
    (x y : standardSimplexZeroHorn 0) : x = y := by
  apply Subtype.ext
  apply Convexity.StdSimplex.ext
  apply Finsupp.ext
  intro j
  have hx1 : x.1.weights (1 : Fin 2) = 0 := by
    obtain ⟨i, hi, hwi⟩ := x.2
    fin_cases i
    · exact (hi rfl).elim
    · exact hwi
  have hy1 : y.1.weights (1 : Fin 2) = 0 := by
    obtain ⟨i, hi, hwi⟩ := y.2
    fin_cases i
    · exact (hi rfl).elim
    · exact hwi
  fin_cases j
  · have hx := x.1.total_of_fintype
    have hy := y.1.total_of_fintype
    rw [Fin.sum_univ_two, hx1, add_zero] at hx
    rw [Fin.sum_univ_two, hy1, add_zero] at hy
    exact hx.trans hy.symm
  · exact hx1.trans hy1.symm

private def standardSimplexZeroHornPoint : standardSimplexZeroHorn 0 :=
  ⟨Convexity.StdSimplex.single (R := ℝ) (0 : Fin 2),
    ⟨1, by simp, by simp⟩⟩

private noncomputable def standardSimplexZeroHornHomeomorph :
    standardSimplexZeroHorn 0 ≃ₜ StandardSimplex 0 where
  toEquiv :=
    { toFun := fun _ ↦ Convexity.StdSimplex.single (R := ℝ) (0 : Fin 1)
      invFun := fun _ ↦ standardSimplexZeroHornPoint
      left_inv := fun _ ↦ standardSimplexZeroHorn_zero_subsingleton _ _
      right_inv := fun _ ↦ standardSimplex_zero_subsingleton _ _ }
  continuous_toFun := continuous_const
  continuous_invFun := continuous_const

private noncomputable abbrev standardSimplexZeroHornIso :
    TopCat.of (standardSimplexZeroHorn 0) ≅
      TopCat.of (StandardSimplex 0) :=
  TopCat.isoOfHomeo standardSimplexZeroHornHomeomorph

private abbrev zeroFaceTargetPair : TopPair.{0} :=
  Hatcher.Relative.TopTriple.pairAB.obj
    (standardSimplexBoundaryHornTriple 0)

private abbrev zeroFaceAmbientMap :
    TopCat.of (StandardSimplex 0) ⟶ TopCat.of (standardSimplexBoundary 1) :=
  TopPair.Hom.fst (standardSimplexZeroFacePairHom 0)

private abbrev zeroHornBoundaryInclusion :
    TopCat.of (standardSimplexZeroHorn 0) ⟶
      TopCat.of (standardSimplexBoundary 1) :=
  (zeroFaceTargetPair).map

private noncomputable abbrev zeroFaceTargetToDoubleSimplexAmbient :
    TopCat.of (standardSimplexBoundary 1) ⟶ doubleSimplex 0 :=
  (standardSimplexZeroFace_isPushout 0).desc
    (doubleSimplexFirstInclusion 0)
    (standardSimplexZeroHornIso.hom ≫
      doubleSimplexSecondInclusion 0) (by
      ext a
      exact (standardSimplexBoundary_zero_false a).elim)

@[simp]
private theorem zeroFaceToBoundary_comp_zeroFaceTargetToDouble (x : StandardSimplex 0) :
    zeroFaceTargetToDoubleSimplexAmbient
        (standardSimplexZeroFaceToBoundary 0 x) =
      doubleSimplexFirstInclusion 0 x := by
  exact ConcreteCategory.congr_hom
    ((standardSimplexZeroFace_isPushout 0).inl_desc _ _ _) x

@[simp]
private theorem zeroHornInclusion_comp_zeroFaceTargetToDouble
    (x : standardSimplexZeroHorn 0) :
    zeroFaceTargetToDoubleSimplexAmbient ((zeroFaceTargetPair).map x) =
      doubleSimplexSecondInclusion 0
        (standardSimplexZeroHornHomeomorph x) := by
  exact ConcreteCategory.congr_hom
    ((standardSimplexZeroFace_isPushout 0).inr_desc _ _ _) x

private noncomputable abbrev doubleSimplexToZeroFaceTargetAmbient :
    doubleSimplex 0 ⟶ TopCat.of (standardSimplexBoundary 1) :=
  pushout.desc
    (zeroFaceAmbientMap)
    (standardSimplexZeroHornIso.inv ≫
      zeroHornBoundaryInclusion) (by
      ext a
      exact (standardSimplexBoundary_zero_false a).elim)

private theorem zeroFaceTargetToDouble_inl :
    zeroFaceAmbientMap ≫
        zeroFaceTargetToDoubleSimplexAmbient =
      doubleSimplexFirstInclusion 0 :=
  (standardSimplexZeroFace_isPushout 0).inl_desc _ _ _

private theorem zeroFaceTargetToDouble_inr :
    zeroHornBoundaryInclusion ≫ zeroFaceTargetToDoubleSimplexAmbient =
      standardSimplexZeroHornIso.hom ≫
        doubleSimplexSecondInclusion 0 :=
  (standardSimplexZeroFace_isPushout 0).inr_desc _ _ _

private theorem doubleToZeroFaceTarget_inl :
    doubleSimplexFirstInclusion 0 ≫ doubleSimplexToZeroFaceTargetAmbient =
      zeroFaceAmbientMap := by
  apply pushout.inl_desc

private theorem doubleToZeroFaceTarget_inr :
    doubleSimplexSecondInclusion 0 ≫ doubleSimplexToZeroFaceTargetAmbient =
      standardSimplexZeroHornIso.inv ≫
        zeroHornBoundaryInclusion := by
  apply pushout.inr_desc

set_option maxHeartbeats 800000 in
private noncomputable def zeroFaceTargetDoubleSimplexAmbientIso :
    TopCat.of (standardSimplexBoundary 1) ≅ doubleSimplex 0 where
  hom := zeroFaceTargetToDoubleSimplexAmbient
  inv := doubleSimplexToZeroFaceTargetAmbient
  hom_inv_id := by
    apply (standardSimplexZeroFace_isPushout 0).hom_ext
    · change zeroFaceAmbientMap ≫
          (zeroFaceTargetToDoubleSimplexAmbient ≫
            doubleSimplexToZeroFaceTargetAmbient) =
        zeroFaceAmbientMap ≫ 𝟙 _
      rw [← Category.assoc, zeroFaceTargetToDouble_inl,
        doubleToZeroFaceTarget_inl, Category.comp_id]
    · change zeroHornBoundaryInclusion ≫
          (zeroFaceTargetToDoubleSimplexAmbient ≫
            doubleSimplexToZeroFaceTargetAmbient) =
        zeroHornBoundaryInclusion ≫ 𝟙 _
      rw [← Category.assoc, zeroFaceTargetToDouble_inr,
        Category.assoc, doubleToZeroFaceTarget_inr]
      rw [Category.comp_id]
      exact standardSimplexZeroHornIso.hom_inv_id_assoc _
  inv_hom_id := by
    apply (IsPushout.of_hasPushout
      (standardSimplexBoundaryInclusion 0)
      (standardSimplexBoundaryInclusion 0)).hom_ext
    · change doubleSimplexFirstInclusion 0 ≫
          (doubleSimplexToZeroFaceTargetAmbient ≫
            zeroFaceTargetToDoubleSimplexAmbient) =
        doubleSimplexFirstInclusion 0 ≫ 𝟙 _
      rw [← Category.assoc, doubleToZeroFaceTarget_inl,
        zeroFaceTargetToDouble_inl, Category.comp_id]
    · change doubleSimplexSecondInclusion 0 ≫
          (doubleSimplexToZeroFaceTargetAmbient ≫
            zeroFaceTargetToDoubleSimplexAmbient) =
        doubleSimplexSecondInclusion 0 ≫ 𝟙 _
      rw [← Category.assoc, doubleToZeroFaceTarget_inr,
        Category.assoc, zeroFaceTargetToDouble_inr]
      change standardSimplexZeroHornIso.inv ≫
          standardSimplexZeroHornIso.hom ≫
            doubleSimplexSecondInclusion 0 =
        doubleSimplexSecondInclusion 0
      exact standardSimplexZeroHornIso.inv_hom_id_assoc _

private noncomputable def zeroFaceTargetDoubleSimplexPairIso :
    zeroFaceTargetPair ≅ doubleSimplexSecondPair 0 :=
  MorphismProperty.Arrow.isoMk
    standardSimplexZeroHornIso
    zeroFaceTargetDoubleSimplexAmbientIso
    (by
      ext x
      exact (zeroHornInclusion_comp_zeroFaceTargetToDouble x).symm)

private theorem zeroFacePairHom_comp_targetIso :
    standardSimplexZeroFacePairHom 0 ≫
        (zeroFaceTargetDoubleSimplexPairIso).hom =
      doubleSimplexFirstPairHom 0 := by
  apply MorphismProperty.Arrow.Hom.ext
  · ext a
    exact (standardSimplexBoundary_zero_false a).elim
  · ext x
    exact zeroFaceToBoundary_comp_zeroFaceTargetToDouble x

universe v u

variable {C : Type u} [Category.{v} C] [HasCoproducts.{0} C] [Abelian C]

/-- **Hatcher, Example 2.23 (page 125).** The canonical map from the first
simplex relative to its boundary into the ordered double simplex relative to
its second simplex induces an isomorphism on relative homology in every
degree. -/
theorem doubleSimplexFirstPair_homologyMap_isIso
    (R : C) (n k : ℕ) :
    IsIso ((Hatcher.Relative.homologyFunctor R k).map
      (doubleSimplexFirstPairHom n)) := by
  cases n with
  | zero =>
      rw [← zeroFacePairHom_comp_targetIso, Functor.map_comp]
      exact IsIso.comp_isIso'
        (zeroFacePair_homologyMap_isIso R 0 k)
        (((Hatcher.Relative.homologyFunctor R k).mapIso
          zeroFaceTargetDoubleSimplexPairIso).isIso_hom)
  | succ n =>
      let P : Hatcher.Relative.GoodPair.{0} :=
        ⟨standardSimplexPair (n + 1),
          ⟨standardSimplexBoundaryGoodPairData n⟩⟩
      let Q : Hatcher.Relative.GoodPair.{0} :=
        ⟨doubleSimplexSecondPair (n + 1),
          ⟨doubleSimplexSecondGoodPairData n⟩⟩
      let f : P ⟶ Q := ObjectProperty.homMk
        (doubleSimplexFirstPairHom (n + 1))
      let F := Hatcher.Relative.goodPairRelativeHomologyFunctor R k
      let G := Hatcher.Relative.goodPairReducedPointQuotientHomologyFunctor R k
      let η := (Hatcher.Relative.goodPairPointQuotientRelativeHomologyNatIso
        R k).hom
      have hSquare : F.map f ≫ η.app Q = η.app P ≫ G.map f :=
        η.naturality f
      have hG : IsIso (G.map f) := by
        change IsIso ((Hatcher.Reduced.homologyFunctor R k).map
          (Hatcher.Relative.pointQuotientMap
            (doubleSimplexFirstPairHom (n + 1))))
        rw [← doubleSimplexFirstPointQuotientIso_hom (n + 1)]
        exact ((Hatcher.Reduced.homologyFunctor R k).mapIso
          (doubleSimplexFirstPointQuotientIso (n + 1))).isIso_hom
      have hf : IsIso (F.map f) := @IsIso.of_isIso_fac_right C _ _ _ _ _ _ _
        (inferInstance : IsIso (η.app Q))
        (IsIso.comp_isIso'
          (inferInstance : IsIso (η.app P))
          hG)
        hSquare
      simpa [F, f, P, Q,
        Hatcher.Relative.goodPairRelativeHomologyFunctor] using hf

end Hatcher.Simplex
