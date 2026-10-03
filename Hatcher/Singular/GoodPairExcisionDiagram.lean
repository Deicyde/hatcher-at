/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Hatcher.Excision.BinaryCover
import Hatcher.Singular.GoodPairNeighborhoodHomology
import Hatcher.Singular.GoodPairNeighborhoodQuotient

/-!
# The complementary excision diagram for a good pair

For a good pair `(X, A)` with chosen neighborhood `V`, this file packages the
two canonical squares in Hatcher's proof that quotienting by `A` preserves
relative homology.  The right vertical map is the isomorphism of pairs induced
by the homeomorphism from `X \ A` to `(X/A) \ (A/A)`.
-/

noncomputable section

open CategoryTheory Set

namespace Hatcher.Relative

universe w

namespace GoodPairData

variable {P : TopPair.{w}}

/-- The source complement pair `(X \ A, V \ A)` in Hatcher's excision
diagram. -/
def complementNeighborhoodPair (h : GoodPairData P) : TopPair.{w} :=
  TopPair.of
    (TopCat.ofHom
      (ContinuousMap.inclusion
        (Set.inter_subset_right :
          h.V \ Set.range P.map ⊆ (Set.range P.map)ᶜ)))
    (Topology.IsEmbedding.inclusion
      (Set.inter_subset_right :
        h.V \ Set.range P.map ⊆ (Set.range P.map)ᶜ))

/-- The target complement pair
`((X/A) \ (A/A), (V/A) \ (A/A))` in Hatcher's excision diagram. -/
def pointQuotientComplementNeighborhoodPair (h : GoodPairData P) :
    TopPair.{w} :=
  TopPair.of
    (TopCat.ofHom
      (ContinuousMap.inclusion
        (Set.inter_subset_right :
          h.pointQuotientNeighborhood \ {pointQuotientPoint P} ⊆
            ({pointQuotientPoint P} : Set (pointQuotient P))ᶜ)))
    (Topology.IsEmbedding.inclusion
      (Set.inter_subset_right :
        h.pointQuotientNeighborhood \ {pointQuotientPoint P} ⊆
          ({pointQuotientPoint P} : Set (pointQuotient P))ᶜ))

/-- The point-quotient projection restricts to a homeomorphism between the
deleted neighborhoods `V \ A` and `(V/A) \ (A/A)`. -/
noncomputable def pointQuotientDeletedNeighborhoodHomeomorph
    (h : GoodPairData P) :
    (h.V \ Set.range P.map : Set P.fst) ≃ₜ
      (h.pointQuotientNeighborhood \ {pointQuotientPoint P} :
        Set (pointQuotient P)) := by
  let _ : Nonempty P.snd := h.nonempty
  let e := pointQuotientComplementHomeomorph P h.isClosed_range
  let f : (h.V \ Set.range P.map : Set P.fst) →
      (h.pointQuotientNeighborhood \ {pointQuotientPoint P} :
        Set (pointQuotient P)) := fun x ↦
    ⟨(e ⟨x.1, x.2.2⟩).1,
      ⟨⟨x.1, x.2.1,
          (pointQuotientComplementHomeomorph_apply
            P h.isClosed_range ⟨x.1, x.2.2⟩).symm⟩,
        (e ⟨x.1, x.2.2⟩).2⟩⟩
  let g : (h.pointQuotientNeighborhood \ {pointQuotientPoint P} :
      Set (pointQuotient P)) → (h.V \ Set.range P.map : Set P.fst) := fun y ↦
    let z := e.symm ⟨y.1, y.2.2⟩
    ⟨z.1,
      ⟨by
          rw [← h.pointQuotientProjection_preimage_neighborhood]
          change pointQuotientProjection P z.1 ∈ h.pointQuotientNeighborhood
          have hz : e z = ⟨y.1, y.2.2⟩ := e.apply_symm_apply _
          have hz' := congrArg Subtype.val hz
          rw [pointQuotientComplementHomeomorph_apply] at hz'
          rw [hz']
          exact y.2.1,
        z.2⟩⟩
  exact
    { toEquiv :=
        { toFun := f
          invFun := g
          left_inv := by
            intro x
            dsimp [f, g]
            apply Subtype.ext
            change (e.symm (e ⟨x.1, x.2.2⟩)).1 = x.1
            exact congrArg Subtype.val (e.symm_apply_apply ⟨x.1, x.2.2⟩)
          right_inv := by
            intro y
            dsimp [f, g]
            apply Subtype.ext
            change (e (e.symm ⟨y.1, y.2.2⟩)).1 = y.1
            exact congrArg Subtype.val (e.apply_symm_apply ⟨y.1, y.2.2⟩) }
      continuous_toFun := by
        dsimp [f]
        have hc : Continuous (fun x : (h.V \ Set.range P.map : Set P.fst) ↦
            (⟨x.1, x.2.2⟩ : ((Set.range P.map)ᶜ : Set P.fst))) :=
          continuous_subtype_val.subtype_mk _
        exact (continuous_subtype_val.comp (e.continuous.comp hc)).subtype_mk _
      continuous_invFun := by
        dsimp [g]
        have hc : Continuous (fun y :
            (h.pointQuotientNeighborhood \ {pointQuotientPoint P} :
              Set (pointQuotient P)) ↦
            (⟨y.1, y.2.2⟩ :
              (({pointQuotientPoint P} : Set (pointQuotient P))ᶜ :
                Set (pointQuotient P)))) :=
          continuous_subtype_val.subtype_mk _
        exact
          (continuous_subtype_val.comp (e.symm.continuous.comp hc)).subtype_mk _ }

@[simp]
lemma pointQuotientDeletedNeighborhoodHomeomorph_apply
    (h : GoodPairData P) (x : (h.V \ Set.range P.map : Set P.fst)) :
    (h.pointQuotientDeletedNeighborhoodHomeomorph x).1 =
      pointQuotientProjection P x.1 := by
  let _ : Nonempty P.snd := h.nonempty
  rfl

/-- The isomorphism of complement pairs induced by the point-quotient
projection away from the collapsed subspace. -/
noncomputable def pointQuotientComplementPairIso (h : GoodPairData P) :
    h.complementNeighborhoodPair ≅
      h.pointQuotientComplementNeighborhoodPair := by
  let _ : Nonempty P.snd := h.nonempty
  exact
    MorphismProperty.Arrow.isoMk
      (TopCat.isoOfHomeo h.pointQuotientDeletedNeighborhoodHomeomorph)
      (TopCat.isoOfHomeo
        (pointQuotientComplementHomeomorph P h.isClosed_range))
      (by
        ext x
        rfl)

/-- The left square of Hatcher's comparison diagram commutes. -/
theorem neighborhood_pointQuotientComparison (h : GoodPairData P) :
    h.neighborhoodPairHom ≫
        h.neighborhoodPairToPointQuotientNeighborhoodPair =
      pointQuotientComparison.app P ≫
        h.pointQuotientPairToNeighborhoodPair := by
  apply MorphismProperty.Arrow.Hom.ext
  · ext a
    apply Subtype.ext
    have ha : P.map a ∈ pointQuotientProjection P ⁻¹'
        ({pointQuotientPoint P} : Set (pointQuotient P)) := by
      rw [pointQuotientProjection_preimage_point]
      exact Set.mem_range_self a
    exact Set.mem_singleton_iff.mp ha
  · change (𝟙 P.fst) ≫ pointQuotientProjection P =
      pointQuotientProjection P ≫ 𝟙 (pointQuotient P)
    rw [Category.comp_id, Category.id_comp]

/-- The right, complementary-excision square of Hatcher's comparison diagram
commutes. -/
theorem pointQuotientComplement_excisionSquare (h : GoodPairData P) :
    h.pointQuotientComplementPairIso.hom ≫
        Hatcher.Excision.deletedSubsetPairHom
          h.pointQuotientNeighborhood {pointQuotientPoint P} =
      Hatcher.Excision.deletedSubsetPairHom h.V (Set.range P.map) ≫
        h.neighborhoodPairToPointQuotientNeighborhoodPair := by
  let _ : Nonempty P.snd := h.nonempty
  apply MorphismProperty.Arrow.Hom.ext
  · ext x
    rfl
  · ext x
    exact pointQuotientComplementHomeomorph_apply
      P h.isClosed_range ⟨x.1, x.2⟩

/-- The two commuting squares used in the complementary-excision proof of
Hatcher's Proposition 2.22. -/
structure PointQuotientExcisionDiagram (h : GoodPairData P) where
  /-- The complement pair isomorphism down the right side of the diagram. -/
  complementIso :
    h.complementNeighborhoodPair ≅ h.pointQuotientComplementNeighborhoodPair
  /-- The square comparing `(X,A) → (X,V)` with its point quotient. -/
  neighborhoodSquare :
    h.neighborhoodPairHom ≫
        h.neighborhoodPairToPointQuotientNeighborhoodPair =
      pointQuotientComparison.app P ≫
        h.pointQuotientPairToNeighborhoodPair
  /-- The square comparing both deleted-subset excision maps. -/
  excisionSquare :
    complementIso.hom ≫
        Hatcher.Excision.deletedSubsetPairHom
          h.pointQuotientNeighborhood {pointQuotientPoint P} =
      Hatcher.Excision.deletedSubsetPairHom h.V (Set.range P.map) ≫
        h.neighborhoodPairToPointQuotientNeighborhoodPair

/-- Hatcher's canonical complementary-excision diagram for chosen good-pair
data. -/
noncomputable def pointQuotientExcisionDiagram (h : GoodPairData P) :
    PointQuotientExcisionDiagram h where
  complementIso := h.pointQuotientComplementPairIso
  neighborhoodSquare := h.neighborhood_pointQuotientComparison
  excisionSquare := h.pointQuotientComplement_excisionSquare

end GoodPairData

end Hatcher.Relative
