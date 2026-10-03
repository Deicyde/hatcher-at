/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Jack McCarthy
-/
import Hatcher.Singular.PointedRelative
import Mathlib.Topology.Category.TopCat.Limits.Basic

/-!
# Functorial point quotients of topological pairs

For a topological pair `A ↪ X`, its point quotient is represented by the
pushout `X ⊔_A PUnit`.  This file packages the collapsed point as a pointed
topological pair, makes the construction functorial for arbitrary maps of
pairs, and records the natural quotient map from the original pair.
-/

noncomputable section

open CategoryTheory Limits

namespace Hatcher.Relative

universe w

/-- The unique map from the subspace of a topological pair to a point. -/
noncomputable def pointQuotientCollapse (P : TopPair.{w}) :
    P.snd ⟶ TopCat.of PUnit :=
  TopCat.isTerminalPUnit.from P.snd

/-- The point quotient `X/A`, represented as the pushout `X ⊔_A PUnit`. -/
noncomputable def pointQuotient (P : TopPair.{w}) : TopCat.{w} :=
  pushout P.map (pointQuotientCollapse P)

/-- The canonical projection `X ⟶ X/A`. -/
noncomputable def pointQuotientProjection (P : TopPair.{w}) :
    P.fst ⟶ pointQuotient P :=
  pushout.inl P.map (pointQuotientCollapse P)

/-- The inclusion of the point to which `A` is collapsed. -/
noncomputable def pointQuotientPointInclusion (P : TopPair.{w}) :
    TopCat.of PUnit ⟶ pointQuotient P :=
  pushout.inr P.map (pointQuotientCollapse P)

/-- The point of `X/A` represented by the collapsed subspace `A`. -/
noncomputable def pointQuotientPoint (P : TopPair.{w}) : pointQuotient P :=
  pointQuotientPointInclusion P PUnit.unit

/-- The point quotient packaged by the existing pointed-pair construction. -/
noncomputable def pointQuotientPair (P : TopPair.{w}) : TopPair.{w} :=
  pointedPair (pointQuotient P) (pointQuotientPoint P)

/-- The structure map of `pointQuotientPair` is the pushout's point inclusion. -/
lemma pointQuotientPair_map (P : TopPair.{w}) :
    (pointQuotientPair P).map = pointQuotientPointInclusion P := by
  ext x
  cases x
  rfl

/-- A map of pairs induces a map of their point quotients. -/
noncomputable def pointQuotientMap {P Q : TopPair.{w}} (f : P ⟶ Q) :
    pointQuotient P ⟶ pointQuotient Q :=
  pushout.map
    P.map (pointQuotientCollapse P)
    Q.map (pointQuotientCollapse Q)
    (TopPair.Hom.fst f) (𝟙 _) (TopPair.Hom.snd f)
    (TopPair.Hom.w f).symm
    (TopCat.isTerminalPUnit.hom_ext _ _)

@[reassoc]
lemma pointQuotientProjection_naturality {P Q : TopPair.{w}} (f : P ⟶ Q) :
    pointQuotientProjection P ≫ pointQuotientMap f =
      TopPair.Hom.fst f ≫ pointQuotientProjection Q := by
  dsimp [pointQuotientProjection, pointQuotientMap, pointQuotient]
  apply pushout.inl_desc

@[reassoc]
lemma pointQuotientPointInclusion_naturality {P Q : TopPair.{w}} (f : P ⟶ Q) :
    pointQuotientPointInclusion P ≫ pointQuotientMap f =
      pointQuotientPointInclusion Q := by
  dsimp [pointQuotientPointInclusion, pointQuotientMap, pointQuotient]
  rw [pushout.inr_desc, Category.id_comp]

@[simp]
lemma pointQuotientMap_id (P : TopPair.{w}) :
    pointQuotientMap (𝟙 P) = 𝟙 (pointQuotient P) := by
  dsimp [pointQuotientMap, pointQuotient]
  apply pushout.hom_ext
  · rw [pushout.inl_desc]
    change (𝟙 P.fst) ≫ _ = _ ≫ 𝟙 _
    rw [Category.id_comp, Category.comp_id]
  · rw [pushout.inr_desc]
    rw [Category.id_comp, Category.comp_id]

@[reassoc]
lemma pointQuotientMap_comp {P Q R : TopPair.{w}} (f : P ⟶ Q) (g : Q ⟶ R) :
    pointQuotientMap (f ≫ g) = pointQuotientMap f ≫ pointQuotientMap g := by
  dsimp [pointQuotientMap, pointQuotient]
  apply pushout.hom_ext
  · rw [pushout.inl_desc]
    change (TopPair.Hom.fst f ≫ TopPair.Hom.fst g) ≫ _ = _
    rw [← Category.assoc]
    conv_rhs => rw [pushout.inl_desc, Category.assoc, pushout.inl_desc]
    exact Category.assoc _ _ _
  · rw [pushout.inr_desc, Category.id_comp]
    rw [← Category.assoc]
    conv_rhs =>
      rw [pushout.inr_desc, Category.id_comp, pushout.inr_desc,
        Category.id_comp]

/-- The map of pointed pairs induced by a map of topological pairs. -/
noncomputable def pointQuotientPairMap {P Q : TopPair.{w}} (f : P ⟶ Q) :
    pointQuotientPair P ⟶ pointQuotientPair Q :=
  TopPair.ofHom (pointQuotientMap f) (𝟙 _) (by
    dsimp [pointQuotientPair, pointedPair, pointQuotientPoint]
    ext x
    cases x
    exact (ConcreteCategory.congr_hom
      (pointQuotientPointInclusion_naturality f) PUnit.unit).symm)

/-- Point quotient, functorial on all topological pairs and their maps. -/
noncomputable def pointQuotientPairFunctor : TopPair.{w} ⥤ TopPair.{w} where
  obj := pointQuotientPair
  map := pointQuotientPairMap
  map_id P := by
    apply MorphismProperty.Arrow.Hom.ext
    · change 𝟙 (TopCat.of PUnit) = 𝟙 (TopCat.of PUnit)
      rfl
    · exact pointQuotientMap_id P
  map_comp f g := by
    apply MorphismProperty.Arrow.Hom.ext
    · change 𝟙 (TopCat.of PUnit) =
        (𝟙 (TopCat.of PUnit)) ≫ 𝟙 (TopCat.of PUnit)
      simp
    · exact pointQuotientMap_comp f g

/-- The natural map from a pair `(X,A)` to its pointed quotient `(X/A,A/A)`. -/
noncomputable def pointQuotientComparison :
    Functor.id TopPair.{w} ⟶ pointQuotientPairFunctor :=
  { app := fun P ↦
      TopPair.ofHom
        (pointQuotientProjection P)
        (pointQuotientCollapse P)
        (by
          dsimp [pointQuotientPair, pointedPair, pointQuotientPoint,
            pointQuotientPointInclusion, pointQuotientProjection,
            pointQuotientCollapse, pointQuotient]
          ext x
          exact (ConcreteCategory.congr_hom
            (pushout.condition (f := P.map)
              (g := TopCat.isTerminalPUnit.from P.snd)) x).symm)
    naturality := by
      intro P Q f
      apply MorphismProperty.Arrow.Hom.ext
      · change TopPair.Hom.snd f ≫ pointQuotientCollapse Q =
          pointQuotientCollapse P ≫ 𝟙 (TopCat.of PUnit)
        rw [Category.comp_id]
        apply TopCat.isTerminalPUnit.hom_ext
      · change TopPair.Hom.fst f ≫ pointQuotientProjection Q =
          pointQuotientProjection P ≫ pointQuotientMap f
        exact (pointQuotientProjection_naturality f).symm }

end Hatcher.Relative
