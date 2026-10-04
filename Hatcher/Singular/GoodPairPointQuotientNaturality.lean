/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Hatcher.Singular.GoodPairPointQuotientHomology
import Hatcher.Singular.PointedRelativeNaturality

/-!
# Naturality of the good-pair point-quotient comparison

The canonical isomorphism from relative homology of a good pair to reduced
homology of its point quotient is natural for arbitrary maps of pairs.  In
particular, these maps need not preserve any chosen good-pair witness data.
-/

noncomputable section

open AlgebraicTopology CategoryTheory Limits

namespace Hatcher.Relative

universe w v u

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C]

/-- A good-pair object carries the property used to construct the full
subcategory. -/
lemma isGoodPair_of_goodPair (P : GoodPair.{w}) : IsGoodPair P.obj := by
  exact P.property

/-- Relative homology restricted to the full subcategory of good pairs. -/
noncomputable def goodPairRelativeHomologyFunctor (R : C) (n : ℕ) :
    GoodPair.{w} ⥤ C :=
  goodPairForget ⋙ homologyFunctor R n

/-- Reduced homology of the point quotient, restricted to good pairs. -/
noncomputable def goodPairReducedPointQuotientHomologyFunctor
    (R : C) (n : ℕ) : GoodPair.{w} ⥤ C :=
  goodPairForget ⋙ pointQuotientPairFunctor ⋙ TopPair.proj₁ ⋙
    Hatcher.Reduced.homologyFunctor R n

/-- The map on point quotients induced by a pair map preserves the collapsed
point. -/
lemma pointQuotientMap_point {P Q : TopPair.{w}} (f : P ⟶ Q) :
    pointQuotientMap f (pointQuotientPoint P) = pointQuotientPoint Q := by
  exact ConcreteCategory.congr_hom
    (pointQuotientPointInclusion_naturality f) PUnit.unit

/-- The functorial map of point-quotient pairs is the corresponding based map
between the pointed-pair models. -/
lemma pointQuotientPairMap_eq_pointedPairMap {P Q : TopPair.{w}} (f : P ⟶ Q) :
    pointQuotientPairMap f =
      pointedPairMap (pointQuotientMap f) (pointQuotientMap_point f) := by
  apply MorphismProperty.Arrow.Hom.ext <;> rfl

set_option backward.isDefEq.respectTransparency false in
/-- **Hatcher, §2.1 (page 128).** The canonical identification of relative
homology of a good pair with reduced homology of its point quotient is natural
for every map of good pairs. -/
noncomputable def goodPairPointQuotientRelativeHomologyNatIso
    (R : C) (n : ℕ) :
    goodPairRelativeHomologyFunctor R n ≅
    goodPairReducedPointQuotientHomologyFunctor R n :=
  NatIso.ofComponents
    (fun P ↦ goodPairRelativeHomologyIsoReducedPointQuotient
      P.obj (isGoodPair_of_goodPair P) R n)
    (by
      intro P Q f
      change
        (homologyFunctor R n).map f.hom ≫
            (goodPairRelativeHomologyIsoReducedPointQuotient
              Q.obj (isGoodPair_of_goodPair Q) R n).hom =
          (goodPairRelativeHomologyIsoReducedPointQuotient
              P.obj (isGoodPair_of_goodPair P) R n).hom ≫
            (Hatcher.Reduced.homologyFunctor R n).map
              (pointQuotientMap f.hom)
      simp only [goodPairRelativeHomologyIsoReducedPointQuotient_hom]
      have hcomparison :
          f.hom ≫ pointQuotientComparison.app Q.obj =
            pointQuotientComparison.app P.obj ≫
              pointQuotientPairMap f.hom := by
        have h := pointQuotientComparison.naturality f.hom
        change
          f.hom ≫ pointQuotientComparison.app Q.obj =
            pointQuotientComparison.app P.obj ≫
              pointQuotientPairMap f.hom at h
        exact h
      rw [← Category.assoc, ← Functor.map_comp,
        hcomparison, Functor.map_comp,
        Category.assoc, pointQuotientPairMap_eq_pointedPairMap,
        pointedPairHomologyIso_naturality]
      simp only [Category.assoc])

/-- The component of the natural isomorphism is the canonical Proposition 2.22
comparison. -/
@[simp]
lemma goodPairPointQuotientRelativeHomologyNatIso_hom_app
    (P : GoodPair.{w}) (R : C) (n : ℕ) :
    (goodPairPointQuotientRelativeHomologyNatIso R n).hom.app P =
      (goodPairRelativeHomologyIsoReducedPointQuotient
        P.obj (isGoodPair_of_goodPair P) R n).hom := by
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Hatcher's map from ambient reduced homology to quotient reduced homology is
literally the map induced by the canonical projection `X ⟶ X/A`. -/
theorem reducedPairProjection_comp_goodPairPointQuotientRelativeHomologyNatIso_hom_app
    (P : GoodPair.{w}) (R : C) (n : ℕ) :
    reducedPairProjection P.obj R n ≫
        (goodPairPointQuotientRelativeHomologyNatIso R n).hom.app P =
      (Hatcher.Reduced.homologyFunctor R n).map
        (pointQuotientProjection P.obj) := by
  rw [goodPairPointQuotientRelativeHomologyNatIso_hom_app,
    goodPairRelativeHomologyIsoReducedPointQuotient_hom,
    ← Category.assoc]
  have hprojection :=
    reducedPairProjection_naturality
      (pointQuotientComparison.app P.obj) R n
  change
    reducedPairProjection P.obj R n ≫
        (homologyFunctor R n).map (pointQuotientComparison.app P.obj) =
      (Hatcher.Reduced.homologyFunctor R n).map
          (pointQuotientProjection P.obj) ≫
        reducedPairProjection
          (pointedPair (pointQuotient P.obj) (pointQuotientPoint P.obj)) R n
      at hprojection
  rw [hprojection]
  have hcancel :
      reducedPairProjection
            (pointedPair (pointQuotient P.obj) (pointQuotientPoint P.obj)) R n ≫
          (pointedPairHomologyIso
            (pointQuotient P.obj) (pointQuotientPoint P.obj) R n).hom =
        𝟙 _ := by
    rw [← pointedPairProjection_eq_reducedPairProjection,
      ← pointedPairHomologyIso_inv]
    exact (pointedPairHomologyIso
      (pointQuotient P.obj) (pointQuotientPoint P.obj) R n).inv_hom_id
  rw [Category.assoc, hcancel]
  change
    (Hatcher.Reduced.homologyFunctor R n).map
          (pointQuotientProjection P.obj) ≫
        𝟙 ((Hatcher.Reduced.homologyFunctor R n).obj
          (pointQuotient P.obj)) =
      (Hatcher.Reduced.homologyFunctor R n).map
        (pointQuotientProjection P.obj)
  exact Category.comp_id _

end Hatcher.Relative
