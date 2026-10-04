/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Hatcher.Singular.GoodPairPointQuotientNaturality
import Hatcher.Singular.PointedWedgePointQuotient
import Hatcher.Singular.SigmaGoodPair
import Hatcher.Singular.SigmaRelativeHomology
import Hatcher.VanKampen.WellPointedWedgeCover

/-!
# Reduced homology of a pointed wedge

This file proves the canonical form of Hatcher's wedge axiom: the morphism
from the coproduct of the reduced homology objects of the summands, whose
components are induced by the summand inclusions, is an isomorphism when the
basepoints form good pairs.  The empty family is handled separately from the
good-pair argument.
-/

noncomputable section

open AlgebraicTopology CategoryTheory Limits

namespace Hatcher.PointedWedge

universe w v u

variable {ι : Type w} (X : ι → TopCat.{w}) (x₀ : ∀ i, X i)
variable {C : Type u} [Category.{v} C] [Abelian C]
  [HasCoproducts.{w} C]

/-- The canonical map from the coproduct of the reduced homology objects of
the summands to reduced homology of their pointed wedge.  Its components are
the maps induced by the canonical summand inclusions. -/
noncomputable def reducedHomologyCoproductMap (R : C) (n : ℕ) :
    (∐ fun i ↦ (Hatcher.Reduced.homologyFunctor R n).obj (X i)) ⟶
      (Hatcher.Reduced.homologyFunctor R n).obj
        (TopCat.of (Hatcher.PointedWedge (fun i ↦ X i) x₀)) :=
  Sigma.desc fun i ↦
    (Hatcher.Reduced.homologyFunctor R n).map
      (Hatcher.Relative.pointedWedgeSummandInclusion x₀ i)

/-- The restriction of the canonical wedge map to a summand is the map on
reduced homology induced by that summand's inclusion. -/
@[reassoc (attr := simp)]
lemma ι_reducedHomologyCoproductMap (R : C) (n : ℕ) (i : ι) :
    Sigma.ι
        (fun i ↦ (Hatcher.Reduced.homologyFunctor R n).obj (X i)) i ≫
      reducedHomologyCoproductMap X x₀ R n =
    (Hatcher.Reduced.homologyFunctor R n).map
      (Hatcher.Relative.pointedWedgeSummandInclusion x₀ i) := by
  simp [reducedHomologyCoproductMap]

section Nonempty

variable [AB4OfSize.{w} C] [Nonempty ι]

/-- The comparison isomorphism assembled through relative homology of the
sigma pointed pair and the good-pair point quotient. -/
private noncomputable def reducedHomologyCoproductIso
    (h : ∀ i, Hatcher.Relative.IsGoodPair
      (Hatcher.Relative.pointedPair (X i) (x₀ i)))
    (R : C) (n : ℕ) :
    (∐ fun i ↦ (Hatcher.Reduced.homologyFunctor R n).obj (X i)) ≅
      (Hatcher.Reduced.homologyFunctor R n).obj
        (TopCat.of (Hatcher.PointedWedge (fun i ↦ X i) x₀)) :=
  (Sigma.mapIso fun i ↦
      Hatcher.Relative.pointedPairHomologyIso (X i) (x₀ i) R n).symm ≪≫
    Hatcher.Relative.relativeHomologySigmaIso X R x₀ n ≪≫
    Hatcher.Relative.goodPairRelativeHomologyIsoReducedPointQuotient
      (Hatcher.Relative.sigmaPointedPair x₀)
      (Hatcher.Relative.sigmaPointedPair_isGoodPair x₀ h) R n ≪≫
    (Hatcher.Reduced.homologyFunctor R n).mapIso
      (Hatcher.Relative.pointQuotientSigmaPointedPairIsoPointedWedge x₀)

set_option backward.isDefEq.respectTransparency false in
private lemma reducedHomologyCoproductIso_hom
    (h : ∀ i, Hatcher.Relative.IsGoodPair
      (Hatcher.Relative.pointedPair (X i) (x₀ i)))
    (R : C) (n : ℕ) :
    (reducedHomologyCoproductIso X x₀ h R n).hom =
      reducedHomologyCoproductMap X x₀ R n := by
  apply Sigma.hom_ext
  intro i
  let P : Hatcher.Relative.GoodPair.{w} :=
    ⟨Hatcher.Relative.sigmaPointedPair x₀,
      Hatcher.Relative.sigmaPointedPair_isGoodPair x₀ h⟩
  have hnatural :=
    Hatcher.Relative.reducedPairProjection_naturality
      (Hatcher.Relative.sigmaPointedPairι x₀ i) R n
  have hquotient :=
    Hatcher.Relative.reducedPairProjection_comp_goodPairPointQuotientRelativeHomologyNatIso_hom_app
      P R n
  change
    Hatcher.Relative.reducedPairProjection
          (Hatcher.Relative.sigmaPointedPair x₀) R n ≫
        (Hatcher.Relative.goodPairRelativeHomologyIsoReducedPointQuotient
          (Hatcher.Relative.sigmaPointedPair x₀)
          (Hatcher.Relative.sigmaPointedPair_isGoodPair x₀ h) R n).hom =
      (Hatcher.Reduced.homologyFunctor R n).map
        (Hatcher.Relative.pointQuotientProjection
          (Hatcher.Relative.sigmaPointedPair x₀)) at hquotient
  have htop :
      (TopPair.Hom.fst (Hatcher.Relative.sigmaPointedPairι x₀ i) ≫
          Hatcher.Relative.pointQuotientProjection
            (Hatcher.Relative.sigmaPointedPair x₀)) ≫
          (Hatcher.Relative.pointQuotientSigmaPointedPairIsoPointedWedge
            x₀).hom =
        Hatcher.Relative.pointedWedgeSummandInclusion x₀ i := by
    simpa only [Hatcher.Relative.sigmaPointedPairι_fst] using
      Hatcher.Relative.sigmaι_pointQuotientProjection_pointQuotientSigmaPointedPairIsoPointedWedge_hom
        x₀ i
  have hcomponent :
      (Hatcher.Relative.pointedPairHomologyIso
          (X i) (x₀ i) R n).inv ≫
          (Hatcher.Relative.homologyFunctor R n).map
            (Hatcher.Relative.sigmaPointedPairι x₀ i) ≫
          (Hatcher.Relative.goodPairRelativeHomologyIsoReducedPointQuotient
            (Hatcher.Relative.sigmaPointedPair x₀)
            (Hatcher.Relative.sigmaPointedPair_isGoodPair x₀ h) R n).hom ≫
          (Hatcher.Reduced.homologyFunctor R n).map
            (Hatcher.Relative.pointQuotientSigmaPointedPairIsoPointedWedge
              x₀).hom =
        (Hatcher.Reduced.homologyFunctor R n).map
          (Hatcher.Relative.pointedWedgeSummandInclusion x₀ i) := by
    let g :=
      (Hatcher.Relative.goodPairRelativeHomologyIsoReducedPointQuotient
        (Hatcher.Relative.sigmaPointedPair x₀)
        (Hatcher.Relative.sigmaPointedPair_isGoodPair x₀ h) R n).hom
    let e :=
      (Hatcher.Reduced.homologyFunctor R n).map
        (Hatcher.Relative.pointQuotientSigmaPointedPairIsoPointedWedge x₀).hom
    have hnaturalAssoc := (reassoc_of% hnatural) (g ≫ e)
    have hquotientAssoc := (reassoc_of% hquotient) e
    have hmiddle := congrArg
      (fun k ↦
        (Hatcher.Reduced.homologyFunctor R n).map
            (TopPair.Hom.fst (Hatcher.Relative.sigmaPointedPairι x₀ i)) ≫ k)
      hquotientAssoc
    have hmap := congrArg
      (Hatcher.Reduced.homologyFunctor R n).map htop
    simp only [Functor.map_comp] at hmap
    have hmapAssoc :
        (Hatcher.Reduced.homologyFunctor R n).map
            (TopPair.Hom.fst (Hatcher.Relative.sigmaPointedPairι x₀ i)) ≫
          (Hatcher.Reduced.homologyFunctor R n).map
              (Hatcher.Relative.pointQuotientProjection
                (Hatcher.Relative.sigmaPointedPair x₀)) ≫ e =
        (Hatcher.Reduced.homologyFunctor R n).map
          (Hatcher.Relative.pointedWedgeSummandInclusion x₀ i) := by
      simpa only [e, Category.assoc] using hmap
    have hinv :
        (Hatcher.Relative.pointedPairHomologyIso
            (X i) (x₀ i) R n).inv =
          Hatcher.Relative.reducedPairProjection
            (Hatcher.Relative.pointedPair (X i) (x₀ i)) R n := by
      rw [Hatcher.Relative.pointedPairHomologyIso_inv]
      exact Hatcher.Relative.pointedPairProjection_eq_reducedPairProjection
        (X i) (x₀ i) R n
    have hinvAssoc := (reassoc_of% hinv)
      ((Hatcher.Relative.homologyFunctor R n).map
          (Hatcher.Relative.sigmaPointedPairι x₀ i) ≫ g ≫ e)
    exact hinvAssoc.trans
      (hnaturalAssoc.trans (hmiddle.trans hmapAssoc))
  rw [ι_reducedHomologyCoproductMap]
  dsimp only [reducedHomologyCoproductIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom]
  rw [← Category.assoc, Sigma.ι_mapIso_inv]
  simp only [Category.assoc]
  rw [Hatcher.Relative.ι_relativeHomologySigmaIso_hom_assoc]
  exact hcomponent

end Nonempty

/-- **Hatcher, Corollary 2.25 (page 126).** If each chosen basepoint forms a
good pair with its summand, then the canonical map from the coproduct of the
summands' reduced homology objects to the reduced homology of their pointed
wedge is an isomorphism.  Exactness of coproducts is used only in the
nonempty-family case. -/
theorem reducedHomologyCoproductMap_isIso [AB4OfSize.{w} C]
    (h : ∀ i, Hatcher.Relative.IsGoodPair
      (Hatcher.Relative.pointedPair (X i) (x₀ i)))
    (R : C) (n : ℕ) :
    IsIso (reducedHomologyCoproductMap X x₀ R n) := by
  cases isEmpty_or_nonempty ι with
  | inl hι =>
      let _ : IsEmpty ι := hι
      let F : Discrete ι ⥤ C := Discrete.functor fun i ↦
        (Hatcher.Reduced.homologyFunctor R n).obj (X i)
      have hsource : IsZero
          (∐ fun i ↦ (Hatcher.Reduced.homologyFunctor R n).obj (X i)) := by
        change IsZero (colimit F)
        exact ((isColimitEquivIsInitialOfIsEmpty C (colimit.cocone F))
          (colimit.isColimit F)).isZero
      have htarget : IsZero
          ((Hatcher.Reduced.homologyFunctor R n).obj
            (TopCat.of (Hatcher.PointedWedge (fun i ↦ X i) x₀))) :=
        Hatcher.Reduced.isZero_homology_of_contractible R n
      exact hsource.isIso htarget _
  | inr hι =>
      let _ : Nonempty ι := hι
      rw [← reducedHomologyCoproductIso_hom X x₀ h R n]
      infer_instance

section Integral

variable {ι₀ : Type} (X₀ : ι₀ → TopCat.{0}) (x₀₀ : ∀ i, X₀ i)

/-- Integral reduced homology of a pointed wedge is the direct sum of the
reduced homology groups of its summands.  Mathlib's `AB4 AddCommGrpCat`
instance supplies the exact-coproduct hypothesis. -/
theorem reducedIntegralHomologyCoproductMap_isIso
    (h : ∀ i, Hatcher.Relative.IsGoodPair
      (Hatcher.Relative.pointedPair (X₀ i) (x₀₀ i)))
    (n : ℕ) :
    IsIso (reducedHomologyCoproductMap X₀ x₀₀ (AddCommGrpCat.of ℤ) n) :=
  reducedHomologyCoproductMap_isIso X₀ x₀₀ h (AddCommGrpCat.of ℤ) n

end Integral

end Hatcher.PointedWedge
