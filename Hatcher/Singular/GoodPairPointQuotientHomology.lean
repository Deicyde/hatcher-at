/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Hatcher.Singular.PointQuotientNeighborhoodExcision
import Hatcher.Singular.PointQuotientNeighborhoodHomology

/-!
# Relative homology of a good pair and its point quotient

This file proves Hatcher's Proposition 2.22: for a good pair `(X, A)`, the
canonical map from `(X, A)` to `(X/A, A/A)` induces an isomorphism on relative
homology.  Composing this map with the pointed-pair comparison identifies
relative homology with reduced homology of `X/A`.
-/

noncomputable section

open AlgebraicTopology CategoryTheory Limits

namespace Hatcher.Relative

universe w v u

namespace GoodPairData

variable {P : TopPair.{w}}
variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C]

/-- **Hatcher, Proposition 2.22 (page 124).** For chosen good-pair data, the
canonical point-quotient comparison induces an isomorphism on relative
homology in every degree. -/
theorem pointQuotientComparison_homologyMap_isIso
    (h : GoodPairData P) (R : C) (n : ℕ) :
    IsIso ((homologyFunctor R n).map (pointQuotientComparison.app P)) := by
  let F := homologyFunctor R n
  have neighborhoodMapIsIso : IsIso (F.map h.neighborhoodPairHom) := by
    dsimp only [F]
    exact h.neighborhoodPairHom_homologyMap_isIso R n
  have quotientNeighborhoodMapIsIso : IsIso
      (F.map h.neighborhoodPairToPointQuotientNeighborhoodPair) := by
    dsimp only [F]
    exact
      h.neighborhoodPairToPointQuotientNeighborhoodPair_homologyMap_isIso R n
  have targetNeighborhoodMapIsIso :
      IsIso (F.map h.pointQuotientPairToNeighborhoodPair) := by
    dsimp only [F]
    exact h.pointQuotientPairToNeighborhoodPair_homologyMap_isIso R n
  have comparisonSquare :
      F.map (pointQuotientComparison.app P) ≫
          F.map h.pointQuotientPairToNeighborhoodPair =
        F.map h.neighborhoodPairHom ≫
          F.map h.neighborhoodPairToPointQuotientNeighborhoodPair := by
    calc
      _ = F.map (pointQuotientComparison.app P ≫
          h.pointQuotientPairToNeighborhoodPair) :=
        (F.map_comp _ _).symm
      _ = F.map (h.neighborhoodPairHom ≫
          h.neighborhoodPairToPointQuotientNeighborhoodPair) :=
        congrArg F.map h.neighborhood_pointQuotientComparison.symm
      _ = _ := F.map_comp _ _
  exact @IsIso.of_isIso_fac_right C _ _ _ _ _ _ _
    targetNeighborhoodMapIsIso
    (IsIso.comp_isIso' neighborhoodMapIsIso quotientNeighborhoodMapIsIso)
    comparisonSquare

end GoodPairData

variable {P : TopPair.{w}}
variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C]

/-- The point-quotient comparison induces an isomorphism on relative homology
for every good pair. -/
theorem pointQuotientComparison_homologyMap_isIso_of_isGoodPair
    (P : TopPair.{w}) (hP : IsGoodPair P) (R : C) (n : ℕ) :
    IsIso ((homologyFunctor R n).map (pointQuotientComparison.app P)) :=
  hP.elim fun h ↦ h.pointQuotientComparison_homologyMap_isIso R n

/-- **Hatcher, Proposition 2.22 (page 124).** Relative homology of a good pair
is canonically isomorphic to reduced homology of its point quotient. -/
noncomputable def goodPairRelativeHomologyIsoReducedPointQuotient
    (P : TopPair.{w}) (hP : IsGoodPair P) (R : C) (n : ℕ) :
    (homologyFunctor R n).obj P ≅
      (Hatcher.Reduced.homologyFunctor R n).obj (pointQuotient P) := by
  let _ := pointQuotientComparison_homologyMap_isIso_of_isGoodPair P hP R n
  exact asIso ((homologyFunctor R n).map (pointQuotientComparison.app P)) ≪≫
    pointedPairHomologyIso (pointQuotient P) (pointQuotientPoint P) R n

/-- The forward map of the good-pair relative-to-reduced comparison is exactly
the quotient-induced relative map followed by the pointed-pair comparison. -/
@[simp]
theorem goodPairRelativeHomologyIsoReducedPointQuotient_hom
    (P : TopPair.{w}) (hP : IsGoodPair P) (R : C) (n : ℕ) :
    (goodPairRelativeHomologyIsoReducedPointQuotient P hP R n).hom =
      (homologyFunctor R n).map (pointQuotientComparison.app P) ≫
        (pointedPairHomologyIso
          (pointQuotient P) (pointQuotientPoint P) R n).hom := by
  rfl

end Hatcher.Relative
