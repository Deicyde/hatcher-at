/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Hatcher.Singular.GoodPairExcisionDiagram

/-!
# Excision for a point-quotient neighborhood

For a good pair `(X, A)` with chosen neighborhood `V`, this file proves that
the quotient projection induces an isomorphism from the relative homology of
`(X, V)` to that of `(X/A, V/A)`.  The proof is the right-hand diagram chase
in Hatcher's proof of Proposition 2.22: deleted-subset excision identifies both
groups with the relative homology of their complements, and the quotient is a
homeomorphism on those complements.
-/

noncomputable section

open AlgebraicTopology CategoryTheory Limits Set

namespace Hatcher.Relative

universe w v u

namespace GoodPairData

variable {P : TopPair.{w}}
variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C]

/-- The quotient projection of neighborhood pairs `(X,V) ⟶ (X/A,V/A)`
induces an isomorphism on relative homology in every degree, including degree
zero. -/
instance neighborhoodPairToPointQuotientNeighborhoodPair_homologyMap_isIso
    (h : GoodPairData P) (R : C) (n : ℕ) :
    IsIso ((homologyFunctor R n).map
      h.neighborhoodPairToPointQuotientNeighborhoodPair) := by
  have sourceExcisionIsIso :
      IsIso ((homologyFunctor R n).map
        (Hatcher.Excision.deletedSubsetPairHom
          h.V (Set.range P.map))) :=
    Hatcher.Excision.deletedSubsetHomologyMap_isIso_of_closure_subset_interior
      h.V (Set.range P.map) h.closure_range_subset_interior_neighborhood R n
  let targetExcision :
      h.pointQuotientComplementNeighborhoodPair ⟶
        h.pointQuotientNeighborhoodPair := by
    simpa only [pointQuotientComplementNeighborhoodPair,
      pointQuotientNeighborhoodPair] using
      Hatcher.Excision.deletedSubsetPairHom
        h.pointQuotientNeighborhood {pointQuotientPoint P}
  let F := homologyFunctor R n
  have complementMapIsIso :
      IsIso (F.map h.pointQuotientComplementPairIso.hom) := by
    infer_instance
  have targetMapIsIso :
      IsIso (F.map targetExcision) := by
    dsimp only [F, targetExcision]
    exact
      Hatcher.Excision.deletedSubsetHomologyMap_isIso_of_closure_subset_interior
        h.pointQuotientNeighborhood {pointQuotientPoint P}
          h.closure_point_subset_interior_pointQuotientNeighborhood R n
  have targetCompositeIsIso :
      IsIso (F.map (h.pointQuotientComplementPairIso.hom ≫
        targetExcision)) := by
    rw [F.map_comp]
    exact IsIso.comp_isIso' complementMapIsIso targetMapIsIso
  have excisionSquare :
      h.pointQuotientComplementPairIso.hom ≫ targetExcision =
        Hatcher.Excision.deletedSubsetPairHom h.V (Set.range P.map) ≫
          h.neighborhoodPairToPointQuotientNeighborhoodPair := by
    simpa only [targetExcision,
      pointQuotientComplementNeighborhoodPair,
      pointQuotientNeighborhoodPair, id_eq] using
      h.pointQuotientComplement_excisionSquare
  have hfac :
      F.map (Hatcher.Excision.deletedSubsetPairHom
          h.V (Set.range P.map)) ≫
        F.map h.neighborhoodPairToPointQuotientNeighborhoodPair =
      F.map (h.pointQuotientComplementPairIso.hom ≫
        targetExcision) := by
    have hsquare :=
      congrArg (homologyFunctor R n).map excisionSquare.symm
    simp only [Functor.map_comp] at hsquare
    convert hsquare using 1
    all_goals rfl
  exact @IsIso.of_isIso_fac_left C _ _ _ _ _ _ _
    sourceExcisionIsIso targetCompositeIsIso hfac

end GoodPairData

end Hatcher.Relative
