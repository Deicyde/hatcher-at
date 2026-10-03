/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Hatcher.Singular.Homology
import Hatcher.Singular.PointQuotientNeighborhoodContraction
import Hatcher.Singular.RelativeIsomorphism

/-!
# Relative homology of point-quotient neighborhoods

For a good pair `(X, A)`, this file proves that enlarging the collapsed point
`A/A` to the contracted quotient neighborhood `V/A` preserves relative
homology.  The map is the canonical map of pairs already used in the
Proposition 2.22 diagram.
-/

noncomputable section

open AlgebraicTopology CategoryTheory Limits

namespace Hatcher.Relative

universe w v u

namespace GoodPairData

variable {P : TopPair.{w}}
variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C]

/-- Enlarging the collapsed point in `X/A` to the quotient neighborhood
`V/A` induces an isomorphism on relative homology in every degree, including
degree zero. -/
instance pointQuotientPairToNeighborhoodPair_homologyMap_isIso
    (h : GoodPairData P) (R : C) (n : ℕ) :
    IsIso ((homologyFunctor R n).map h.pointQuotientPairToNeighborhoodPair) := by
  apply homologyMap_isIso_of_components
  · intro k
    let e := h.pointQuotientNeighborhoodHomotopyEquiv
    change IsIso (((singularHomologyFunctor C k).obj R).map
      (TopCat.ofHom e.toFun))
    exact (Hatcher.Singular.homologyIsoOfHomotopyEquiv e R k).isIso_hom
  · intro k
    change IsIso (((singularHomologyFunctor C k).obj R).map
      (𝟙 (pointQuotient P)))
    infer_instance

end GoodPairData

end Hatcher.Relative
