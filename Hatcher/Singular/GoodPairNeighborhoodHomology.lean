/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Hatcher.Singular.GoodPair
import Hatcher.Singular.Homology
import Hatcher.Singular.RelativeIsomorphism

/-!
# Relative homology of a good-pair neighborhood

For a good pair `(X, A)` with chosen neighborhood `V`, this file packages the
canonical map of pairs `(X, A) ⟶ (X, V)` and proves that it induces an
isomorphism on relative homology in every degree.
-/

noncomputable section

open AlgebraicTopology CategoryTheory Limits

namespace Hatcher.Relative

universe w v u

namespace GoodPairData

variable {P : TopPair.{w}}

/-- The ambient space paired with the chosen good-pair neighborhood. -/
def neighborhoodPair (h : GoodPairData P) : TopPair.{w} :=
  TopPair.ofSubset h.V

/-- The canonical map of pairs `(X, A) ⟶ (X, V)` associated to chosen
good-pair data. Its ambient component is the identity and its subspace
component is the chosen neighborhood inclusion. -/
def neighborhoodPairHom (h : GoodPairData P) : P ⟶ h.neighborhoodPair :=
  TopPair.ofHom
    (𝟙 P.fst)
    (TopCat.ofHom
      (goodPairNeighborhoodInclusion P h.V
        (h.range_subset_interior.trans interior_subset)))
    (by ext; rfl)

@[simp]
lemma neighborhoodPairHom_fst (h : GoodPairData P) :
    TopPair.Hom.fst h.neighborhoodPairHom = 𝟙 P.fst := rfl

@[simp]
lemma neighborhoodPairHom_snd (h : GoodPairData P) :
    TopPair.Hom.snd h.neighborhoodPairHom =
      TopCat.ofHom
        (goodPairNeighborhoodInclusion P h.V
          (h.range_subset_interior.trans interior_subset)) := rfl

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C]

/-- Enlarging the subspace of a good pair to its chosen neighborhood induces
an isomorphism on relative homology in every degree, including degree zero. -/
instance neighborhoodPairHom_homologyMap_isIso
    (h : GoodPairData P) (R : C) (n : ℕ) :
    IsIso ((homologyFunctor R n).map h.neighborhoodPairHom) := by
  apply homologyMap_isIso_of_components
  · intro k
    let e := h.strongDeformationRetract.toHomotopyEquiv.symm
    change IsIso (((singularHomologyFunctor C k).obj R).map
      (TopCat.ofHom e.toFun))
    exact (Hatcher.Singular.homologyIsoOfHomotopyEquiv e R k).isIso_hom
  · intro k
    change IsIso (((singularHomologyFunctor C k).obj R).map (𝟙 P.fst))
    infer_instance

end GoodPairData

end Hatcher.Relative
