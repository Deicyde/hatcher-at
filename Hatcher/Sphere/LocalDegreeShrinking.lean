/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Hatcher.Sphere.NeighborhoodLocalDegree

/-!
# Local degree is independent under shrinking

The punctured-pair map of a smaller isolated-preimage neighborhood factors
through that of every containing neighborhood.  Naturality of the ordered
local fundamental classes then shows that both neighborhoods have the same
local degree.
-/

noncomputable section

open AlgebraicTopology CategoryTheory Set Topology

namespace Hatcher.Sphere

namespace LocalDegreeNeighborhood

variable {n : ℕ}
  {f : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n}
  {x y : TopCat.sphere.{0} n}

set_option backward.isDefEq.respectTransparency false in
/-- Inclusion from a smaller punctured neighborhood followed by its containing
neighborhood's local pair map is the smaller neighborhood's local pair map. -/
@[reassoc]
theorem restrictionPairHom_comp_pairHom
    (M N : LocalDegreeNeighborhood f x y) (hMN : M.U ⊆ N.U) :
    Hatcher.Relative.localHomologyOpenNeighborhoodRestrictionPairHom
        x M.U N.U M.x_mem N.x_mem hMN ≫
      N.pairHom =
    M.pairHom := by
  apply MorphismProperty.Arrow.Hom.ext
  · ext z
    apply Subtype.ext
    change f z.1.1 = f z.1.1
    rfl
  · ext z
    change f z.1 = f z.1
    rfl

/-- The local-homology map of a smaller neighborhood factors through every
containing neighborhood. -/
@[reassoc]
theorem restrictionMap_comp_pairHom_map
    (M N : LocalDegreeNeighborhood f x y) (hMN : M.U ⊆ N.U)
    (k : ℕ) :
    Hatcher.Relative.localHomologyOpenNeighborhoodRestrictionMap
          x M.U N.U M.x_mem N.x_mem hMN (AddCommGrpCat.of ℤ) k ≫
        (Hatcher.Relative.homologyFunctor
          (AddCommGrpCat.of ℤ) k).map N.pairHom =
      (Hatcher.Relative.homologyFunctor
        (AddCommGrpCat.of ℤ) k).map M.pairHom := by
  change
    (Hatcher.Relative.homologyFunctor (AddCommGrpCat.of ℤ) k).map
          (Hatcher.Relative.localHomologyOpenNeighborhoodRestrictionPairHom
            x M.U N.U M.x_mem N.x_mem hMN) ≫
        (Hatcher.Relative.homologyFunctor
          (AddCommGrpCat.of ℤ) k).map N.pairHom =
      (Hatcher.Relative.homologyFunctor
        (AddCommGrpCat.of ℤ) k).map M.pairHom
  rw [← Functor.map_comp, restrictionPairHom_comp_pairHom]

/-- On spheres, the restriction map from one open local neighborhood to a
containing one is an isomorphism on relative homology. -/
theorem restrictionMap_isIso
    (M N : LocalDegreeNeighborhood f x y) (hMN : M.U ⊆ N.U)
    (k : ℕ) :
    IsIso (Hatcher.Relative.localHomologyOpenNeighborhoodRestrictionMap
      x M.U N.U M.x_mem N.x_mem hMN (AddCommGrpCat.of ℤ) k) := by
  let _ : T1Space (TopCat.sphere.{0} n) :=
    (sphereULiftHomeomorph n).symm.t1Space
  exact Hatcher.Relative.localHomologyOpenNeighborhoodRestrictionMap_isIso_of_t1
    x M.U N.U M.x_mem N.x_mem hMN M.isOpen_U N.isOpen_U
      (AddCommGrpCat.of ℤ) k

end LocalDegreeNeighborhood

/-- **Hatcher, local degree (printed page 136).** Shrinking an
isolated-preimage neighborhood does not change its local degree. -/
theorem neighborhoodLocalDegree_eq_of_subset
    (n : ℕ) (hn : 0 < n)
    {f : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n}
    {x y : TopCat.sphere.{0} n}
    (M N : LocalDegreeNeighborhood f x y) (hMN : M.U ⊆ N.U) :
    neighborhoodLocalDegree n hn M = neighborhoodLocalDegree n hn N := by
  let R := AddCommGrpCat.of ℤ
  let H := Hatcher.Relative.homologyFunctor R n
  let r := Hatcher.Relative.localHomologyOpenNeighborhoodRestrictionMap
    x M.U N.U M.x_mem N.x_mem hMN R n
  let classM := integralSphereNeighborhoodFundamentalClass
    n hn x M.U M.x_mem M.isOpen_U
  let classN := integralSphereNeighborhoodFundamentalClass
    n hn x N.U N.x_mem N.isOpen_U
  have htriangle :
      r ≫ H.map N.pairHom = H.map M.pairHom := by
    exact LocalDegreeNeighborhood.restrictionMap_comp_pairHom_map
      M N hMN n
  have hclass : classM ≫ r = classN := by
    exact integralSphereNeighborhoodFundamentalClass_restrict
      n hn x M.U N.U M.x_mem N.x_mem M.isOpen_U N.isOpen_U hMN
  have hmaps :
      classM ≫ H.map M.pairHom = classN ≫ H.map N.pairHom := by
    calc
      classM ≫ H.map M.pairHom =
          classM ≫ (r ≫ H.map N.pairHom) := by rw [htriangle]
      _ = (classM ≫ r) ≫ H.map N.pairHom :=
        (Category.assoc _ _ _).symm
      _ = classN ≫ H.map N.pairHom := by rw [hclass]
  have hscaled :
      AddCommGrpCat.asHom (neighborhoodLocalDegree n hn M) ≫
          integralSphereLocalFundamentalClass n hn y =
        AddCommGrpCat.asHom (neighborhoodLocalDegree n hn N) ≫
          integralSphereLocalFundamentalClass n hn y := by
    calc
      _ = classM ≫ H.map M.pairHom :=
        (localFundamentalClass_map_eq_neighborhoodLocalDegree n hn M).symm
      _ = classN ≫ H.map N.pairHom := hmaps
      _ = _ := localFundamentalClass_map_eq_neighborhoodLocalDegree n hn N
  let _ : IsIso (integralSphereLocalFundamentalClass n hn y) :=
    integralSphereLocalFundamentalClass_isIso n hn y
  have hhom :
      AddCommGrpCat.asHom (G := AddCommGrpCat.of ℤ)
          (neighborhoodLocalDegree n hn M) =
        AddCommGrpCat.asHom (G := AddCommGrpCat.of ℤ)
          (neighborhoodLocalDegree n hn N) := by
    rw [← cancel_mono (integralSphereLocalFundamentalClass n hn y)]
    exact hscaled
  exact AddCommGrpCat.asHom_injective hhom

end Hatcher.Sphere
