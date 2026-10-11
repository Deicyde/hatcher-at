/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Hatcher.Sphere.LocalDegreeNeighborhood
import Hatcher.Sphere.LocalOrientation

/-!
# Local degree on a chosen neighborhood

An isolated-preimage neighborhood determines a map between oriented local
homology groups.  Conjugating this map through the ordered integral
orientations gives an endomorphism of `ℤ`; its value at `1` is the local degree
on the chosen neighborhood.
-/

noncomputable section

open AlgebraicTopology CategoryTheory

namespace Hatcher.Sphere

/-- The endomorphism of `ℤ` obtained from the map on local homology of a chosen
isolated-preimage neighborhood and the ordered local orientations. -/
noncomputable def neighborhoodLocalDegreeEndomorphism
    (n : ℕ) (hn : 0 < n)
    {f : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n}
    {x y : TopCat.sphere.{0} n} (N : LocalDegreeNeighborhood f x y) :
    AddCommGrpCat.of ℤ ⟶ AddCommGrpCat.of ℤ :=
  integralSphereNeighborhoodFundamentalClass
      n hn x N.U N.x_mem N.isOpen_U ≫
    (Hatcher.Relative.homologyFunctor (AddCommGrpCat.of ℤ) n).map N.pairHom ≫
    (integralSphereLocalHomologyIso n hn y).hom

/-- **Hatcher, local degree (printed page 136).** The local degree on a chosen
isolated-preimage neighborhood is the image of `1` under the corresponding
oriented local-homology endomorphism. -/
noncomputable def neighborhoodLocalDegree
    (n : ℕ) (hn : 0 < n)
    {f : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n}
    {x y : TopCat.sphere.{0} n} (N : LocalDegreeNeighborhood f x y) : ℤ :=
  neighborhoodLocalDegreeEndomorphism n hn N (1 : ℤ)

/-- The conjugated local-homology endomorphism is multiplication by the local
degree on the chosen neighborhood. -/
theorem neighborhoodLocalDegreeEndomorphism_eq_asHom
    (n : ℕ) (hn : 0 < n)
    {f : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n}
    {x y : TopCat.sphere.{0} n} (N : LocalDegreeNeighborhood f x y) :
    neighborhoodLocalDegreeEndomorphism n hn N =
      AddCommGrpCat.asHom (neighborhoodLocalDegree n hn N) := by
  apply AddCommGrpCat.int_hom_ext
  change neighborhoodLocalDegree n hn N =
    (1 : ℤ) • neighborhoodLocalDegree n hn N
  simp

/-- **Hatcher, local-degree characterization (printed page 136).** The map on
local homology sends the ordered source class to the local-degree multiple of
the ordered target class. -/
@[reassoc]
theorem localFundamentalClass_map_eq_neighborhoodLocalDegree
    (n : ℕ) (hn : 0 < n)
    {f : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n}
    {x y : TopCat.sphere.{0} n} (N : LocalDegreeNeighborhood f x y) :
    integralSphereNeighborhoodFundamentalClass
          n hn x N.U N.x_mem N.isOpen_U ≫
        (Hatcher.Relative.homologyFunctor (AddCommGrpCat.of ℤ) n).map N.pairHom =
      AddCommGrpCat.asHom (neighborhoodLocalDegree n hn N) ≫
        integralSphereLocalFundamentalClass n hn y := by
  rw [← cancel_mono (integralSphereLocalHomologyIso n hn y).hom]
  simpa only [neighborhoodLocalDegreeEndomorphism, Category.assoc,
    integralSphereLocalFundamentalClass_comp_homologyIso,
    Category.comp_id] using
      neighborhoodLocalDegreeEndomorphism_eq_asHom n hn N

end Hatcher.Sphere
