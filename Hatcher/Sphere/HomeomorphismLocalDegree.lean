/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Hatcher.Sphere.LocalDegree
import Hatcher.Sphere.DegreeProperties

/-!
# Local degree of a homeomorphism

A local-degree neighborhood on which the map is a homeomorphism onto an open
target neighborhood induces an isomorphism on local homology.  Its local degree
is therefore a unit in `ℤ`.  For a homeomorphism of the whole sphere, naturality
of the ordered local fundamental class identifies that local degree, including
its sign, with the global degree.
-/

noncomputable section

open AlgebraicTopology CategoryTheory Set Topology

namespace Hatcher.Sphere

namespace LocalDegreeNeighborhood

variable {n : ℕ}
  {f : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n}
  {x y : TopCat.sphere.{0} n}

/-- Data saying that a chosen local-degree neighborhood maps homeomorphically
onto an open neighborhood of the target point. -/
structure LocalHomeomorphData (N : LocalDegreeNeighborhood f x y) where
  /-- The open target neighborhood. -/
  V : Set (TopCat.sphere.{0} n)
  /-- The target neighborhood is open. -/
  isOpen_V : IsOpen V
  /-- The distinguished target point belongs to the target neighborhood. -/
  y_mem : y ∈ V
  /-- The restriction of the map is a homeomorphism onto the target
  neighborhood. -/
  e : N.U ≃ₜ V
  /-- The homeomorphism agrees pointwise with the original sphere map. -/
  e_apply : ∀ z : N.U, (e z).1 = f z.1

namespace LocalHomeomorphData

variable {N : LocalDegreeNeighborhood f x y}

/-- The local homeomorphism carries the center of the source neighborhood to
the distinguished target point. -/
theorem map_center (D : LocalHomeomorphData N) :
    D.e ⟨x, N.x_mem⟩ = ⟨y, D.y_mem⟩ := by
  apply Subtype.ext
  rw [D.e_apply]
  exact N.map_eq

/-- The isomorphism between punctured pairs induced by the local
homeomorphism. -/
noncomputable def pairIso (D : LocalHomeomorphData N) :
    Hatcher.Relative.puncturedPair (TopCat.of N.U) ⟨x, N.x_mem⟩ ≅
      Hatcher.Relative.puncturedPair (TopCat.of D.V) ⟨y, D.y_mem⟩ :=
  Hatcher.Relative.puncturedPairIso D.e D.map_center

/-- The punctured-pair isomorphism followed by inclusion of the target
neighborhood is exactly the original local pair map. -/
@[reassoc]
theorem pairIso_hom_comp_localHomologyOpenNeighborhoodPairHom
    (D : LocalHomeomorphData N) :
    D.pairIso.hom ≫
        Hatcher.Relative.localHomologyOpenNeighborhoodPairHom
          y D.V D.y_mem =
      N.pairHom := by
  apply MorphismProperty.Arrow.Hom.ext
  · ext z
    apply Subtype.ext
    exact D.e_apply z.1
  · ext z
    exact D.e_apply z

/-- The actual relative-homology map induced by the local pair map is an
isomorphism in every degree. -/
theorem pairHom_homologyMap_isIso (D : LocalHomeomorphData N) (k : ℕ) :
    IsIso ((Hatcher.Relative.homologyFunctor
      (AddCommGrpCat.of ℤ) k).map N.pairHom) := by
  let _ : T1Space (TopCat.sphere.{0} n) :=
    (sphereULiftHomeomorph n).symm.t1Space
  rw [← D.pairIso_hom_comp_localHomologyOpenNeighborhoodPairHom]
  rw [Functor.map_comp]
  exact IsIso.comp_isIso'
    ((Hatcher.Relative.homologyFunctor
      (AddCommGrpCat.of ℤ) k).mapIso D.pairIso).isIso_hom
    (Hatcher.Relative.localHomologyOpenNeighborhoodMap_isIso_of_t1
      y D.V D.y_mem D.isOpen_V (AddCommGrpCat.of ℤ) k)

end LocalHomeomorphData

end LocalDegreeNeighborhood

/-- The local degree on a chosen neighborhood where the map is a local
homeomorphism is `1` or `-1`. -/
theorem neighborhoodLocalDegree_eq_one_or_neg_one_of_localHomeomorph
    (n : ℕ) (hn : 0 < n)
    {f : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n}
    {x y : TopCat.sphere.{0} n}
    (N : LocalDegreeNeighborhood f x y)
    (D : N.LocalHomeomorphData) :
    neighborhoodLocalDegree n hn N = 1 ∨
      neighborhoodLocalDegree n hn N = -1 := by
  let H := Hatcher.Relative.homologyFunctor (AddCommGrpCat.of ℤ) n
  let d := neighborhoodLocalDegree n hn N
  let a := AddCommGrpCat.asHom (G := AddCommGrpCat.of ℤ) d
  let _ : IsIso (integralSphereNeighborhoodFundamentalClass
      n hn x N.U N.x_mem N.isOpen_U) :=
    integralSphereNeighborhoodFundamentalClass_isIso
      n hn x N.U N.x_mem N.isOpen_U
  let _ : IsIso (H.map N.pairHom) := D.pairHom_homologyMap_isIso n
  let _ : IsIso (integralSphereLocalHomologyIso n hn y).hom :=
    (integralSphereLocalHomologyIso n hn y).isIso_hom
  have ha : IsIso a := by
    change IsIso (AddCommGrpCat.asHom (G := AddCommGrpCat.of ℤ)
      (neighborhoodLocalDegree n hn N))
    rw [← neighborhoodLocalDegreeEndomorphism_eq_asHom n hn N]
    dsimp only [neighborhoodLocalDegreeEndomorphism, H]
    infer_instance
  let _ : IsIso a := ha
  have hcomp : inv a ≫ a = 𝟙 (AddCommGrpCat.of ℤ) := by simp
  have hmul : (inv a (1 : ℤ)) * d = 1 := by
    have h := congrArg (fun q : AddCommGrpCat.of ℤ ⟶
      AddCommGrpCat.of ℤ ↦ q (1 : ℤ)) hcomp
    change a (inv a (1 : ℤ)) = 1 at h
    change (inv a (1 : ℤ)) * d = 1 at h
    exact h
  have hu : IsUnit d :=
    IsUnit.of_mul_eq_one (inv a (1 : ℤ)) (by simpa [mul_comm] using hmul)
  obtain ⟨u, hu'⟩ := hu
  obtain rfl | rfl := Int.units_eq_one_or u
  · left
    simpa [d] using hu'.symm
  · right
    simpa [d] using hu'.symm

/-- The public local degree at an isolated preimage where the map is locally a
homeomorphism is `1` or `-1`. -/
theorem localDegree_eq_one_or_neg_one_of_localHomeomorph
    (n : ℕ) (hn : 0 < n)
    {f : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n}
    {x y : TopCat.sphere.{0} n}
    (h : IsolatedPreimage f x y)
    (N : LocalDegreeNeighborhood f x y)
    (D : N.LocalHomeomorphData) :
    localDegree n hn f x y h = 1 ∨
      localDegree n hn f x y h = -1 := by
  rw [localDegree_eq_neighborhoodLocalDegree n hn f x y h N]
  exact neighborhoodLocalDegree_eq_one_or_neg_one_of_localHomeomorph
    n hn N D

/-- The full sphere is the canonical local-degree neighborhood for a sphere
homeomorphism. -/
def homeomorphLocalDegreeNeighborhood
    {n : ℕ} (e : TopCat.sphere.{0} n ≃ₜ TopCat.sphere.{0} n)
    (x : TopCat.sphere.{0} n) :
    LocalDegreeNeighborhood (TopCat.isoOfHomeo e).hom x (e x) where
  U := Set.univ
  isOpen_U := isOpen_univ
  x_mem := Set.mem_univ x
  map_eq := rfl
  eq_of_mem_of_map_eq _ h := e.injective h

/-- The restriction of a sphere homeomorphism to the canonical full-sphere
neighborhood supplies local-homeomorphism data. -/
noncomputable def homeomorphLocalHomeomorphData
    {n : ℕ} (e : TopCat.sphere.{0} n ≃ₜ TopCat.sphere.{0} n)
    (x : TopCat.sphere.{0} n) :
    (homeomorphLocalDegreeNeighborhood e x).LocalHomeomorphData where
  V := Set.univ
  isOpen_V := isOpen_univ
  y_mem := Set.mem_univ (e x)
  e := e.subtype fun z ↦ by
    change z ∈ Set.univ ↔ e z ∈ Set.univ
    simp
  e_apply _ := rfl

/-- The pair map of the canonical full-sphere neighborhood factors as the
inclusion of that neighborhood followed by the punctured-pair isomorphism of
the homeomorphism. -/
@[reassoc]
theorem homeomorphLocalDegreeNeighborhood_pairHom
    {n : ℕ} (e : TopCat.sphere.{0} n ≃ₜ TopCat.sphere.{0} n)
    (x : TopCat.sphere.{0} n) :
    Hatcher.Relative.localHomologyOpenNeighborhoodPairHom
          x Set.univ (Set.mem_univ x) ≫
        (Hatcher.Relative.puncturedPairIso e rfl).hom =
      (homeomorphLocalDegreeNeighborhood e x).pairHom := by
  apply MorphismProperty.Arrow.Hom.ext
  · ext z
    rfl
  · ext z
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- A sphere homeomorphism sends the ordered local class to the global-degree
multiple of the ordered local class at the image point. -/
@[reassoc]
theorem integralSphereLocalFundamentalClass_map_homeomorph
    (n : ℕ) (hn : 0 < n)
    (e : TopCat.sphere.{0} n ≃ₜ TopCat.sphere.{0} n)
    (x : TopCat.sphere.{0} n) :
    integralSphereLocalFundamentalClass n hn x ≫
        (Hatcher.Relative.homologyFunctor
          (AddCommGrpCat.of ℤ) n).map
            (Hatcher.Relative.puncturedPairIso e rfl).hom =
      AddCommGrpCat.asHom (degree n hn (TopCat.isoOfHomeo e).hom) ≫
        integralSphereLocalFundamentalClass n hn (e x) := by
  have hordered :
      Hatcher.Simplex.doubleSimplexSphereFundamentalClass
            (AddCommGrpCat.of ℤ) n ≫
          (Hatcher.Reduced.homologyFunctor
            (AddCommGrpCat.of ℤ) n).map (TopCat.isoOfHomeo e).hom =
        AddCommGrpCat.asHom (degree n hn (TopCat.isoOfHomeo e).hom) ≫
          Hatcher.Simplex.doubleSimplexSphereFundamentalClass
            (AddCommGrpCat.of ℤ) n := by
    let i := Hatcher.Reduced.homologyIsoOfPositiveDegree
      (C := AddCommGrpCat.{0}) (AddCommGrpCat.of ℤ) n hn
    have hnat := i.hom.naturality (TopCat.isoOfHomeo e).hom
    rw [← cancel_mono (i.hom.app (TopCat.sphere.{0} n))]
    rw [Category.assoc, hnat]
    change integralSphereFundamentalClass n hn ≫
        ((singularHomologyFunctor AddCommGrpCat n).obj
          (AddCommGrpCat.of ℤ)).map (TopCat.isoOfHomeo e).hom =
      AddCommGrpCat.asHom (degree n hn (TopCat.isoOfHomeo e).hom) ≫
        integralSphereFundamentalClass n hn
    exact integralSphereFundamentalClass_map
      n hn (TopCat.isoOfHomeo e).hom
  dsimp only [integralSphereLocalFundamentalClass]
  rw [Category.assoc,
    Hatcher.Relative.reducedPairProjection_naturality]
  change
    Hatcher.Simplex.doubleSimplexSphereFundamentalClass
          (AddCommGrpCat.of ℤ) n ≫
        (Hatcher.Reduced.homologyFunctor
          (AddCommGrpCat.of ℤ) n).map (TopCat.isoOfHomeo e).hom ≫
        Hatcher.Relative.reducedPairProjection
          (Hatcher.Relative.puncturedPair
            (TopCat.sphere.{0} n) (e x))
          (AddCommGrpCat.of ℤ) n =
      AddCommGrpCat.asHom (degree n hn (TopCat.isoOfHomeo e).hom) ≫
        Hatcher.Simplex.doubleSimplexSphereFundamentalClass
          (AddCommGrpCat.of ℤ) n ≫
        Hatcher.Relative.reducedPairProjection
          (Hatcher.Relative.puncturedPair
            (TopCat.sphere.{0} n) (e x))
          (AddCommGrpCat.of ℤ) n
  rw [← Category.assoc, hordered, Category.assoc]

/-- For every isolation witness, the local degree of a sphere homeomorphism is
its ordered global degree. -/
theorem localDegree_homeomorph_eq_degree
    (n : ℕ) (hn : 0 < n)
    (e : TopCat.sphere.{0} n ≃ₜ TopCat.sphere.{0} n)
    (x : TopCat.sphere.{0} n)
    (h : IsolatedPreimage (TopCat.isoOfHomeo e).hom x (e x)) :
    localDegree n hn (TopCat.isoOfHomeo e).hom x (e x) h =
      degree n hn (TopCat.isoOfHomeo e).hom := by
  let N := homeomorphLocalDegreeNeighborhood e x
  let H := Hatcher.Relative.homologyFunctor (AddCommGrpCat.of ℤ) n
  have hcanonical :
      integralSphereNeighborhoodFundamentalClass
            n hn x N.U N.x_mem N.isOpen_U ≫
          H.map N.pairHom =
        AddCommGrpCat.asHom (degree n hn (TopCat.isoOfHomeo e).hom) ≫
          integralSphereLocalFundamentalClass n hn (e x) := by
    have hsource :
        integralSphereNeighborhoodFundamentalClass
              n hn x Set.univ (Set.mem_univ x) isOpen_univ ≫
            (Hatcher.Relative.homologyFunctor
              (AddCommGrpCat.of ℤ) n).map
                (Hatcher.Relative.localHomologyOpenNeighborhoodPairHom
                  x Set.univ (Set.mem_univ x)) =
          integralSphereLocalFundamentalClass n hn x := by
      exact integralSphereNeighborhoodFundamentalClass_map
        n hn x Set.univ (Set.mem_univ x) isOpen_univ
    change
      integralSphereNeighborhoodFundamentalClass
            n hn x Set.univ (Set.mem_univ x) isOpen_univ ≫
          H.map (homeomorphLocalDegreeNeighborhood e x).pairHom =
        AddCommGrpCat.asHom (degree n hn (TopCat.isoOfHomeo e).hom) ≫
          integralSphereLocalFundamentalClass n hn (e x)
    dsimp only [H]
    rw [← homeomorphLocalDegreeNeighborhood_pairHom e x]
    rw [Functor.map_comp, ← Category.assoc]
    rw [hsource]
    exact integralSphereLocalFundamentalClass_map_homeomorph n hn e x
  have hscaled :
      AddCommGrpCat.asHom
            (localDegree n hn (TopCat.isoOfHomeo e).hom x (e x) h) ≫
          integralSphereLocalFundamentalClass n hn (e x) =
        AddCommGrpCat.asHom (degree n hn (TopCat.isoOfHomeo e).hom) ≫
          integralSphereLocalFundamentalClass n hn (e x) := by
    rw [← localFundamentalClass_map_eq_localDegree
      n hn (TopCat.isoOfHomeo e).hom x (e x) h N]
    exact hcanonical
  let _ : IsIso (integralSphereLocalFundamentalClass n hn (e x)) :=
    integralSphereLocalFundamentalClass_isIso n hn (e x)
  apply AddCommGrpCat.asHom_injective
  rw [← cancel_mono (integralSphereLocalFundamentalClass n hn (e x))]
  exact hscaled

end Hatcher.Sphere
