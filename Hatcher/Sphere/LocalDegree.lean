/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Hatcher.Sphere.LocalDegreeShrinking

/-!
# Local degree at an isolated preimage

Any two isolated-preimage neighborhoods have a common refinement, so shrinking
invariance makes their local degrees equal.  This permits a choice-independent
public local degree and a fundamental-class equation stated against every
chosen neighborhood.
-/

noncomputable section

open AlgebraicTopology CategoryTheory Set Topology

namespace Hatcher.Sphere

namespace LocalDegreeNeighborhood

variable {n : ℕ}
  {f : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n}
  {x y : TopCat.sphere.{0} n}

/-- The intersection of two local-degree neighborhoods is a common
local-degree neighborhood. -/
def inter (N M : LocalDegreeNeighborhood f x y) :
    LocalDegreeNeighborhood f x y where
  U := N.U ∩ M.U
  isOpen_U := N.isOpen_U.inter M.isOpen_U
  x_mem := ⟨N.x_mem, M.x_mem⟩
  map_eq := N.map_eq
  eq_of_mem_of_map_eq hz hzy :=
    N.eq_of_mem_of_map_eq hz.1 hzy

@[simp]
theorem inter_U (N M : LocalDegreeNeighborhood f x y) :
    (N.inter M).U = N.U ∩ M.U :=
  rfl

/-- The intersection neighborhood is contained in its left member. -/
theorem inter_U_subset_left (N M : LocalDegreeNeighborhood f x y) :
    (N.inter M).U ⊆ N.U :=
  Set.inter_subset_left

/-- The intersection neighborhood is contained in its right member. -/
theorem inter_U_subset_right (N M : LocalDegreeNeighborhood f x y) :
    (N.inter M).U ⊆ M.U :=
  Set.inter_subset_right

end LocalDegreeNeighborhood

/-- Any two packaged neighborhoods of the same isolated preimage determine the
same local degree. -/
theorem neighborhoodLocalDegree_eq
    (n : ℕ) (hn : 0 < n)
    {f : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n}
    {x y : TopCat.sphere.{0} n}
    (N M : LocalDegreeNeighborhood f x y) :
    neighborhoodLocalDegree n hn N = neighborhoodLocalDegree n hn M := by
  let I := N.inter M
  calc
    neighborhoodLocalDegree n hn N =
        neighborhoodLocalDegree n hn I :=
      (neighborhoodLocalDegree_eq_of_subset n hn I N
        (LocalDegreeNeighborhood.inter_U_subset_left N M)).symm
    _ = neighborhoodLocalDegree n hn M :=
      neighborhoodLocalDegree_eq_of_subset n hn I M
        (LocalDegreeNeighborhood.inter_U_subset_right N M)

/-- **Hatcher, local degree (printed page 136).** The local degree at an
isolated preimage, independent of the chosen isolating neighborhood. -/
noncomputable def localDegree
    (n : ℕ) (hn : 0 < n)
    (f : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n)
    (x y : TopCat.sphere.{0} n) (h : IsolatedPreimage f x y) : ℤ :=
  neighborhoodLocalDegree n hn (Classical.choice h)

/-- The public local degree agrees with the degree computed in every packaged
isolated-preimage neighborhood. -/
theorem localDegree_eq_neighborhoodLocalDegree
    (n : ℕ) (hn : 0 < n)
    (f : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n)
    (x y : TopCat.sphere.{0} n) (h : IsolatedPreimage f x y)
    (N : LocalDegreeNeighborhood f x y) :
    localDegree n hn f x y h = neighborhoodLocalDegree n hn N := by
  unfold localDegree
  exact neighborhoodLocalDegree_eq n hn (Classical.choice h) N

/-- The public local degree is proof-irrelevant in the witness that the
preimage is isolated. -/
theorem localDegree_proof_irrel
    (n : ℕ) (hn : 0 < n)
    (f : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n)
    (x y : TopCat.sphere.{0} n)
    (h₁ h₂ : IsolatedPreimage f x y) :
    localDegree n hn f x y h₁ = localDegree n hn f x y h₂ := by
  let N : LocalDegreeNeighborhood f x y := Classical.choice h₁
  calc
    localDegree n hn f x y h₁ = neighborhoodLocalDegree n hn N :=
      localDegree_eq_neighborhoodLocalDegree n hn f x y h₁ N
    _ = localDegree n hn f x y h₂ :=
      (localDegree_eq_neighborhoodLocalDegree n hn f x y h₂ N).symm

/-- **Hatcher, local-degree characterization (printed page 136).** For every
isolating neighborhood, the induced local-homology map sends its ordered source
class to the public local-degree multiple of the ordered target class. -/
@[reassoc]
theorem localFundamentalClass_map_eq_localDegree
    (n : ℕ) (hn : 0 < n)
    (f : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n)
    (x y : TopCat.sphere.{0} n) (h : IsolatedPreimage f x y)
    (N : LocalDegreeNeighborhood f x y) :
    integralSphereNeighborhoodFundamentalClass
          n hn x N.U N.x_mem N.isOpen_U ≫
        (Hatcher.Relative.homologyFunctor (AddCommGrpCat.of ℤ) n).map N.pairHom =
      AddCommGrpCat.asHom (localDegree n hn f x y h) ≫
        integralSphereLocalFundamentalClass n hn y := by
  rw [localDegree_eq_neighborhoodLocalDegree n hn f x y h N]
  exact localFundamentalClass_map_eq_neighborhoodLocalDegree n hn N

end Hatcher.Sphere


namespace Hatcher.Sphere

namespace LocalDegreeNeighborhood

variable {n : ℕ}
  {f g : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n}
  {x y : TopCat.sphere.{0} n}

/-- Transfer an isolating neighborhood to a map that agrees on its open set. -/
def ofEqOn (N : LocalDegreeNeighborhood f x y) (hfg : Set.EqOn f g N.U) :
    LocalDegreeNeighborhood g x y where
  U := N.U
  isOpen_U := N.isOpen_U
  x_mem := N.x_mem
  map_eq := (hfg N.x_mem).symm.trans N.map_eq
  eq_of_mem_of_map_eq hz hzy :=
    N.eq_of_mem_of_map_eq hz ((hfg hz).trans hzy)

set_option backward.isDefEq.respectTransparency false in
/-- Agreement on an isolating neighborhood identifies the actual induced
morphisms of punctured pairs. -/
theorem pairHom_ofEqOn
    (N : LocalDegreeNeighborhood f x y) (hfg : Set.EqOn f g N.U) :
    (N.ofEqOn hfg).pairHom = N.pairHom := by
  apply MorphismProperty.Arrow.Hom.ext
  · ext z
    apply Subtype.ext
    change g z.1.1 = f z.1.1
    exact (hfg z.1.2).symm
  · ext z
    change g z.1 = f z.1
    exact (hfg z.2).symm

end LocalDegreeNeighborhood

/-- Agreement on an open neighborhood preserves isolation and the signed
local degree, for every choice of isolation witnesses. -/
theorem localDegree_germ_invariance
    (n : ℕ) (hn : 0 < n)
    {f g : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n}
    {x y : TopCat.sphere.{0} n}
    (U : Set (TopCat.sphere.{0} n))
    (hU : IsOpen U) (hxU : x ∈ U)
    (hfg : Set.EqOn f g U) (hf : IsolatedPreimage f x y) :
    IsolatedPreimage g x y ∧
      ∀ (hf' : IsolatedPreimage f x y) (hg : IsolatedPreimage g x y),
        localDegree n hn f x y hf' = localDegree n hn g x y hg := by
  classical
  let N : LocalDegreeNeighborhood f x y := Classical.choice hf
  let M := N.restrict (N.U ∩ U) ⟨N.x_mem, hxU⟩
    (N.isOpen_U.inter hU) Set.inter_subset_left
  have hfgM : Set.EqOn f g M.U := by
    intro z hz
    exact hfg hz.2
  let Ng := M.ofEqOn hfgM
  refine ⟨Ng.isolatedPreimage, ?_⟩
  intro hf' hg
  let H := Hatcher.Relative.homologyFunctor (AddCommGrpCat.of ℤ) n
  let classM := integralSphereNeighborhoodFundamentalClass
    n hn x M.U M.x_mem M.isOpen_U
  have hpair : Ng.pairHom = M.pairHom :=
    M.pairHom_ofEqOn hfgM
  have hscaled :
      AddCommGrpCat.asHom (localDegree n hn f x y hf') ≫
          integralSphereLocalFundamentalClass n hn y =
        AddCommGrpCat.asHom (localDegree n hn g x y hg) ≫
          integralSphereLocalFundamentalClass n hn y := by
    calc
      _ = classM ≫ H.map M.pairHom :=
        (localFundamentalClass_map_eq_localDegree n hn f x y hf' M).symm
      _ = classM ≫ H.map Ng.pairHom := by rw [hpair]
      _ = _ := localFundamentalClass_map_eq_localDegree n hn g x y hg Ng
  let _ : IsIso (integralSphereLocalFundamentalClass n hn y) :=
    integralSphereLocalFundamentalClass_isIso n hn y
  have hhom :
      AddCommGrpCat.asHom (G := AddCommGrpCat.of ℤ)
          (localDegree n hn f x y hf') =
        AddCommGrpCat.asHom (G := AddCommGrpCat.of ℤ)
          (localDegree n hn g x y hg) := by
    rw [← cancel_mono (integralSphereLocalFundamentalClass n hn y)]
    exact hscaled
  exact AddCommGrpCat.asHom_injective hhom

end Hatcher.Sphere
