/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Hatcher.Singular.LocalHomology
import Mathlib.Topology.Category.TopCat.Sphere

/-!
# Isolated preimages and local-degree neighborhoods

An isolated preimage of a sphere map is packaged by an open neighborhood on
which no other point maps to the chosen target.  Restricting the map to this
neighborhood gives the canonical morphism between the corresponding
punctured pairs.
-/

open CategoryTheory Set Topology

namespace Hatcher.Sphere

/-- A chosen open neighborhood witnessing that `x` is an isolated preimage
of `y` under a sphere map `f`. -/
structure LocalDegreeNeighborhood {n : ℕ}
    (f : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n)
    (x y : TopCat.sphere.{0} n) where
  /-- The chosen neighborhood of the isolated preimage. -/
  U : Set (TopCat.sphere.{0} n)
  /-- The chosen neighborhood is open. -/
  isOpen_U : IsOpen U
  /-- The isolated preimage belongs to the chosen neighborhood. -/
  x_mem : x ∈ U
  /-- The distinguished source point maps to the target point. -/
  map_eq : f x = y
  /-- No other point of the chosen neighborhood maps to the target. -/
  eq_of_mem_of_map_eq : ∀ {z}, z ∈ U → f z = y → z = x

/-- A point is an isolated preimage when it admits a local-degree
neighborhood. -/
def IsolatedPreimage {n : ℕ}
    (f : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n)
    (x y : TopCat.sphere.{0} n) : Prop :=
  Nonempty (LocalDegreeNeighborhood f x y)

namespace LocalDegreeNeighborhood

variable {n : ℕ}
  {f : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n}
  {x y : TopCat.sphere.{0} n}

/-- Every chosen local-degree neighborhood witnesses that its center is an
isolated preimage. -/
theorem isolatedPreimage (N : LocalDegreeNeighborhood f x y) :
    IsolatedPreimage f x y :=
  ⟨N⟩

/-- Away from the center of a local-degree neighborhood, the map avoids the
chosen target. -/
theorem map_ne_target_of_mem_of_ne (N : LocalDegreeNeighborhood f x y)
    {z : TopCat.sphere.{0} n} (hz : z ∈ N.U) (hzx : z ≠ x) :
    f z ≠ y := by
  intro hzy
  exact hzx (N.eq_of_mem_of_map_eq hz hzy)

/-- Restrict a local-degree neighborhood to a smaller open set containing
the same center. -/
def restrict (N : LocalDegreeNeighborhood f x y)
    (V : Set (TopCat.sphere.{0} n)) (hxV : x ∈ V) (hV : IsOpen V)
    (hVU : V ⊆ N.U) : LocalDegreeNeighborhood f x y where
  U := V
  isOpen_U := hV
  x_mem := hxV
  map_eq := N.map_eq
  eq_of_mem_of_map_eq hz hzy :=
    N.eq_of_mem_of_map_eq (hVU hz) hzy

@[simp]
theorem restrict_U (N : LocalDegreeNeighborhood f x y)
    (V : Set (TopCat.sphere.{0} n)) (hxV : x ∈ V) (hV : IsOpen V)
    (hVU : V ⊆ N.U) :
    (N.restrict V hxV hV hVU).U = V :=
  rfl

private noncomputable def puncturedMap
    {n : ℕ} {f : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n}
    {x y : TopCat.sphere.{0} n}
    (N : LocalDegreeNeighborhood f x y) :
    C(({⟨x, N.x_mem⟩}ᶜ : Set N.U),
      ({y}ᶜ : Set (TopCat.sphere.{0} n))) where
  toFun z := ⟨f z.1.1, by
    have hz : z.1 ≠ (⟨x, N.x_mem⟩ : N.U) := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using z.2
    intro hzy
    exact hz (Subtype.ext (N.eq_of_mem_of_map_eq z.1.2 hzy))⟩
  continuous_toFun :=
    (f.hom.continuous.comp
      (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _

/-- Restricting a sphere map to an isolated-preimage neighborhood gives the
canonical morphism from its punctured pair to the target punctured sphere. -/
noncomputable def pairHom (N : LocalDegreeNeighborhood f x y) :
    Hatcher.Relative.puncturedPair (TopCat.of N.U) ⟨x, N.x_mem⟩ ⟶
      Hatcher.Relative.puncturedPair (TopCat.sphere.{0} n) y :=
  TopPair.ofHom
    (TopCat.ofHom
      { toFun := fun z ↦ f z.1
        continuous_toFun := f.hom.continuous.comp continuous_subtype_val })
    (TopCat.ofHom N.puncturedMap)
    (by ext z; rfl)

/-- The ambient component of the local pair map is the restriction of `f`. -/
@[simp]
theorem pairHom_fst_apply (N : LocalDegreeNeighborhood f x y) (z : N.U) :
    TopPair.Hom.fst N.pairHom z = f z.1 :=
  rfl

/-- The punctured-subspace component of the local pair map is also the
restriction of `f`, independently of subtype membership proofs. -/
@[simp]
theorem pairHom_snd_apply_coe (N : LocalDegreeNeighborhood f x y)
    (z : (Hatcher.Relative.puncturedPair
      (TopCat.of N.U) ⟨x, N.x_mem⟩).snd) :
    (TopPair.Hom.snd
      (pairHom (f := f) (x := x) (y := y) N) z).1 = f z.1.1 :=
  rfl

end LocalDegreeNeighborhood

end Hatcher.Sphere
