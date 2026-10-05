/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Hatcher.Sphere.DegreeProperties
import Mathlib.Data.ZMod.IntUnitsPower
import Mathlib.Tactic.FinCases

/-!
# The degree character of a sphere action

An action is represented exactly as a homomorphism into the group of
self-homeomorphisms.  In positive dimension the degrees of these
homeomorphisms are units of `ℤ`, and multiplicativity of degree packages them
as a character.  We also identify the two-element group `ℤˣ` explicitly with
the additive group `ZMod 2`, written multiplicatively.
-/

noncomputable section

open CategoryTheory

namespace Hatcher.Sphere

/-- An action of `G` on the standard `n`-sphere, represented as Hatcher does
by a homomorphism to the group of self-homeomorphisms. -/
abbrev SphereAction (G : Type*) [Group G] (n : ℕ) :=
  G →* (((TopCat.sphere.{0} n : TopCat.{0}) : Type) ≃ₜ
    ((TopCat.sphere.{0} n : TopCat.{0}) : Type))

namespace SphereAction

variable {G : Type*} [Group G] {n : ℕ}

/-- A sphere action is free when every nonidentity element acts without a
fixed point. -/
def IsFree (ρ : SphereAction G n) : Prop :=
  ∀ g, g ≠ 1 → ∀ x, ρ g x ≠ x

end SphereAction

/-- The degree of each acting homeomorphism, bundled as a multiplicative
character with values in the units of `ℤ`. -/
noncomputable def sphereActionDegreeHom
    {G : Type*} [Group G] (n : ℕ) (hn : 0 < n)
    (ρ : SphereAction G n) : G →* ℤˣ where
  toFun g := (isUnit_degree_of_homeomorph n hn (ρ g)).unit
  map_one' := by
    apply Units.ext
    rw [IsUnit.unit_spec]
    rw [ρ.map_one]
    change degree n hn (𝟙 _) = 1
    exact degree_id n hn
  map_mul' g h := by
    apply Units.ext
    simp only [Units.val_mul, IsUnit.unit_spec]
    rw [ρ.map_mul]
    change degree n hn
        ((TopCat.isoOfHomeo (ρ h)).hom ≫
          (TopCat.isoOfHomeo (ρ g)).hom) =
      degree n hn (TopCat.isoOfHomeo (ρ g)).hom *
        degree n hn (TopCat.isoOfHomeo (ρ h)).hom
    rw [degree_comp, mul_comm]

/-- The underlying integer of the action-degree character at `g` is the
degree of the homeomorphism `ρ g`. -/
@[simp]
theorem sphereActionDegreeHom_coe
    {G : Type*} [Group G] (n : ℕ) (hn : 0 < n)
    (ρ : SphereAction G n) (g : G) :
    ((sphereActionDegreeHom n hn ρ g : ℤˣ) : ℤ) =
      degree n hn (TopCat.isoOfHomeo (ρ g)).hom :=
  IsUnit.unit_spec (isUnit_degree_of_homeomorph n hn (ρ g))

/-- The homomorphism from the additive group `ZMod 2`, written
multiplicatively, to `ℤˣ` that sends `1` to `-1`. -/
def zmodTwoToIntUnitsHom : Multiplicative (ZMod 2) →* ℤˣ where
  toFun z := (-1 : ℤˣ) ^ z.toAdd
  map_one' := by simp
  map_mul' x y := by
    change (-1 : ℤˣ) ^ (x.toAdd + y.toAdd) =
      (-1 : ℤˣ) ^ x.toAdd * (-1 : ℤˣ) ^ y.toAdd
    exact uzpow_add (-1 : ℤˣ) x.toAdd y.toAdd

@[simp]
theorem zmodTwoToIntUnitsHom_zero :
    zmodTwoToIntUnitsHom (Multiplicative.ofAdd (0 : ZMod 2)) = 1 := by
  simp [zmodTwoToIntUnitsHom]

@[simp]
theorem zmodTwoToIntUnitsHom_one :
    zmodTwoToIntUnitsHom (Multiplicative.ofAdd (1 : ZMod 2)) = -1 := by
  simp [zmodTwoToIntUnitsHom]

private theorem zmodTwo_eq_zero_or_one (z : ZMod 2) : z = 0 ∨ z = 1 := by
  fin_cases z
  · exact Or.inl rfl
  · exact Or.inr rfl

private theorem zmodTwoToIntUnitsHom_bijective :
    Function.Bijective zmodTwoToIntUnitsHom := by
  constructor
  · intro x y hxy
    apply Multiplicative.toAdd.injective
    obtain hx | hx := zmodTwo_eq_zero_or_one x.toAdd
    · obtain hy | hy := zmodTwo_eq_zero_or_one y.toAdd
      · exact hx.trans hy.symm
      · have hx' : x = Multiplicative.ofAdd (0 : ZMod 2) :=
          Multiplicative.toAdd.injective (by simpa using hx)
        have hy' : y = Multiplicative.ofAdd (1 : ZMod 2) :=
          Multiplicative.toAdd.injective (by simpa using hy)
        subst x
        subst y
        simp at hxy
    · obtain hy | hy := zmodTwo_eq_zero_or_one y.toAdd
      · have hx' : x = Multiplicative.ofAdd (1 : ZMod 2) :=
          Multiplicative.toAdd.injective (by simpa using hx)
        have hy' : y = Multiplicative.ofAdd (0 : ZMod 2) :=
          Multiplicative.toAdd.injective (by simpa using hy)
        subst x
        subst y
        simp at hxy
      · exact hx.trans hy.symm
  · intro u
    obtain rfl | rfl := Int.units_eq_one_or u
    · exact ⟨Multiplicative.ofAdd 0, zmodTwoToIntUnitsHom_zero⟩
    · exact ⟨Multiplicative.ofAdd 1, zmodTwoToIntUnitsHom_one⟩

/-- The explicit multiplicative equivalence between the units of `ℤ` and the
additive group `ZMod 2`, written as a multiplicative group. It sends `1` to
`0` and `-1` to `1`. -/
noncomputable def intUnitsMulEquivZModTwo :
    ℤˣ ≃* Multiplicative (ZMod 2) :=
  (MulEquiv.ofBijective zmodTwoToIntUnitsHom
    zmodTwoToIntUnitsHom_bijective).symm

@[simp]
theorem intUnitsMulEquivZModTwo_apply_one :
    intUnitsMulEquivZModTwo 1 = Multiplicative.ofAdd (0 : ZMod 2) := by
  apply intUnitsMulEquivZModTwo.symm.injective
  simp [intUnitsMulEquivZModTwo]

@[simp]
theorem intUnitsMulEquivZModTwo_apply_neg_one :
    intUnitsMulEquivZModTwo (-1) = Multiplicative.ofAdd (1 : ZMod 2) := by
  apply intUnitsMulEquivZModTwo.symm.injective
  simp [intUnitsMulEquivZModTwo]

end Hatcher.Sphere
