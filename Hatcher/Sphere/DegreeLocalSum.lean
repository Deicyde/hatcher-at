/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Hatcher.Sphere.FinitePunctureOrientation
import Hatcher.Sphere.FiniteFiberLocalMap
import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
import Hatcher.Sphere.HomeomorphismLocalDegree
import Hatcher.Sphere.CirclePowerFiber
import Hatcher.Sphere.CircleInversion
import Hatcher.Sphere.NonsurjectiveDegree

/-!
# Degree is the sum of local degrees

The finite-puncture orientation sum and the local and global class equations
identify the two multipliers of the ordered target local class. Cancelling
that actual orientation isomorphism gives an equality of integer
endomorphisms, whose values at `1` are the global degree and the sum of the
local degrees. The same argument applies to an empty finite fiber.
-/

noncomputable section

open AlgebraicTopology CategoryTheory CategoryTheory.Limits
open scoped BigOperators

namespace Hatcher.Sphere

/-- Every point of a finite sphere-map fiber is an isolated preimage, witnessed
by the canonical separated neighborhood construction. No positivity or
nonempty-fiber assumption is required. -/
theorem finiteFiberIsolatedPreimage {n : ℕ}
    (f : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n)
    (y : TopCat.sphere.{0} n) (hfinite : (fiber f y).Finite)
    (i : fiber f y) : IsolatedPreimage f i.1 y :=
  ((finiteFiberNeighborhoods f y hfinite).neighborhood i).isolatedPreimage

/-- The degree-sum formula holds for every family of disjoint isolating fiber
neighborhoods. The sum's finite indexing instance is installed only inside
the proposition and proof. -/
theorem degree_eq_sum_localDegree_of_neighborhoods
    (n : ℕ) (hn : 0 < n)
    (f : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n)
    (y : TopCat.sphere.{0} n) (hfinite : (fiber f y).Finite)
    (D : FiniteFiberNeighborhoods f y) :
    letI : Fintype (fiber f y) := finiteFiberFintype hfinite
    degree n hn f = ∑ i : fiber f y,
      localDegree n hn f i.1 y (D.neighborhood i).isolatedPreimage := by
  classical
  let : Fintype (fiber f y) := finiteFiberFintype hfinite
  let H := Hatcher.Relative.homologyFunctor (AddCommGrpCat.of ℤ) n
  let L (i : fiber f y) :=
    H.obj (Hatcher.Relative.puncturedPair (TopCat.of (D.U i))
      ⟨i.1, D.center_mem i⟩)
  let c (i : fiber f y) : AddCommGrpCat.of ℤ ⟶ L i :=
    integralSphereNeighborhoodFundamentalClass
      n hn i.1 (D.U i) (D.center_mem i) (D.isOpen_U i)
  let d (i : fiber f y) : ℤ :=
    localDegree n hn f i.1 y (D.neighborhood i).isolatedPreimage
  let j : AddCommGrpCat.of ℤ ⟶
      H.obj (Hatcher.Relative.deletedPair (TopCat.sphere.{0} n) (fiber f y)) := by
    change AddCommGrpCat.of ℤ ⟶ H.obj (TopPair.ofSubset (fiber f y)ᶜ)
    exact finitePunctureFundamentalClass n f y
  let p : H.obj (Hatcher.Relative.deletedPair (TopCat.sphere.{0} n) (fiber f y)) ⟶
      H.obj (Hatcher.Relative.puncturedPair (TopCat.sphere.{0} n) y) := by
    change H.obj (TopPair.ofSubset (fiber f y)ᶜ) ⟶
      H.obj (Hatcher.Relative.puncturedPair (TopCat.sphere.{0} n) y)
    exact H.map (finiteFiberPairMap f y)
  let e := finitePunctureHomologyIso D hfinite n
  let t : AddCommGrpCat.of ℤ ⟶
      H.obj (Hatcher.Relative.puncturedPair (TopCat.sphere.{0} n) y) :=
    integralSphereLocalFundamentalClass n hn y
  change degree n hn f = ∑ i : fiber f y, d i
  have hclasses :
      AddCommGrpCat.asHom (degree n hn f) ≫ t =
        (∑ i : fiber f y,
          (AddCommGrpCat.asHom (d i) :
            AddCommGrpCat.of ℤ ⟶ AddCommGrpCat.of ℤ)) ≫ t := by
    calc
      AddCommGrpCat.asHom (degree n hn f) ≫ t =
          j ≫ p :=
        (finiteFiberFundamentalClass_map n hn f y).symm
      _ = (finitePunctureLocalFundamentalClassSum D hfinite hn ≫ e.hom) ≫ p :=
        congrArg (fun m ↦ m ≫ p)
          (finitePunctureFundamentalClass_eq_sum D hfinite hn)
      _ = ∑ i : fiber f y, c i ≫ Sigma.ι L i ≫ e.hom ≫ p := by
        change ((∑ i : fiber f y, c i ≫ Sigma.ι L i) ≫ e.hom) ≫ p = _
        rw [Preadditive.sum_comp, Preadditive.sum_comp]
        simp only [Category.assoc]
      _ = ∑ i : fiber f y, AddCommGrpCat.asHom (d i) ≫ t := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [ι_finitePunctureHomologyIso_hom_assoc]
        exact finiteFiberPairMap_localClass n hn f y D i
      _ = (∑ i : fiber f y,
          (AddCommGrpCat.asHom (d i) :
            AddCommGrpCat.of ℤ ⟶ AddCommGrpCat.of ℤ)) ≫ t :=
        (Preadditive.sum_comp _ _ t).symm
  let : IsIso t := integralSphereLocalFundamentalClass_isIso n hn y
  have hendo :
      (AddCommGrpCat.asHom (degree n hn f) :
        AddCommGrpCat.of ℤ ⟶ AddCommGrpCat.of ℤ) =
        ∑ i : fiber f y,
          (AddCommGrpCat.asHom (d i) :
            AddCommGrpCat.of ℤ ⟶ AddCommGrpCat.of ℤ) :=
    (cancel_mono t).1 hclasses
  have hhom := congrArg
    (fun m : AddCommGrpCat.of ℤ ⟶ AddCommGrpCat.of ℤ ↦
      AddCommGrpCat.homAddEquiv m) hendo
  rw [map_sum] at hhom
  change (AddCommGrpCat.asHom (degree n hn f) :
      AddCommGrpCat.of ℤ ⟶ AddCommGrpCat.of ℤ).hom =
    ∑ i : fiber f y,
      (AddCommGrpCat.asHom (d i) :
        AddCommGrpCat.of ℤ ⟶ AddCommGrpCat.of ℤ).hom at hhom
  have happly := congrArg (fun m : ℤ →+ ℤ ↦ m (1 : ℤ)) hhom
  rw [AddMonoidHom.finsetSum_apply] at happly
  change (1 : ℤ) • degree n hn f =
    ∑ i : fiber f y, (1 : ℤ) • d i at happly
  simpa only [one_zsmul] using happly

/-- **Hatcher, Proposition 2.30 (printed page 136).** The ordered global
integral degree is the finite sum of the neighborhood-independent local
degrees over the actual fiber. Canonical isolation witnesses are derived from
finiteness, and an empty fiber gives the empty sum without a separate case. -/
theorem degree_eq_sum_localDegree
    (n : ℕ) (hn : 0 < n)
    (f : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n)
    (y : TopCat.sphere.{0} n) (hfinite : (fiber f y).Finite) :
    letI : Fintype (fiber f y) := finiteFiberFintype hfinite
    degree n hn f = ∑ i : fiber f y,
      localDegree n hn f i.1 y (finiteFiberIsolatedPreimage f y hfinite i) := by
  classical
  let : Fintype (fiber f y) := finiteFiberFintype hfinite
  let D := finiteFiberNeighborhoods f y hfinite
  calc
    degree n hn f = ∑ i : fiber f y,
        localDegree n hn f i.1 y (D.neighborhood i).isolatedPreimage :=
      degree_eq_sum_localDegree_of_neighborhoods n hn f y hfinite D
    _ = ∑ i : fiber f y,
        localDegree n hn f i.1 y (finiteFiberIsolatedPreimage f y hfinite i) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact localDegree_proof_irrel n hn f i.1 y
        (D.neighborhood i).isolatedPreimage
        (finiteFiberIsolatedPreimage f y hfinite i)

/-- A singleton sphere-map fiber gives an isolated preimage in every
dimension. The required finiteness and fiber membership are consequences of
the singleton equation. -/
theorem singletonFiberIsolatedPreimage {n : ℕ}
    (f : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n)
    (x y : TopCat.sphere.{0} n) (hfiber : fiber f y = {x}) :
    IsolatedPreimage f x y := by
  have hfinite : (fiber f y).Finite := by
    rw [hfiber]
    exact Set.finite_singleton x
  have hx : x ∈ fiber f y := by
    rw [hfiber]
    exact Set.mem_singleton x
  exact finiteFiberIsolatedPreimage f y hfinite ⟨x, hx⟩

/-- A singleton fiber's neighborhood-independent local degree is the global
degree for every isolation witness. This specializes Proposition 2.30 and
does not require a local-homeomorphism hypothesis. -/
theorem localDegree_eq_degree_of_fiber_eq_singleton
    (n : ℕ) (hn : 0 < n)
    (f : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n)
    (x y : TopCat.sphere.{0} n) (hfiber : fiber f y = {x})
    (h : IsolatedPreimage f x y) :
    localDegree n hn f x y h = degree n hn f := by
  classical
  have hfinite : (fiber f y).Finite := by
    rw [hfiber]
    exact Set.finite_singleton x
  have hx : x ∈ fiber f y := by
    rw [hfiber]
    exact Set.mem_singleton x
  let i : fiber f y := ⟨x, hx⟩
  let : Fintype (fiber f y) := finiteFiberFintype hfinite
  let : Subsingleton (fiber f y) := ⟨fun a b ↦ Subtype.ext (by
    have ha : a.1 = x :=
      Set.mem_singleton_iff.mp ((Set.ext_iff.mp hfiber a.1).mp a.2)
    have hb : b.1 = x :=
      Set.mem_singleton_iff.mp ((Set.ext_iff.mp hfiber b.1).mp b.2)
    exact ha.trans hb.symm)⟩
  have hsum : degree n hn f =
      localDegree n hn f x y (finiteFiberIsolatedPreimage f y hfinite i) := by
    calc
      degree n hn f = ∑ j : fiber f y,
          localDegree n hn f j.1 y (finiteFiberIsolatedPreimage f y hfinite j) :=
        degree_eq_sum_localDegree n hn f y hfinite
      _ = localDegree n hn f x y (finiteFiberIsolatedPreimage f y hfinite i) :=
        Fintype.sum_subsingleton
          (fun j : fiber f y ↦
            localDegree n hn f j.1 y (finiteFiberIsolatedPreimage f y hfinite j)) i
  exact (localDegree_proof_irrel n hn f x y h
    (finiteFiberIsolatedPreimage f y hfinite i)).trans hsum.symm

/-- The actual positive integer-power map of the standard circle has its
exponent as signed degree, by summing its local degrees over its actual fiber. -/
theorem circlePowerMap_positive_degree (k : ℕ) (hk : 0 < k) :
    degree 1 (by decide) (circlePowerMap (k : ℤ)) = (k : ℤ) := by
  classical
  let f : TopCat.sphere.{0} 1 ⟶ TopCat.sphere.{0} 1 := circlePowerMap (k : ℤ)
  let y : TopCat.sphere.{0} 1 := diskBoundaryTwoBasepoint.{0}
  change degree 1 (by decide) f = (k : ℤ)
  obtain ⟨_, _, E₀, _⟩ := circlePowerMap_positive_fiber k hk y
  change ({z : TopCat.sphere.{0} 1 // f z = y} ≃ Fin k) at E₀
  let E : fiber f y ≃ Fin k :=
    (Equiv.subtypeEquivRight
      (p := fun z : TopCat.sphere.{0} 1 => z ∈ fiber f y)
      (q := fun z => f z = y)
      (fun z => mem_fiber (f := f) (y := y) (z := z))).trans E₀
  have hfinite : (fiber f y).Finite := by
    letI : Fintype (fiber f y) := Fintype.ofEquiv (Fin k) E.symm
    exact Set.toFinite (fiber f y)
  letI : Fintype (fiber f y) := finiteFiberFintype hfinite
  have hcard : Fintype.card (fiber f y) = k := by
    simpa only [Fintype.card_fin] using Fintype.card_congr E
  have hone (i : fiber f y) :
      localDegree 1 (by decide) f i.1 y
        (finiteFiberIsolatedPreimage f y hfinite i) = 1 := by
    have hi : f i.1 = y := mem_fiber.mp i.property
    have himage : IsolatedPreimage f i.1 (f i.1) := by
      simpa only [hi] using finiteFiberIsolatedPreimage f y hfinite i
    have hlocal := (circlePowerMap_positive_localDegree k hk i.1).2 himage
    change localDegree 1 (by decide) f i.1 (f i.1) himage = 1 at hlocal
    simpa only [hi] using hlocal
  have hsum := degree_eq_sum_localDegree 1 (by decide) f y hfinite
  change degree 1 (by decide) f = ∑ i : fiber f y,
    localDegree 1 (by decide) f i.1 y
      (finiteFiberIsolatedPreimage f y hfinite i) at hsum
  calc
    degree 1 (by decide) f = ∑ i : fiber f y,
        localDegree 1 (by decide) f i.1 y
          (finiteFiberIsolatedPreimage f y hfinite i) := hsum
    _ = ∑ i : fiber f y, (1 : ℤ) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hone i
    _ = (k : ℤ) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, hcard]

/-- **Hatcher, Example 2.32 (printed page 137).** The actual integer-power map
of the standard circle has its signed integer exponent as degree. -/
theorem circlePowerMap_degree (d : ℤ) :
    degree 1 (by decide) (circlePowerMap d) = d := by
  cases d with
  | ofNat k =>
      cases k with
      | zero =>
          rw [circlePowerMap_zero]
          apply degree_eq_zero_of_not_surjective 1 (by decide)
            (TopCat.const diskBoundaryTwoBasepoint.{0})
          intro hsurj
          obtain ⟨x, hx⟩ := hsurj
            (diskBoundaryTwoHomeomorphCircle.{0}.symm
              (_root_.Circle.exp Real.pi))
          change diskBoundaryTwoBasepoint.{0} =
            diskBoundaryTwoHomeomorphCircle.{0}.symm
              (_root_.Circle.exp Real.pi) at hx
          have heq := congrArg diskBoundaryTwoHomeomorphCircle.{0} hx
          exact _root_.Circle.exp_pi_ne_one (by
            simpa only [diskBoundaryTwoHomeomorphCircle_basepoint,
              Homeomorph.apply_symm_apply] using heq.symm)
      | succ k =>
          exact circlePowerMap_positive_degree (k + 1) (Nat.succ_pos k)
  | negSucc k =>
      change degree 1 (by decide)
        (circlePowerMap (-((k + 1 : ℕ) : ℤ))) = -((k + 1 : ℕ) : ℤ)
      calc
        degree 1 (by decide) (circlePowerMap (-((k + 1 : ℕ) : ℤ))) =
            degree 1 (by decide) (circlePowerMap ((k + 1 : ℕ) : ℤ)) *
              degree 1 (by decide) (circlePowerMap (-1)) := by
          rw [circlePowerMap_neg_natCast, degree_comp]
        _ = ((k + 1 : ℕ) : ℤ) * (-1) := by
          rw [circlePowerMap_positive_degree (k + 1) (Nat.succ_pos k),
            circlePowerMap_inversion_reflection_and_degree.2]
        _ = -((k + 1 : ℕ) : ℤ) := by
          simp only [mul_neg, mul_one]

end Hatcher.Sphere
