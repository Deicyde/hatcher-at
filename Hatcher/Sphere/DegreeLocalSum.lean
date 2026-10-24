/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Hatcher.Sphere.FinitePunctureOrientation
import Hatcher.Sphere.FiniteFiberLocalMap
import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas

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

end Hatcher.Sphere
