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
          change degree 1 (by decide) (circlePowerMap (0 : ℤ)) = (0 : ℤ)
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

namespace Hatcher.Sphere

/-- **Hatcher, the pole observation after Proposition 2.33.** Either existing
suspension pole is an isolated preimage of itself, and its local degree is the
global degree of the suspension for every isolation witness. This includes
`n = 0` and arbitrary continuous sphere maps. -/
theorem sphere_suspension_pole_local_degree
    (n : ℕ)
    (f : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n)
    (p : TopCat.sphere.{0} (n + 1))
    (hp : p = northPole.{0} n ∨ p = southPole.{0} n) :
    IsolatedPreimage (sphereSuspensionMap n f) p p ∧
      ∀ (h : IsolatedPreimage (sphereSuspensionMap n f) p p),
        localDegree (n + 1) (Nat.zero_lt_succ n)
            (sphereSuspensionMap n f) p p h =
          degree (n + 1) (Nat.zero_lt_succ n) (sphereSuspensionMap n f) := by
  have hfiber : fiber (sphereSuspensionMap n f) p = {p} := by
    change (sphereSuspensionMap n f) ⁻¹' {p} = {p}
    rcases hp with rfl | rfl
    · exact (sphere_suspension_pole_fibers n f).1
    · exact (sphere_suspension_pole_fibers n f).2
  refine ⟨singletonFiberIsolatedPreimage
    (sphereSuspensionMap n f) p p hfiber, ?_⟩
  intro h
  exact localDegree_eq_degree_of_fiber_eq_singleton
    (n + 1) (Nat.zero_lt_succ n) (sphereSuspensionMap n f) p p hfiber h

end Hatcher.Sphere

namespace Hatcher.Sphere

namespace SphereBallPinchData

/-- Every actual component collapse of certified sphere-ball pinch data has
signed degree `1` or `-1`, using its punctured-sphere chart. -/
theorem component_collapse_degree_eq_one_or_neg_one
    {n k : ℕ} {hn : 0 < n} (D : SphereBallPinchData n hn k) (i : Fin k) :
    degree n hn (TopCat.ofHom (D.componentCollapse i)) = 1 ∨
      degree n hn (TopCat.ofHom (D.componentCollapse i)) = -1 := by
  classical
  let : T2Space (TopCat.sphere.{0} n) :=
    (sphereULiftHomeomorph.{0} n).isEmbedding.t2Space
  let f : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n :=
    TopCat.ofHom (D.componentCollapse i)
  change degree n hn f = 1 ∨ degree n hn f = -1
  let y₀ : ({D.b}ᶜ : Set (TopCat.sphere.{0} n)) :=
    (puncturedSphereHomeomorphEuclidean n D.b).symm 0
  let y : TopCat.sphere.{0} n := y₀.1
  have hy : y ≠ D.b := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using y₀.property
  let u : sphereBallOpen hn D.b i := (D.ballChart i).symm y₀
  let x : TopCat.sphere.{0} n := u.1
  have hmap (z : sphereBallOpen hn D.b i) :
      f z.1 = (D.ballChart i z).1 := by
    change D.componentCollapse i z.1 = (D.ballChart i z).1
    exact D.component_collapse_apply_ball i z
  have hfx : f x = y := by
    calc
      f x = (D.ballChart i u).1 := hmap u
      _ = y := congrArg Subtype.val ((D.ballChart i).apply_symm_apply y₀)
  have hfiber : fiber f y = {x} := by
    ext z
    constructor
    · intro hz
      have hzmap : f z = y := mem_fiber.mp hz
      have hzB : z ∈ sphereBallOpen hn D.b i := by
        by_contra hzB
        have hconst : f z = D.b := by
          change D.componentCollapse i z = D.b
          exact D.component_collapse_apply_not_mem i z hzB
        exact hy (hzmap.symm.trans hconst)
      let z' : sphereBallOpen hn D.b i := ⟨z, hzB⟩
      have hzH : D.ballChart i z' = D.ballChart i u := by
        apply Subtype.ext
        calc
          (D.ballChart i z').1 = f z := (hmap z').symm
          _ = y := hzmap
          _ = f x := hfx.symm
          _ = (D.ballChart i u).1 := hmap u
      have hzu : z' = u := (D.ballChart i).injective hzH
      have hzx : z = x := congrArg Subtype.val hzu
      exact Set.mem_singleton_iff.mpr hzx
    · intro hz
      have hzx : z = x := Set.mem_singleton_iff.mp hz
      apply mem_fiber.mpr
      rw [hzx]
      exact hfx
  let h : IsolatedPreimage f x y :=
    singletonFiberIsolatedPreimage f x y hfiber
  let N : LocalDegreeNeighborhood f x y :=
    { U := sphereBallOpen hn D.b i
      isOpen_U := (D.closed_properties i).2.2.2.2.1
      x_mem := u.property
      map_eq := hfx
      eq_of_mem_of_map_eq := by
        intro z _ hzy
        have hzF : z ∈ fiber f y := mem_fiber.mpr hzy
        rw [hfiber] at hzF
        exact Set.mem_singleton_iff.mp hzF }
  let L : N.LocalHomeomorphData :=
    { V := ({D.b}ᶜ : Set (TopCat.sphere.{0} n))
      isOpen_V := isClosed_singleton.isOpen_compl
      y_mem := y₀.property
      e := D.ballChart i
      e_apply := by
        intro z
        change (D.ballChart i z).1 = f z.1
        exact (hmap z).symm }
  have hunit := localDegree_eq_one_or_neg_one_of_localHomeomorph n hn h N L
  have hglobal :=
    localDegree_eq_degree_of_fiber_eq_singleton n hn f x y hfiber h
  simpa only [hglobal] using hunit

end SphereBallPinchData

/-- Each component collapse of the canonical positive-dimensional sphere pinch
has signed degree `1` or `-1`. The index `Fin k` includes the empty family. -/
theorem sphere_ball_collapse_degree_unit
    (n : ℕ) (hn : 0 < n) (k : ℕ) (i : Fin k) :
    degree n hn
        (TopCat.ofHom ((sphereBallPinch n hn k).componentCollapse i)) = 1 ∨
      degree n hn
        (TopCat.ofHom ((sphereBallPinch n hn k).componentCollapse i)) = -1 :=
  (sphereBallPinch n hn k).component_collapse_degree_eq_one_or_neg_one i

end Hatcher.Sphere

open CategoryTheory
open scoped EuclideanSpace

namespace Hatcher.Sphere

namespace SphereBallPinchData

variable {n k : ℕ} {hn : 0 < n}

/-- The actual zeroth coordinate reflection fixes the pinch's omitted point. -/
theorem zeroth_reflection_apply_basepoint (D : SphereBallPinchData n hn k) :
    (coordinateReflectionIso n (0 : Fin (n + 1))).hom D.b = D.b := by
  rw [← reflectionIso_coordinateNormal n (0 : Fin (n + 1))]
  apply (sphereULiftHomeomorph.{0} n).injective
  apply Subtype.ext
  rw [sphereULiftHomeomorph_reflectionIso_apply]
  change
    ((ℝ ∙ EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ))ᗮ).reflection
        (sphereULiftHomeomorph.{0} n D.b).1 =
      (sphereULiftHomeomorph.{0} n D.b).1
  exact D.zeroth_reflection

/-- Choose identity or the actual zeroth reflection by comparing the component's
signed degree with the prescribed sign. -/
noncomputable def signedCorrectionIso (D : SphereBallPinchData n hn k)
    (σ : Fin k → ℤ) (i : Fin k) :
    TopCat.sphere.{0} n ≅ TopCat.sphere.{0} n := by
  classical
  exact if degree n hn (TopCat.ofHom (D.componentCollapse i)) = σ i
    then Iso.refl (TopCat.sphere.{0} n)
    else coordinateReflectionIso n (0 : Fin (n + 1))

/-- Every selected correction preserves the actual common basepoint. -/
theorem signed_correction_apply_basepoint (D : SphereBallPinchData n hn k)
    (σ : Fin k → ℤ) (i : Fin k) :
    (D.signedCorrectionIso σ i).hom D.b = D.b := by
  classical
  unfold signedCorrectionIso
  split_ifs with heq
  · rfl
  · exact D.zeroth_reflection_apply_basepoint

/-- The actual component followed by its correction has the prescribed signed
degree, using the computed unit and the reflection calculation. -/
theorem signed_corrected_component_degree (D : SphereBallPinchData n hn k)
    (σ : Fin k → ℤ) (hσ : ∀ i, σ i = 1 ∨ σ i = -1) (i : Fin k) :
    degree n hn
        (TopCat.ofHom (D.componentCollapse i) ≫ (D.signedCorrectionIso σ i).hom) =
      σ i := by
  classical
  let c : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n :=
    TopCat.ofHom (D.componentCollapse i)
  change degree n hn (c ≫ (D.signedCorrectionIso σ i).hom) = σ i
  by_cases heq : degree n hn c = σ i
  · have ha : D.signedCorrectionIso σ i = Iso.refl (TopCat.sphere.{0} n) := by
      change (if degree n hn c = σ i then Iso.refl (TopCat.sphere.{0} n)
        else coordinateReflectionIso n (0 : Fin (n + 1))) = _
      exact ite_eq_left heq
    have hmap : c ≫ (D.signedCorrectionIso σ i).hom = c := by
      rw [ha]
      exact Category.comp_id c
    exact (congrArg (degree n hn) hmap).trans heq
  · have ha : D.signedCorrectionIso σ i =
        coordinateReflectionIso n (0 : Fin (n + 1)) := by
      change (if degree n hn c = σ i then Iso.refl (TopCat.sphere.{0} n)
        else coordinateReflectionIso n (0 : Fin (n + 1))) = _
      exact ite_eq_right heq
    have hdegree : degree n hn (c ≫ (D.signedCorrectionIso σ i).hom) =
        degree n hn c * (-1) := by
      calc
        degree n hn (c ≫ (D.signedCorrectionIso σ i).hom) =
            degree n hn c * degree n hn (D.signedCorrectionIso σ i).hom :=
          degree_comp n hn c (D.signedCorrectionIso σ i).hom
        _ = degree n hn c * (-1) := by
          rw [ha, degree_coordinateReflection]
    rw [hdegree]
    have hunit : degree n hn c = 1 ∨ degree n hn c = -1 :=
      D.component_collapse_degree_eq_one_or_neg_one i
    rcases hunit with hc | hc
    · rcases hσ i with hs | hs
      · exact (heq (hc.trans hs.symm)).elim
      · rw [hc, hs]
        norm_num
    · rcases hσ i with hs | hs
      · rw [hc, hs]
        norm_num
      · exact (heq (hc.trans hs.symm)).elim

/-- The actual based continuous fold induced by the selected correction maps. -/
noncomputable def basedSignedFold (D : SphereBallPinchData n hn k)
    (σ : Fin k → ℤ) :
    C(Hatcher.PointedWedge (fun _ : Fin k ↦ TopCat.sphere.{0} n)
      (fun _ ↦ D.b), TopCat.sphere.{0} n) :=
  Hatcher.PointedWedge.desc (fun _ : Fin k ↦ D.b) D.b
    (fun i ↦ (D.signedCorrectionIso σ i).hom.hom)
    (by
      intro i
      change (D.signedCorrectionIso σ i).hom D.b = D.b
      exact D.signed_correction_apply_basepoint σ i)

/-- The fold sends the retained wedge point to the actual sphere basepoint. -/
theorem based_signed_fold_apply_basepoint (D : SphereBallPinchData n hn k)
    (σ : Fin k → ℤ) :
    D.basedSignedFold σ
        (Hatcher.PointedWedge.basepoint (fun _ : Fin k ↦ D.b)) = D.b :=
  rfl

/-- On each summand the fold is its selected correction. -/
theorem based_signed_fold_apply_inclusion (D : SphereBallPinchData n hn k)
    (σ : Fin k → ℤ) (i : Fin k) (x : TopCat.sphere.{0} n) :
    D.basedSignedFold σ
        (Hatcher.PointedWedge.inclusion (fun _ : Fin k ↦ D.b) i x) =
      (D.signedCorrectionIso σ i).hom x :=
  rfl

end SphereBallPinchData

/-- An output certificate for the actual fold with the fixed correction maps.
Its component-degree equations are derived by the constructor. -/
structure SignedSphereFoldData {n k : ℕ} {hn : 0 < n}
    (D : SphereBallPinchData n hn k) (σ : Fin k → ℤ) where
  fold :
    C(Hatcher.PointedWedge (fun _ : Fin k ↦ TopCat.sphere.{0} n)
      (fun _ ↦ D.b), TopCat.sphere.{0} n)
  fold_basepoint :
    fold (Hatcher.PointedWedge.basepoint (fun _ : Fin k ↦ D.b)) = D.b
  fold_inclusion :
    ∀ (i : Fin k) (x : TopCat.sphere.{0} n),
      fold (Hatcher.PointedWedge.inclusion (fun _ : Fin k ↦ D.b) i x) =
        (D.signedCorrectionIso σ i).hom x
  corrected_component_degree :
    ∀ i : Fin k,
      degree n hn
          (TopCat.ofHom (D.componentCollapse i) ≫ (D.signedCorrectionIso σ i).hom) =
        σ i

private theorem signed_sphere_fold_data_nonempty {n k : ℕ} {hn : 0 < n}
    (D : SphereBallPinchData n hn k) (σ : Fin k → ℤ)
    (hσ : ∀ i, σ i = 1 ∨ σ i = -1) :
    Nonempty (SignedSphereFoldData D σ) := by
  exact ⟨{
    fold := D.basedSignedFold σ
    fold_basepoint := D.based_signed_fold_apply_basepoint σ
    fold_inclusion := D.based_signed_fold_apply_inclusion σ
    corrected_component_degree := D.signed_corrected_component_degree σ hσ }⟩

/-- The canonical signed fold construction for prescribed unit signs, including
the empty family, using the actual sphere-ball pinch. -/
noncomputable def signedSphereFoldMap
    (n : ℕ) (hn : 0 < n) (k : ℕ) (σ : Fin k → ℤ)
    (hσ : ∀ i, σ i = 1 ∨ σ i = -1) :
    SignedSphereFoldData (sphereBallPinch n hn k) σ :=
  Classical.choice
    (signed_sphere_fold_data_nonempty (sphereBallPinch n hn k) σ hσ)

namespace SignedSphereFoldData

variable {n k : ℕ} {hn : 0 < n}
  {D : SphereBallPinchData n hn k} {σ : Fin k → ℤ}

/-- The actual signed sphere self-map is the fold composed with the pinch. -/
noncomputable def selfMap (F : SignedSphereFoldData D σ) :
    C(TopCat.sphere.{0} n, TopCat.sphere.{0} n) :=
  F.fold.comp D.pinchMap

/-- On a chosen ball the signed self-map is the corrected actual component. -/
theorem self_map_apply_ball (F : SignedSphereFoldData D σ)
    (i : Fin k) (x : sphereBallOpen hn D.b i) :
    F.selfMap x.1 =
      (D.signedCorrectionIso σ i).hom (D.componentCollapse i x.1) := by
  change F.fold (D.pinchMap x.1) = _
  rw [D.pinch_map_apply_ball, F.fold_inclusion, D.component_collapse_apply_ball]

/-- The signed self-map sends the complement of the ball union to the basepoint. -/
theorem self_map_apply_compl (F : SignedSphereFoldData D σ)
    (x : TopCat.sphere.{0} n) (hx : x ∉ sphereBallUnion n hn k D.b) :
    F.selfMap x = D.b := by
  change F.fold (D.pinchMap x) = D.b
  rw [D.pinch_map_apply_compl x hx]
  exact F.fold_basepoint

/-- The signed sphere self-map preserves the actual basepoint. -/
theorem self_map_apply_basepoint (F : SignedSphereFoldData D σ) :
    F.selfMap D.b = D.b := by
  apply self_map_apply_compl F D.b
  intro hb
  rcases Set.mem_iUnion.mp hb with ⟨i, hi⟩
  exact (D.closed_properties i).2.2.1
    (Set.image_mono Metric.ball_subset_closedBall hi)

/-- For zero balls the actual signed self-map is constant at the basepoint. -/
theorem self_map_zero {n : ℕ} {hn : 0 < n}
    {D : SphereBallPinchData n hn 0} {σ : Fin 0 → ℤ}
    (F : SignedSphereFoldData D σ) :
    F.selfMap = ContinuousMap.const (TopCat.sphere.{0} n) D.b := by
  apply ContinuousMap.ext
  intro x
  change F.fold (D.pinchMap x) = D.b
  have hq :
      D.pinchMap x =
        Hatcher.PointedWedge.basepoint (fun _ : Fin 0 ↦ D.b) :=
    DFunLike.congr_fun D.pinch_map_zero x
  rw [hq]
  exact F.fold_basepoint

end SignedSphereFoldData

end Hatcher.Sphere

namespace Hatcher.Sphere

namespace SphereBallPinchData

variable {n k : ℕ} {hn : 0 < n}

private theorem signed_correction_inverse_ne_basepoint (D : SphereBallPinchData n hn k)
    (σ : Fin k → ℤ) (i : Fin k) (y : TopCat.sphere.{0} n) (hy : y ≠ D.b) :
    (D.signedCorrectionIso σ i).inv y ≠ D.b := by
  intro h
  have heq := congrArg (fun x => (D.signedCorrectionIso σ i).hom x) h
  have hleft : (D.signedCorrectionIso σ i).hom ((D.signedCorrectionIso σ i).inv y) = y :=
    TopCat.inv_hom_id_apply (D.signedCorrectionIso σ i) y
  have hright : (D.signedCorrectionIso σ i).hom D.b = D.b :=
    D.signed_correction_apply_basepoint σ i
  exact hy (hleft.symm.trans (heq.trans hright))

/-- The actual point of the ith ball over a regular target, obtained by applying
its chart inverse to the inverse correction of that target. -/
noncomputable def signedRegularBallPoint (D : SphereBallPinchData n hn k)
    (σ : Fin k → ℤ) (y : TopCat.sphere.{0} n) (hy : y ≠ D.b) (i : Fin k) :
    sphereBallOpen hn D.b i :=
  (D.ballChart i).symm
    ⟨(D.signedCorrectionIso σ i).inv y, by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using
        signed_correction_inverse_ne_basepoint D σ i y hy⟩

private theorem signed_regular_ball_point_chart (D : SphereBallPinchData n hn k)
    (σ : Fin k → ℤ) (y : TopCat.sphere.{0} n) (hy : y ≠ D.b) (i : Fin k) :
    (D.ballChart i (D.signedRegularBallPoint σ y hy i)).1 =
      (D.signedCorrectionIso σ i).inv y := by
  exact congrArg Subtype.val ((D.ballChart i).apply_symm_apply _)

end SphereBallPinchData

namespace SignedSphereFoldData

variable {n k : ℕ} {hn : 0 < n}
  {D : SphereBallPinchData n hn k} {σ : Fin k → ℤ}

private theorem regular_ball_point_image (F : SignedSphereFoldData D σ)
    (y : TopCat.sphere.{0} n) (hy : y ≠ D.b) (i : Fin k) :
    F.selfMap (D.signedRegularBallPoint σ y hy i).1 = y := by
  have hmap := F.self_map_apply_ball i (D.signedRegularBallPoint σ y hy i)
  have hc := D.component_collapse_apply_ball i (D.signedRegularBallPoint σ y hy i)
  calc
    F.selfMap (D.signedRegularBallPoint σ y hy i).1 =
        (D.signedCorrectionIso σ i).hom
          (D.componentCollapse i (D.signedRegularBallPoint σ y hy i).1) := hmap
    _ = (D.signedCorrectionIso σ i).hom
          (D.ballChart i (D.signedRegularBallPoint σ y hy i)).1 :=
      congrArg (fun x => (D.signedCorrectionIso σ i).hom x) hc
    _ = (D.signedCorrectionIso σ i).hom ((D.signedCorrectionIso σ i).inv y) :=
      congrArg (fun x => (D.signedCorrectionIso σ i).hom x)
        (SphereBallPinchData.signed_regular_ball_point_chart D σ y hy i)
    _ = y := TopCat.inv_hom_id_apply (D.signedCorrectionIso σ i) y

/-- The explicitly constructed point of the actual signed-map fiber indexed by
an actual ball. -/
noncomputable def regularFiberPoint (F : SignedSphereFoldData D σ)
    (y : TopCat.sphere.{0} n) (hy : y ≠ D.b) (i : Fin k) :
    fiber (TopCat.ofHom F.selfMap) y :=
  ⟨(D.signedRegularBallPoint σ y hy i).1, by
    apply mem_fiber.mpr
    exact regular_ball_point_image F y hy i⟩

private theorem regular_fiber_point_bijective (F : SignedSphereFoldData D σ)
    (y : TopCat.sphere.{0} n) (hy : y ≠ D.b) :
    Function.Bijective (F.regularFiberPoint y hy) := by
  constructor
  · intro i j hij
    by_contra hne
    have hsource : (D.signedRegularBallPoint σ y hy i).1 =
        (D.signedRegularBallPoint σ y hy j).1 := congrArg Subtype.val hij
    have hclosed_i : (D.signedRegularBallPoint σ y hy i).1 ∈ sphereBallClosed hn D.b i :=
      Set.image_mono Metric.ball_subset_closedBall
        (D.signedRegularBallPoint σ y hy i).property
    have hclosed_j : (D.signedRegularBallPoint σ y hy i).1 ∈ sphereBallClosed hn D.b j := by
      rw [hsource]
      exact Set.image_mono Metric.ball_subset_closedBall
        (D.signedRegularBallPoint σ y hy j).property
    exact Set.disjoint_left.mp (D.closed_disjoint hne) hclosed_i hclosed_j
  · intro z
    have hz : F.selfMap z.1 = y := mem_fiber.mp z.property
    have hzV : z.1 ∈ sphereBallUnion n hn k D.b := by
      by_contra hzV
      have hconst := F.self_map_apply_compl z.1 hzV
      exact hy (hz.symm.trans hconst)
    rcases Set.mem_iUnion.mp hzV with ⟨i, hzi⟩
    let u : sphereBallOpen hn D.b i := ⟨z.1, hzi⟩
    have hcorr : (D.signedCorrectionIso σ i).hom (D.ballChart i u).1 = y := by
      calc
        (D.signedCorrectionIso σ i).hom (D.ballChart i u).1 =
            (D.signedCorrectionIso σ i).hom (D.componentCollapse i u.1) :=
          congrArg (fun x => (D.signedCorrectionIso σ i).hom x)
            (D.component_collapse_apply_ball i u).symm
        _ = F.selfMap u.1 := (F.self_map_apply_ball i u).symm
        _ = y := hz
    have hchart_val : (D.ballChart i u).1 =
        (D.signedCorrectionIso σ i).inv y := by
      have hi := congrArg (fun x => (D.signedCorrectionIso σ i).inv x) hcorr
      exact (TopCat.hom_inv_id_apply (D.signedCorrectionIso σ i)
        (D.ballChart i u).1).symm.trans hi
    have hchart : D.ballChart i u =
        D.ballChart i (D.signedRegularBallPoint σ y hy i) := by
      apply Subtype.ext
      exact hchart_val.trans
        (SphereBallPinchData.signed_regular_ball_point_chart D σ y hy i).symm
    have hu : u = D.signedRegularBallPoint σ y hy i := (D.ballChart i).injective hchart
    refine ⟨i, ?_⟩
    apply Subtype.ext
    exact (congrArg Subtype.val hu).symm

/-- The actual regular signed-map fiber is equivalent to the prescribed ball
index set; the inverse is the explicit point construction. -/
noncomputable def regularFiberEquiv (F : SignedSphereFoldData D σ)
    (y : TopCat.sphere.{0} n) (hy : y ≠ D.b) :
    fiber (TopCat.ofHom F.selfMap) y ≃ Fin k :=
  (Equiv.ofBijective (F.regularFiberPoint y hy)
    (regular_fiber_point_bijective F y hy)).symm

@[simp]
theorem regular_fiber_equiv_apply_point (F : SignedSphereFoldData D σ)
    (y : TopCat.sphere.{0} n) (hy : y ≠ D.b) (i : Fin k) :
    F.regularFiberEquiv y hy (F.regularFiberPoint y hy i) = i :=
  (Equiv.ofBijective (F.regularFiberPoint y hy)
    (regular_fiber_point_bijective F y hy)).symm_apply_apply i

@[simp]
theorem regular_fiber_point_apply_index (F : SignedSphereFoldData D σ)
    (y : TopCat.sphere.{0} n) (hy : y ≠ D.b)
    (z : fiber (TopCat.ofHom F.selfMap) y) :
    F.regularFiberPoint y hy (F.regularFiberEquiv y hy z) = z :=
  (Equiv.ofBijective (F.regularFiberPoint y hy)
    (regular_fiber_point_bijective F y hy)).apply_symm_apply z

/-- The inverse equivalence has the required chart/correction inverse formula
and lies in its actual indexed open ball. -/
theorem regular_fiber_equiv_symm_point (F : SignedSphereFoldData D σ)
    (y : TopCat.sphere.{0} n) (hy : y ≠ D.b) (i : Fin k) :
    ((F.regularFiberEquiv y hy).symm i).1 =
        (D.signedRegularBallPoint σ y hy i).1 ∧
      ((F.regularFiberEquiv y hy).symm i).1 ∈ sphereBallOpen hn D.b i := by
  constructor
  · rfl
  · exact (D.signedRegularBallPoint σ y hy i).property

/-- Finiteness is derived from the actual regular fiber equivalence. -/
theorem regular_fiber_finite (F : SignedSphereFoldData D σ)
    (y : TopCat.sphere.{0} n) (hy : y ≠ D.b) :
    (fiber (TopCat.ofHom F.selfMap) y).Finite := by
  classical
  let : Fintype (fiber (TopCat.ofHom F.selfMap) y) :=
    Fintype.ofEquiv (Fin k) (F.regularFiberEquiv y hy).symm
  exact Set.toFinite _

/-- For no balls the literal regular fiber is empty. -/
theorem regular_fiber_zero {n : ℕ} {hn : 0 < n}
    {D : SphereBallPinchData n hn 0} {σ : Fin 0 → ℤ}
    (F : SignedSphereFoldData D σ) (y : TopCat.sphere.{0} n) (hy : y ≠ D.b) :
    fiber (TopCat.ofHom F.selfMap) y = ∅ := by
  ext x
  constructor
  · intro hx
    exact Fin.elim0 (F.regularFiberEquiv y hy ⟨x, hx⟩)
  · intro hx
    simpa only [Set.mem_empty_iff_false] using hx

end SignedSphereFoldData

/-- The actual regular fiber of the canonical signed sphere pinch has exactly
one point in each prescribed ball, with its explicit correction/chart inverse. -/
theorem sphere_signed_pinch_fiber (n : ℕ) (hn : 0 < n) (k : ℕ)
    (σ : Fin k → ℤ) (hσ : ∀ i, σ i = 1 ∨ σ i = -1)
    (y : TopCat.sphere.{0} n) (hy : y ≠ (sphereBallPinch n hn k).b) :
    ∃ E : fiber (TopCat.ofHom (signedSphereFoldMap n hn k σ hσ).selfMap) y ≃ Fin k,
      (∀ i : Fin k,
        (E.symm i).1 =
            ((sphereBallPinch n hn k).signedRegularBallPoint σ y hy i).1 ∧
          (E.symm i).1 ∈ sphereBallOpen hn (sphereBallPinch n hn k).b i) ∧
      (fiber (TopCat.ofHom (signedSphereFoldMap n hn k σ hσ).selfMap) y).Finite := by
  let F := signedSphereFoldMap n hn k σ hσ
  exact ⟨F.regularFiberEquiv y hy,
    (fun i => F.regular_fiber_equiv_symm_point y hy i),
    F.regular_fiber_finite y hy⟩

end Hatcher.Sphere

namespace Hatcher.Sphere

namespace SignedSphereFoldData

variable {n k : ℕ} {hn : 0 < n}
  {D : SphereBallPinchData n hn k} {σ : Fin k → ℤ}

private theorem corrected_component_fiber_singleton (F : SignedSphereFoldData D σ)
    (y : TopCat.sphere.{0} n) (hy : y ≠ D.b) (i : Fin k) :
    fiber (TopCat.ofHom (D.componentCollapse i) ≫ (D.signedCorrectionIso σ i).hom) y =
      {(F.regularFiberPoint y hy i).1} := by
  let g : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n :=
    TopCat.ofHom (D.componentCollapse i) ≫ (D.signedCorrectionIso σ i).hom
  let u : sphereBallOpen hn D.b i := D.signedRegularBallPoint σ y hy i
  let x : TopCat.sphere.{0} n := (F.regularFiberPoint y hy i).1
  have hx : x = u.1 := by
    rfl
  have hmap (z : sphereBallOpen hn D.b i) :
      g z.1 = (D.signedCorrectionIso σ i).hom (D.ballChart i z).1 := by
    change (D.signedCorrectionIso σ i).hom (D.componentCollapse i z.1) = _
    exact congrArg (fun q => (D.signedCorrectionIso σ i).hom q)
      (D.component_collapse_apply_ball i z)
  have hxu : F.selfMap u.1 = y := regular_ball_point_image F y hy i
  have hgu : g u.1 = y := by
    have hEq : F.selfMap u.1 = g u.1 := F.self_map_apply_ball i u
    exact hEq.symm.trans hxu
  have hgx : g x = y := by
    rw [hx]
    exact hgu
  change fiber g y = {x}
  ext z
  constructor
  · intro hz
    have hzg : g z = y := mem_fiber.mp hz
    have hzB : z ∈ sphereBallOpen hn D.b i := by
      by_contra hzB
      have hconstant : g z = D.b := by
        change (D.signedCorrectionIso σ i).hom (D.componentCollapse i z) = D.b
        rw [D.component_collapse_apply_not_mem i z hzB]
        exact D.signed_correction_apply_basepoint σ i
      exact hy (hzg.symm.trans hconstant)
    let z' : sphereBallOpen hn D.b i := ⟨z, hzB⟩
    have hsame : (D.signedCorrectionIso σ i).hom (D.ballChart i z').1 =
        (D.signedCorrectionIso σ i).hom (D.ballChart i u).1 :=
      (hmap z').symm.trans (hzg.trans (hgu.symm.trans (hmap u)))
    have hchart_val : (D.ballChart i z').1 = (D.ballChart i u).1 := by
      have hinv := congrArg (fun q => (D.signedCorrectionIso σ i).inv q) hsame
      exact (TopCat.hom_inv_id_apply (D.signedCorrectionIso σ i)
        (D.ballChart i z').1).symm.trans
        (hinv.trans (TopCat.hom_inv_id_apply (D.signedCorrectionIso σ i)
          (D.ballChart i u).1))
    have hchart : D.ballChart i z' = D.ballChart i u := Subtype.ext hchart_val
    have hz' : z' = u := (D.ballChart i).injective hchart
    have hzx : z = x := (congrArg Subtype.val hz').trans hx.symm
    exact Set.mem_singleton_iff.mpr hzx
  · intro hz
    have hzx : z = x := Set.mem_singleton_iff.mp hz
    apply mem_fiber.mpr
    rw [hzx]
    exact hgx

/-- Each explicit point of a regular signed-pinch fiber is isolated and has
its prescribed signed local degree, for every isolation witness. -/
theorem regular_point_local_degree (F : SignedSphereFoldData D σ)
    (y : TopCat.sphere.{0} n) (hy : y ≠ D.b) (i : Fin k) :
    IsolatedPreimage (TopCat.ofHom F.selfMap) (F.regularFiberPoint y hy i).1 y ∧
      ∀ h : IsolatedPreimage (TopCat.ofHom F.selfMap) (F.regularFiberPoint y hy i).1 y,
        localDegree n hn (TopCat.ofHom F.selfMap)
          (F.regularFiberPoint y hy i).1 y h = σ i := by
  let f : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n := TopCat.ofHom F.selfMap
  let g : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n :=
    TopCat.ofHom (D.componentCollapse i) ≫ (D.signedCorrectionIso σ i).hom
  let x : TopCat.sphere.{0} n := (F.regularFiberPoint y hy i).1
  have hfiber : fiber g y = {x} := corrected_component_fiber_singleton F y hy i
  have hg : IsolatedPreimage g x y := singletonFiberIsolatedPreimage g x y hfiber
  have hU : IsOpen (sphereBallOpen hn D.b i) := (D.closed_properties i).2.2.2.2.1
  have hxU : x ∈ sphereBallOpen hn D.b i :=
    (D.signedRegularBallPoint σ y hy i).property
  have hEq : Set.EqOn g f (sphereBallOpen hn D.b i) := by
    intro z hz
    exact (F.self_map_apply_ball i ⟨z, hz⟩).symm
  have hGerm := localDegree_germ_invariance n hn
    (f := g) (g := f) (x := x) (y := y)
    (sphereBallOpen hn D.b i) hU hxU hEq hg
  refine ⟨hGerm.1, ?_⟩
  intro h
  exact (hGerm.2 hg h).symm.trans
    ((localDegree_eq_degree_of_fiber_eq_singleton n hn g x y hfiber hg).trans
      (F.corrected_component_degree i))

end SignedSphereFoldData

/-- The canonical signed sphere pinch has its prescribed local sign at the
point indexed by each actual regular ball, with isolation derived and every
isolation witness allowed. -/
theorem sphere_signed_pinch_local_degree (n : ℕ) (hn : 0 < n) (k : ℕ)
    (σ : Fin k → ℤ) (hσ : ∀ i, σ i = 1 ∨ σ i = -1)
    (y : TopCat.sphere.{0} n) (hy : y ≠ (sphereBallPinch n hn k).b) (i : Fin k) :
    IsolatedPreimage (TopCat.ofHom (signedSphereFoldMap n hn k σ hσ).selfMap)
        ((signedSphereFoldMap n hn k σ hσ).regularFiberPoint y hy i).1 y ∧
      ∀ h : IsolatedPreimage (TopCat.ofHom (signedSphereFoldMap n hn k σ hσ).selfMap)
          ((signedSphereFoldMap n hn k σ hσ).regularFiberPoint y hy i).1 y,
        localDegree n hn (TopCat.ofHom (signedSphereFoldMap n hn k σ hσ).selfMap)
          ((signedSphereFoldMap n hn k σ hσ).regularFiberPoint y hy i).1 y h = σ i :=
  (signedSphereFoldMap n hn k σ hσ).regular_point_local_degree y hy i

end Hatcher.Sphere

namespace Hatcher.Sphere

namespace SignedSphereFoldData

variable {n k : ℕ} {hn : 0 < n}
  {D : SphereBallPinchData n hn k} {σ : Fin k → ℤ}

/-- The actual signed pinch-and-fold map has degree equal to the sum of its
prescribed local signs, with the empty family included. -/
theorem degree_eq_sum_signs (F : SignedSphereFoldData D σ) :
    degree n hn (TopCat.ofHom F.selfMap) = ∑ i : Fin k, σ i := by
  classical
  let f : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n := TopCat.ofHom F.selfMap
  let y₀ : ({D.b}ᶜ : Set (TopCat.sphere.{0} n)) :=
    (puncturedSphereHomeomorphEuclidean n D.b).symm 0
  let y : TopCat.sphere.{0} n := y₀.1
  have hy : y ≠ D.b := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using y₀.property
  let E : fiber f y ≃ Fin k := F.regularFiberEquiv y hy
  have hfinite : (fiber f y).Finite := F.regular_fiber_finite y hy
  let : Fintype (fiber f y) := finiteFiberFintype hfinite
  let a (z : fiber f y) : ℤ :=
    localDegree n hn f z.1 y (finiteFiberIsolatedPreimage f y hfinite z)
  have hpoint (z : fiber f y) : F.regularFiberPoint y hy (E z) = z :=
    F.regular_fiber_point_apply_index y hy z
  have hlocal (z : fiber f y) : a z = σ (E z) := by
    have hl := F.regular_point_local_degree y hy (E z)
    rw [hpoint z] at hl
    exact hl.2 (finiteFiberIsolatedPreimage f y hfinite z)
  have hsum := degree_eq_sum_localDegree n hn f y hfinite
  change degree n hn f = ∑ z : fiber f y, a z at hsum
  change degree n hn f = ∑ i : Fin k, σ i
  exact hsum.trans (Fintype.sum_equiv E a σ hlocal)

end SignedSphereFoldData

/-- **Hatcher, Example 2.31 (printed page 136).** The canonical geometric signed
pinch has degree equal to the sum of its unit signs. -/
theorem sphere_signed_pinch_degree_sum
    (n : ℕ) (hn : 0 < n) (k : ℕ) (σ : Fin k → ℤ)
    (hσ : ∀ i, σ i = 1 ∨ σ i = -1) :
    degree n hn (TopCat.ofHom (signedSphereFoldMap n hn k σ hσ).selfMap) =
      ∑ i : Fin k, σ i :=
  (signedSphereFoldMap n hn k σ hσ).degree_eq_sum_signs

end Hatcher.Sphere

namespace Hatcher.Sphere

/-- **Hatcher, Example 2.31.** Every integer is the existing signed degree of
an actual geometric pinch-and-fold map of each positive-dimensional sphere. -/
theorem sphere_degree_realization (n : ℕ) (hn : 0 < n) (d : ℤ) :
    ∃ f : TopCat.sphere.{0} n ⟶ TopCat.sphere.{0} n,
      degree n hn f = d := by
  classical
  cases d with
  | ofNat k =>
      let σ : Fin (Int.ofNat k).natAbs → ℤ := fun _ => 1
      have hσ : ∀ i, σ i = 1 ∨ σ i = -1 := fun _ => Or.inl rfl
      let F := signedSphereFoldMap n hn (Int.ofNat k).natAbs σ hσ
      refine ⟨TopCat.ofHom F.selfMap, ?_⟩
      have hdegree := sphere_signed_pinch_degree_sum
        n hn (Int.ofNat k).natAbs σ hσ
      change degree n hn (TopCat.ofHom F.selfMap) = ∑ i : Fin k, σ i at hdegree
      change degree n hn (TopCat.ofHom F.selfMap) = (k : ℤ)
      calc
        degree n hn (TopCat.ofHom F.selfMap) = ∑ i : Fin k, σ i := hdegree
        _ = (k : ℤ) := by
          simp only [σ, Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, Int.nsmul_eq_mul, mul_one]
  | negSucc k =>
      let σ : Fin (Int.negSucc k).natAbs → ℤ := fun _ => -1
      have hσ : ∀ i, σ i = 1 ∨ σ i = -1 := fun _ => Or.inr rfl
      let F := signedSphereFoldMap n hn (Int.negSucc k).natAbs σ hσ
      refine ⟨TopCat.ofHom F.selfMap, ?_⟩
      have hdegree := sphere_signed_pinch_degree_sum
        n hn (Int.negSucc k).natAbs σ hσ
      change degree n hn (TopCat.ofHom F.selfMap) =
        ∑ i : Fin (k + 1), σ i at hdegree
      change degree n hn (TopCat.ofHom F.selfMap) = -((k + 1 : ℕ) : ℤ)
      calc
        degree n hn (TopCat.ofHom F.selfMap) =
            ∑ i : Fin (k + 1), σ i := hdegree
        _ = -((k + 1 : ℕ) : ℤ) := by
          simp only [σ, Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, Int.nsmul_eq_mul, mul_neg, mul_one]

end Hatcher.Sphere
