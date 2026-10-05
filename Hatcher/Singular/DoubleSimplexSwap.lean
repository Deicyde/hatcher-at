/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Hatcher.Singular.DoubleSimplexFundamentalClass

/-!
# The symmetry of the ordered double simplex

Exchanging the two copies of the standard simplex defines an involution of
their ordered double.  It exchanges the two canonical singular simplices, so
it negates their difference cycle and the resulting reduced-homology class.
-/

noncomputable section

open AlgebraicTopology CategoryTheory Limits Opposite Simplicial

namespace Hatcher.Simplex

/-- The involution of the ordered double simplex that exchanges its two
standard-simplex summands. -/
noncomputable def doubleSimplexSwapMap (n : ℕ) :
    doubleSimplex n ⟶ doubleSimplex n :=
  pushout.desc (doubleSimplexSecondInclusion n)
    (doubleSimplexFirstInclusion n) (pushout.condition.symm)

@[reassoc (attr := simp)]
theorem doubleSimplexFirstInclusion_swapMap (n : ℕ) :
    doubleSimplexFirstInclusion n ≫ doubleSimplexSwapMap n =
      doubleSimplexSecondInclusion n := by
  apply pushout.inl_desc

@[reassoc (attr := simp)]
theorem doubleSimplexSecondInclusion_swapMap (n : ℕ) :
    doubleSimplexSecondInclusion n ≫ doubleSimplexSwapMap n =
      doubleSimplexFirstInclusion n := by
  apply pushout.inr_desc

/-- Swapping the two summands twice is the identity. -/
@[simp]
theorem doubleSimplexSwapMap_sq (n : ℕ) :
    doubleSimplexSwapMap n ≫ doubleSimplexSwapMap n = 𝟙 _ := by
  apply pushout.hom_ext
  · simp
  · simp

/-- The summand-exchanging automorphism of the ordered double simplex. -/
noncomputable def doubleSimplexSwapIso (n : ℕ) :
    doubleSimplex n ≅ doubleSimplex n where
  hom := doubleSimplexSwapMap n
  inv := doubleSimplexSwapMap n
  hom_inv_id := doubleSimplexSwapMap_sq n
  inv_hom_id := doubleSimplexSwapMap_sq n

@[simp]
theorem doubleSimplexSwapIso_hom (n : ℕ) :
    (doubleSimplexSwapIso n).hom = doubleSimplexSwapMap n :=
  rfl

@[simp]
theorem doubleSimplexSwapIso_inv (n : ℕ) :
    (doubleSimplexSwapIso n).inv = doubleSimplexSwapMap n :=
  rfl

private theorem doubleSimplexFirstSingularSimplex_map_swap (n : ℕ) :
    (TopCat.toSSet.map (doubleSimplexSwapIso n).hom).app _
        (doubleSimplexFirstSingularSimplex n) =
      doubleSimplexSecondSingularSimplex n := by
  apply (TopCat.toSSetObjEquiv _ _).injective
  ext x
  change
    (doubleSimplexSwapIso n).hom
        (doubleSimplexFirstInclusion n x) =
      doubleSimplexSecondInclusion n x
  exact ConcreteCategory.congr_hom
    (doubleSimplexFirstInclusion_swapMap n) x

private theorem doubleSimplexSecondSingularSimplex_map_swap (n : ℕ) :
    (TopCat.toSSet.map (doubleSimplexSwapIso n).hom).app _
        (doubleSimplexSecondSingularSimplex n) =
      doubleSimplexFirstSingularSimplex n := by
  apply (TopCat.toSSetObjEquiv _ _).injective
  ext x
  change
    (doubleSimplexSwapIso n).hom
        (doubleSimplexSecondInclusion n x) =
      doubleSimplexFirstInclusion n x
  exact ConcreteCategory.congr_hom
    (doubleSimplexSecondInclusion_swapMap n) x

universe v u

section Chain

variable {C : Type u} [Category.{v} C] [HasCoproducts.{0} C]
  [Preadditive C]

/-- At chain level, exchanging the two simplices negates their ordered
difference. -/
theorem doubleSimplexFundamentalCycle_map_swap (R : C) (n : ℕ) :
    doubleSimplexFundamentalCycle R n ≫
        ((Hatcher.Reduced.augmentedSingularChainComplexFunctor R).map
          (doubleSimplexSwapIso n).hom).f (n + 1) =
      -doubleSimplexFundamentalCycle R n := by
  change
    ((TopCat.toSSet.obj (doubleSimplex n)).ιChainComplex
          (doubleSimplexFirstSingularSimplex n) -
        (TopCat.toSSet.obj (doubleSimplex n)).ιChainComplex
          (doubleSimplexSecondSingularSimplex n)) ≫
        (SSet.chainComplexMap
          (TopCat.toSSet.map (doubleSimplexSwapIso n).hom) R).f n =
      -((TopCat.toSSet.obj (doubleSimplex n)).ιChainComplex
          (doubleSimplexFirstSingularSimplex n) -
        (TopCat.toSSet.obj (doubleSimplex n)).ιChainComplex
          (doubleSimplexSecondSingularSimplex n))
  rw [Preadditive.sub_comp, SSet.ι_chainComplexMap_f,
    SSet.ι_chainComplexMap_f,
    doubleSimplexFirstSingularSimplex_map_swap,
    doubleSimplexSecondSingularSimplex_map_swap]
  exact (neg_sub _ _).symm

end Chain

variable {C : Type u} [Category.{v} C] [HasCoproducts.{0} C]
  [Abelian C]

omit [HasCoproducts.{0} C] in
private theorem homologyClass_map
    {K L : ChainComplex C ℕ} (f : K ⟶ L) (T : C)
    (i j : ℕ) (hij : (ComplexShape.down ℕ).next i = j)
    (x : T ⟶ K.X i) (hx : x ≫ K.d i j = 0) :
    (K.liftCycles x j hij hx ≫ K.homologyπ i) ≫
        HomologicalComplex.homologyMap f i =
      L.liftCycles (x ≫ f.f i) j hij
          (by rw [Category.assoc, f.comm, reassoc_of% hx, zero_comp]) ≫
        L.homologyπ i := by
  rw [Category.assoc, HomologicalComplex.homologyπ_naturality]
  rw [← Category.assoc, HomologicalComplex.liftCycles_comp_cyclesMap]

omit [HasCoproducts.{0} C] in
private theorem homologyClass_neg
    (K : ChainComplex C ℕ) (T : C)
    (i j : ℕ) (hij : (ComplexShape.down ℕ).next i = j)
    (x : T ⟶ K.X i) (hx : x ≫ K.d i j = 0) :
    K.liftCycles (-x) j hij (by rw [Preadditive.neg_comp, hx, neg_zero]) ≫
        K.homologyπ i =
      -(K.liftCycles x j hij hx ≫ K.homologyπ i) := by
  rw [← cancel_mono (K.homologyι i)]
  simp

/-- **Hatcher, §2.2, degree property (e), page 134.** Exchanging the two
ordered top-dimensional simplices sends their explicit reduced fundamental
class to its negative. -/
theorem doubleSimplexFundamentalClass_map_swap (R : C) (n : ℕ) :
    doubleSimplexFundamentalClass R n ≫
        (Hatcher.Reduced.homologyFunctor R n).map
          (doubleSimplexSwapIso n).hom =
      -doubleSimplexFundamentalClass R n := by
  let K :=
    (Hatcher.Reduced.augmentedSingularChainComplexFunctor R).obj
      (doubleSimplex n)
  let f :=
    (Hatcher.Reduced.augmentedSingularChainComplexFunctor R).map
      (doubleSimplexSwapIso n).hom
  change
    (K.liftCycles (doubleSimplexFundamentalCycle R n) n (by simp)
          (doubleSimplexFundamentalCycle_d R n) ≫
        K.homologyπ (n + 1)) ≫
        HomologicalComplex.homologyMap f (n + 1) =
      -(K.liftCycles (doubleSimplexFundamentalCycle R n) n (by simp)
          (doubleSimplexFundamentalCycle_d R n) ≫
        K.homologyπ (n + 1))
  rw [homologyClass_map]
  have hcycle :
      doubleSimplexFundamentalCycle R n ≫ f.f (n + 1) =
        -doubleSimplexFundamentalCycle R n := by
    simpa only [f] using doubleSimplexFundamentalCycle_map_swap R n
  simp only [hcycle]
  apply homologyClass_neg

end Hatcher.Simplex
