/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Hatcher.Singular.ContractibleSubspaceRelative
import Hatcher.Singular.DoubleSimplexRelative
import Hatcher.Singular.RelativeSimplexFundamentalClass
import Mathlib.Analysis.Convex.Contractible

/-!
# The fundamental class of the ordered double simplex

The difference of the two canonical top-dimensional simplices defines a
class in reduced homology.  Projection relative to the second simplex sends
this literal difference cycle to the identity simplex in the first summand,
so the class is a generator in every dimension, including dimension zero.
-/

noncomputable section

open AlgebraicTopology CategoryTheory Limits Opposite Simplicial ZeroObject

namespace Hatcher.Simplex

universe v u

variable {C : Type u} [Category.{v} C] [HasCoproducts.{0} C] [Abelian C]

/-- **Hatcher, Example 2.23 (page 125).** The reduced-homology class
represented by the first canonical simplex minus the second canonical
simplex in the ordered double-simplex model. -/
noncomputable def doubleSimplexFundamentalClass (R : C) (n : ℕ) :
    R ⟶
      (Hatcher.Reduced.homologyFunctor R n).obj (doubleSimplex n) :=
  let K :=
    (Hatcher.Reduced.augmentedSingularChainComplexFunctor R).obj
      (doubleSimplex n)
  K.liftCycles (doubleSimplexFundamentalCycle R n) n (by simp)
      (doubleSimplexFundamentalCycle_d R n) ≫
    K.homologyπ (n + 1)

private noncomputable abbrev doubleSimplexAugmentedProjection
    (R : C) (n : ℕ) :
    (Hatcher.Reduced.augmentedSingularChainComplexFunctor R).obj
        (doubleSimplex n) ⟶
      Hatcher.Relative.augmentedRelativeChainComplex
        (doubleSimplexSecondPair n) R :=
  Hatcher.Relative.augmentedPairProjection
    (doubleSimplexSecondPair n) R

private theorem standardSimplexIdentityChain_map_doubleSimplexFirst
    (R : C) (n : ℕ) :
    standardSimplexIdentityChain R n ≫
        (((singularChainComplexFunctor C).obj R).map
          (doubleSimplexFirstInclusion n)).f n =
      (TopCat.toSSet.obj (doubleSimplex n)).ιChainComplex
        (doubleSimplexFirstSingularSimplex n) := by
  unfold standardSimplexIdentityChain
  unfold standardSimplexPairIdentitySingularSimplex
  change
    (TopCat.toSSet.obj (TopCat.of (StandardSimplex n))).ιChainComplex
          ((TopCat.toSSetObjEquiv _ _).symm (ContinuousMap.id _)) ≫
        (SSet.chainComplexMap
          (TopCat.toSSet.map (doubleSimplexFirstInclusion n)) R).f n = _
  rw [SSet.ι_chainComplexMap_f]
  congr 1

private theorem standardSimplexIdentityChain_map_doubleSimplexSecond
    (R : C) (n : ℕ) :
    standardSimplexIdentityChain R n ≫
        (((singularChainComplexFunctor C).obj R).map
          (doubleSimplexSecondInclusion n)).f n =
      (TopCat.toSSet.obj (doubleSimplex n)).ιChainComplex
        (doubleSimplexSecondSingularSimplex n) := by
  unfold standardSimplexIdentityChain
  unfold standardSimplexPairIdentitySingularSimplex
  change
    (TopCat.toSSet.obj (TopCat.of (StandardSimplex n))).ιChainComplex
          ((TopCat.toSSetObjEquiv _ _).symm (ContinuousMap.id _)) ≫
        (SSet.chainComplexMap
          (TopCat.toSSet.map (doubleSimplexSecondInclusion n)) R).f n = _
  rw [SSet.ι_chainComplexMap_f]
  congr 1

set_option backward.isDefEq.respectTransparency false in
/-- At chain level, quotienting by the second simplex sends the ordered
difference cycle to the image of the identity simplex from the first
summand.  The second term vanishes in the relative quotient. -/
theorem doubleSimplexFundamentalCycle_relativeProjection
    (R : C) (n : ℕ) :
    doubleSimplexFundamentalCycle R n ≫
        ((Hatcher.Relative.chainComplexFunctorπ R).app
          (doubleSimplexSecondPair n)).f n =
      relativeSimplexIdentityChain R n ≫
        ((Hatcher.Relative.chainComplexFunctor R).map
          (doubleSimplexFirstPairHom n)).f n := by
  let P := standardSimplexPair n
  let Q := doubleSimplexSecondPair n
  let f := doubleSimplexFirstPairHom n
  have hπ :
      ((Hatcher.Relative.chainComplexFunctorπ R).app P).f n ≫
          ((Hatcher.Relative.chainComplexFunctor R).map f).f n =
        (((singularChainComplexFunctor C).obj R).map
            (TopPair.Hom.fst f)).f n ≫
          ((Hatcher.Relative.chainComplexFunctorπ R).app Q).f n := by
    exact congrArg (fun φ ↦ φ.f n)
      (((Hatcher.Relative.chainComplexFunctorπ R).naturality f).symm)
  change
    ((TopCat.toSSet.obj (doubleSimplex n)).ιChainComplex
          (doubleSimplexFirstSingularSimplex n) -
        (TopCat.toSSet.obj (doubleSimplex n)).ιChainComplex
          (doubleSimplexSecondSingularSimplex n)) ≫
        ((Hatcher.Relative.chainComplexFunctorπ R).app Q).f n =
      (standardSimplexIdentityChain R n ≫
          ((Hatcher.Relative.chainComplexFunctorπ R).app P).f n) ≫
        ((Hatcher.Relative.chainComplexFunctor R).map f).f n
  rw [Preadditive.sub_comp,
    ← standardSimplexIdentityChain_map_doubleSimplexFirst R n,
    ← standardSimplexIdentityChain_map_doubleSimplexSecond R n]
  rw [Category.assoc, Category.assoc]
  change
    standardSimplexIdentityChain R n ≫
          (((singularChainComplexFunctor C).obj R).map
            (TopPair.Hom.fst f)).f n ≫
          ((Hatcher.Relative.chainComplexFunctorπ R).app Q).f n -
        standardSimplexIdentityChain R n ≫
          (((singularChainComplexFunctor C).obj R).map Q.map).f n ≫
          ((Hatcher.Relative.chainComplexFunctorπ R).app Q).f n = _
  rw [← hπ, Hatcher.Relative.chainComplexFunctor_condition_f]
  simp

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
private lemma augmentZeroHomologyIso_zero (K : ChainComplex C ℕ) :
    Hatcher.Relative.augmentZeroHomologyIso K 0 =
      Hatcher.Relative.augmentZeroHomologyIsoZero K := by
  rfl

omit [HasCoproducts.{0} C] in
private lemma augmentZeroHomologyIso_succ (K : ChainComplex C ℕ) (n : ℕ) :
    Hatcher.Relative.augmentZeroHomologyIso K (n + 1) =
      Hatcher.Relative.augmentZeroPositiveHomologyIso K n := by
  rfl

omit [HasCoproducts.{0} C] in
set_option backward.isDefEq.respectTransparency false in
private theorem augmentZeroClass_hom
    (K : ChainComplex C ℕ) (T : C) (n : ℕ)
    (x : T ⟶ K.X n)
    (hx : x ≫ K.d n ((ComplexShape.down ℕ).next n) = 0) :
    (ChainComplex.augment K (0 : K.X 0 ⟶ (0 : C)) (by simp)).liftCycles
          x n (by simp)
          (by
            cases n with
            | zero =>
                change x ≫ (0 : K.X 0 ⟶ (0 : C)) = 0
                simp
            | succ n =>
                change x ≫ K.d (n + 1) n = 0
                rw [show (ComplexShape.down ℕ).next (n + 1) = n by simp] at hx
                exact hx) ≫
        (ChainComplex.augment K (0 : K.X 0 ⟶ (0 : C)) (by simp)).homologyπ
          (n + 1) ≫
        (Hatcher.Relative.augmentZeroHomologyIso K n).hom =
      K.liftCycles x ((ComplexShape.down ℕ).next n) rfl hx ≫
        K.homologyπ n := by
  cases n with
  | zero =>
      rw [augmentZeroHomologyIso_zero]
      rw [← cancel_mono (K.homologyι 0)]
      dsimp only [Hatcher.Relative.augmentZeroHomologyIsoZero, Iso.trans_hom]
      rw [HomologicalComplex.isoHomologyι_hom]
      simp only [Category.assoc,
        HomologicalComplex.homology_π_ι_assoc,
        HomologicalComplex.liftCycles_i_assoc,
        HomologicalComplex.homology_π_ι,
        Iso.symm_hom]
      rw [HomologicalComplex.isoHomologyι_inv_hom_id,
        Category.comp_id,
        Hatcher.Relative.pOpcycles_augmentZeroOpcyclesIso_hom]
  | succ n =>
      rw [augmentZeroHomologyIso_succ]
      rw [← cancel_mono (K.homologyι (n + 1))]
      let A := ChainComplex.augment K (0 : K.X 0 ⟶ (0 : C)) (by simp)
      let e := Hatcher.Relative.augmentZeroPositiveShortComplexIso K n
      let xA : T ⟶ (A.sc (n + 2)).X₂ := x
      let xK : T ⟶ (K.sc (n + 1)).X₂ := x
      let l : T ⟶ A.cycles (n + 2) :=
        A.liftCycles xA (n + 1) (by simp) (by
          dsimp only [xA, A]
          change x ≫ K.d (n + 1) n = 0
          rw [show (ComplexShape.down ℕ).next (n + 1) = n by simp] at hx
          exact hx)
      have h :
          A.homologyπ (n + 2) ≫ ShortComplex.homologyMap e.hom ≫
              K.homologyι (n + 1) =
            A.iCycles (n + 2) ≫ e.hom.τ₂ ≫ K.pOpcycles (n + 1) :=
        ShortComplex.π_homologyMap_ι e.hom
      have hl := congrArg
        (fun q : A.cycles (n + 2) ⟶ K.opcycles (n + 1) ↦ l ≫ q) h
      have he' : xA ≫ e.hom.τ₂ = xK := by
        dsimp [e, Hatcher.Relative.augmentZeroPositiveShortComplexIso]
        rw [HomologicalComplex.natIsoSc'_hom_app_τ₂,
          HomologicalComplex.natIsoSc'_inv_app_τ₂]
        erw [Category.comp_id]
        erw [Category.comp_id]
        erw [Category.comp_id]
      dsimp only [Hatcher.Relative.augmentZeroPositiveHomologyIso,
        ShortComplex.homologyMapIso_hom]
      dsimp only [l] at hl
      rw [HomologicalComplex.liftCycles_i_assoc] at hl
      rw [reassoc_of% he'] at hl
      simpa [A, xA, xK, Category.assoc] using hl

private theorem standardSimplex_contractibleSpace (n : ℕ) :
    ContractibleSpace (StandardSimplex n) := by
  let weights : StandardSimplex n → Fin (n + 1) → ℝ :=
    fun x ↦ x.weights
  have hconv : Convex ℝ (Set.range weights) := by
    rw [Convexity.StdSimplex.range_toFun_comp_weights]
    intro f hf g hg a b ha hb hab
    simp only [Set.mem_inter_iff, Set.mem_iInter,
      Set.mem_ofPred_eq] at hf hg ⊢
    constructor
    · intro i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact add_nonneg (mul_nonneg ha (hf.1 i))
        (mul_nonneg hb (hg.1 i))
    · simp_rw [Pi.add_apply, Pi.smul_apply]
      rwa [Finset.sum_add_distrib, ← Finset.smul_sum,
        ← Finset.smul_sum, hf.2, hg.2, smul_eq_mul,
        smul_eq_mul, mul_one, mul_one]
  let _ : ContractibleSpace (Set.range weights) := by
    exact hconv.contractibleSpace
      ⟨weights (Convexity.StdSimplex.single 0),
        ⟨Convexity.StdSimplex.single 0, rfl⟩⟩
  exact (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ
    (Fin (n + 1))).toHomeomorph.contractibleSpace

set_option backward.isDefEq.respectTransparency false in
/-- The explicit difference class projects to the image of the explicit
relative identity-simplex class under the canonical first-summand map. -/
theorem doubleSimplexFundamentalClass_relativeProjection
    (R : C) (n : ℕ) :
    doubleSimplexFundamentalClass R n ≫
        Hatcher.Relative.reducedPairProjection
          (doubleSimplexSecondPair n) R n =
      relativeSimplexFundamentalClass R n ≫
        (Hatcher.Relative.homologyFunctor R n).map
          (doubleSimplexFirstPairHom n) := by
  let A :=
    (Hatcher.Reduced.augmentedSingularChainComplexFunctor R).obj
      (doubleSimplex n)
  let B := Hatcher.Relative.augmentedRelativeChainComplex
    (doubleSimplexSecondPair n) R
  let p : A ⟶ B := doubleSimplexAugmentedProjection R n
  change
    (A.liftCycles (doubleSimplexFundamentalCycle R n) n (by simp)
          (doubleSimplexFundamentalCycle_d R n) ≫
        A.homologyπ (n + 1)) ≫
        (HomologicalComplex.homologyMap
          p (n + 1) ≫
        (Hatcher.Relative.augmentedRelativeHomologyIso
          (doubleSimplexSecondPair n) R n).hom) = _
  rw [← Category.assoc]
  rw [homologyClass_map]
  have hcycle :
      doubleSimplexFundamentalCycle R n ≫ p.f (n + 1) =
        relativeSimplexIdentityChain R n ≫
          ((Hatcher.Relative.chainComplexFunctor R).map
            (doubleSimplexFirstPairHom n)).f n := by
    simpa [p, doubleSimplexAugmentedProjection,
      Hatcher.Relative.augmentedPairProjection] using
        doubleSimplexFundamentalCycle_relativeProjection R n
  simp only [hcycle]
  let K := (Hatcher.Relative.chainComplexFunctor R).obj
    (doubleSimplexSecondPair n)
  let f := (Hatcher.Relative.chainComplexFunctor R).map
    (doubleSimplexFirstPairHom n)
  let x := relativeSimplexIdentityChain R n ≫ f.f n
  have hxB : x ≫ B.d (n + 1) n = 0 := by
    dsimp only [x, f]
    rw [← hcycle]
    rw [Category.assoc, p.comm]
    rw [← Category.assoc, doubleSimplexFundamentalCycle_d, zero_comp]
  have hx : x ≫ K.d n ((ComplexShape.down ℕ).next n) = 0 := by
    cases n with
    | zero => simp
    | succ n =>
        rw [show (ComplexShape.down ℕ).next (n + 1) = n by simp]
        change x ≫ K.d (n + 1) n = 0 at hxB
        exact hxB
  have haug := augmentZeroClass_hom K R n x hx
  calc
    _ = K.liftCycles x ((ComplexShape.down ℕ).next n) rfl hx ≫
          K.homologyπ n := by
      simpa only [B, K, x, f, Category.assoc,
        Hatcher.Relative.chainComplexFunctor, Functor.comp_obj,
        Hatcher.Relative.augmentedRelativeHomologyIso,
        Hatcher.Relative.augmentedRelativeChainComplex] using haug
    _ = _ := by
      dsimp only [x, f, relativeSimplexFundamentalClass]
      dsimp only [Hatcher.Relative.homologyFunctor, Functor.comp_map,
        SSetPair.homologyFunctor_map]
      (rw [homologyClass_map]; rfl)

/-- **Hatcher, Example 2.23 (page 125).** The ordered difference of the two
top-dimensional simplices is a generator of reduced homology of the ordered
double simplex. -/
theorem doubleSimplexFundamentalClass_isIso (R : C) (n : ℕ) :
    IsIso (doubleSimplexFundamentalClass R n) := by
  let P := doubleSimplexSecondPair n
  let _ : ContractibleSpace P.snd := by
    change ContractibleSpace (StandardSimplex n)
    exact standardSimplex_contractibleSpace n
  have hprojection :
      IsIso (Hatcher.Relative.reducedPairProjection P R n) :=
    Hatcher.Relative.reducedPairProjection_isIso_of_contractibleSubspace
      P R n
  have hrelative :
      IsIso (relativeSimplexFundamentalClass R n ≫
        (Hatcher.Relative.homologyFunctor R n).map
          (doubleSimplexFirstPairHom n)) :=
    IsIso.comp_isIso'
      (relativeSimplexFundamentalClass_isIso R n)
      (doubleSimplexFirstPair_homologyMap_isIso R n n)
  exact @IsIso.of_isIso_fac_right C _ _ _ _ _ _ _
    hprojection hrelative
      (doubleSimplexFundamentalClass_relativeProjection R n)

end Hatcher.Simplex
