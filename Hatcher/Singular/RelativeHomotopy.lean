/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Jack McCarthy
-/
import Hatcher.Singular.Relative
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance

/-!
# Homotopy invariance of relative singular chains

This file descends the compatible singular-chain homotopies associated to a
homotopy of topological pairs through the relative-chain cokernel.
-/

noncomputable section

open AlgebraicTopology CategoryTheory Limits MonoidalCategory
open scoped Simplicial

namespace Hatcher.Relative

universe w v u

private lemma toSSet_map_compat
    {X Y : TopPair.{w}} {f g : X ⟶ Y} (H : TopPair.Homotopy f g) :
    MonoidalCategoryStruct.whiskerRight (TopCat.toSSet.map X.map) Δ[1] ≫
        H.fst.toSSet.h =
      H.snd.toSSet.h ≫ TopCat.toSSet.map Y.map := by
  dsimp [TopCat.Homotopy.toSSet]
  simp only [Category.assoc]
  rw [← whisker_exchange_assoc]
  rw [Functor.LaxMonoidal.μ_natural_left_assoc]
  rw [← Functor.map_comp]
  rw [H.w]
  rw [Functor.map_comp]

private lemma toSSet_h_compat
    {X Y : TopPair.{w}} {f g : X ⟶ Y} (H : TopPair.Homotopy f g)
    {n : ℕ} (i : Fin (n + 1)) :
    (TopCat.toSSet.map X.map).app _ ≫
        H.fst.toSSet.toSimplicialObjectHomotopy.h i =
      H.snd.toSSet.toSimplicialObjectHomotopy.h i ≫
        (TopCat.toSSet.map Y.map).app _ := by
  ext x
  have hm :
      MonoidalCategoryStruct.whiskerRight
          (SSet.yonedaEquiv.symm
            ((TopCat.toSSet.map X.map).app _ x)) Δ[1] ≫
          H.fst.toSSet.h =
        MonoidalCategoryStruct.whiskerRight (SSet.yonedaEquiv.symm x) Δ[1] ≫
          H.snd.toSSet.h ≫ TopCat.toSSet.map Y.map := by
    rw [← SSet.yonedaEquiv_symm_comp]
    rw [comp_whiskerRight_assoc]
    rw [toSSet_map_compat H]
  exact congr($(hm).app _ (SSet.prodStdSimplex₁.nonDegenerateEquiv i).1)

private lemma singularChainHomotopy_compat
    {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]
    {X Y : TopPair.{w}} {f g : X ⟶ Y}
    (H : TopPair.Homotopy f g) (R : C) (p q : ℕ) :
    (((singularChainComplexFunctor C).obj R).map X.map).f p ≫
        (H.fst.singularChainComplexFunctorObjMap R).hom p q =
      (H.snd.singularChainComplexFunctorObjMap R).hom p q ≫
        (((singularChainComplexFunctor C).obj R).map Y.map).f q := by
  change (SSet.chainComplexMap (TopCat.toSSet.map X.map) R).f p ≫
      (H.fst.toSSet.chainComplexMap R).hom p q =
    (H.snd.toSSet.chainComplexMap R).hom p q ≫
      (SSet.chainComplexMap (TopCat.toSSet.map Y.map) R).f q
  by_cases hpq : p + 1 = q
  · subst q
    simp only [SSet.Homotopy.chainComplexMap,
      CategoryTheory.SimplicialObject.Homotopy.sSetChainComplexMap,
      CategoryTheory.SimplicialObject.Homotopy.toChainHomotopy,
      CategoryTheory.SimplicialObject.Homotopy.ToChainHomotopy.hom_eq,
      Preadditive.comp_neg, Preadditive.neg_comp, Preadditive.comp_sum,
      Preadditive.sum_comp, Preadditive.comp_zsmul, Preadditive.zsmul_comp]
    rw [Finset.sum_congr rfl (fun i _ ↦ ?_)]
    congr 1
    change (sigmaConst.obj R).map ((TopCat.toSSet.map X.map).app _) ≫
        (sigmaConst.obj R).map
          (H.fst.toSSet.toSimplicialObjectHomotopy.h i) =
      (sigmaConst.obj R).map
          (H.snd.toSSet.toSimplicialObjectHomotopy.h i) ≫
        (sigmaConst.obj R).map ((TopCat.toSSet.map Y.map).app _)
    rw [← Functor.map_comp, ← Functor.map_comp, toSSet_h_compat H i]
  · rw [(H.fst.toSSet.chainComplexMap R).zero p q (by simpa),
      (H.snd.toSSet.chainComplexMap R).zero p q (by simpa),
      comp_zero, zero_comp]

private noncomputable def subspaceChainHomotopy
    {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]
    {X Y : TopPair.{w}} {f g : X ⟶ Y}
    (H : TopPair.Homotopy f g) (R : C) :
    _root_.Homotopy
      (SSet.chainComplexMap (singularPairFunctor.map f).left R)
      (SSet.chainComplexMap (singularPairFunctor.map g).left R) := by
  change _root_.Homotopy
    (((singularChainComplexFunctor C).obj R).map (TopPair.Hom.snd f))
    (((singularChainComplexFunctor C).obj R).map (TopPair.Hom.snd g))
  exact H.snd.singularChainComplexFunctorObjMap R

private noncomputable def ambientChainHomotopy
    {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]
    {X Y : TopPair.{w}} {f g : X ⟶ Y}
    (H : TopPair.Homotopy f g) (R : C) :
    _root_.Homotopy
      (SSet.chainComplexMap (singularPairFunctor.map f).right R)
      (SSet.chainComplexMap (singularPairFunctor.map g).right R) := by
  change _root_.Homotopy
    (((singularChainComplexFunctor C).obj R).map (TopPair.Hom.fst f))
    (((singularChainComplexFunctor C).obj R).map (TopPair.Hom.fst g))
  exact H.fst.singularChainComplexFunctorObjMap R

private lemma pairChainHomotopy_compat
    {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]
    {X Y : TopPair.{w}} {f g : X ⟶ Y}
    (H : TopPair.Homotopy f g) (R : C) (i j : ℕ) :
    (SSet.chainComplexMap (singularPairFunctor.obj X).hom R).f i ≫
        (ambientChainHomotopy H R).hom i j =
      (subspaceChainHomotopy H R).hom i j ≫
        (SSet.chainComplexMap (singularPairFunctor.obj Y).hom R).f j := by
  change (((singularChainComplexFunctor C).obj R).map X.map).f i ≫
      (H.fst.singularChainComplexFunctorObjMap R).hom i j =
    (H.snd.singularChainComplexFunctorObjMap R).hom i j ≫
      (((singularChainComplexFunctor C).obj R).map Y.map).f j
  exact singularChainHomotopy_compat H R i j

private noncomputable def homotopyHom
    {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]
    {X Y : TopPair.{w}} {f g : X ⟶ Y}
    (H : TopPair.Homotopy f g) (R : C) (i j : ℕ) :
    ((singularPairFunctor.obj X).chainComplex R).X i ⟶
      ((singularPairFunctor.obj Y).chainComplex R).X j :=
  (CokernelCofork.IsColimit.desc'
    ((singularPairFunctor.obj X).isColimitCokernelCoforkChainComplexX R i)
    ((ambientChainHomotopy H R).hom i j ≫
      ((singularPairFunctor.obj Y).chainComplexπ R).f j)
    (by
      rw [← Category.assoc, pairChainHomotopy_compat H R]
      simp)).1

@[reassoc]
private lemma chainComplexFunctorπ_f_homotopyHom
    {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]
    {X Y : TopPair.{w}} {f g : X ⟶ Y}
    (H : TopPair.Homotopy f g) (R : C) (i j : ℕ) :
    ((singularPairFunctor.obj X).chainComplexπ R).f i ≫ homotopyHom H R i j =
      (ambientChainHomotopy H R).hom i j ≫
        ((singularPairFunctor.obj Y).chainComplexπ R).f j := by
  exact (CokernelCofork.IsColimit.desc'
    ((singularPairFunctor.obj X).isColimitCokernelCoforkChainComplexX R i)
    ((ambientChainHomotopy H R).hom i j ≫
      ((singularPairFunctor.obj Y).chainComplexπ R).f j) _).2

@[reassoc]
private lemma chainComplexπ_f_naturality
    {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]
    (R : C) {P Q : SSetPair.{w}} (f : P ⟶ Q) (n : ℕ) :
    (P.chainComplexπ R).f n ≫ (SSetPair.chainComplexMap f R).f n =
      (SSet.chainComplexMap f.right R).f n ≫ (Q.chainComplexπ R).f n := by
  change ((((SSetPair.chainComplexFunctorπ C).app R).app P ≫
      ((SSetPair.chainComplexFunctor C).obj R).map f).f n) =
    ((((SSetPair.chainComplexFunctorRight C).obj R).map f ≫
      ((SSetPair.chainComplexFunctorπ C).app R).app Q).f n)
  exact congrArg (fun φ => φ.f n)
    (((SSetPair.chainComplexFunctorπ C).app R).naturality f).symm

/-- A homotopy of maps of topological pairs induces a chain homotopy on
relative singular chain complexes. -/
noncomputable def chainHomotopyOfPairHomotopy
    {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]
    {X Y : TopPair.{w}} {f g : X ⟶ Y}
    (H : TopPair.Homotopy f g) (R : C) :
    _root_.Homotopy
      ((chainComplexFunctor R).map f)
      ((chainComplexFunctor R).map g) := by
  change _root_.Homotopy
    (SSetPair.chainComplexMap (singularPairFunctor.map f) R)
    (SSetPair.chainComplexMap (singularPairFunctor.map g) R)
  exact
    { hom := homotopyHom H R
      zero i j hij := by
        apply (cancel_epi (((singularPairFunctor.obj X).chainComplexπ R).f i)).1
        rw [chainComplexFunctorπ_f_homotopyHom]
        rw [(ambientChainHomotopy H R).zero i j hij]
        simp
      comm i := by
        apply (cancel_epi (((singularPairFunctor.obj X).chainComplexπ R).f i)).1
        rw [Preadditive.comp_add, Preadditive.comp_add]
        rw [chainComplexπ_f_naturality]
        rw [← dNext_comp_left, ← prevD_comp_left]
        simp_rw [chainComplexFunctorπ_f_homotopyHom]
        rw [dNext_comp_right, prevD_comp_right]
        rw [chainComplexπ_f_naturality]
        rw [← Preadditive.add_comp, ← Preadditive.add_comp]
        rw [← (ambientChainHomotopy H R).comm i] }

end Hatcher.Relative
