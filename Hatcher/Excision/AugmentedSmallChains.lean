/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Hatcher.Excision.SmallChainEquivalence
import Hatcher.Algebra.Homology.Augment
import Hatcher.Singular.Reduced

/-!
# Augmented small singular chains

This file restricts the singular-chain augmentation to the small-chain
subcomplex and extends the canonical small-chain inclusion to augmented
complexes.  For an interior cover, the resulting map is a chain-homotopy
equivalence.
-/

noncomputable section

open AlgebraicTopology CategoryTheory Limits HomologicalComplex Simplicial

namespace Hatcher.Excision

universe w v u

variable {X : TopCat.{w}} {ι : Type*} (U : ι → Set X)
variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasCoproducts.{w} C]

/-- The augmentation on small singular chains, obtained by restricting the
ordinary singular-chain augmentation. -/
noncomputable def smallChainAugmentation (R : C) :
    ((smallSubcomplex U).toSSet.chainComplex R).X 0 ⟶ R :=
  (SSet.chainComplexMap (smallSubcomplex U).ι R).f 0 ≫
    Hatcher.Reduced.chainAugmentation R X

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma smallChainAugmentation_condition (R : C) :
    ((smallSubcomplex U).toSSet.chainComplex R).d 1 0 ≫
      smallChainAugmentation U R = 0 := by
  rw [smallChainAugmentation,
    ← (SSet.chainComplexMap (smallSubcomplex U).ι R).comm_assoc]
  change (SSet.chainComplexMap (smallSubcomplex U).ι R).f 1 ≫
    ((((singularChainComplexFunctor C).obj R).obj X).d 1 0 ≫
      Hatcher.Reduced.chainAugmentation R X) = 0
  rw [Hatcher.Reduced.d_chainAugmentation, comp_zero]

/-- The small singular chain complex augmented by the restriction of the
ordinary singular-chain augmentation.  This is defined for every family of
subsets, without a cover hypothesis. -/
noncomputable def smallAugmentedChainComplex (R : C) : ChainComplex C ℕ :=
  ChainComplex.augment ((smallSubcomplex U).toSSet.chainComplex R)
    (smallChainAugmentation U R) (smallChainAugmentation_condition U R)

set_option backward.isDefEq.respectTransparency false in
/-- The canonical inclusion from augmented small singular chains to augmented
singular chains.  It is the identity on the inserted coefficient object and
the usual small-chain inclusion in every successor degree. -/
noncomputable def smallAugmentedChainInclusion (R : C) :
    smallAugmentedChainComplex U R ⟶
      (Hatcher.Reduced.augmentedSingularChainComplexFunctor R).obj X :=
  ChainComplex.augmentMap (smallChainAugmentation U R)
    (smallChainAugmentation_condition U R)
    (Hatcher.Reduced.chainAugmentation R X)
    (Hatcher.Reduced.d_chainAugmentation R X)
    (SSet.chainComplexMap (smallSubcomplex U).ι R) (𝟙 R) (by
      change ((SSet.chainComplexMap (smallSubcomplex U).ι R).f 0 ≫
        Hatcher.Reduced.chainAugmentation R X) ≫ 𝟙 R = _
      rw [Category.comp_id])

@[simp]
lemma smallAugmentedChainInclusion_f_zero (R : C) :
    (smallAugmentedChainInclusion U R).f 0 = 𝟙 R := rfl

@[simp]
lemma smallAugmentedChainInclusion_f_succ (R : C) (n : ℕ) :
    (smallAugmentedChainInclusion U R).f (n + 1) =
      (SSet.chainComplexMap (smallSubcomplex U).ι R).f n := rfl

set_option backward.isDefEq.respectTransparency false in
private lemma smallChainRetraction_augmentation
    (hU : SmallSimplicesCondition U) (R : C) :
    (smallChainInclusionHomotopyEquiv hU R).inv.f 0 ≫
        smallChainAugmentation U R =
      Hatcher.Reduced.chainAugmentation R X := by
  let e := smallChainInclusionHomotopyEquiv hU R
  have he := e.homotopyInvHomId.comm 0
  rw [Homotopy.dNext_zero_chainComplex,
    Homotopy.prevD_chainComplex] at he
  change e.inv.f 0 ≫ (e.hom.f 0 ≫
    Hatcher.Reduced.chainAugmentation R X) = _
  rw [← Category.assoc]
  change (e.inv ≫ e.hom).f 0 ≫
    Hatcher.Reduced.chainAugmentation R X = _
  rw [he, Preadditive.add_comp, Preadditive.add_comp, Category.assoc,
    Hatcher.Reduced.d_chainAugmentation, comp_zero, zero_comp]
  simp

/-- For an interior cover, the canonical inclusion of augmented small
singular chains into augmented singular chains is a chain-homotopy
equivalence. -/
noncomputable def smallAugmentedChainInclusionHomotopyEquiv
    (hU : SmallSimplicesCondition U) (R : C) :
    HomotopyEquiv (smallAugmentedChainComplex U R)
      ((Hatcher.Reduced.augmentedSingularChainComplexFunctor R).obj X) :=
  ChainComplex.augmentHomotopyEquiv (smallChainAugmentation U R)
    (smallChainAugmentation_condition U R)
    (Hatcher.Reduced.chainAugmentation R X)
    (Hatcher.Reduced.d_chainAugmentation R X)
    (smallChainInclusionHomotopyEquiv hU R) rfl
    (smallChainRetraction_augmentation U hU R).symm

@[simp]
lemma smallAugmentedChainInclusionHomotopyEquiv_hom
    (hU : SmallSimplicesCondition U) (R : C) :
    (smallAugmentedChainInclusionHomotopyEquiv U hU R).hom =
      smallAugmentedChainInclusion U R := rfl

end Hatcher.Excision
