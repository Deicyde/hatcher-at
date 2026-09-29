/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Hatcher.Excision.SmallChainEquivalence
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

private noncomputable def augmentMap
    {K L : ChainComplex C ℕ} {P Q : C}
    (εK : K.X 0 ⟶ P) (hK : K.d 1 0 ≫ εK = 0)
    (εL : L.X 0 ⟶ Q) (hL : L.d 1 0 ≫ εL = 0)
    (f : K ⟶ L) (a : P ⟶ Q)
    (ha : εK ≫ a = f.f 0 ≫ εL) :
    ChainComplex.augment K εK hK ⟶ ChainComplex.augment L εL hL where
  f
    | 0 => a
    | n + 1 => f.f n
  comm' i j _ := by
    match i, j with
    | 0, _ => simp [ChainComplex.augment]
    | 1, 0 => exact ha.symm
    | _ + 2, 0 => simp [ChainComplex.augment]
    | i + 1, j + 1 => simp [ChainComplex.augment, f.comm]

private noncomputable def augmentHomotopyHom
    {K L : ChainComplex C ℕ} {P Q : C}
    (εK : K.X 0 ⟶ P) (hK : K.d 1 0 ≫ εK = 0)
    (εL : L.X 0 ⟶ Q) (hL : L.d 1 0 ≫ εL = 0)
    {f g : K ⟶ L} (h : Homotopy f g) :
    ∀ i j, (ChainComplex.augment K εK hK).X i ⟶
      (ChainComplex.augment L εL hL).X j := fun i j ↦
  match i, j with
  | 0, _ => 0
  | _ + 1, 0 => 0
  | i + 1, j + 1 => h.hom i j

set_option backward.isDefEq.respectTransparency false in
private noncomputable def augmentHomotopy
    {K L : ChainComplex C ℕ} {P Q : C}
    (εK : K.X 0 ⟶ P) (hK : K.d 1 0 ≫ εK = 0)
    (εL : L.X 0 ⟶ Q) (hL : L.d 1 0 ≫ εL = 0)
    {f g : K ⟶ L} {F G :
      ChainComplex.augment K εK hK ⟶ ChainComplex.augment L εL hL}
    (h : Homotopy f g) (hzero : F.f 0 = G.f 0)
    (hF : ∀ n, F.f (n + 1) = f.f n)
    (hG : ∀ n, G.f (n + 1) = g.f n) : Homotopy F G where
  hom := augmentHomotopyHom εK hK εL hL h
  zero i j hij := by
    obtain _ | i := i
    · rfl
    obtain _ | j := j
    · rfl
    apply h.zero i j
    simpa using hij
  comm i := by
    obtain _ | n := i
    · rw [Homotopy.dNext_zero_chainComplex,
        Homotopy.prevD_chainComplex]
      simpa only [augmentHomotopyHom, zero_comp, zero_add] using hzero
    · rw [Homotopy.dNext_succ_chainComplex,
        Homotopy.prevD_chainComplex, hF n, hG n]
      obtain _ | n := n
      · have hn := h.comm 0
        rw [Homotopy.dNext_zero_chainComplex,
          Homotopy.prevD_chainComplex] at hn
        change f.f 0 = εK ≫ (0 : P ⟶ L.X 0) +
          h.hom 0 (0 + 1) ≫ L.d (0 + 1) 0 + g.f 0
        rw [comp_zero, zero_add]
        simpa only [zero_add] using hn
      · have hn := h.comm (n + 1)
        rw [Homotopy.dNext_succ_chainComplex,
          Homotopy.prevD_chainComplex] at hn
        change f.f (n + 1) =
          K.d (n + 1) n ≫ h.hom n (n + 1) +
            h.hom (n + 1) (n + 1 + 1) ≫
              L.d (n + 1 + 1) (n + 1) + g.f (n + 1)
        exact hn

private noncomputable def augmentHomotopyEquiv
    {K L : ChainComplex C ℕ} {P : C}
    (εK : K.X 0 ⟶ P) (hK : K.d 1 0 ≫ εK = 0)
    (εL : L.X 0 ⟶ P) (hL : L.d 1 0 ≫ εL = 0)
    (e : HomotopyEquiv K L)
    (he : εK = e.hom.f 0 ≫ εL)
    (he' : εL = e.inv.f 0 ≫ εK) :
    HomotopyEquiv (ChainComplex.augment K εK hK)
      (ChainComplex.augment L εL hL) where
  hom := augmentMap εK hK εL hL e.hom (𝟙 P) (by simpa using he)
  inv := augmentMap εL hL εK hK e.inv (𝟙 P) (by simpa using he')
  homotopyHomInvId :=
    augmentHomotopy εK hK εK hK e.homotopyHomInvId
      (by simp [augmentMap])
      (fun n ↦ by simp [augmentMap])
      (fun n ↦ by simp)
  homotopyInvHomId :=
    augmentHomotopy εL hL εL hL e.homotopyInvHomId
      (by simp [augmentMap])
      (fun n ↦ by simp [augmentMap])
      (fun n ↦ by simp)

set_option backward.isDefEq.respectTransparency false in
/-- The canonical inclusion from augmented small singular chains to augmented
singular chains.  It is the identity on the inserted coefficient object and
the usual small-chain inclusion in every successor degree. -/
noncomputable def smallAugmentedChainInclusion (R : C) :
    smallAugmentedChainComplex U R ⟶
      (Hatcher.Reduced.augmentedSingularChainComplexFunctor R).obj X :=
  augmentMap (smallChainAugmentation U R)
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
  augmentHomotopyEquiv (smallChainAugmentation U R)
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
