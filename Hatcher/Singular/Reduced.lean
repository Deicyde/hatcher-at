/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Jack McCarthy
-/
import Mathlib.Algebra.Homology.Augment
import Mathlib.AlgebraicTopology.SingularHomology.Basic

/-!
# Reduced singular chains

This file constructs Hatcher's augmented singular chain complex. The ordinary
singular complex is shifted up one degree and its degree-zero chains map to the
coefficient object by sending every singular vertex to the identity.
-/

noncomputable section

open AlgebraicTopology CategoryTheory Limits Simplicial

namespace Hatcher.Reduced

universe w v u

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]

/-- The augmentation of degree-zero singular chains, sending every singular
vertex to the identity of the coefficient object. -/
noncomputable def chainAugmentation (R : C) (X : TopCat.{w}) :
    (((singularChainComplexFunctor C).obj R).obj X).X 0 ⟶ R :=
  Sigma.desc (fun _ ↦ 𝟙 R)

/-- The singular-chain augmentation sends every degree-zero generator to the
identity of the coefficient object. -/
@[reassoc (attr := simp)]
lemma ι_chainAugmentation (R : C) (X : TopCat.{w})
    (x : (TopCat.toSSet.obj X) _⦋0⦌) :
    (TopCat.toSSet.obj X).ιChainComplex x ≫ chainAugmentation R X = 𝟙 R := by
  change Sigma.ι (fun _ : (TopCat.toSSet.obj X) _⦋0⦌ ↦ R) x ≫
    Sigma.desc (fun _ ↦ 𝟙 R) = 𝟙 R
  rw [Sigma.ι_desc]

/-- The degree-one singular boundary is killed by the augmentation. -/
lemma d_chainAugmentation (R : C) (X : TopCat.{w}) :
    (((singularChainComplexFunctor C).obj R).obj X).d 1 0 ≫
      chainAugmentation R X = 0 := by
  change ((TopCat.toSSet.obj X).chainComplex R).d 1 0 ≫
    chainAugmentation R X = 0
  apply (TopCat.toSSet.obj X).chainComplex_hom_ext
  intro x
  rw [← Category.assoc, SSet.ιChainComplex_d]
  simp

/-- Naturality of the singular-chain augmentation in the space. -/
lemma chainMap_f_zero_chainAugmentation
    {X Y : TopCat.{w}} (R : C) (f : X ⟶ Y) :
    (((singularChainComplexFunctor C).obj R).map f).f 0 ≫
      chainAugmentation R Y =
      chainAugmentation R X := by
  change (SSet.chainComplexMap (TopCat.toSSet.map f) R).f 0 ≫
      chainAugmentation R Y = chainAugmentation R X
  apply (TopCat.toSSet.obj X).chainComplex_hom_ext
  intro x
  rw [← Category.assoc]
  rw [SSet.ι_chainComplexMap_f]
  simp

/-- A continuous map induces a map of augmented singular chain complexes. -/
noncomputable def augmentedMap
    {X Y : TopCat.{w}} (R : C) (f : X ⟶ Y) :
    ChainComplex.augment
        (((singularChainComplexFunctor C).obj R).obj X)
        (chainAugmentation R X) (d_chainAugmentation R X) ⟶
      ChainComplex.augment
        (((singularChainComplexFunctor C).obj R).obj Y)
        (chainAugmentation R Y) (d_chainAugmentation R Y) where
  f
    | 0 => 𝟙 R
    | n + 1 => (((singularChainComplexFunctor C).obj R).map f).f n
  comm' i j _ := by
    match i, j with
    | 0, _ => simp [ChainComplex.augment]
    | 1, 0 => simpa [ChainComplex.augment] using
        chainMap_f_zero_chainAugmentation R f
    | _ + 2, 0 => simp [ChainComplex.augment]
    | i + 1, j + 1 => simp [ChainComplex.augment]

/-- **Hatcher, §2.1 (page 110).** The augmented singular chain complex,
functorial in the space. Its degree zero is the coefficient object `R`, its
degree `n + 1` is the ordinary singular chain object in degree `n`, and its
degree-one differential is the singular-chain augmentation. -/
noncomputable def augmentedSingularChainComplexFunctor (R : C) :
    TopCat.{w} ⥤ ChainComplex C ℕ where
  obj X := ChainComplex.augment
    (((singularChainComplexFunctor C).obj R).obj X)
    (chainAugmentation R X) (d_chainAugmentation R X)
  map f := augmentedMap R f
  map_id X := by
    ext (_ | n)
    · rfl
    · simp [augmentedMap]
  map_comp f g := by
    ext (_ | n)
    · simp [augmentedMap]
    · simp [augmentedMap]

section Homology

variable [CategoryWithHomology C]

/-- **Hatcher, §2.1 (pages 110 and 113).** Reduced singular homology in degree
`n`, defined as degree `n + 1` homology of the augmented singular chain
complex. This is functorial in the space. -/
noncomputable def homologyFunctor (R : C) (n : ℕ) : TopCat.{w} ⥤ C :=
  augmentedSingularChainComplexFunctor R ⋙
    HomologicalComplex.homologyFunctor C (ComplexShape.down ℕ) (n + 1)

end Homology

end Hatcher.Reduced
