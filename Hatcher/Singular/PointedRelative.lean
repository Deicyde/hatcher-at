/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Jack McCarthy
-/
import Hatcher.Singular.Homology
import Hatcher.Singular.ReducedRelative

/-!
# Relative homology at a basepoint

The pair consisting of a space and a chosen point has relative homology
canonically isomorphic to the reduced homology of the space.  The proof uses
the reduced long exact sequence, with a separate degree-zero endpoint argument.
-/

noncomputable section

open AlgebraicTopology CategoryTheory Limits ZeroObject

namespace Hatcher.Reduced

universe w v u

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C]

/-- The singular-chain augmentation of a one-point space is an isomorphism. -/
noncomputable def pointChainAugmentationIso (R : C) :
    ((TopCat.toSSet.obj (TopCat.of PUnit)).chainComplex R).X 0 ≅ R where
  hom := chainAugmentation R (TopCat.of PUnit)
  inv := (TopCat.toSSet.obj (TopCat.of PUnit)).ιChainComplex
    (TopCat.toSSetObj₀Equiv.symm PUnit.unit)
  hom_inv_id := by
    apply Sigma.hom_ext
    intro y
    obtain rfl : y = TopCat.toSSetObj₀Equiv.symm PUnit.unit := by
      apply TopCat.toSSetObj₀Equiv.injective
      exact Subsingleton.elim _ _
    dsimp [chainAugmentation]
    simp [SSet.ιChainComplex]
    exact (Category.comp_id _).symm
  inv_hom_id := ι_chainAugmentation R (TopCat.of PUnit)
    (TopCat.toSSetObj₀Equiv.symm PUnit.unit)

instance (R : C) : IsIso (chainAugmentation R (TopCat.of PUnit)) :=
  (pointChainAugmentationIso R).isIso_hom

/-- Reduced homology of a point vanishes in every nonnegative degree. -/
lemma isZero_pointHomology (R : C) (n : ℕ) :
    IsZero ((homologyFunctor R n).obj (TopCat.of PUnit)) := by
  cases n with
  | zero =>
      let A := (augmentedSingularChainComplexFunctor R).obj (TopCat.of PUnit)
      change IsZero (A.homology 1)
      rw [← HomologicalComplex.exactAt_iff_isZero_homology]
      rw [HomologicalComplex.exactAt_iff' A 2 1 0 (by simp) (by simp)]
      let _ : IsIso (A.d 1 0) := by
        change IsIso (chainAugmentation R (TopCat.of PUnit))
        infer_instance
      have hd : (A.sc' 2 1 0).f = 0 := by
        change A.d 2 1 = 0
        rw [← cancel_mono (A.d 1 0)]
        simp
      apply ((A.sc' 2 1 0).exact_iff_mono hd).2
      change Mono (A.d 1 0)
      infer_instance
  | succ k =>
      exact (isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
          C (k + 1) R (TopCat.of PUnit) (by omega)).of_iso
        ((homologyIsoOfPositiveDegree R (k + 1) (by omega)).app
          (TopCat.of PUnit))

end Hatcher.Reduced

namespace Hatcher.Relative

universe w v u

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C]

/-- The topological pair `(X, {x})`, represented by the embedding of a
one-point space whose image is the chosen point `x`. -/
noncomputable def pointedPair (X : TopCat.{w}) (x : X) : TopPair.{w} :=
  TopPair.of
    (TopCat.ofHom ⟨fun _ : PUnit ↦ x, continuous_const⟩)
    (Topology.IsEmbedding.of_subsingleton _)

/-- The map from reduced homology to relative homology supplied by the reduced
long exact sequence of the pointed pair. -/
noncomputable def pointedPairProjection
    (X : TopCat.{w}) (x : X) (R : C) (n : ℕ) :
    (Hatcher.Reduced.homologyFunctor R n).obj X ⟶
      (homologyFunctor R n).obj (pointedPair X x) :=
  HomologicalComplex.homologyMap
      (augmentedPairProjection (pointedPair X x) R) (n + 1) ≫
    (augmentedRelativeHomologyIso (pointedPair X x) R n).hom

set_option backward.isDefEq.respectTransparency false in
lemma pointedPairProjection_isIso
    (X : TopCat.{w}) (x : X) (R : C) (n : ℕ) :
    IsIso (pointedPairProjection X x R n) := by
  cases n with
  | zero =>
      let P := pointedPair X x
      let S := reducedPairZeroSequence P R
      have hS : S.Exact := reducedPairZeroSequence_exact P R PUnit.unit
      have hpoint :
          IsZero ((Hatcher.Reduced.homologyFunctor R 0).obj P.snd) := by
        change IsZero
          ((Hatcher.Reduced.homologyFunctor R 0).obj (TopCat.of PUnit))
        exact Hatcher.Reduced.isZero_pointHomology R 0
      have _ : Mono (S.map' 1 2) :=
        (hS.exact 0).mono_g (hpoint.eq_of_src _ _)
      have _ : Epi (S.map' 1 2) :=
        (hS.exact 1).epi_f ((isZero_zero C).eq_of_tgt _ _)
      change IsIso (S.map' 1 2)
      apply isIso_of_mono_of_epi
  | succ k =>
      let P := pointedPair X x
      let S := reducedPairSequence P R (k + 1) k rfl
      have hS : S.Exact := reducedPairSequence_exact P R (k + 1) k rfl
      have hpointHigh :
          IsZero ((Hatcher.Reduced.homologyFunctor R (k + 1)).obj P.snd) := by
        change IsZero
          ((Hatcher.Reduced.homologyFunctor R (k + 1)).obj (TopCat.of PUnit))
        exact Hatcher.Reduced.isZero_pointHomology R (k + 1)
      have hpointLow :
          IsZero ((Hatcher.Reduced.homologyFunctor R k).obj P.snd) := by
        change IsZero
          ((Hatcher.Reduced.homologyFunctor R k).obj (TopCat.of PUnit))
        exact Hatcher.Reduced.isZero_pointHomology R k
      have _ : Mono (S.map' 1 2) :=
        (hS.exact 0).mono_g (hpointHigh.eq_of_src _ _)
      have _ : Epi (S.map' 1 2) :=
        (hS.exact 1).epi_f (hpointLow.eq_of_tgt _ _)
      change IsIso (S.map' 1 2)
      apply isIso_of_mono_of_epi

/-- **Hatcher, Example 2.18 (page 118).** Relative homology at a chosen
basepoint is canonically isomorphic to reduced homology in every degree,
including degree zero. -/
noncomputable def pointedPairHomologyIso
    (X : TopCat.{w}) (x : X) (R : C) (n : ℕ) :
    (homologyFunctor R n).obj (pointedPair X x) ≅
      (Hatcher.Reduced.homologyFunctor R n).obj X := by
  have := pointedPairProjection_isIso X x R n
  exact (asIso (pointedPairProjection X x R n)).symm

end Hatcher.Relative
