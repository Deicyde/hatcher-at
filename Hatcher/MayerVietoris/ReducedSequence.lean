/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Hatcher.Excision.BinaryCover
import Hatcher.MayerVietoris.AugmentedChainComplex
import Hatcher.Singular.ReducedRelative
import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-!
# The reduced Mayer--Vietoris sequence

This file transports the homology sequence of the augmented binary-cover
chain complex to reduced singular homology of the actual subspaces and the
ambient space.  If the intersection is nonempty, it also supplies the
terminal degree-zero exact sequence.
-/

noncomputable section

open AlgebraicTopology CategoryTheory Limits ZeroObject

attribute [local instance] preservesBinaryBiproduct_of_preservesBiproduct

namespace Hatcher.MayerVietoris

universe w v u

variable {X : TopCat.{w}}
variable {C : Type u} [Category.{v} C] [Abelian C]
  [HasCoproducts.{w} C]

local instance reducedSequenceHasFiniteCoproducts : HasFiniteCoproducts C :=
  hasFiniteCoproducts_of_hasCoproducts C

local instance reducedSequenceHasBinaryBiproducts : HasBinaryBiproducts C :=
  HasBinaryBiproducts.of_hasBinaryCoproducts

private noncomputable abbrev augmentedSubspaceChains
    (A : Set X) (R : C) : ChainComplex C ℕ :=
  (Hatcher.Reduced.augmentedSingularChainComplexFunctor R).obj
    (TopCat.of A)

/-- The biproduct of the augmented singular complexes of the actual
subspaces, identified with the custom middle complex used to prove chain
exactness. -/
private noncomputable def augmentedSubspaceBiprodChainIso
    (A B : Set X) (R : C) :
    augmentedSubspaceChains A R ⊞ augmentedSubspaceChains B R ≅
      augmentedMiddleChains A B R :=
  biprod.mapIso (augmentedSubspaceChainIso A R)
      (augmentedSubspaceChainIso B R) ≪≫
    (augmentedMiddleChainsIso A B R).symm

/-- The augmented signed intersection map, expressed using the singular
chains of the actual subspaces. -/
private noncomputable def augmentedSubspaceIntersectionMap
    (A B : Set X) (R : C) :
    augmentedSubspaceChains (A ∩ B) R ⟶
      augmentedSubspaceChains A R ⊞ augmentedSubspaceChains B R :=
  (augmentedSubspaceChainIso (A ∩ B) R).hom ≫
    augmentedChainComplexIntersectionMap A B R ≫
    (augmentedSubspaceBiprodChainIso A B R).inv

/-- The augmented addition map from the singular chains of the actual
subspaces to the small-cover complex. -/
private noncomputable def augmentedSubspaceUnionMap
    (A B : Set X) (R : C) :
    augmentedSubspaceChains A R ⊞ augmentedSubspaceChains B R ⟶
      Hatcher.Excision.smallAugmentedChainComplex (Bool.rec A B) R :=
  (augmentedSubspaceBiprodChainIso A B R).hom ≫
    augmentedChainComplexUnionMap A B R

@[reassoc (attr := simp)]
private lemma augmentedSubspaceIntersectionMap_comp_unionMap
    (A B : Set X) (R : C) :
    augmentedSubspaceIntersectionMap A B R ≫
      augmentedSubspaceUnionMap A B R = 0 := by
  simp [augmentedSubspaceIntersectionMap, augmentedSubspaceUnionMap,
    Category.assoc]

/-- The augmented binary-cover short complex expressed using singular chains
of the actual subspaces. -/
private noncomputable abbrev augmentedSubspaceShortComplex
    (A B : Set X) (R : C) : ShortComplex (ChainComplex C ℕ) :=
  ShortComplex.mk (augmentedSubspaceIntersectionMap A B R)
    (augmentedSubspaceUnionMap A B R)
    (augmentedSubspaceIntersectionMap_comp_unionMap A B R)

private noncomputable def augmentedSubspaceShortComplexIso
    (A B : Set X) (R : C) :
    augmentedChainComplexShortComplex A B R ≅
      augmentedSubspaceShortComplex A B R :=
  ShortComplex.isoMk (augmentedSubspaceChainIso (A ∩ B) R).symm
    (augmentedSubspaceBiprodChainIso A B R).symm (Iso.refl _)
    (by simp [augmentedChainComplexShortComplex,
      augmentedSubspaceIntersectionMap])
    (by simp [augmentedChainComplexShortComplex,
      augmentedSubspaceUnionMap])

private theorem augmentedSubspaceShortComplex_shortExact
    (A B : Set X) (R : C) :
    (augmentedSubspaceShortComplex A B R).ShortExact :=
  ShortComplex.shortExact_of_iso (augmentedSubspaceShortComplexIso A B R)
    (augmentedChainComplexShortComplex_shortExact A B R)

/-- Homology takes the biproduct of the two augmented subspace complexes to
the biproduct of their homology objects. -/
private noncomputable def reducedMiddleHomologyIso
    (A B : Set X) (R : C) (n : ℕ) :
    (augmentedSubspaceChains A R ⊞
        augmentedSubspaceChains B R).homology (n + 1) ≅
      (Hatcher.Reduced.homologyFunctor R n).obj (TopCat.of A) ⊞
        (Hatcher.Reduced.homologyFunctor R n).obj (TopCat.of B) :=
  (HomologicalComplex.homologyFunctor C (ComplexShape.down ℕ)
    (n + 1)).mapBiprod _ _

/-- For a binary interior cover, augmented small-chain homology is reduced
singular homology of the ambient space. -/
private noncomputable def smallCoverReducedHomologyIso
    {A B : Set X} (h : Hatcher.Excision.CoverCondition A B)
    (R : C) (n : ℕ) :
    (Hatcher.Excision.smallAugmentedChainComplex
        (Bool.rec A B) R).homology (n + 1) ≅
      (Hatcher.Reduced.homologyFunctor R n).obj X :=
  (Hatcher.Excision.smallAugmentedChainInclusionHomotopyEquiv
    (Bool.rec A B) h.smallSimplicesCondition R).toHomologyIso (n + 1)

/-- The first map in the reduced Mayer--Vietoris sequence, with Hatcher's
sign convention `x ↦ (x, -x)`. -/
noncomputable def reducedIntersectionMap
    (A B : Set X) (R : C) (n : ℕ) :
    (Hatcher.Reduced.homologyFunctor R n).obj (TopCat.of ↥(A ∩ B)) ⟶
      (Hatcher.Reduced.homologyFunctor R n).obj (TopCat.of A) ⊞
        (Hatcher.Reduced.homologyFunctor R n).obj (TopCat.of B) :=
  HomologicalComplex.homologyMap
      (augmentedSubspaceIntersectionMap A B R) (n + 1) ≫
    (reducedMiddleHomologyIso A B R n).hom

/-- The second map in the reduced Mayer--Vietoris sequence, induced by
addition of the two inclusion maps into the ambient space. -/
noncomputable def reducedUnionMap
    (A B : Set X) (R : C) (n : ℕ) :
    (Hatcher.Reduced.homologyFunctor R n).obj (TopCat.of A) ⊞
        (Hatcher.Reduced.homologyFunctor R n).obj (TopCat.of B) ⟶
      (Hatcher.Reduced.homologyFunctor R n).obj X :=
  (reducedMiddleHomologyIso A B R n).inv ≫
    HomologicalComplex.homologyMap
      (augmentedSubspaceUnionMap A B R) (n + 1) ≫
    HomologicalComplex.homologyMap
      (Hatcher.Excision.smallAugmentedChainInclusion
        (Bool.rec A B) R) (n + 1)

private lemma homologyMap_augmentedSubspaceIntersectionMap
    (A B : Set X) (R : C) (n : ℕ) :
    HomologicalComplex.homologyMap
          (augmentedSubspaceIntersectionMap A B R) (n + 1) ≫
        (reducedMiddleHomologyIso A B R n).hom =
      reducedIntersectionMap A B R n := rfl

private lemma homologyMap_augmentedSubspaceUnionMap
    {A B : Set X} (h : Hatcher.Excision.CoverCondition A B)
    (R : C) (n : ℕ) :
    HomologicalComplex.homologyMap
          (augmentedSubspaceUnionMap A B R) (n + 1) ≫
        (smallCoverReducedHomologyIso h R n).hom =
      (reducedMiddleHomologyIso A B R n).hom ≫
        reducedUnionMap A B R n := by
  dsimp only [smallCoverReducedHomologyIso,
    HomotopyEquiv.toHomologyIso]
  rw [Hatcher.Excision.smallAugmentedChainInclusionHomotopyEquiv_hom]
  simp [reducedUnionMap]

/-- The connecting morphism in the reduced Mayer--Vietoris sequence. -/
noncomputable def reducedConnecting {A B : Set X}
    (h : Hatcher.Excision.CoverCondition A B)
    (R : C) (n m : ℕ) (hnm : m + 1 = n) :
    (Hatcher.Reduced.homologyFunctor R n).obj X ⟶
      (Hatcher.Reduced.homologyFunctor R m).obj (TopCat.of ↥(A ∩ B)) :=
  (smallCoverReducedHomologyIso h R n).inv ≫
    (augmentedSubspaceShortComplex_shortExact A B R).δ
      (n + 1) (m + 1) (by simpa using hnm)

private noncomputable abbrev augmentedReducedSequence
    (A B : Set X) (R : C) (n m : ℕ) (hnm : m + 1 = n) :
    ComposableArrows C 5 :=
  HomologicalComplex.HomologySequence.composableArrows₅
    (augmentedSubspaceShortComplex_shortExact A B R)
    (n + 1) (m + 1) (by simpa using hnm)

/-- Six consecutive terms in the reduced binary-cover Mayer--Vietoris
sequence. -/
noncomputable def reducedSequence {A B : Set X}
    (h : Hatcher.Excision.CoverCondition A B)
    (R : C) (n m : ℕ) (hnm : m + 1 = n) :
    ComposableArrows C 5 :=
  ComposableArrows.mk₅
    (reducedIntersectionMap A B R n)
    (reducedUnionMap A B R n)
    (reducedConnecting h R n m hnm)
    (reducedIntersectionMap A B R m)
    (reducedUnionMap A B R m)

set_option backward.isDefEq.respectTransparency false in
private noncomputable def augmentedReducedSequenceIso
    {A B : Set X} (h : Hatcher.Excision.CoverCondition A B)
    (R : C) (n m : ℕ) (hnm : m + 1 = n) :
    augmentedReducedSequence A B R n m hnm ≅
      reducedSequence h R n m hnm :=
  ComposableArrows.isoMk₅
    (Iso.refl _) (reducedMiddleHomologyIso A B R n)
    (smallCoverReducedHomologyIso h R n) (Iso.refl _)
    (reducedMiddleHomologyIso A B R m)
    (smallCoverReducedHomologyIso h R m)
    (by
      simpa [augmentedReducedSequence, reducedSequence] using
        homologyMap_augmentedSubspaceIntersectionMap A B R n)
    (by
      simpa [augmentedReducedSequence, reducedSequence] using
        homologyMap_augmentedSubspaceUnionMap h R n)
    (by simp [augmentedReducedSequence, reducedSequence,
      reducedConnecting])
    (by
      simpa [augmentedReducedSequence, reducedSequence] using
        homologyMap_augmentedSubspaceIntersectionMap A B R m)
    (by
      simpa [augmentedReducedSequence, reducedSequence] using
        homologyMap_augmentedSubspaceUnionMap h R m)

/-- **Hatcher, §2.2 (page 150).** Every adjacent-degree six-term window
in the reduced binary-cover Mayer--Vietoris sequence is exact. -/
theorem reducedSequence_exact {A B : Set X}
    (h : Hatcher.Excision.CoverCondition A B)
    (R : C) (n m : ℕ) (hnm : m + 1 = n) :
    (reducedSequence h R n m hnm).Exact := by
  apply ComposableArrows.exact_of_iso
    (augmentedReducedSequenceIso h R n m hnm)
  exact HomologicalComplex.HomologySequence.composableArrows₅_exact
    (augmentedSubspaceShortComplex_shortExact A B R)
    (n + 1) (m + 1) (by simpa using hnm)

/-- The six-term augmented homology sequence at chain degrees one and zero. -/
private noncomputable abbrev augmentedReducedZeroSequence
    (A B : Set X) (R : C) : ComposableArrows C 5 :=
  HomologicalComplex.HomologySequence.composableArrows₅
    (augmentedSubspaceShortComplex_shortExact A B R) 1 0 (by simp)

/-- The terminal degree-zero reduced Mayer--Vietoris sequence. -/
noncomputable def reducedZeroSequence
    (A B : Set X) (R : C) : ComposableArrows C 3 :=
  ComposableArrows.mk₃
    (reducedIntersectionMap A B R 0)
    (reducedUnionMap A B R 0)
    (0 : (Hatcher.Reduced.homologyFunctor R 0).obj X ⟶ (0 : C))

set_option backward.isDefEq.respectTransparency false in
private noncomputable def augmentedReducedZeroSequenceIso
    {A B : Set X} (h : Hatcher.Excision.CoverCondition A B)
    (R : C) (x : ↥(A ∩ B)) :
    (augmentedReducedZeroSequence A B R).δlast.δlast ≅
      reducedZeroSequence A B R :=
  ComposableArrows.isoMk₃
    (Iso.refl _) (reducedMiddleHomologyIso A B R 0)
    (smallCoverReducedHomologyIso h R 0)
    (Hatcher.Reduced.isZero_augmentedHomology_zero
      R (TopCat.of ↥(A ∩ B)) x).isoZero
    (by
      simpa [augmentedReducedZeroSequence, reducedZeroSequence] using
        homologyMap_augmentedSubspaceIntersectionMap A B R 0)
    (by
      simpa [augmentedReducedZeroSequence, reducedZeroSequence] using
        homologyMap_augmentedSubspaceUnionMap h R 0)
    (by exact (isZero_zero C).eq_of_tgt _ _)

/-- **Hatcher, §2.2 (page 150), degree-zero endpoint.** If the
intersection is nonempty, the sequence
`H̃₀(A ∩ B) ⟶ H̃₀(A) ⊞ H̃₀(B) ⟶ H̃₀(X) ⟶ 0`
is exact. -/
theorem reducedZeroSequence_exact {A B : Set X}
    (h : Hatcher.Excision.CoverCondition A B)
    (R : C) (hAB : Nonempty ↥(A ∩ B)) :
    (reducedZeroSequence A B R).Exact := by
  apply ComposableArrows.exact_of_iso
    (augmentedReducedZeroSequenceIso h R hAB.some)
  exact ((HomologicalComplex.HomologySequence.composableArrows₅_exact
    (augmentedSubspaceShortComplex_shortExact A B R)
    1 0 (by simp)).δlast).δlast

/-- The reduced Mayer--Vietoris sequence is exact in every adjacent-degree
window and, for nonempty intersection, at its terminal degree-zero end. -/
theorem reducedLongExact {A B : Set X}
    (h : Hatcher.Excision.CoverCondition A B)
    (R : C) (hAB : Nonempty ↥(A ∩ B)) :
    (∀ (n m : ℕ) (hnm : m + 1 = n),
      (reducedSequence h R n m hnm).Exact) ∧
      (reducedZeroSequence A B R).Exact := by
  exact ⟨fun n m hnm ↦ reducedSequence_exact h R n m hnm,
    reducedZeroSequence_exact h R hAB⟩

end Hatcher.MayerVietoris
