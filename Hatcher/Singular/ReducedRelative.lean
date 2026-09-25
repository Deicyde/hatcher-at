/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Jack McCarthy
-/
import Hatcher.Singular.Reduced
import Hatcher.Singular.Relative

/-!
# The reduced long exact sequence of a pair

The relative singular chain complex is shifted up by one degree and given a
zero object in degree zero.  Together with the augmented singular complexes
of the subspace and ambient space, this gives a short exact sequence of chain
complexes whose homology sequence is the reduced long exact sequence.
-/

noncomputable section

open AlgebraicTopology CategoryTheory Limits ZeroObject

namespace Hatcher.Reduced

universe w v u

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C]

/-- The augmentation of a nonempty space is a split epimorphism: a chosen
vertex gives a section. -/
lemma chainAugmentation_epi (R : C) (X : TopCat.{w}) (x : X) :
    Epi (chainAugmentation R X) := by
  let x₀ := TopCat.toSSetObj₀Equiv.symm x
  let s : R ⟶ (((singularChainComplexFunctor C).obj R).obj X).X 0 :=
    (TopCat.toSSet.obj X).ιChainComplex x₀
  have hs : s ≫ chainAugmentation R X = 𝟙 R := by
    exact ι_chainAugmentation R X x₀
  let _ : IsSplitEpi (chainAugmentation R X) :=
    IsSplitEpi.mk' { section_ := s, id := hs }
  infer_instance

/-- The degree-zero homology of the augmented singular complex of a nonempty
space vanishes.  This is the augmentation argument at the end of the reduced
long exact sequence. -/
lemma isZero_augmentedHomology_zero (R : C) (X : TopCat.{w}) (x : X) :
    IsZero (((augmentedSingularChainComplexFunctor R).obj X).homology 0) := by
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  rw [HomologicalComplex.exactAt_iff'
    ((augmentedSingularChainComplexFunctor R).obj X) 1 0 0 (by simp) (by simp)]
  apply (ShortComplex.exact_iff_epi _ (by rfl)).2
  exact chainAugmentation_epi R X x

end Hatcher.Reduced

namespace Hatcher.Relative

universe w v u

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C]

/-- The relative singular complex shifted up by one degree, with a zero object
inserted in degree zero. -/
noncomputable def augmentedRelativeChainComplex (P : TopPair.{w}) (R : C) :
    ChainComplex C ℕ :=
  ChainComplex.augment ((chainComplexFunctor R).obj P)
    (0 : ((chainComplexFunctor R).obj P).X 0 ⟶ (0 : C)) (by simp)

/-- The inclusion of the augmented singular chains of the subspace in those
of the ambient space. -/
noncomputable def augmentedPairInclusion (P : TopPair.{w}) (R : C) :
    (Hatcher.Reduced.augmentedSingularChainComplexFunctor R).obj P.snd ⟶
      (Hatcher.Reduced.augmentedSingularChainComplexFunctor R).obj P.fst :=
  Hatcher.Reduced.augmentedMap R P.map

/-- The quotient from augmented ambient chains to the shifted relative
complex.  In degree zero this is `R ⟶ 0`; in successor degrees it is the
ordinary relative-chain quotient. -/
noncomputable def augmentedPairProjection (P : TopPair.{w}) (R : C) :
    (Hatcher.Reduced.augmentedSingularChainComplexFunctor R).obj P.fst ⟶
      augmentedRelativeChainComplex P R where
  f
    | 0 => 0
    | n + 1 => ((chainComplexFunctorπ R).app P).f n
  comm' i j hij := by
    match i, j with
    | 0, _ => simp at hij
    | 1, 0 =>
        change ((chainComplexFunctorπ R).app P).f 0 ≫ 0 =
          Hatcher.Reduced.chainAugmentation R P.fst ≫ 0
        rw [comp_zero, comp_zero]
        rfl
    | _ + 2, 0 => simp at hij
    | i + 1, j + 1 =>
        simp [augmentedRelativeChainComplex,
          Hatcher.Reduced.augmentedSingularChainComplexFunctor,
          ChainComplex.augment]
        exact ((chainComplexFunctorπ R).app P).comm i j

@[reassoc (attr := simp)]
lemma augmentedPair_condition (P : TopPair.{w}) (R : C) :
    augmentedPairInclusion P R ≫ augmentedPairProjection P R = 0 := by
  ext (_ | n)
  · change (𝟙 R) ≫ (0 : R ⟶ (0 : C)) = 0
    simp
  · change ((((singularChainComplexFunctor C).obj R).map P.map).f n ≫
      ((chainComplexFunctorπ R).app P).f n) = 0
    exact chainComplexFunctor_condition_f R P n

/-- The augmented short complex whose homology sequence is the reduced long
exact sequence of a pair. -/
noncomputable def augmentedPairChainComplexShortComplex
    (P : TopPair.{w}) (R : C) : ShortComplex (ChainComplex C ℕ) :=
  ShortComplex.mk (augmentedPairInclusion P R) (augmentedPairProjection P R)
    (augmentedPair_condition P R)

/-- The augmented pair sequence is short exact degree by degree.  Its degree
zero part is explicitly `R ⟶ R ⟶ 0`; its successor parts are the usual
short exact sequences of relative singular chains. -/
theorem augmentedPairChainComplexShortComplex_shortExact
    (P : TopPair.{w}) (R : C) :
    (augmentedPairChainComplexShortComplex P R).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  cases i with
  | zero =>
      change (ShortComplex.mk (𝟙 R) (0 : R ⟶ (0 : C)) (by simp)).ShortExact
      refine ShortComplex.ShortExact.mk' ?_ inferInstance inferInstance
      apply (ShortComplex.exact_iff_epi _ (by simp)).2
      infer_instance
  | succ n =>
      change (((singularPairFunctor.obj P).chainComplexShortComplex R).map
        (HomologicalComplex.eval C (ComplexShape.down ℕ) n)).ShortExact
      exact ((singularPairFunctor.obj P).shortExact_chainComplexShortComplex R).map
        (HomologicalComplex.eval C (ComplexShape.down ℕ) n)

/-- Homology in degree `n + 1` of a chain complex augmented by a zero object
is canonically isomorphic to the original complex's homology in degree `n`. -/
noncomputable def augmentZeroHomologyIso (K : ChainComplex C ℕ) (n : ℕ) :
    (ChainComplex.augment K (0 : K.X 0 ⟶ (0 : C)) (by simp)).homology (n + 1) ≅
      K.homology n := by
  cases n with
  | zero =>
      let A := ChainComplex.augment K (0 : K.X 0 ⟶ (0 : C)) (by simp)
      let eA : A.homology 1 ≅ A.opcycles 1 :=
        A.isoHomologyι 1 0 (by simp) (by rfl)
      let hA := A.opcyclesIsCokernel 2 1 (by simp)
      let hK := K.opcyclesIsCokernel 1 0 (by simp)
      let eO : A.opcycles 1 ≅ K.opcycles 0 :=
        IsColimit.coconePointUniqueUpToIso hA hK
      let eK : K.homology 0 ≅ K.opcycles 0 := K.isoHomologyι₀
      exact eA ≪≫ eO ≪≫ eK.symm
  | succ k =>
      let A := ChainComplex.augment K (0 : K.X 0 ⟶ (0 : C)) (by simp)
      exact A.homologyIsoSc' (k + 3) (k + 2) (k + 1) (by simp) (by simp) ≪≫
        ShortComplex.homologyMapIso (Iso.refl _) ≪≫
        (K.homologyIsoSc' (k + 2) (k + 1) k (by simp) (by simp)).symm

/-- Homology in degree `n + 1` of the zero-augmented relative complex is
canonically isomorphic to ordinary relative homology in degree `n`. -/
noncomputable def augmentedRelativeHomologyIso
    (P : TopPair.{w}) (R : C) (n : ℕ) :
    (augmentedRelativeChainComplex P R).homology (n + 1) ≅
      (homologyFunctor R n).obj P :=
  augmentZeroHomologyIso ((chainComplexFunctor R).obj P) n

/-- Six consecutive terms in the homology sequence of the augmented pair
short complex. -/
noncomputable def augmentedPairSequence
    (P : TopPair.{w}) (R : C) (n m : ℕ) (h : m + 1 = n) :
    ComposableArrows C 5 :=
  HomologicalComplex.HomologySequence.composableArrows₅
    (augmentedPairChainComplexShortComplex_shortExact P R)
    (n + 1) (m + 1) (by simpa using h)

/-- Six consecutive terms in the reduced long exact sequence of a pair.  The
absolute terms are reduced homology, while the relative terms are ordinary
relative homology. -/
noncomputable def reducedPairSequence
    (P : TopPair.{w}) (R : C) (n m : ℕ) (h : m + 1 = n) :
    ComposableArrows C 5 :=
  let S := augmentedPairSequence P R n m h
  ComposableArrows.mk₅
    (S.map' 0 1)
    (S.map' 1 2 ≫ (augmentedRelativeHomologyIso P R n).hom)
    ((augmentedRelativeHomologyIso P R n).inv ≫ S.map' 2 3)
    (S.map' 3 4)
    (S.map' 4 5 ≫ (augmentedRelativeHomologyIso P R m).hom)

set_option backward.isDefEq.respectTransparency false in
/-- The augmented homology sequence and the reduced pair sequence differ only
by the canonical identifications of shifted relative homology with ordinary
relative homology. -/
noncomputable def augmentedPairSequenceIso
    (P : TopPair.{w}) (R : C) (n m : ℕ) (h : m + 1 = n) :
    augmentedPairSequence P R n m h ≅ reducedPairSequence P R n m h :=
  ComposableArrows.isoMk₅
    (Iso.refl _) (Iso.refl _) (augmentedRelativeHomologyIso P R n)
    (Iso.refl _) (Iso.refl _) (augmentedRelativeHomologyIso P R m)
    (by simp [reducedPairSequence])
    (by simp [reducedPairSequence])
    (by simp [reducedPairSequence])
    (by simp [reducedPairSequence])
    (by simp [reducedPairSequence])

/-- **Hatcher, §2.1 (page 118).** Each six-term window obtained from the long
exact sequence of a pair by replacing the absolute groups with reduced
homology is exact. The augmented construction proves this without a
nonemptiness assumption; nonemptiness enters only at the terminal degree-zero
end below. Its positive-degree terms agree with ordinary homology through
`Hatcher.Reduced.homologyIsoOfPositiveDegree`. -/
theorem reducedPairSequence_exact
    (P : TopPair.{w}) (R : C) (n m : ℕ) (h : m + 1 = n) :
    (reducedPairSequence P R n m h).Exact := by
  apply ComposableArrows.exact_of_iso (augmentedPairSequenceIso P R n m h)
  exact HomologicalComplex.HomologySequence.composableArrows₅_exact
    (augmentedPairChainComplexShortComplex_shortExact P R)
    (n + 1) (m + 1) (by simpa using h)

/-- Consecutive six-term windows of the reduced pair sequence agree on their
three common terms. -/
lemma reducedPairSequence_overlap
    (P : TopPair.{w}) (R : C) (n m k : ℕ)
    (h : m + 1 = n) (h' : k + 1 = m) :
    (reducedPairSequence P R n m h).δ₀.δ₀.δ₀ =
      (reducedPairSequence P R m k h').δlast.δlast.δlast := by
  apply ComposableArrows.ext₂_of_arrow
  · rfl
  · rfl

/-- The six-term augmented homology sequence at degrees one and zero.  Its
first three objects are `H̃₀(A)`, `H̃₀(X)`, and `H₀(X,A)`; the fourth is
degree-zero homology of the augmented complex of `A`. -/
noncomputable def augmentedPairZeroSequence
    (P : TopPair.{w}) (R : C) : ComposableArrows C 5 :=
  HomologicalComplex.HomologySequence.composableArrows₅
    (augmentedPairChainComplexShortComplex_shortExact P R) 1 0 (by simp)

/-- The degree-zero end
`H̃₀(A) ⟶ H̃₀(X) ⟶ H₀(X,A) ⟶ 0` of the reduced long exact
sequence. -/
noncomputable def reducedPairZeroSequence
    (P : TopPair.{w}) (R : C) : ComposableArrows C 3 :=
  let S := (augmentedPairZeroSequence P R).δlast.δlast
  ComposableArrows.mk₃
    (S.map' 0 1)
    (S.map' 1 2 ≫ (augmentedRelativeHomologyIso P R 0).hom)
    (0 : (homologyFunctor R 0).obj P ⟶ (0 : C))

/-- The first three terms of the degree-zero endpoint are exactly the last
three terms of the adjacent-degree window from degree one to degree zero. -/
lemma reducedPairZeroSequence_δlast
    (P : TopPair.{w}) (R : C) :
    (reducedPairZeroSequence P R).δlast =
      (reducedPairSequence P R 1 0 rfl).δ₀.δ₀.δ₀ := by
  apply ComposableArrows.ext₂_of_arrow
  · rfl
  · rfl

set_option backward.isDefEq.respectTransparency false in
/-- The initial four terms of the degree-one/degree-zero augmented homology
sequence identify with the degree-zero end of the reduced pair sequence. -/
noncomputable def augmentedPairZeroSequenceIso
    (P : TopPair.{w}) (R : C) (x : P.snd) :
    (augmentedPairZeroSequence P R).δlast.δlast ≅
      reducedPairZeroSequence P R :=
  ComposableArrows.isoMk₃
    (Iso.refl _) (Iso.refl _) (augmentedRelativeHomologyIso P R 0)
    (Hatcher.Reduced.isZero_augmentedHomology_zero R P.snd x).isoZero
    (by
      dsimp [reducedPairZeroSequence]
      rw [Category.comp_id, Category.id_comp])
    (by
      dsimp [reducedPairZeroSequence]
      simp)
    (by exact (isZero_zero C).eq_of_tgt _ _)

/-- **Hatcher, §2.1 (page 118), degree-zero endpoint.** If the subspace is
nonempty, the terminal sequence
`H̃₀(A) ⟶ H̃₀(X) ⟶ H₀(X,A) ⟶ 0` is exact. -/
theorem reducedPairZeroSequence_exact
    (P : TopPair.{w}) (R : C) (x : P.snd) :
    (reducedPairZeroSequence P R).Exact := by
  apply ComposableArrows.exact_of_iso (augmentedPairZeroSequenceIso P R x)
  exact ((HomologicalComplex.HomologySequence.composableArrows₅_exact
    (augmentedPairChainComplexShortComplex_shortExact P R) 1 0 (by simp)).δlast).δlast

/-- The reduced pair sequence is exact in every adjacent-degree window and at
its terminal degree-zero end. -/
theorem reducedPairLongExact
    (P : TopPair.{w}) (R : C) (hP : Nonempty P.snd) :
    (∀ (n m : ℕ) (h : m + 1 = n),
      (reducedPairSequence P R n m h).Exact) ∧
      (reducedPairZeroSequence P R).Exact := by
  exact ⟨fun n m h ↦ reducedPairSequence_exact P R n m h,
    reducedPairZeroSequence_exact P R hP.some⟩

end Hatcher.Relative
