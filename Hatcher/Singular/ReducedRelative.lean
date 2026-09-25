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

/-- A chain map induces a map between the corresponding complexes augmented
by a zero object. -/
noncomputable def augmentZeroMap {K L : ChainComplex C ℕ} (f : K ⟶ L) :
    ChainComplex.augment K (0 : K.X 0 ⟶ (0 : C)) (by simp) ⟶
      ChainComplex.augment L (0 : L.X 0 ⟶ (0 : C)) (by simp) where
  f
    | 0 => 0
    | n + 1 => f.f n
  comm' i j hij := by
    match i, j with
    | 0, _ => simp at hij
    | 1, 0 =>
        change f.f 0 ≫ (0 : L.X 0 ⟶ (0 : C)) =
          (0 : K.X 0 ⟶ (0 : C)) ≫ 0
        simp
    | k + 2, 0 =>
        change f.f (k + 1) ≫ (0 : L.X (k + 1) ⟶ (0 : C)) =
          (0 : K.X (k + 1) ⟶ (0 : C)) ≫ 0
        simp
    | i + 1, j + 1 => simp [ChainComplex.augment, f.comm]

/-- In the lowest shifted degree, the opcycles of a zero-augmented complex
are canonically the degree-zero opcycles of the original complex. -/
noncomputable def augmentZeroOpcyclesIso (K : ChainComplex C ℕ) :
    (ChainComplex.augment K (0 : K.X 0 ⟶ (0 : C)) (by simp)).opcycles 1 ≅
      K.opcycles 0 :=
  ((ChainComplex.augment K (0 : K.X 0 ⟶ (0 : C)) (by simp)).opcyclesIsCokernel
      2 1 (by simp)).coconePointUniqueUpToIso
    (K.opcyclesIsCokernel 1 0 (by simp))

omit [HasCoproducts.{w} C] in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma pOpcycles_augmentZeroOpcyclesIso_hom (K : ChainComplex C ℕ) :
    (ChainComplex.augment K (0 : K.X 0 ⟶ (0 : C)) (by simp)).pOpcycles 1 ≫
        (augmentZeroOpcyclesIso K).hom =
      K.pOpcycles 0 := by
  simpa only [augmentZeroOpcyclesIso, Cofork.ofπ_ι_app] using
    ((ChainComplex.augment K (0 : K.X 0 ⟶ (0 : C)) (by simp)).opcyclesIsCokernel
        2 1 (by simp)).comp_coconePointUniqueUpToIso_hom
      (K.opcyclesIsCokernel 1 0 (by simp)) WalkingParallelPair.one

omit [HasCoproducts.{w} C] in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma augmentZeroOpcyclesIso_naturality {K L : ChainComplex C ℕ} (f : K ⟶ L) :
    HomologicalComplex.opcyclesMap (augmentZeroMap f) 1 ≫
        (augmentZeroOpcyclesIso L).hom =
      (augmentZeroOpcyclesIso K).hom ≫
        HomologicalComplex.opcyclesMap f 0 := by
  rw [← cancel_epi
    ((ChainComplex.augment K (0 : K.X 0 ⟶ (0 : C)) (by simp)).pOpcycles 1)]
  simp [augmentZeroMap]

/-- The degree-one homology of a zero-augmented complex is canonically the
degree-zero homology of the original complex. -/
noncomputable def augmentZeroHomologyIsoZero (K : ChainComplex C ℕ) :
    (ChainComplex.augment K (0 : K.X 0 ⟶ (0 : C)) (by simp)).homology 1 ≅
      K.homology 0 :=
  (ChainComplex.augment K (0 : K.X 0 ⟶ (0 : C)) (by simp)).isoHomologyι
      1 0 (by simp) (by rfl) ≪≫
    augmentZeroOpcyclesIso K ≪≫ K.isoHomologyι₀.symm

omit [HasCoproducts.{w} C] in
set_option backward.isDefEq.respectTransparency false in
lemma augmentZeroHomologyIsoZero_naturality
    {K L : ChainComplex C ℕ} (f : K ⟶ L) :
    HomologicalComplex.homologyMap (augmentZeroMap f) 1 ≫
        (augmentZeroHomologyIsoZero L).hom =
      (augmentZeroHomologyIsoZero K).hom ≫
        HomologicalComplex.homologyMap f 0 := by
  rw [← cancel_mono (L.homologyι 0)]
  simp only [augmentZeroHomologyIsoZero, Iso.trans_hom, Category.assoc,
    Iso.symm_hom, HomologicalComplex.isoHomologyι_hom,
    HomologicalComplex.homologyι_naturality_assoc,
    ChainComplex.isoHomologyι₀_inv_naturality_assoc,
    HomologicalComplex.isoHomologyι_inv_hom_id]
  simp only [augmentZeroOpcyclesIso_naturality_assoc]

/-- Away from the newly inserted degree zero, the short complexes computing
homology before and after zero augmentation agree naturally. -/
noncomputable def augmentZeroPositiveShortComplexIso
    (K : ChainComplex C ℕ) (k : ℕ) :
    (ChainComplex.augment K (0 : K.X 0 ⟶ (0 : C)) (by simp)).sc (k + 2) ≅
      K.sc (k + 1) :=
  (ChainComplex.augment K (0 : K.X 0 ⟶ (0 : C)) (by simp)).isoSc'
      (k + 3) (k + 2) (k + 1) (by simp) (by simp) ≪≫
    (Iso.refl _) ≪≫
    (K.isoSc' (k + 2) (k + 1) k (by simp) (by simp)).symm

omit [HasCoproducts.{w} C] in
set_option backward.isDefEq.respectTransparency false in
lemma augmentZeroPositiveShortComplexIso_naturality
    {K L : ChainComplex C ℕ} (f : K ⟶ L) (k : ℕ) :
    ((HomologicalComplex.shortComplexFunctor C (ComplexShape.down ℕ) (k + 2)).map
        (augmentZeroMap f)) ≫ (augmentZeroPositiveShortComplexIso L k).hom =
      (augmentZeroPositiveShortComplexIso K k).hom ≫
        ((HomologicalComplex.shortComplexFunctor C (ComplexShape.down ℕ)
          (k + 1)).map f) := by
  dsimp [augmentZeroPositiveShortComplexIso]
  simp only [Category.assoc]
  simp only [Category.id_comp]
  rw [(HomologicalComplex.natIsoSc' C (ComplexShape.down ℕ)
    (k + 3) (k + 2) (k + 1) (by simp) (by simp)).hom.naturality_assoc
      (augmentZeroMap f)]
  congr 1
  change ((HomologicalComplex.shortComplexFunctor' C (ComplexShape.down ℕ)
      (k + 2) (k + 1) k).map f) ≫
        (HomologicalComplex.natIsoSc' C (ComplexShape.down ℕ)
          (k + 2) (k + 1) k (by simp) (by simp)).inv.app L =
    (HomologicalComplex.natIsoSc' C (ComplexShape.down ℕ)
          (k + 2) (k + 1) k (by simp) (by simp)).inv.app K ≫
      ((HomologicalComplex.shortComplexFunctor C (ComplexShape.down ℕ)
        (k + 1)).map f)
  exact (HomologicalComplex.natIsoSc' C (ComplexShape.down ℕ)
    (k + 2) (k + 1) k (by simp) (by simp)).inv.naturality f

/-- The positive-degree part of the homology comparison induced by zero
augmentation. -/
noncomputable def augmentZeroPositiveHomologyIso
    (K : ChainComplex C ℕ) (k : ℕ) :
    (ChainComplex.augment K (0 : K.X 0 ⟶ (0 : C)) (by simp)).homology (k + 2) ≅
      K.homology (k + 1) :=
  ShortComplex.homologyMapIso (augmentZeroPositiveShortComplexIso K k)

omit [HasCoproducts.{w} C] in
set_option backward.isDefEq.respectTransparency false in
lemma augmentZeroPositiveHomologyIso_naturality
    {K L : ChainComplex C ℕ} (f : K ⟶ L) (k : ℕ) :
    HomologicalComplex.homologyMap (augmentZeroMap f) (k + 2) ≫
        (augmentZeroPositiveHomologyIso L k).hom =
      (augmentZeroPositiveHomologyIso K k).hom ≫
        HomologicalComplex.homologyMap f (k + 1) := by
  change ShortComplex.homologyMap _ ≫ ShortComplex.homologyMap _ =
    ShortComplex.homologyMap _ ≫ ShortComplex.homologyMap _
  rw [← ShortComplex.homologyMap_comp, ← ShortComplex.homologyMap_comp]
  congr 1
  exact augmentZeroPositiveShortComplexIso_naturality f k

/-- Homology in degree `n + 1` of a chain complex augmented by a zero object
is canonically isomorphic to the original complex's homology in degree `n`. -/
noncomputable def augmentZeroHomologyIso (K : ChainComplex C ℕ) (n : ℕ) :
    (ChainComplex.augment K (0 : K.X 0 ⟶ (0 : C)) (by simp)).homology (n + 1) ≅
      K.homology n := by
  cases n with
  | zero => exact augmentZeroHomologyIsoZero K
  | succ k => exact augmentZeroPositiveHomologyIso K k

omit [HasCoproducts.{w} C] in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma augmentZeroHomologyIso_naturality
    {K L : ChainComplex C ℕ} (f : K ⟶ L) (n : ℕ) :
    HomologicalComplex.homologyMap (augmentZeroMap f) (n + 1) ≫
        (augmentZeroHomologyIso L n).hom =
      (augmentZeroHomologyIso K n).hom ≫
        HomologicalComplex.homologyMap f n := by
  cases n with
  | zero => exact augmentZeroHomologyIsoZero_naturality f
  | succ k => exact augmentZeroPositiveHomologyIso_naturality f k

/-- A map of pairs induces a map of their zero-augmented relative chain
complexes. -/
noncomputable def augmentedRelativeMap {P Q : TopPair.{w}}
    (f : P ⟶ Q) (R : C) :
    augmentedRelativeChainComplex P R ⟶ augmentedRelativeChainComplex Q R :=
  augmentZeroMap ((chainComplexFunctor R).map f)

/-- A map of pairs induces a morphism between the augmented short complexes
whose homology sequences give the reduced pair sequences. -/
noncomputable def augmentedPairChainComplexMap {P Q : TopPair.{w}}
    (f : P ⟶ Q) (R : C) :
    augmentedPairChainComplexShortComplex P R ⟶
      augmentedPairChainComplexShortComplex Q R where
  τ₁ := Hatcher.Reduced.augmentedMap R (TopPair.Hom.snd f)
  τ₂ := Hatcher.Reduced.augmentedMap R (TopPair.Hom.fst f)
  τ₃ := augmentedRelativeMap f R
  comm₁₂ := by
    change (Hatcher.Reduced.augmentedSingularChainComplexFunctor R).map
          (TopPair.Hom.snd f) ≫
        (Hatcher.Reduced.augmentedSingularChainComplexFunctor R).map Q.map =
      (Hatcher.Reduced.augmentedSingularChainComplexFunctor R).map P.map ≫
        (Hatcher.Reduced.augmentedSingularChainComplexFunctor R).map
          (TopPair.Hom.fst f)
    rw [← Functor.map_comp, TopPair.Hom.w, Functor.map_comp]
  comm₂₃ := by
    ext (_ | n)
    · change (𝟙 R) ≫ (0 : R ⟶ (0 : C)) =
          (0 : R ⟶ (0 : C)) ≫ (0 : (0 : C) ⟶ (0 : C))
      simp
    · change ((((singularChainComplexFunctor C).obj R).map
          (TopPair.Hom.fst f)).f n ≫ ((chainComplexFunctorπ R).app Q).f n) =
        ((chainComplexFunctorπ R).app P).f n ≫
          ((chainComplexFunctor R).map f).f n
      exact HomologicalComplex.congr_hom ((chainComplexFunctorπ R).naturality f) n

set_option backward.isDefEq.respectTransparency false in
/-- The augmented pair short complex is functorial in the pair. -/
noncomputable def augmentedPairChainComplexShortComplexFunctor (R : C) :
    TopPair.{w} ⥤ ShortComplex (ChainComplex C ℕ) where
  obj P := augmentedPairChainComplexShortComplex P R
  map f := augmentedPairChainComplexMap f R
  map_id P := by
    apply ShortComplex.hom_ext
    · exact (Hatcher.Reduced.augmentedSingularChainComplexFunctor R).map_id P.snd
    · exact (Hatcher.Reduced.augmentedSingularChainComplexFunctor R).map_id P.fst
    · ext (_ | n)
      · exact (isZero_zero C).eq_of_src _ _
      · change ((chainComplexFunctor R).map (𝟙 P)).f n = 𝟙 _
        exact HomologicalComplex.congr_hom ((chainComplexFunctor R).map_id P) n
  map_comp f g := by
    apply ShortComplex.hom_ext
    · exact (Hatcher.Reduced.augmentedSingularChainComplexFunctor R).map_comp
        (TopPair.Hom.snd f) (TopPair.Hom.snd g)
    · exact (Hatcher.Reduced.augmentedSingularChainComplexFunctor R).map_comp
        (TopPair.Hom.fst f) (TopPair.Hom.fst g)
    · ext (_ | n)
      · exact (isZero_zero C).eq_of_src _ _
      · change ((chainComplexFunctor R).map (f ≫ g)).f n =
            ((chainComplexFunctor R).map f).f n ≫
              ((chainComplexFunctor R).map g).f n
        exact HomologicalComplex.congr_hom ((chainComplexFunctor R).map_comp f g) n

/-- Homology in degree `n + 1` of the zero-augmented relative complex is
canonically isomorphic to ordinary relative homology in degree `n`. -/
noncomputable def augmentedRelativeHomologyIso
    (P : TopPair.{w}) (R : C) (n : ℕ) :
    (augmentedRelativeChainComplex P R).homology (n + 1) ≅
      (homologyFunctor R n).obj P :=
  augmentZeroHomologyIso ((chainComplexFunctor R).obj P) n

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma augmentedRelativeHomologyIso_naturality {P Q : TopPair.{w}}
    (f : P ⟶ Q) (R : C) (n : ℕ) :
    HomologicalComplex.homologyMap (augmentedRelativeMap f R) (n + 1) ≫
        (augmentedRelativeHomologyIso Q R n).hom =
      (augmentedRelativeHomologyIso P R n).hom ≫
        (homologyFunctor R n).map f := by
  change HomologicalComplex.homologyMap
        (augmentZeroMap ((chainComplexFunctor R).map f)) (n + 1) ≫
      (augmentZeroHomologyIso ((chainComplexFunctor R).obj Q) n).hom =
    (augmentZeroHomologyIso ((chainComplexFunctor R).obj P) n).hom ≫
      HomologicalComplex.homologyMap ((chainComplexFunctor R).map f) n
  exact augmentZeroHomologyIso_naturality ((chainComplexFunctor R).map f) n

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma augmentedRelativeHomologyIso_inv_naturality {P Q : TopPair.{w}}
    (f : P ⟶ Q) (R : C) (n : ℕ) :
    (homologyFunctor R n).map f ≫
        (augmentedRelativeHomologyIso Q R n).inv =
      (augmentedRelativeHomologyIso P R n).inv ≫
        HomologicalComplex.homologyMap (augmentedRelativeMap f R) (n + 1) := by
  rw [← cancel_mono (augmentedRelativeHomologyIso Q R n).hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [augmentedRelativeHomologyIso_naturality]
  simp

/-- Six consecutive terms in the homology sequence of the augmented pair
short complex. -/
noncomputable def augmentedPairSequence
    (P : TopPair.{w}) (R : C) (n m : ℕ) (h : m + 1 = n) :
    ComposableArrows C 5 :=
  HomologicalComplex.HomologySequence.composableArrows₅
    (augmentedPairChainComplexShortComplex_shortExact P R)
    (n + 1) (m + 1) (by simpa using h)

/-- A map of pairs induces a morphism between the corresponding six-term
windows of the augmented homology sequences. -/
noncomputable def augmentedPairSequenceMap {P Q : TopPair.{w}} (f : P ⟶ Q)
    (R : C) (n m : ℕ) (h : m + 1 = n) :
    augmentedPairSequence P R n m h ⟶ augmentedPairSequence Q R n m h :=
  HomologicalComplex.HomologySequence.mapComposableArrows₅
    ((augmentedPairChainComplexShortComplexFunctor R).map f)
    (augmentedPairChainComplexShortComplex_shortExact P R)
    (augmentedPairChainComplexShortComplex_shortExact Q R)
    (n + 1) (m + 1) (by simpa using h)

@[reassoc]
lemma augmentedPairConnecting_naturality {P Q : TopPair.{w}} (f : P ⟶ Q)
    (R : C) (n m : ℕ) (h : m + 1 = n) :
    (augmentedPairChainComplexShortComplex_shortExact P R).δ
          (n + 1) (m + 1) (by simpa using h) ≫
        HomologicalComplex.homologyMap
          (Hatcher.Reduced.augmentedMap R (TopPair.Hom.snd f)) (m + 1) =
      HomologicalComplex.homologyMap (augmentedRelativeMap f R) (n + 1) ≫
        (augmentedPairChainComplexShortComplex_shortExact Q R).δ
          (n + 1) (m + 1) (by simpa using h) := by
  exact HomologicalComplex.HomologySequence.δ_naturality
    (augmentedPairChainComplexMap f R)
    (augmentedPairChainComplexShortComplex_shortExact P R)
    (augmentedPairChainComplexShortComplex_shortExact Q R)
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

/-- The connecting morphism in the reduced long exact sequence of a pair. -/
noncomputable def reducedPairConnecting
    (P : TopPair.{w}) (R : C) (n m : ℕ) (h : m + 1 = n) :
    (homologyFunctor R n).obj P ⟶
      (Hatcher.Reduced.homologyFunctor R m).obj P.snd :=
  (augmentedRelativeHomologyIso P R n).inv ≫
    (augmentedPairChainComplexShortComplex_shortExact P R).δ
      (n + 1) (m + 1) (by simpa using h)

@[simp]
lemma reducedPairSequence_map_two_three
    (P : TopPair.{w}) (R : C) (n m : ℕ) (h : m + 1 = n) :
    (reducedPairSequence P R n m h).map' 2 3 =
      reducedPairConnecting P R n m h := by
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- **Hatcher, §2.1 (pages 127–128).** The connecting morphism in the
reduced long exact sequence is natural for maps of pairs.  The construction
uses the functorial augmented chain complexes, including at degree zero, and
does not choose a point of either subspace. -/
@[reassoc]
lemma reducedPairConnecting_naturality {P Q : TopPair.{w}} (f : P ⟶ Q)
    (R : C) (n m : ℕ) (h : m + 1 = n) :
    reducedPairConnecting P R n m h ≫
        (Hatcher.Reduced.homologyFunctor R m).map (TopPair.Hom.snd f) =
      (homologyFunctor R n).map f ≫
        reducedPairConnecting Q R n m h := by
  change ((augmentedRelativeHomologyIso P R n).inv ≫
      (augmentedPairChainComplexShortComplex_shortExact P R).δ
        (n + 1) (m + 1) _) ≫
      HomologicalComplex.homologyMap
        (Hatcher.Reduced.augmentedMap R (TopPair.Hom.snd f)) (m + 1) =
    (homologyFunctor R n).map f ≫
      ((augmentedRelativeHomologyIso Q R n).inv ≫
        (augmentedPairChainComplexShortComplex_shortExact Q R).δ
          (n + 1) (m + 1) _)
  erw [Category.assoc]
  erw [augmentedPairConnecting_naturality f R n m h]
  rw [← augmentedRelativeHomologyIso_inv_naturality_assoc]

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

set_option backward.isDefEq.respectTransparency false in
/-- A map of pairs induces a morphism between six consecutive terms of their
reduced long exact sequences, by conjugating the augmented sequence map with
the canonical comparison isomorphisms. -/
noncomputable def reducedPairSequenceMap {P Q : TopPair.{w}} (f : P ⟶ Q)
    (R : C) (n m : ℕ) (h : m + 1 = n) :
    reducedPairSequence P R n m h ⟶ reducedPairSequence Q R n m h :=
  (augmentedPairSequenceIso P R n m h).inv ≫
    augmentedPairSequenceMap f R n m h ≫
    (augmentedPairSequenceIso Q R n m h).hom

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
