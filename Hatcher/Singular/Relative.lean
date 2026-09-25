import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Relative
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.AlgebraicTopology.SingularSet
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
import Mathlib.Topology.Category.TopPair

/-!
# Relative singular homology

This file lifts the singular-set functor from topological spaces to
topological pairs, then composes it with Mathlib's relative simplicial chain
complex and homology functors. An embedding of spaces induces a monomorphism
of singular simplicial sets, so the intermediate object is naturally a
simplicial-set pair.
-/

noncomputable section

open AlgebraicTopology CategoryTheory Limits

namespace Hatcher.Relative

universe w v u

/-- The singular simplicial-set pair associated to a topological pair. -/
noncomputable def singularPairFunctor : TopPair.{w} ⥤ SSetPair.{w} where
  obj P := by
    letI : Mono P.map :=
      (TopCat.mono_iff_injective P.map).2 P.isEmbedding_map.injective
    exact SSetPair.of (TopCat.toSSet.map P.map)
  map {P Q} f :=
    SSetPair.homMk
      (TopCat.toSSet.map (TopPair.Hom.snd f))
      (TopCat.toSSet.map (TopPair.Hom.fst f))
      (by
        change TopCat.toSSet.map (TopPair.Hom.snd f) ≫ TopCat.toSSet.map Q.map =
          TopCat.toSSet.map P.map ≫ TopCat.toSSet.map (TopPair.Hom.fst f)
        rw [← TopCat.toSSet.map_comp, TopPair.Hom.w, TopCat.toSSet.map_comp])
  map_id P := by
    apply MorphismProperty.Arrow.Hom.ext
    · change TopCat.toSSet.map (𝟙 P.snd) = 𝟙 _
      exact TopCat.toSSet.map_id _
    · change TopCat.toSSet.map (𝟙 P.fst) = 𝟙 _
      exact TopCat.toSSet.map_id _
  map_comp f g := by
    apply MorphismProperty.Arrow.Hom.ext
    · change TopCat.toSSet.map
        (TopPair.Hom.snd f ≫ TopPair.Hom.snd g) = _
      exact TopCat.toSSet.map_comp _ _
    · change TopCat.toSSet.map
        (TopPair.Hom.fst f ≫ TopPair.Hom.fst g) = _
      exact TopCat.toSSet.map_comp _ _

section Homology

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]

/-- The relative singular chain complex, functorial in topological pairs. -/
noncomputable def chainComplexFunctor (R : C) :
    TopPair.{w} ⥤ ChainComplex C ℕ :=
  singularPairFunctor ⋙ (SSetPair.chainComplexFunctor C).obj R

/-- The natural quotient from ambient singular chains to relative singular
chains. -/
noncomputable def chainComplexFunctorπ (R : C) :
    TopPair.proj₁ ⋙ (singularChainComplexFunctor C).obj R ⟶
      chainComplexFunctor R :=
  Functor.whiskerLeft singularPairFunctor
    ((SSetPair.chainComplexFunctorπ C).app R)

instance (R : C) (P : TopPair.{w}) : Epi ((chainComplexFunctorπ R).app P) := by
  change Epi ((singularPairFunctor.obj P).chainComplexπ R)
  infer_instance

instance (R : C) : Epi (chainComplexFunctorπ R) :=
  NatTrans.epi_of_epi_app _

@[reassoc (attr := simp)]
lemma chainComplexFunctor_condition (R : C) (P : TopPair.{w}) :
    ((singularChainComplexFunctor C).obj R).map P.map ≫
      (chainComplexFunctorπ R).app P = 0 := by
  exact (singularPairFunctor.obj P).chainComplex_condition R

@[reassoc (attr := simp)]
lemma chainComplexFunctor_condition_f (R : C) (P : TopPair.{w}) (n : ℕ) :
    (((singularChainComplexFunctor C).obj R).map P.map).f n ≫
      ((chainComplexFunctorπ R).app P).f n = 0 := by
  exact (singularPairFunctor.obj P).chainComplex_condition_f R n

instance (R : C) (P : TopPair.{w}) (n : ℕ) :
    Epi (((chainComplexFunctorπ R).app P).f n) := by
  change Epi (((singularPairFunctor.obj P).chainComplexπ R).f n)
  infer_instance

/-- The cokernel cofork expressing relative singular chains as the quotient of
ambient singular chains by subspace singular chains. -/
noncomputable def cokernelCoforkChainComplex (R : C) (P : TopPair.{w}) :
    CokernelCofork (((singularChainComplexFunctor C).obj R).map P.map) :=
  CokernelCofork.ofπ _ (chainComplexFunctor_condition R P)

/-- The relative singular chain complex has the universal property of the
quotient of ambient singular chains by subspace singular chains. -/
noncomputable def isColimitCokernelCoforkChainComplex
    (R : C) (P : TopPair.{w}) :
    IsColimit (cokernelCoforkChainComplex R P) := by
  exact (singularPairFunctor.obj P).isColimitCokernelCoforkChainComplex R

/-- The degree-`n` cokernel cofork for relative singular chains. -/
noncomputable def cokernelCoforkChainComplexX
    (R : C) (P : TopPair.{w}) (n : ℕ) :
    CokernelCofork ((((singularChainComplexFunctor C).obj R).map P.map).f n) :=
  CokernelCofork.ofπ _ (chainComplexFunctor_condition_f R P n)

/-- The degree-`n` relative singular chains have the expected cokernel
universal property. -/
noncomputable def isColimitCokernelCoforkChainComplexX
    (R : C) (P : TopPair.{w}) (n : ℕ) :
    IsColimit (cokernelCoforkChainComplexX R P n) := by
  exact (singularPairFunctor.obj P).isColimitCokernelCoforkChainComplexX R n

variable [CategoryWithHomology C]

/-- **Hatcher, §2.1 (pages 115–118).** Relative singular homology with
coefficients in `R`, functorial in topological pairs. -/
noncomputable def homologyFunctor (R : C) (n : ℕ) : TopPair.{w} ⥤ C :=
  singularPairFunctor ⋙ SSetPair.homologyFunctor R n

end Homology

section ExactSequence

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C]

/-- The short complex of subspace, ambient, and relative chains, before
specializing to a topological pair. -/
private noncomputable abbrev sSetPairChainComplexShortComplex (R : C) :
    ShortComplex (SSetPair.{w} ⥤ ChainComplex C ℕ) :=
  ShortComplex.mk
    ((SSetPair.chainComplexFunctorLeftToRight C).app R)
    ((SSetPair.chainComplexFunctorπ C).app R)
    (NatTrans.congr_app (SSetPair.chainComplexFunctor_condition C) R)

/-- The short complex of subspace, ambient, and relative singular chains,
functorial in the topological pair. -/
noncomputable def pairChainComplexShortComplexFunctor (R : C) :
    TopPair.{w} ⥤ ShortComplex (ChainComplex C ℕ) :=
  singularPairFunctor ⋙
    (ShortComplex.functorEquivalence SSetPair.{w} (ChainComplex C ℕ)).functor.obj
      (sSetPairChainComplexShortComplex R)

/-- The connecting morphism from relative singular homology in degree `n` to
the singular homology of the subspace in the adjacent degree `m`. -/
noncomputable def pairConnecting
    (P : TopPair.{w}) (R : C) (n m : ℕ) (h : m + 1 = n) :
    (homologyFunctor R n).obj P ⟶
      ((singularHomologyFunctor C m).obj R).obj P.snd :=
  (singularPairFunctor.obj P).homologyδ R n m h

/-- Six consecutive terms in the long exact singular-homology sequence of a
topological pair. -/
noncomputable def pairSequence
    (P : TopPair.{w}) (R : C) (n m : ℕ) (h : m + 1 = n) :
    ComposableArrows C 5 :=
  HomologicalComplex.HomologySequence.composableArrows₅
    ((singularPairFunctor.obj P).shortExact_chainComplexShortComplex R)
    n m (by simpa)

/-- A map of topological pairs induces a morphism between six consecutive
terms of their long exact singular-homology sequences. -/
noncomputable def pairSequenceMap {P Q : TopPair.{w}} (f : P ⟶ Q)
    (R : C) (n m : ℕ) (h : m + 1 = n) :
    pairSequence P R n m h ⟶ pairSequence Q R n m h :=
  HomologicalComplex.HomologySequence.mapComposableArrows₅
    ((pairChainComplexShortComplexFunctor R).map f)
    ((singularPairFunctor.obj P).shortExact_chainComplexShortComplex R)
    ((singularPairFunctor.obj Q).shortExact_chainComplexShortComplex R)
    n m (by simpa)

/-- **Hatcher, Theorem 2.16 (page 117).** The singular-homology sequence of a
topological pair is exact at every position across adjacent degrees. -/
theorem pairSequence_exact
    (P : TopPair.{w}) (R : C) (n m : ℕ) (h : m + 1 = n) :
    (pairSequence P R n m h).Exact := by
  exact HomologicalComplex.HomologySequence.composableArrows₅_exact
    ((singularPairFunctor.obj P).shortExact_chainComplexShortComplex R)
    n m (by simpa)

/-- The connecting morphism sends a relative cycle to the homology class of
its boundary in the subspace.  Specializing to `AddCommGrpCat` and generalized
elements from `ℤ` gives Hatcher's formula `δ[α] = [∂α]`. -/
theorem pairConnecting_eq
    (P : TopPair.{w}) (R : C) (n m : ℕ) (h : m + 1 = n)
    {T : C}
    (x₃ : T ⟶ ((singularPairFunctor.obj P).chainComplex R).X n)
    (hx₃ : x₃ ≫ ((singularPairFunctor.obj P).chainComplex R).d n m = 0)
    (x₂ : T ⟶ ((singularPairFunctor.obj P).right.chainComplex R).X n)
    (hx₂ : x₂ ≫ ((singularPairFunctor.obj P).chainComplexπ R).f n = x₃)
    (x₁ : T ⟶ ((singularPairFunctor.obj P).left.chainComplex R).X m)
    (hx₁ : x₁ ≫ (SSet.chainComplexMap (singularPairFunctor.obj P).hom R).f m =
      x₂ ≫ ((singularPairFunctor.obj P).right.chainComplex R).d n m)
    (k : ℕ) (hk : (ComplexShape.down ℕ).next m = k)
    (hx₁cycle : x₁ ≫ ((singularPairFunctor.obj P).left.chainComplex R).d m k = 0) :
    ((singularPairFunctor.obj P).chainComplex R).liftCycles x₃ m
        ((ComplexShape.down ℕ).next_eq' (by simpa using h)) hx₃ ≫
      ((singularPairFunctor.obj P).chainComplex R).homologyπ n ≫
      pairConnecting P R n m h =
    ((singularPairFunctor.obj P).left.chainComplex R).liftCycles x₁ k hk hx₁cycle ≫
      ((singularPairFunctor.obj P).left.chainComplex R).homologyπ m := by
  let hP := (singularPairFunctor.obj P).shortExact_chainComplexShortComplex R
  change _ ≫ _ ≫ hP.δ n m _ = _
  exact hP.δ_eq n m (by simpa using h) x₃ hx₃ x₂ hx₂ x₁ hx₁ k hk

set_option backward.isDefEq.respectTransparency false in
/-- **Hatcher, §2.1 (page 127).** The connecting morphism in the long exact
sequence of a pair is natural with respect to maps of topological pairs. -/
@[reassoc]
lemma pairConnecting_naturality {P Q : TopPair.{w}} (f : P ⟶ Q)
    (R : C) (n m : ℕ) (h : m + 1 = n) :
    pairConnecting P R n m h ≫
        ((singularHomologyFunctor C m).obj R).map (TopPair.Hom.snd f) =
      (homologyFunctor R n).map f ≫ pairConnecting Q R n m h := by
  exact HomologicalComplex.HomologySequence.δ_naturality
    ((pairChainComplexShortComplexFunctor R).map f)
    ((singularPairFunctor.obj P).shortExact_chainComplexShortComplex R)
    ((singularPairFunctor.obj Q).shortExact_chainComplexShortComplex R)
    n m (by simpa)

end ExactSequence

end Hatcher.Relative
