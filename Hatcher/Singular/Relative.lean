import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Relative
import Mathlib.AlgebraicTopology.SingularSet
import Mathlib.AlgebraicTopology.SingularHomology.Basic
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

end Hatcher.Relative
