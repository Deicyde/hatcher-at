import Hatcher.Appendix.CompactSubspaceFiniteSubcomplex
import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
import Hatcher.Appendix.SuccessorSkeletonQuotient
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Hatcher.Singular.SigmaPointedPair
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Topology.ContinuousMap.Sigma

/-!
# Relative singular chains of a topological coproduct
-/

noncomputable section

open AlgebraicTopology CategoryTheory Limits

namespace Hatcher.Relative

universe w v u d c

open scoped Simplicial

variable {ι : Type w} (X : ι → TopCat.{w}) (P : ι → TopPair.{w})

private abbrev sigmaTop : TopCat.{w} :=
  TopCat.of (Σ i, X i)



/-- Singular simplices in a topological coproduct are precisely singular
simplices in one of its summands. -/
noncomputable def singularSimplexSigmaEquiv (n : ℕ) :
    (Σ i, (TopCat.toSSet.obj (X i)).obj (.op ⦋n⦌)) ≃
      (TopCat.toSSet.obj (sigmaTop X)).obj (.op ⦋n⦌) :=
  (Equiv.sigmaCongrRight fun i ↦
      TopCat.toSSetObjEquiv (X i) (.op ⦋n⦌)).trans <|
    (ContinuousMap.sigmaCodHomeomorph
      (Convexity.StdSimplex ℝ (Fin (n + 1))) (fun i ↦ X i)).toEquiv.symm |>.trans <|
      (TopCat.toSSetObjEquiv (sigmaTop X) (.op ⦋n⦌)).symm

/-- Under the singular-simplex equivalence, a simplex in one summand is sent
to its composite with that summand's sigma inclusion. -/
@[simp]
lemma singularSimplexSigmaEquiv_mk (n : ℕ) (i : ι)
    (x : (TopCat.toSSet.obj (X i)).obj (.op ⦋n⦌)) :
    singularSimplexSigmaEquiv X n ⟨i, x⟩ =
      (TopCat.toSSet.map (TopCat.sigmaι X i)).app (.op ⦋n⦌) x := by
  change
    (TopCat.toSSetObjEquiv (sigmaTop X) (.op ⦋n⦌)).symm
        ((ContinuousMap.sigmaCodHomeomorph
          (Convexity.StdSimplex ℝ (Fin (n + 1))) (fun i ↦ X i)).symm
            ⟨i, TopCat.toSSetObjEquiv (X i) (.op ⦋n⦌) x⟩) = _
  apply (TopCat.toSSetObjEquiv (sigmaTop X) (.op ⦋n⦌)).injective
  rw [Equiv.apply_symm_apply,
    ContinuousMap.sigmaCodHomeomorph_symm_apply]
  apply ContinuousMap.ext
  intro y
  apply Sigma.ext
  · rfl
  · rfl

section Coefficients

variable {C : Type c} [Category.{d} C] [Preadditive C]
  [HasCoproducts.{w} C] (R : C)

/-- The canonical chain map from the coproduct of the singular chain complexes
of the summands to the singular chain complex of the topological coproduct. -/
noncomputable def singularChainComplexSigmaMap :
    (∐ fun i ↦ ((singularChainComplexFunctor.{w} C).obj R).obj (X i)) ⟶
      ((singularChainComplexFunctor.{w} C).obj R).obj (sigmaTop X) :=
  Sigma.desc fun i ↦
    ((singularChainComplexFunctor.{w} C).obj R).map (TopCat.sigmaι X i)

/-- Degreewise basis identification underlying
`singularChainComplexSigmaMap`. -/
noncomputable def singularChainComplexSigmaIsoX (n : ℕ) :
    ((∐ fun i ↦ ((singularChainComplexFunctor.{w} C).obj R).obj (X i)) :
        ChainComplex C ℕ).X n ≅
      (((singularChainComplexFunctor.{w} C).obj R).obj (sigmaTop X)).X n :=
  PreservesCoproduct.iso (HomologicalComplex.eval C (ComplexShape.down ℕ) n)
      (fun i ↦ ((singularChainComplexFunctor.{w} C).obj R).obj (X i)) ≪≫
    sigmaSigmaIso
      (fun i ↦ (TopCat.toSSet.obj (X i)).obj (.op ⦋n⦌))
      (fun _ _ ↦ R) ≪≫
    Sigma.whiskerEquiv (singularSimplexSigmaEquiv X n) (fun _ ↦ Iso.refl R)

/-- The degreewise basis identification has the canonical coproduct map as
its forward morphism. -/
lemma singularChainComplexSigmaIsoX_hom (n : ℕ) :
    (singularChainComplexSigmaIsoX X R n).hom =
      (singularChainComplexSigmaMap X R).f n := by
  apply (isColimitOfHasCoproductOfPreservesColimit
    (HomologicalComplex.eval C (ComplexShape.down ℕ) n)
    (fun i ↦ ((singularChainComplexFunctor.{w} C).obj R).obj (X i))).hom_ext
  intro i
  have houter :
      (Sigma.ι (fun i ↦ ((singularChainComplexFunctor.{w} C).obj R).obj (X i))
          i.as).f n ≫
          (PreservesCoproduct.iso
            (HomologicalComplex.eval C (ComplexShape.down ℕ) n)
            (fun i ↦ ((singularChainComplexFunctor.{w} C).obj R).obj (X i))).hom =
        Sigma.ι
          (fun i ↦ (((singularChainComplexFunctor.{w} C).obj R).obj (X i)).X n)
          i.as := by
    exact IsColimit.comp_coconePointUniqueUpToIso_hom
      (isColimitOfHasCoproductOfPreservesColimit
        (HomologicalComplex.eval C (ComplexShape.down ℕ) n)
        (fun i ↦ ((singularChainComplexFunctor.{w} C).obj R).obj (X i)))
      (colimit.isColimit _) i
  change
    (Sigma.ι (fun i ↦ ((singularChainComplexFunctor.{w} C).obj R).obj (X i))
        i.as).f n ≫ (singularChainComplexSigmaIsoX X R n).hom =
      (Sigma.ι (fun i ↦ ((singularChainComplexFunctor.{w} C).obj R).obj (X i))
        i.as).f n ≫ (singularChainComplexSigmaMap X R).f n
  dsimp only [singularChainComplexSigmaIsoX, Iso.trans_hom]
  rw [← Category.assoc, houter]
  apply SSet.chainComplex_hom_ext
  intro x
  have hright :
      (Sigma.ι
          (fun i ↦ ((singularChainComplexFunctor.{w} C).obj R).obj (X i))
          i.as).f n ≫ (singularChainComplexSigmaMap X R).f n =
        (((singularChainComplexFunctor.{w} C).obj R).map
          (TopCat.sigmaι X i.as)).f n := by
    rw [← HomologicalComplex.comp_f]
    simp [singularChainComplexSigmaMap]
  rw [hright]
  change _ =
    (TopCat.toSSet.obj (X i.as)).ιChainComplex x ≫
      (SSet.chainComplexMap
        (TopCat.toSSet.map (TopCat.sigmaι X i.as)) R).f n
  rw [SSet.ι_chainComplexMap_f]
  change
    Sigma.ι (fun _ : (TopCat.toSSet.obj (X i.as)).obj (.op ⦋n⦌) ↦ R) x ≫
        Sigma.ι
          (fun i ↦ ∐ fun _ : (TopCat.toSSet.obj (X i)).obj (.op ⦋n⦌) ↦ R)
          i.as ≫
          (sigmaSigmaIso
              (fun i ↦ (TopCat.toSSet.obj (X i)).obj (.op ⦋n⦌))
              (fun _ _ ↦ R) ≪≫
            Sigma.whiskerEquiv (singularSimplexSigmaEquiv X n)
              (fun _ ↦ Iso.refl R)).hom =
      Sigma.ι
        (fun _ : (TopCat.toSSet.obj (sigmaTop X)).obj (.op ⦋n⦌) ↦ R)
        ((TopCat.toSSet.map (TopCat.sigmaι X i.as)).app (.op ⦋n⦌) x)
  simp [singularSimplexSigmaEquiv_mk, SSet.ιChainComplex,
    sigmaSigmaIso, Sigma.whiskerEquiv, Category.assoc]

noncomputable instance singularChainComplexSigmaMap_isIso :
    IsIso (singularChainComplexSigmaMap X R) := by
  letI (n : ℕ) : IsIso ((singularChainComplexSigmaMap X R).f n) := by
    rw [← singularChainComplexSigmaIsoX_hom X R n]
    infer_instance
  exact HomologicalComplex.Hom.isIso_of_components _

/-- Singular chains carry a topological coproduct to the categorical
coproduct of the singular chain complexes. -/
noncomputable def singularChainComplexSigmaIso :
    (∐ fun i ↦ ((singularChainComplexFunctor.{w} C).obj R).obj (X i)) ≅
      ((singularChainComplexFunctor.{w} C).obj R).obj (sigmaTop X) :=
  asIso (singularChainComplexSigmaMap X R)

@[simp]
lemma singularChainComplexSigmaIso_hom :
    (singularChainComplexSigmaIso X R).hom =
      singularChainComplexSigmaMap X R := rfl

section CoproductCokernel

variable {A B Q : ι → C} (f : ∀ i, A i ⟶ B i)
  (p : ∀ i, B i ⟶ Q i) (hp : ∀ i, f i ≫ p i = 0)

/-- The coproduct of a family of cokernel coforks. -/
noncomputable abbrev sigmaCokernelCofork :
  CokernelCofork (Limits.Sigma.map f) :=
  CokernelCofork.ofπ (Limits.Sigma.map p) (by
    ext i
    rw [← Category.assoc, Sigma.ι_map, Category.assoc, Sigma.ι_map,
      ← Category.assoc, hp, zero_comp, comp_zero])

/-- A coproduct of cokernel coforks is again a cokernel cofork. -/
noncomputable def isColimitSigmaCokernelCofork
    (h : ∀ i, IsColimit (CokernelCofork.ofπ (p i) (hp i))) :
    IsColimit (sigmaCokernelCofork f p hp) := by
  unfold sigmaCokernelCofork
  refine CokernelCofork.IsColimit.ofπ _ _ ?_ ?_ ?_
  · intro Z g hg
    exact Sigma.desc fun i ↦
      (h i).desc (CokernelCofork.ofπ (Sigma.ι B i ≫ g) (by
        rw [← Category.assoc, ← Sigma.ι_map, Category.assoc, hg,
          comp_zero]))
  · intro Z g hg
    ext i
    simp only [sigmaCokernelCofork, CokernelCofork.π_ofπ,
      Sigma.ι_map_assoc, Sigma.ι_desc]
    exact (h i).fac _ WalkingParallelPair.one
  · intro Z g hg m hm
    apply Sigma.hom_ext
    intro i
    have hgi : f i ≫ (Sigma.ι B i ≫ g) = 0 := by
      rw [← Category.assoc, ← Sigma.ι_map, Category.assoc, hg,
        comp_zero]
    letI : Epi (p i) := Cofork.IsColimit.epi (h i)
    apply (cancel_epi (p i)).1
    simp only [Sigma.ι_desc]
    calc
      p i ≫ Sigma.ι Q i ≫ m =
          (p i ≫ Sigma.ι Q i) ≫ m :=
        (Category.assoc _ _ _).symm
      _ =
          (Sigma.ι B i ≫ Limits.Sigma.map p) ≫ m := by
            rw [Sigma.ι_map]
      _ = Sigma.ι B i ≫ g := by rw [Category.assoc, hm]
      _ = p i ≫ (h i).desc
          (CokernelCofork.ofπ (Sigma.ι B i ≫ g) hgi) :=
        by
          have hi := Cofork.IsColimit.π_desc (h i)
            (t := CokernelCofork.ofπ (Sigma.ι B i ≫ g) hgi)
          simpa only [CokernelCofork.π_ofπ] using hi.symm

end CoproductCokernel

section RelativePair

/-- The canonical map from the coproduct of the relative singular chain
complexes of arbitrary pairs to the relative chains of their sigma pair. -/
noncomputable def relativeChainComplexSigmaPairMap :
    (∐ fun i ↦ (chainComplexFunctor R).obj (P i)) ⟶
      (chainComplexFunctor R).obj (sigmaPair P) :=
  Sigma.desc fun i ↦ (chainComplexFunctor R).map (sigmaPairι P i)

private noncomputable def sigmaPairSourceMap :
    (∐ fun i ↦ (singularPairFunctor.obj (P i)).left.chainComplex R) ⟶
      (∐ fun i ↦ (singularPairFunctor.obj (P i)).right.chainComplex R) :=
  Limits.Sigma.map fun i ↦
    SSet.chainComplexMap (singularPairFunctor.obj (P i)).hom R

private noncomputable abbrev sigmaPairSummandπ (i : ι) :
    (singularPairFunctor.obj (P i)).right.chainComplex R ⟶
      (chainComplexFunctor R).obj (P i) :=
  (singularPairFunctor.obj (P i)).chainComplexπ R

private noncomputable def sigmaPairSourceπ :
    (∐ fun i ↦ (singularPairFunctor.obj (P i)).right.chainComplex R) ⟶
      (∐ fun i ↦ (chainComplexFunctor R).obj (P i)) :=
  Limits.Sigma.map fun i ↦ sigmaPairSummandπ P R i

private noncomputable abbrev sigmaPairSourceCofork :
    CokernelCofork (sigmaPairSourceMap P R) :=
  sigmaCokernelCofork
    (Q := fun i ↦ (chainComplexFunctor R).obj (P i))
    (fun i ↦ SSet.chainComplexMap (singularPairFunctor.obj (P i)).hom R)
    (fun i ↦ sigmaPairSummandπ P R i)
    (fun i ↦ (singularPairFunctor.obj (P i)).chainComplex_condition R)

private noncomputable def isColimitSigmaPairSourceCofork :
    IsColimit (sigmaPairSourceCofork P R) :=
  isColimitSigmaCokernelCofork
    (Q := fun i ↦ (chainComplexFunctor R).obj (P i))
    (f := fun i ↦
      SSet.chainComplexMap (singularPairFunctor.obj (P i)).hom R)
    (p := fun i ↦ sigmaPairSummandπ P R i)
    (hp := fun i ↦
      (singularPairFunctor.obj (P i)).chainComplex_condition R)
    (fun i ↦
      (singularPairFunctor.obj
        (P i)).isColimitCokernelCoforkChainComplex R)

private noncomputable abbrev sigmaPairTargetMap :
    (singularPairFunctor.obj (sigmaPair P)).left.chainComplex R ⟶
      (singularPairFunctor.obj (sigmaPair P)).right.chainComplex R :=
  SSet.chainComplexMap (singularPairFunctor.obj (sigmaPair P)).hom R

private noncomputable def sigmaPairLeftMap :
    (∐ fun i ↦ (singularPairFunctor.obj (P i)).left.chainComplex R) ⟶
      (singularPairFunctor.obj (sigmaPair P)).left.chainComplex R :=
  Sigma.desc fun i ↦
    SSet.chainComplexMap (singularPairFunctor.map (sigmaPairι P i)).left R

private noncomputable def sigmaPairRightMap :
    (∐ fun i ↦ (singularPairFunctor.obj (P i)).right.chainComplex R) ⟶
      (singularPairFunctor.obj (sigmaPair P)).right.chainComplex R :=
  Sigma.desc fun i ↦
    SSet.chainComplexMap (singularPairFunctor.map (sigmaPairι P i)).right R

private noncomputable instance sigmaPairLeftMap_isIso :
    IsIso (sigmaPairLeftMap P R) := by
  change IsIso (singularChainComplexSigmaMap (fun i ↦ (P i).snd) R)
  infer_instance

private noncomputable instance sigmaPairRightMap_isIso :
    IsIso (sigmaPairRightMap P R) := by
  change IsIso (singularChainComplexSigmaMap (fun i ↦ (P i).fst) R)
  infer_instance

private noncomputable def sigmaPairArrowIso :
    Arrow.mk (sigmaPairSourceMap P R) ≅ Arrow.mk (sigmaPairTargetMap P R) :=
  Arrow.isoMk'
    (sigmaPairSourceMap P R)
    (sigmaPairTargetMap P R)
    (asIso (sigmaPairLeftMap P R))
    (asIso (sigmaPairRightMap P R))
    (by
      apply Sigma.hom_ext
      intro i
      simp [sigmaPairLeftMap, sigmaPairRightMap, sigmaPairSourceMap,
        sigmaPairTargetMap, ← Functor.map_comp]
      apply ((SSet.chainComplexFunctor C).obj R).congr_map
      simpa using (singularPairFunctor.map (sigmaPairι P i)).w)

@[simp]
private lemma sigmaPairArrowIso_hom_right :
    (sigmaPairArrowIso P R).hom.right = sigmaPairRightMap P R := rfl

private lemma ι_sigmaPairRightMap_comp_π (i : ι) :
    Sigma.ι
        (fun b ↦ (singularPairFunctor.obj (P b)).right.chainComplex R) i ≫
      ((Sigma.desc fun b ↦ SSet.chainComplexMap
          (singularPairFunctor.map (sigmaPairι P b)).right R) ≫
        (chainComplexFunctorπ R).app (sigmaPair P)) =
    SSet.chainComplexMap
        (singularPairFunctor.map (sigmaPairι P i)).right R ≫
      (chainComplexFunctorπ R).app (sigmaPair P) := by
  calc
    _ = (Sigma.ι
          (fun b ↦ (singularPairFunctor.obj (P b)).right.chainComplex R) i ≫
        Sigma.desc (fun b ↦ SSet.chainComplexMap
          (singularPairFunctor.map (sigmaPairι P b)).right R)) ≫
        (chainComplexFunctorπ R).app (sigmaPair P) :=
      (Category.assoc _ _ _).symm
    _ = _ := congrArg
      (fun k ↦ k ≫ (chainComplexFunctorπ R).app (sigmaPair P))
      (Sigma.ι_comp_desc
        (fun b ↦ SSet.chainComplexMap
          (singularPairFunctor.map (sigmaPairι P b)).right R) i)

private noncomputable def sigmaPairSourcePointIso :
    (∐ fun i ↦ (chainComplexFunctor R).obj (P i)) ≅
      (sigmaPairSourceCofork P R).pt :=
  Iso.refl _

private noncomputable def sigmaPairTargetPointIso :
    ((singularPairFunctor.obj
      (sigmaPair P)).cokernelCoforkChainComplex R).pt ≅
      (chainComplexFunctor R).obj (sigmaPair P) :=
  Iso.refl _

@[simp]
private lemma sigmaPairSourcePointIso_hom :
    (sigmaPairSourcePointIso P R).hom = 𝟙 _ := rfl

@[simp]
private lemma sigmaPairTargetPointIso_hom :
    (sigmaPairTargetPointIso P R).hom = 𝟙 _ := rfl

private noncomputable def sigmaPairCokernelIso :
    (sigmaPairSourceCofork P R).pt ≅
      ((singularPairFunctor.obj
        (sigmaPair P)).cokernelCoforkChainComplex R).pt :=
  CokernelCofork.mapIsoOfIsColimit
    (isColimitSigmaPairSourceCofork P R)
    ((singularPairFunctor.obj
      (sigmaPair P)).isColimitCokernelCoforkChainComplex R)
    (sigmaPairArrowIso P R)

@[reassoc]
private lemma sigmaPairSourceπ_comp_sourcePointIso :
    Limits.Sigma.map (sigmaPairSummandπ P R) ≫
        (sigmaPairSourcePointIso P R).hom =
      Cofork.π (sigmaPairSourceCofork P R) := by
  rw [sigmaPairSourcePointIso_hom]
  rw [Category.comp_id]
  symm
  apply CokernelCofork.π_ofπ
  exact CokernelCofork.condition (sigmaPairSourceCofork P R)

@[reassoc]
private lemma sigmaPairTargetπ_comp_targetPointIso :
    (singularPairFunctor.obj (sigmaPair P)).chainComplexπ R ≫
        (sigmaPairTargetPointIso P R).hom =
      (chainComplexFunctorπ R).app (sigmaPair P) := by
  rw [sigmaPairTargetPointIso_hom]
  change (chainComplexFunctorπ R).app (sigmaPair P) ≫ 𝟙 _ = _
  rw [Category.comp_id]

@[reassoc]
private lemma sigmaPairArrowTarget_fac :
    ((sigmaPairArrowIso P R).hom.right ≫
        (singularPairFunctor.obj (sigmaPair P)).chainComplexπ R) ≫
      (sigmaPairTargetPointIso P R).hom =
    (sigmaPairArrowIso P R).hom.right ≫
      (chainComplexFunctorπ R).app (sigmaPair P) := by
  calc
    _ = (sigmaPairArrowIso P R).hom.right ≫
        ((singularPairFunctor.obj (sigmaPair P)).chainComplexπ R ≫
          (sigmaPairTargetPointIso P R).hom) :=
      Category.assoc _ _ _
    _ = _ := by rw [sigmaPairTargetπ_comp_targetPointIso]

private lemma ι_sigmaPairArrowTarget_fac (i : ι) :
    Sigma.ι
        (fun b ↦ (singularPairFunctor.obj (P b)).right.chainComplex R) i ≫
      (((sigmaPairArrowIso P R).hom.right ≫
          (singularPairFunctor.obj (sigmaPair P)).chainComplexπ R) ≫
        (sigmaPairTargetPointIso P R).hom) =
    Sigma.ι
        (fun b ↦ (singularPairFunctor.obj (P b)).right.chainComplex R) i ≫
      ((sigmaPairArrowIso P R).hom.right ≫
        (chainComplexFunctorπ R).app (sigmaPair P)) :=
  congrArg
    (fun k ↦ Sigma.ι
      (fun b ↦ (singularPairFunctor.obj (P b)).right.chainComplex R) i ≫ k)
    (sigmaPairArrowTarget_fac P R)

@[reassoc]
private lemma sigmaPairCokernelIso_fac :
    Cofork.π (sigmaPairSourceCofork P R) ≫
        (sigmaPairCokernelIso P R).hom =
      (sigmaPairArrowIso P R).hom.right ≫
        (singularPairFunctor.obj (sigmaPair P)).chainComplexπ R :=
  CokernelCofork.π_mapOfIsColimit
    (isColimitSigmaPairSourceCofork P R)
    ((singularPairFunctor.obj
      (sigmaPair P)).cokernelCoforkChainComplex R)
    (sigmaPairArrowIso P R).hom

/-- Relative singular chains carry the sigma pair of an arbitrary family of
topological pairs to the categorical coproduct of the relative chain
complexes. This includes empty indexing types. -/
noncomputable def relativeChainComplexSigmaPairIso :
    (∐ fun i ↦ (chainComplexFunctor R).obj (P i)) ≅
      (chainComplexFunctor R).obj (sigmaPair P) :=
  sigmaPairSourcePointIso P R ≪≫
    sigmaPairCokernelIso P R ≪≫
    sigmaPairTargetPointIso P R

/-- The forward map of `relativeChainComplexSigmaPairIso` is the canonical
map induced by the inclusions of the summand pairs. -/
lemma relativeChainComplexSigmaPairIso_hom :
    (relativeChainComplexSigmaPairIso P R).hom =
      relativeChainComplexSigmaPairMap P R := by
  apply Sigma.hom_ext
  intro i
  let Q := P i
  let p := sigmaPairSummandπ P R i
  let _ : Epi p :=
    Cofork.IsColimit.epi
      ((singularPairFunctor.obj Q).isColimitCokernelCoforkChainComplex R)
  apply (cancel_epi p).1
  dsimp only [p, Q]
  simp only [relativeChainComplexSigmaPairIso, Iso.trans_hom,
    relativeChainComplexSigmaPairMap]
  rw [← Category.assoc, ← Sigma.ι_map]
  rw [Category.assoc]
  rw [sigmaPairSourceπ_comp_sourcePointIso_assoc]
  rw [sigmaPairCokernelIso_fac_assoc]
  refine (ι_sigmaPairArrowTarget_fac P R i).trans ?_
  rw [sigmaPairArrowIso_hom_right]
  unfold sigmaPairRightMap
  refine (ι_sigmaPairRightMap_comp_π P R i).trans ?_
  rw [Sigma.ι_comp_desc]
  exact ((SSetPair.chainComplexFunctorπ C).app R).naturality
    (singularPairFunctor.map (sigmaPairι P i))

/-- On every coproduct summand, the generic forward isomorphism is exactly
the relative-chain map induced by the canonical sigma-pair inclusion. -/
@[reassoc (attr := simp)]
lemma ι_relativeChainComplexSigmaPairIso_hom (i : ι) :
    Sigma.ι (fun i ↦ (chainComplexFunctor R).obj (P i)) i ≫
      (relativeChainComplexSigmaPairIso P R).hom =
    (chainComplexFunctor R).map (sigmaPairι P i) := by
  rw [relativeChainComplexSigmaPairIso_hom]
  simp [relativeChainComplexSigmaPairMap]

end RelativePair

section PointedRelative

variable (x₀ : ∀ i, X i)

/-- The pointed canonical map is the specialization of the arbitrary-pair
sigma map. -/
noncomputable def relativeChainComplexSigmaMap :
    (∐ fun i ↦
      (chainComplexFunctor R).obj (pointedPair (X i) (x₀ i))) ⟶
      (chainComplexFunctor R).obj (sigmaPointedPair x₀) :=
  relativeChainComplexSigmaPairMap
    (fun i ↦ pointedPair (X i) (x₀ i)) R

/-- The pointed relative-chain sigma isomorphism is the exact specialization
of the arbitrary-pair construction. -/
noncomputable def relativeChainComplexSigmaIso :
    (∐ fun i ↦
      (chainComplexFunctor R).obj (pointedPair (X i) (x₀ i))) ≅
      (chainComplexFunctor R).obj (sigmaPointedPair x₀) :=
  relativeChainComplexSigmaPairIso
    (fun i ↦ pointedPair (X i) (x₀ i)) R

/-- The forward pointed comparison remains the canonical pointed sigma map. -/
lemma relativeChainComplexSigmaIso_hom :
    (relativeChainComplexSigmaIso X R x₀).hom =
      relativeChainComplexSigmaMap X R x₀ := by
  simpa only [relativeChainComplexSigmaIso, relativeChainComplexSigmaMap,
    sigmaPointedPair] using
    relativeChainComplexSigmaPairIso_hom
      (fun i ↦ pointedPair (X i) (x₀ i)) R

/-- On every pointed summand, the forward isomorphism is exactly the
relative-chain map induced by the canonical sigma inclusion. -/
@[reassoc (attr := simp)]
lemma ι_relativeChainComplexSigmaIso_hom (i : ι) :
    Sigma.ι
        (fun i ↦ (chainComplexFunctor R).obj
          (pointedPair (X i) (x₀ i))) i ≫
      (relativeChainComplexSigmaIso X R x₀).hom =
    (chainComplexFunctor R).map (sigmaPointedPairι x₀ i) := by
  simpa only [relativeChainComplexSigmaIso, sigmaPointedPair,
    sigmaPointedPairι] using
    ι_relativeChainComplexSigmaPairIso_hom
      (fun i ↦ pointedPair (X i) (x₀ i)) R i

end PointedRelative

end Coefficients

end Hatcher.Relative


noncomputable section

open AlgebraicTopology CategoryTheory Limits Topology
open scoped Simplicial

namespace Hatcher.ClassicalCW

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X]
  (C : Set X) [CWComplex C]

/-- The literal ordinary zero-skeleton pair, with empty predecessor. -/
noncomputable def zeroSkeletonPair : TopPair.{u} :=
  let h : (CWComplex.skeletonLT C (0 : ℕ∞) : Set X) ⊆
      (CWComplex.skeletonLT C (1 : ℕ∞) : Set X) :=
    CWComplex.skeletonLT_mono (C := C) (by norm_num)
  TopPair.of (TopCat.ofHom (ContinuousMap.inclusion h))
    (IsEmbedding.inclusion h)

private abbrev zeroSkeletonCoefficient : AddCommGrpCat.{u} :=
  AddCommGrpCat.of.{u} (ULift.{u} ℤ)

private abbrev zeroSkeletonSpace : TopCat.{u} := (zeroSkeletonPair C).fst

private instance zeroSkeletonPair_empty : IsEmpty (zeroSkeletonPair C).snd := by
  change IsEmpty ↑(CWComplex.skeletonLT C (0 : ℕ∞) : Set X)
  refine ⟨fun x => ?_⟩
  have hx : (x.1 : X) ∈ (∅ : Set X) := by
    simpa only [CWComplex.skeletonLT_zero_eq_empty] using x.2
  exact hx.elim

private instance zeroSkeletonSingularPair_left_dimension :
    (Hatcher.Relative.singularPairFunctor.obj (zeroSkeletonPair C)).left.HasDimensionLT 0 := by
  apply (SSet.notNonempty_iff_hasDimensionLT_zero
    (Hatcher.Relative.singularPairFunctor.obj (zeroSkeletonPair C)).left).mp
  rintro ⟨s⟩
  let x : (zeroSkeletonPair C).snd := TopCat.toSSetObj₀Equiv s
  exact IsEmpty.false x

/-- Ordinary-to-relative chains is the actual quotient projection for the
literal empty-subspace pair. -/
noncomputable def zeroSkeletonOrdinaryRelativeChainIso :
    ((singularChainComplexFunctor AddCommGrpCat.{u}).obj
        zeroSkeletonCoefficient.{u}).obj (zeroSkeletonSpace C) ≅
      (Hatcher.Relative.chainComplexFunctor zeroSkeletonCoefficient.{u}).obj
        (zeroSkeletonPair C) :=
  by
    let R : AddCommGrpCat.{u} := zeroSkeletonCoefficient.{u}
    let Q : SSetPair.{u} :=
      Hatcher.Relative.singularPairFunctor.obj (zeroSkeletonPair C)
    let _ : Q.left.HasDimensionLT 0 := zeroSkeletonSingularPair_left_dimension C
    let q : ((singularChainComplexFunctor AddCommGrpCat.{u}).obj R).obj
        (zeroSkeletonSpace C) ⟶
        (Hatcher.Relative.chainComplexFunctor R).obj (zeroSkeletonPair C) :=
      Q.chainComplexπ R
    let hq : IsIso q := SSetPair.isIso_chainComplexπ Q R
    exact @asIso (ChainComplex AddCommGrpCat.{u} ℕ) _ _ _ q hq

@[simp]
theorem zeroSkeletonOrdinaryRelativeChainIso_hom :
    (zeroSkeletonOrdinaryRelativeChainIso C).hom =
      (Hatcher.Relative.chainComplexFunctorπ zeroSkeletonCoefficient.{u}).app
        (zeroSkeletonPair C) := by
  rfl

/-- The induced homology comparison retains the actual chain quotient map. -/
noncomputable def zeroSkeletonOrdinaryRelativeHomologyIso (n : ℕ) :
    ((singularHomologyFunctor AddCommGrpCat.{u} n).obj
        zeroSkeletonCoefficient.{u}).obj (zeroSkeletonSpace C) ≅
      (Hatcher.Relative.homologyFunctor zeroSkeletonCoefficient.{u} n).obj
        (zeroSkeletonPair C) :=
  (HomologicalComplex.homologyFunctor AddCommGrpCat.{u}
    (ComplexShape.down ℕ) n).mapIso (zeroSkeletonOrdinaryRelativeChainIso C)

@[simp]
theorem zeroSkeletonOrdinaryRelativeHomologyIso_hom (n : ℕ) :
    (zeroSkeletonOrdinaryRelativeHomologyIso C n).hom =
      (Hatcher.Relative.singularPairFunctor.obj (zeroSkeletonPair C)).homologyπ
        zeroSkeletonCoefficient.{u} n := by
  change (HomologicalComplex.homologyFunctor AddCommGrpCat.{u}
    (ComplexShape.down ℕ) n).map (zeroSkeletonOrdinaryRelativeChainIso C).hom = _
  rw [zeroSkeletonOrdinaryRelativeChainIso_hom]
  rfl

private instance zeroSkeleton_discrete : DiscreteTopology (zeroSkeletonSpace C) :=
  (zeroSkeletonHomeomorphCells C).symm.isEmbedding.discreteTopology

private instance zeroSkeleton_totallyDisconnected :
    TotallyDisconnectedSpace (zeroSkeletonSpace C) := inferInstance

/-- The actual characteristic point of a zero-cell in the actual skeleton. -/
noncomputable def zeroCellPoint (i : RelCWComplex.cell C 0) : zeroSkeletonSpace C :=
  (zeroSkeletonHomeomorphCells C) (WithTopology.toTopology ⊥ i)

@[simp]
theorem zeroCellPoint_val (i : RelCWComplex.cell C 0) :
    (zeroCellPoint C i).1 = RelCWComplex.map 0 i 0 :=
  zeroSkeletonHomeomorphCells_apply C i

private noncomputable def zeroCellVertex (i : RelCWComplex.cell C 0) :
    (TopCat.toSSet.obj (zeroSkeletonSpace C)) _⦋0⦌ :=
  TopCat.toSSetObj₀Equiv.symm (zeroCellPoint C i)

private noncomputable def zeroCellOrdinaryClassMap (i : RelCWComplex.cell C 0) :
    zeroSkeletonCoefficient.{u} ⟶
      ((singularHomologyFunctor AddCommGrpCat.{u} 0).obj
        zeroSkeletonCoefficient.{u}).obj (zeroSkeletonSpace C) :=
  let S := TopCat.toSSet.obj (zeroSkeletonSpace C)
  (S.chainComplex zeroSkeletonCoefficient.{u}).liftCycles
      (k := S.ιChainComplex (zeroCellVertex C i)) 0 (by simp) (by simp) ≫
    (S.chainComplex zeroSkeletonCoefficient.{u}).homologyπ 0

/-- The integral relative class of the actual characteristic point. -/
noncomputable def zeroCellRelativeClass (i : RelCWComplex.cell C 0) :
    (Hatcher.Relative.homologyFunctor zeroSkeletonCoefficient.{u} 0).obj
      (zeroSkeletonPair C) :=
  (zeroCellOrdinaryClassMap C i ≫
    (zeroSkeletonOrdinaryRelativeHomologyIso C 0).hom) (ULift.up (1 : ℤ))

private theorem zeroCellOrdinaryClassMap_components
    (i : RelCWComplex.cell C 0) :
    zeroCellOrdinaryClassMap C i ≫
        ((zeroSkeletonSpace C).singularHomology₀Iso zeroSkeletonCoefficient.{u}).hom =
      Sigma.ι (fun _ : ZerothHomotopy (zeroSkeletonSpace C) => zeroSkeletonCoefficient.{u})
        (ZerothHomotopy.mk (zeroCellPoint C i)) := by
  let S := TopCat.toSSet.obj (zeroSkeletonSpace C)
  let R : AddCommGrpCat.{u} := zeroSkeletonCoefficient.{u}
  let c : R ⟶ S.homology R 0 :=
    (S.chainComplex R).liftCycles
        (k := S.ιChainComplex (zeroCellVertex C i)) 0 (by simp) (by simp) ≫
      (S.chainComplex R).homologyπ 0
  let J : (∐ fun _ : S.π₀ => R) ≅
      (∐ fun _ : ZerothHomotopy (zeroSkeletonSpace C) => R) :=
    (sigmaConst.obj R).mapIso
      (TopCat.zerothHomotopyEquiv (X := zeroSkeletonSpace C)).toIso.symm
  have hv : c ≫ (S.homology₀Iso R).hom =
      Sigma.ι (fun _ : S.π₀ => R) (SSet.π₀.mk (zeroCellVertex C i)) := by
    exact (Category.assoc _ _ _).trans
      (SSet.liftCycles_ιChainComplex_homologyπ_homology₀Iso_hom
        S R (zeroCellVertex C i))
  change c ≫ ((S.homology₀Iso R).hom ≫ J.hom) = _
  rw [← Category.assoc, hv]
  have hpoint : (TopCat.toSSetObj₀Equiv (X := zeroSkeletonSpace C))
      (zeroCellVertex C i) = zeroCellPoint C i :=
    (TopCat.toSSetObj₀Equiv (X := zeroSkeletonSpace C)).apply_symm_apply
      (zeroCellPoint C i)
  have hindex := (TopCat.zerothHomotopyEquiv_symm_mk
    (X := zeroSkeletonSpace C) (zeroCellVertex C i)).trans
      (congrArg (ZerothHomotopy.mk (X := zeroSkeletonSpace C)) hpoint)
  change Sigma.ι (fun _ : S.π₀ => R) (SSet.π₀.mk (zeroCellVertex C i)) ≫
      Sigma.map' (g := fun _ : S.π₀ => R)
        (f := fun _ : ZerothHomotopy (zeroSkeletonSpace C) => R)
        (TopCat.zerothHomotopyEquiv (X := zeroSkeletonSpace C)).symm
        (fun _ => 𝟙 R) = _
  exact (Sigma.ι_comp_map' (g := fun _ : S.π₀ => R)
    (f := fun _ : ZerothHomotopy (zeroSkeletonSpace C) => R)
    (TopCat.zerothHomotopyEquiv (X := zeroSkeletonSpace C)).symm
    (fun _ => 𝟙 R) (SSet.π₀.mk (zeroCellVertex C i))).trans
      ((Category.id_comp _).trans (congrArg
        (fun a : ZerothHomotopy (zeroSkeletonSpace C) =>
          Sigma.ι (fun _ : ZerothHomotopy (zeroSkeletonSpace C) => R) a) hindex))

private noncomputable def zeroSkeletonPointComponentEquiv :
    zeroSkeletonSpace C ≃ ZerothHomotopy (zeroSkeletonSpace C) :=
  Equiv.ofBijective ZerothHomotopy.mk
    ⟨by
      intro x y h
      have hj : Joined x y := Quotient.exact h
      have hy : y ∈ connectedComponent x := pathComponent_subset_component x hj
      have hyx : y = x := by
        simpa only [connectedComponent_eq_singleton, Set.mem_singleton_iff] using hy
      exact hyx.symm,
      ZerothHomotopy.mk_surjective⟩

private noncomputable def zeroSkeletonComponentCellEquiv :
    ZerothHomotopy (zeroSkeletonSpace C) ≃ RelCWComplex.cell C 0 :=
  (zeroSkeletonPointComponentEquiv C).symm.trans
    ((zeroSkeletonHomeomorphCells C).symm.toEquiv.trans
      (WithTopology.equiv (RelCWComplex.cell C 0) ⊥))

private theorem zeroSkeletonComponentCellEquiv_mk
    (i : RelCWComplex.cell C 0) :
    zeroSkeletonComponentCellEquiv C (ZerothHomotopy.mk (zeroCellPoint C i)) = i := by
  change ((zeroSkeletonHomeomorphCells C).symm
    ((zeroSkeletonPointComponentEquiv C).symm
      ((zeroSkeletonPointComponentEquiv C) (zeroCellPoint C i)))).ofTopology = i
  rw [Equiv.symm_apply_apply]
  change ((zeroSkeletonHomeomorphCells C).symm
    ((zeroSkeletonHomeomorphCells C) (WithTopology.toTopology ⊥ i))).ofTopology = i
  rw [Homeomorph.symm_apply_apply]

/- The standard integer-module Finsupp cofan is transported by the actual
forgetful functor preserving colimits. All indexing types may be empty. -/
private noncomputable def zeroCellIntegerCoproductIso :
    (∐ fun _ : RelCWComplex.cell C 0 => zeroSkeletonCoefficient.{u}) ≅
      AddCommGrpCat.of.{u} (RelCWComplex.cell C 0 →₀ ULift.{u} ℤ) :=
  let F := forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}
  let cofan := F.mapCocone
    (ModuleCat.finsuppCocone ℤ (ULift.{u} ℤ) (RelCWComplex.cell C 0))
  let hc : IsColimit cofan := isColimitOfPreserves F
    (ModuleCat.finsuppCoconeIsColimit ℤ (ULift.{u} ℤ) (RelCWComplex.cell C 0))
  (colimit.isColimit (Discrete.functor
    (fun _ : RelCWComplex.cell C 0 => zeroSkeletonCoefficient.{u}))).coconePointUniqueUpToIso hc

omit [T2Space X] in
private theorem zeroCellIntegerCoproductIso_single
    (i : RelCWComplex.cell C 0) (a : ULift.{u} ℤ) :
    (zeroCellIntegerCoproductIso C).hom
        (Sigma.ι (fun _ : RelCWComplex.cell C 0 => zeroSkeletonCoefficient.{u}) i a) =
      Finsupp.single i a := by
  have h := IsColimit.comp_coconePointUniqueUpToIso_hom
    (colimit.isColimit (Discrete.functor
      (fun _ : RelCWComplex.cell C 0 => zeroSkeletonCoefficient.{u})))
    (isColimitOfPreserves (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u})
      (ModuleCat.finsuppCoconeIsColimit ℤ (ULift.{u} ℤ)
        (RelCWComplex.cell C 0))) (Discrete.mk i)
  exact ConcreteCategory.congr_hom h a

private noncomputable def zeroCellLowerCoefficientEquiv :
    (RelCWComplex.cell C 0 →₀ ULift.{u} ℤ) ≃+
      (RelCWComplex.cell C 0 →₀ ℤ) where
  toFun := Finsupp.mapRange ULift.down rfl
  invFun := Finsupp.mapRange ULift.up rfl
  left_inv := by intro a; ext i; rfl
  right_inv := by intro a; ext i; rfl
  map_add' := by intro a b; ext i; rfl

private noncomputable def zeroCellIntegerFinsuppIso :
    (∐ fun _ : RelCWComplex.cell C 0 => zeroSkeletonCoefficient.{u}) ≅
      AddCommGrpCat.of.{u} (RelCWComplex.cell C 0 →₀ ℤ) :=
  zeroCellIntegerCoproductIso C ≪≫
    (zeroCellLowerCoefficientEquiv C).toAddCommGrpIso

omit [T2Space X] in
private theorem zeroCellIntegerFinsuppIso_single
    (i : RelCWComplex.cell C 0) (a : ULift.{u} ℤ) :
    (zeroCellIntegerFinsuppIso C).hom
        (Sigma.ι (fun _ : RelCWComplex.cell C 0 => zeroSkeletonCoefficient.{u}) i a) =
      Finsupp.single i a.down := by
  change zeroCellLowerCoefficientEquiv C
    ((zeroCellIntegerCoproductIso C).hom
      (Sigma.ι (fun _ : RelCWComplex.cell C 0 => zeroSkeletonCoefficient.{u}) i a)) = _
  rw [zeroCellIntegerCoproductIso_single]
  change Finsupp.mapRange ULift.down rfl (Finsupp.single i a) =
    Finsupp.single i a.down
  classical
  ext j
  by_cases h : i = j
  · subst j
    simp
  · simp [h]

/-- The actual relative H₀ isomorphism, with the canonical zero-cell basis. -/
noncomputable def zeroSkeletonRelativeHomologyIso :
    (Hatcher.Relative.homologyFunctor zeroSkeletonCoefficient.{u} 0).obj
        (zeroSkeletonPair C) ≅
      AddCommGrpCat.of.{u} (RelCWComplex.cell C 0 →₀ ℤ) :=
  (zeroSkeletonOrdinaryRelativeHomologyIso C 0).symm ≪≫
    (zeroSkeletonSpace C).singularHomology₀Iso zeroSkeletonCoefficient.{u} ≪≫
    (sigmaConst.obj zeroSkeletonCoefficient.{u}).mapIso
      (zeroSkeletonComponentCellEquiv C).toIso ≪≫
    zeroCellIntegerFinsuppIso C

private theorem zeroCell_relative_class_forward
    (i : RelCWComplex.cell C 0) :
    (zeroSkeletonRelativeHomologyIso C).hom (zeroCellRelativeClass C i) =
      Finsupp.single i 1 := by
  have hcomponent := zeroCellOrdinaryClassMap_components C i
  have hvalue := ConcreteCategory.congr_hom hcomponent (ULift.up (1 : ℤ))
  change ((zeroSkeletonSpace C).singularHomology₀Iso zeroSkeletonCoefficient.{u}).hom
      (zeroCellOrdinaryClassMap C i (ULift.up (1 : ℤ))) =
    Sigma.ι (fun _ : ZerothHomotopy (zeroSkeletonSpace C) => zeroSkeletonCoefficient.{u})
      (ZerothHomotopy.mk (zeroCellPoint C i)) (ULift.up (1 : ℤ)) at hvalue
  dsimp only [zeroSkeletonRelativeHomologyIso, Iso.trans_hom, Iso.symm_hom,
    zeroCellRelativeClass, Functor.mapIso_hom]
  change (zeroCellIntegerFinsuppIso C).hom
    (((sigmaConst.obj zeroSkeletonCoefficient.{u}).map
      (zeroSkeletonComponentCellEquiv C).toIso.hom)
      (((zeroSkeletonSpace C).singularHomology₀Iso zeroSkeletonCoefficient.{u}).hom
        ((zeroSkeletonOrdinaryRelativeHomologyIso C 0).inv
          ((zeroSkeletonOrdinaryRelativeHomologyIso C 0).hom
            (zeroCellOrdinaryClassMap C i (ULift.up (1 : ℤ))))))) = _
  rw [(zeroSkeletonOrdinaryRelativeHomologyIso C 0).hom_inv_id_apply]
  rw [hvalue]
  have hreindex := ConcreteCategory.congr_hom
    (Sigma.ι_comp_map'
      (g := fun _ : ZerothHomotopy (zeroSkeletonSpace C) => zeroSkeletonCoefficient.{u})
      (f := fun _ : RelCWComplex.cell C 0 => zeroSkeletonCoefficient.{u})
      (zeroSkeletonComponentCellEquiv C) (fun _ => 𝟙 zeroSkeletonCoefficient.{u})
      (ZerothHomotopy.mk (zeroCellPoint C i))) (ULift.up (1 : ℤ))
  change (Sigma.map'
      (g := fun _ : ZerothHomotopy (zeroSkeletonSpace C) => zeroSkeletonCoefficient.{u})
      (f := fun _ : RelCWComplex.cell C 0 => zeroSkeletonCoefficient.{u})
      (zeroSkeletonComponentCellEquiv C) (fun _ => 𝟙 zeroSkeletonCoefficient.{u}))
      (Sigma.ι (fun _ : ZerothHomotopy (zeroSkeletonSpace C) => zeroSkeletonCoefficient.{u})
        (ZerothHomotopy.mk (zeroCellPoint C i)) (ULift.up (1 : ℤ))) =
    Sigma.ι (fun _ : RelCWComplex.cell C 0 => zeroSkeletonCoefficient.{u})
      (zeroSkeletonComponentCellEquiv C (ZerothHomotopy.mk (zeroCellPoint C i)))
      (ULift.up (1 : ℤ)) at hreindex
  change (zeroCellIntegerFinsuppIso C).hom
    ((Sigma.map'
      (g := fun _ : ZerothHomotopy (zeroSkeletonSpace C) => zeroSkeletonCoefficient.{u})
      (f := fun _ : RelCWComplex.cell C 0 => zeroSkeletonCoefficient.{u})
      (zeroSkeletonComponentCellEquiv C) (fun _ => 𝟙 zeroSkeletonCoefficient.{u}))
      (Sigma.ι (fun _ : ZerothHomotopy (zeroSkeletonSpace C) => zeroSkeletonCoefficient.{u})
        (ZerothHomotopy.mk (zeroCellPoint C i)) (ULift.up (1 : ℤ)))) = _
  rw [hreindex, zeroSkeletonComponentCellEquiv_mk]
  exact zeroCellIntegerFinsuppIso_single C i (ULift.up (1 : ℤ))

/-- Each standard vector pulls back to its actual characteristic-point class. -/
theorem zeroSkeletonRelativeHomologyIso_inv_single
    (i : RelCWComplex.cell C 0) :
    (zeroSkeletonRelativeHomologyIso C).inv (Finsupp.single i 1) =
      zeroCellRelativeClass C i := by
  rw [← zeroCell_relative_class_forward C i]
  exact (zeroSkeletonRelativeHomologyIso C).hom_inv_id_apply (zeroCellRelativeClass C i)

/-- All positive ordinary relative homology groups of the zero-skeleton pair vanish. -/
theorem zeroSkeletonRelativeHomology_isZero (n : ℕ) (hn : 0 < n) :
    IsZero ((Hatcher.Relative.homologyFunctor zeroSkeletonCoefficient.{u} n).obj
      (zeroSkeletonPair C)) := by
  have h := isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
    AddCommGrpCat.{u} n zeroSkeletonCoefficient.{u} (zeroSkeletonSpace C) (Nat.ne_of_gt hn)
  exact h.of_iso (zeroSkeletonOrdinaryRelativeHomologyIso C n).symm

/-- Hatcher Lemma 2.34(a), degree-zero endpoint with the actual vertex basis.
The proof includes arbitrary and empty cell families. -/
theorem zeroSkeletonRelativeHomology :
    (∀ n : ℕ, 0 < n →
      IsZero ((Hatcher.Relative.homologyFunctor zeroSkeletonCoefficient.{u} n).obj
        (zeroSkeletonPair C))) ∧
    ∃ E : (Hatcher.Relative.homologyFunctor zeroSkeletonCoefficient.{u} 0).obj
          (zeroSkeletonPair C) ≅
        AddCommGrpCat.of.{u} (RelCWComplex.cell C 0 →₀ ℤ),
      ∀ i : RelCWComplex.cell C 0,
        E.inv (Finsupp.single i 1) = zeroCellRelativeClass C i :=
  ⟨zeroSkeletonRelativeHomology_isZero C,
    zeroSkeletonRelativeHomologyIso C, zeroSkeletonRelativeHomologyIso_inv_single C⟩

end Hatcher.ClassicalCW

noncomputable section

namespace Hatcher.ClassicalCW

open AlgebraicTopology CategoryTheory CategoryTheory.Limits _root_.Topology
open scoped Simplicial

universe u v

private abbrev boundedSingularCoefficient : AddCommGrpCat.{u} :=
  AddCommGrpCat.of.{u} (ULift.{u} ℤ)

private abbrev boundedSingularChains (Y : TopCat.{u}) :
    ChainComplex AddCommGrpCat.{u} ℕ :=
  ((singularChainComplexFunctor AddCommGrpCat.{u}).obj
    boundedSingularCoefficient.{u}).obj Y

/-- Construct finite-support coordinates from the two actual colimit cofans. -/
private noncomputable def singularChainFinsuppIso (Y : TopCat.{u}) (n : ℕ) :
    AddCommGrpCat.of.{u}
        ((TopCat.toSSet.obj Y).obj (.op ⦋n⦌) →₀ ULift.{u} ℤ) ≅
      (boundedSingularChains Y).X n :=
  let S := TopCat.toSSet.obj Y
  let F := forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}
  let cofan := F.mapCocone
    (ModuleCat.finsuppCocone ℤ (ULift.{u} ℤ) (S.obj (.op ⦋n⦌)))
  let hc : IsColimit cofan := isColimitOfPreserves F
    (ModuleCat.finsuppCoconeIsColimit ℤ (ULift.{u} ℤ) (S.obj (.op ⦋n⦌)))
  hc.coconePointUniqueUpToIso
    (S.isColimitChainComplexXCofan boundedSingularCoefficient.{u} n)

private theorem singularChainFinsuppIso_single (Y : TopCat.{u}) (n : ℕ)
    (σ : (TopCat.toSSet.obj Y).obj (.op ⦋n⦌)) (a : ULift.{u} ℤ) :
    (singularChainFinsuppIso Y n).hom (Finsupp.single σ a) =
      (TopCat.toSSet.obj Y).ιChainComplex
        (R := boundedSingularCoefficient.{u}) σ a := by
  let S := TopCat.toSSet.obj Y
  let F := forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}
  have h := IsColimit.comp_coconePointUniqueUpToIso_hom
    (isColimitOfPreserves F
      (ModuleCat.finsuppCoconeIsColimit ℤ (ULift.{u} ℤ) (S.obj (.op ⦋n⦌))))
    (S.isColimitChainComplexXCofan boundedSingularCoefficient.{u} n)
    (Discrete.mk σ)
  exact ConcreteCategory.congr_hom h a

private theorem boundedSingularChain_expansion (Y : TopCat.{u}) (n : ℕ)
    (z : (boundedSingularChains Y).X n) :
    z = ∑ σ ∈ ((singularChainFinsuppIso Y n).inv z).support,
      (TopCat.toSSet.obj Y).ιChainComplex
        (R := boundedSingularCoefficient.{u}) σ
        ((singularChainFinsuppIso Y n).inv z σ) := by
  classical
  let E := singularChainFinsuppIso Y n
  let a := E.inv z
  have ha : (∑ σ ∈ a.support, Finsupp.single σ (a σ)) = a := by
    simpa only [Finsupp.sum] using Finsupp.sum_single a
  have hz : E.hom a = z := ConcreteCategory.congr_hom E.inv_hom_id z
  calc
    z = E.hom a := hz.symm
    _ = E.hom (∑ σ ∈ a.support, Finsupp.single σ (a σ)) :=
      congrArg E.hom ha.symm
    _ = ∑ σ ∈ a.support, E.hom (Finsupp.single σ (a σ)) :=
      map_sum E.hom.hom (fun σ ↦ Finsupp.single σ (a σ)) a.support
    _ = ∑ σ ∈ a.support,
        (TopCat.toSSet.obj Y).ιChainComplex
          (R := boundedSingularCoefficient.{u}) σ (a σ) := by
      apply Finset.sum_congr rfl
      intro σ hσ
      exact singularChainFinsuppIso_single Y n σ (a σ)

variable {X : Type u} [TopologicalSpace X] [T2Space X]
  (C : Set X) [CWComplex C]

private abbrev boundedCWTop : TopCat.{u} := TopCat.of ↑C

private abbrev boundedSkeletonTop (N : ℕ) : TopCat.{u} :=
  TopCat.of ↑(CWComplex.skeleton C (N : ℕ∞) : Set X)

/-- The literal inclusion of a finite-dimensional stage into the whole CW complex. -/
noncomputable def singularSkeletonInclusion (N : ℕ) :
    TopCat.of ↑(CWComplex.skeleton C (N : ℕ∞) : Set X) ⟶ TopCat.of ↑C :=
  TopCat.ofHom
    (ContinuousMap.inclusion (CWComplex.skeleton C (N : ℕ∞)).subset_complex)

/-- The actual ordinary integral singular-chain map of the skeleton inclusion. -/
noncomputable def singularSkeletonChainMap (N : ℕ) :
    boundedSingularChains (boundedSkeletonTop C N) ⟶
      boundedSingularChains (boundedCWTop C) :=
  ((singularChainComplexFunctor AddCommGrpCat.{u}).obj
    boundedSingularCoefficient.{u}).map (singularSkeletonInclusion C N)

/-- The actual inclusion map is injective in every singular degree. -/
theorem singularSkeletonChainMap_injective (N k : ℕ) :
    Function.Injective ((singularSkeletonChainMap C N).f k) := by
  have hi : Function.Injective (singularSkeletonInclusion C N) := by
    intro a b h
    apply Subtype.ext
    exact congrArg (fun x : ↑C ↦ x.val) h
  letI : Mono (singularSkeletonInclusion C N) :=
    (TopCat.mono_iff_injective _).mpr hi
  letI : Mono (singularSkeletonChainMap C N) := by
    change Mono (((singularChainComplexFunctor AddCommGrpCat.{u}).obj
      boundedSingularCoefficient.{u}).map (singularSkeletonInclusion C N))
    infer_instance
  have hm : Mono ((singularSkeletonChainMap C N).f k) := inferInstance
  exact (AddCommGrpCat.mono_iff_injective _).mp hm

/-- Every differential equation after inclusion already holds in the skeleton. -/
theorem singularSkeletonChainMap_boundary_iff (N k l : ℕ)
    (w : (boundedSingularChains (boundedSkeletonTop C N)).X k)
    (z : (boundedSingularChains (boundedSkeletonTop C N)).X l) :
    (boundedSingularChains (boundedCWTop C)).d k l
        ((singularSkeletonChainMap C N).f k w) =
      (singularSkeletonChainMap C N).f l z ↔
    (boundedSingularChains (boundedSkeletonTop C N)).d k l w = z := by
  have h := ConcreteCategory.congr_hom ((singularSkeletonChainMap C N).comm k l) w
  change (boundedSingularChains (boundedCWTop C)).d k l
      ((singularSkeletonChainMap C N).f k w) =
    (singularSkeletonChainMap C N).f l
      ((boundedSingularChains (boundedSkeletonTop C N)).d k l w) at h
  rw [h]
  constructor
  · intro h
    exact singularSkeletonChainMap_injective C N l h
  · intro h
    exact congrArg ((singularSkeletonChainMap C N).f l) h

/-- Cycle reflection uses the ordinary, unaugmented singular differential. -/
theorem singularSkeletonChainMap_cycle_iff (N k l : ℕ)
    (w : (boundedSingularChains (boundedSkeletonTop C N)).X k) :
    (boundedSingularChains (boundedCWTop C)).d k l
        ((singularSkeletonChainMap C N).f k w) = 0 ↔
      (boundedSingularChains (boundedSkeletonTop C N)).d k l w = 0 := by
  simpa only [map_zero] using
    singularSkeletonChainMap_boundary_iff C N k l w 0

private theorem singularSkeletonSimplexEquiv_map (N n : ℕ)
    (σ : (TopCat.toSSet.obj (boundedSkeletonTop C N)).obj (.op ⦋n⦌)) :
    TopCat.toSSetObjEquiv (boundedCWTop C) (.op ⦋n⦌)
        ((TopCat.toSSet.map (singularSkeletonInclusion C N)).app (.op ⦋n⦌) σ) =
      (singularSkeletonInclusion C N).hom.comp
        (TopCat.toSSetObjEquiv (boundedSkeletonTop C N) (.op ⦋n⦌) σ) := by
  apply ContinuousMap.ext
  intro t
  rfl

/-- Restrict the original simplex itself once its image bound is proved internally. -/
private noncomputable def singularSimplexRestricted (N n : ℕ)
    (σ : (TopCat.toSSet.obj (boundedCWTop C)).obj (.op ⦋n⦌))
    (hσ : ∀ t : Convexity.StdSimplex ℝ (Fin (n + 1)),
      (TopCat.toSSetObjEquiv (boundedCWTop C) (.op ⦋n⦌) σ t).val ∈
        (CWComplex.skeleton C (N : ℕ∞) : Set X)) :
    (TopCat.toSSet.obj (boundedSkeletonTop C N)).obj (.op ⦋n⦌) :=
  (TopCat.toSSetObjEquiv (boundedSkeletonTop C N) (.op ⦋n⦌)).symm
    { toFun := fun t ↦
        ⟨(TopCat.toSSetObjEquiv (boundedCWTop C) (.op ⦋n⦌) σ t).val, hσ t⟩
      continuous_toFun :=
        (continuous_subtype_val.comp
          (TopCat.toSSetObjEquiv (boundedCWTop C) (.op ⦋n⦌) σ).continuous).subtype_mk _ }

private theorem singularSimplexRestricted_map (N n : ℕ)
    (σ : (TopCat.toSSet.obj (boundedCWTop C)).obj (.op ⦋n⦌))
    (hσ : ∀ t : Convexity.StdSimplex ℝ (Fin (n + 1)),
      (TopCat.toSSetObjEquiv (boundedCWTop C) (.op ⦋n⦌) σ t).val ∈
        (CWComplex.skeleton C (N : ℕ∞) : Set X)) :
    (TopCat.toSSet.map (singularSkeletonInclusion C N)).app (.op ⦋n⦌)
        (singularSimplexRestricted C N n σ hσ) = σ := by
  apply (TopCat.toSSetObjEquiv (boundedCWTop C) (.op ⦋n⦌)).injective
  rw [singularSkeletonSimplexEquiv_map, singularSimplexRestricted,
    Equiv.apply_symm_apply]
  apply ContinuousMap.ext
  intro t
  apply Subtype.ext
  rfl

private theorem singularSkeletonChainMap_generator (N n : ℕ)
    (σ : (TopCat.toSSet.obj (boundedSkeletonTop C N)).obj (.op ⦋n⦌))
    (a : ULift.{u} ℤ) :
    (singularSkeletonChainMap C N).f n
        ((TopCat.toSSet.obj (boundedSkeletonTop C N)).ιChainComplex
          (R := boundedSingularCoefficient.{u}) σ a) =
      (TopCat.toSSet.obj (boundedCWTop C)).ιChainComplex
        (R := boundedSingularCoefficient.{u})
        ((TopCat.toSSet.map (singularSkeletonInclusion C N)).app (.op ⦋n⦌) σ) a := by
  have h := SSet.ι_chainComplexMap_f
    (X := TopCat.toSSet.obj (boundedSkeletonTop C N))
    (Y := TopCat.toSSet.obj (boundedCWTop C))
    (f := TopCat.toSSet.map (singularSkeletonInclusion C N))
    (R := boundedSingularCoefficient.{u}) σ
  exact ConcreteCategory.congr_hom h a

private theorem singularFamily_exists_boundedSkeletonLift
    {ι : Type v} [Finite ι] (degree : ι → ℕ)
    (z : ∀ i, (boundedSingularChains (boundedCWTop C)).X (degree i))
    (L : ℕ) :
    ∃ N : ℕ, L ≤ N ∧ (IsEmpty ι → N = L) ∧
      ∃ lift : ∀ i, (boundedSingularChains (boundedSkeletonTop C N)).X (degree i),
        ∀ i, (singularSkeletonChainMap C N).f (degree i) (lift i) = z i := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  rcases isEmpty_or_nonempty ι with hι | hι
  · letI : IsEmpty ι := hι
    refine ⟨L, le_rfl, (fun _ ↦ rfl), (fun i ↦ False.elim (IsEmpty.false i)), ?_⟩
    intro i
    exact (IsEmpty.false i).elim
  · let a : ∀ i,
        (TopCat.toSSet.obj (boundedCWTop C)).obj (.op ⦋degree i⦌) →₀ ULift.{u} ℤ :=
      fun i ↦ (singularChainFinsuppIso (boundedCWTop C) (degree i)).inv (z i)
    let E : Type (max u v) := Σ i : ι,
      {σ : (TopCat.toSSet.obj (boundedCWTop C)).obj (.op ⦋degree i⦌) //
        σ ∈ (a i).support}
    letI : Finite E := inferInstance
    let T : Set X := ⋃ e : E, Set.range
      (fun t : Convexity.StdSimplex ℝ (Fin (degree e.1 + 1)) ↦
        (TopCat.toSSetObjEquiv (boundedCWTop C) (.op ⦋degree e.1⦌) e.2.val t).val)
    have hcompact : IsCompact T := by
      apply isCompact_iUnion
      intro e
      exact isCompact_range (continuous_subtype_val.comp
        (TopCat.toSSetObjEquiv (boundedCWTop C) (.op ⦋degree e.1⦌) e.2.val).continuous)
    have hTC : T ⊆ C := by
      intro x hx
      obtain ⟨e, he⟩ := Set.mem_iUnion.mp hx
      obtain ⟨t, rfl⟩ := he
      exact (TopCat.toSSetObjEquiv (boundedCWTop C) (.op ⦋degree e.1⦌) e.2.val t).property
    obtain ⟨m, hm⟩ := Hatcher.compact_subset_skeleton (C := C) hcompact hTC
    let N := max m L
    have hTN : T ⊆ (CWComplex.skeleton C (N : ℕ∞) : Set X) :=
      hm.trans (CWComplex.skeleton_mono (C := C)
        (Nat.cast_le.mpr (Nat.le_max_left m L)))
    have hσ : ∀ (i : ι)
        (σ : (TopCat.toSSet.obj (boundedCWTop C)).obj (.op ⦋degree i⦌)),
        σ ∈ (a i).support →
        ∀ t : Convexity.StdSimplex ℝ (Fin (degree i + 1)),
          (TopCat.toSSetObjEquiv (boundedCWTop C) (.op ⦋degree i⦌) σ t).val ∈
            (CWComplex.skeleton C (N : ℕ∞) : Set X) := by
      intro i σ h t
      exact hTN (Set.mem_iUnion_of_mem (⟨i, ⟨σ, h⟩⟩ : E) ⟨t, rfl⟩)
    let lift : ∀ i, (boundedSingularChains (boundedSkeletonTop C N)).X (degree i) :=
      fun i ↦ ∑ σ ∈ (a i).support.attach,
        (TopCat.toSSet.obj (boundedSkeletonTop C N)).ιChainComplex
          (R := boundedSingularCoefficient.{u})
          (singularSimplexRestricted C N (degree i) σ.val (hσ i σ.val σ.property))
          (a i σ.val)
    have hEmpty : IsEmpty ι → N = L := by
      intro h
      letI : IsEmpty ι := h
      obtain ⟨i⟩ := hι
      exact (IsEmpty.false i).elim
    refine ⟨N, Nat.le_max_right m L, hEmpty, lift, ?_⟩
    intro i
    change (singularSkeletonChainMap C N).f (degree i)
        (∑ σ ∈ (a i).support.attach,
          (TopCat.toSSet.obj (boundedSkeletonTop C N)).ιChainComplex
            (R := boundedSingularCoefficient.{u})
            (singularSimplexRestricted C N (degree i) σ.val (hσ i σ.val σ.property))
            (a i σ.val)) = z i
    calc
      (singularSkeletonChainMap C N).f (degree i)
          (∑ σ ∈ (a i).support.attach,
            (TopCat.toSSet.obj (boundedSkeletonTop C N)).ιChainComplex
              (R := boundedSingularCoefficient.{u})
              (singularSimplexRestricted C N (degree i) σ.val (hσ i σ.val σ.property))
              (a i σ.val)) =
        ∑ σ ∈ (a i).support.attach,
          (singularSkeletonChainMap C N).f (degree i)
            ((TopCat.toSSet.obj (boundedSkeletonTop C N)).ιChainComplex
              (R := boundedSingularCoefficient.{u})
              (singularSimplexRestricted C N (degree i) σ.val (hσ i σ.val σ.property))
              (a i σ.val)) :=
        map_sum ((singularSkeletonChainMap C N).f (degree i)).hom
          (fun σ ↦
            (TopCat.toSSet.obj (boundedSkeletonTop C N)).ιChainComplex
              (R := boundedSingularCoefficient.{u})
              (singularSimplexRestricted C N (degree i) σ.val (hσ i σ.val σ.property))
              (a i σ.val))
          (a i).support.attach
      _ = ∑ σ ∈ (a i).support.attach,
          (TopCat.toSSet.obj (boundedCWTop C)).ιChainComplex
            (R := boundedSingularCoefficient.{u}) σ.val (a i σ.val) := by
        apply Finset.sum_congr rfl
        intro σ h
        rw [singularSkeletonChainMap_generator, singularSimplexRestricted_map]
      _ = ∑ σ ∈ (a i).support,
          (TopCat.toSSet.obj (boundedCWTop C)).ιChainComplex
            (R := boundedSingularCoefficient.{u}) σ (a i σ) :=
        Finset.sum_attach _ _
      _ = z i := (boundedSingularChain_expansion (boundedCWTop C) (degree i) (z i)).symm

/-- A finite family of actual chains, even in different degrees, lifts to one
actual skeleton. The same inclusion reflects all cycle and boundary equations.
The empty-family proof uses the prescribed bound itself. -/
theorem singularChain_exists_boundedSkeletonLift
    {ι : Type v} [Finite ι] (degree : ι → ℕ)
    (z : ∀ i, (boundedSingularChains (boundedCWTop C)).X (degree i))
    (L : ℕ) :
    ∃ N : ℕ, L ≤ N ∧ (IsEmpty ι → N = L) ∧
      (∀ k : ℕ, Function.Injective ((singularSkeletonChainMap C N).f k)) ∧
      (∀ (k l : ℕ)
        (w : (boundedSingularChains (boundedSkeletonTop C N)).X k)
        (v : (boundedSingularChains (boundedSkeletonTop C N)).X l),
        (boundedSingularChains (boundedCWTop C)).d k l
            ((singularSkeletonChainMap C N).f k w) =
          (singularSkeletonChainMap C N).f l v ↔
        (boundedSingularChains (boundedSkeletonTop C N)).d k l w = v) ∧
      (∀ (k l : ℕ) (w : (boundedSingularChains (boundedSkeletonTop C N)).X k),
        (boundedSingularChains (boundedCWTop C)).d k l
            ((singularSkeletonChainMap C N).f k w) = 0 ↔
          (boundedSingularChains (boundedSkeletonTop C N)).d k l w = 0) ∧
      ∃ lift : ∀ i, (boundedSingularChains (boundedSkeletonTop C N)).X (degree i),
        ∀ i, (singularSkeletonChainMap C N).f (degree i) (lift i) = z i := by
  obtain ⟨N, hNL, hEmpty, lift, hlift⟩ :=
    singularFamily_exists_boundedSkeletonLift C degree z L
  exact ⟨N, hNL, hEmpty, singularSkeletonChainMap_injective C N,
    singularSkeletonChainMap_boundary_iff C N,
    singularSkeletonChainMap_cycle_iff C N, lift, hlift⟩

end Hatcher.ClassicalCW
