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
  AddCommGrpCat.of (ULift.{u} ℤ)

private abbrev zeroSkeletonSpace : TopCat.{u} := (zeroSkeletonPair C).fst

private instance zeroSkeletonPair_empty : IsEmpty (zeroSkeletonPair C).snd := by
  change IsEmpty ↑(CWComplex.skeletonLT C (0 : ℕ∞) : Set X)
  refine ⟨fun x => ?_⟩
  have hx : (x.1 : X) ∈ (∅ : Set X) := by
    simpa only [CWComplex.skeletonLT_zero_eq_empty] using x.2
  exact hx.elim

private instance zeroSkeletonSingularPair_left_dimension :
    (Hatcher.Relative.singularPairFunctor.obj (zeroSkeletonPair C)).left.HasDimensionLT 0 := by
  apply SSet.notNonempty_iff_hasDimensionLT_zero.mp
  rintro ⟨s⟩
  let x : (zeroSkeletonPair C).snd := TopCat.toSSetObj₀Equiv s
  exact IsEmpty.false x

/-- Ordinary-to-relative chains is the actual quotient projection for the
literal empty-subspace pair. -/
noncomputable def zeroSkeletonOrdinaryRelativeChainIso :
    ((singularChainComplexFunctor AddCommGrpCat.{u}).obj
        zeroSkeletonCoefficient).obj (zeroSkeletonSpace C) ≅
      (Hatcher.Relative.chainComplexFunctor zeroSkeletonCoefficient).obj
        (zeroSkeletonPair C) :=
  asIso ((Hatcher.Relative.singularPairFunctor.obj
    (zeroSkeletonPair C)).chainComplexπ zeroSkeletonCoefficient)

@[simp]
theorem zeroSkeletonOrdinaryRelativeChainIso_hom :
    (zeroSkeletonOrdinaryRelativeChainIso C).hom =
      (Hatcher.Relative.chainComplexFunctorπ zeroSkeletonCoefficient).app
        (zeroSkeletonPair C) := rfl

/-- The induced homology comparison retains the actual chain quotient map. -/
noncomputable def zeroSkeletonOrdinaryRelativeHomologyIso (n : ℕ) :
    ((singularHomologyFunctor AddCommGrpCat.{u} n).obj
        zeroSkeletonCoefficient).obj (zeroSkeletonSpace C) ≅
      (Hatcher.Relative.homologyFunctor zeroSkeletonCoefficient n).obj
        (zeroSkeletonPair C) :=
  (HomologicalComplex.homologyFunctor AddCommGrpCat.{u}
    (ComplexShape.down ℕ) n).mapIso (zeroSkeletonOrdinaryRelativeChainIso C)

@[simp]
theorem zeroSkeletonOrdinaryRelativeHomologyIso_hom (n : ℕ) :
    (zeroSkeletonOrdinaryRelativeHomologyIso C n).hom =
      (Hatcher.Relative.singularPairFunctor.obj (zeroSkeletonPair C)).homologyπ
        zeroSkeletonCoefficient n := rfl

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
    zeroSkeletonCoefficient ⟶
      ((singularHomologyFunctor AddCommGrpCat.{u} 0).obj
        zeroSkeletonCoefficient).obj (zeroSkeletonSpace C) :=
  let S := TopCat.toSSet.obj (zeroSkeletonSpace C)
  (S.chainComplex zeroSkeletonCoefficient).liftCycles
      (k := S.ιChainComplex (zeroCellVertex C i)) 0 (by simp) (by simp) ≫
    (S.chainComplex zeroSkeletonCoefficient).homologyπ 0

/-- The integral relative class of the actual characteristic point. -/
noncomputable def zeroCellRelativeClass (i : RelCWComplex.cell C 0) :
    (Hatcher.Relative.homologyFunctor zeroSkeletonCoefficient 0).obj
      (zeroSkeletonPair C) :=
  (zeroCellOrdinaryClassMap C i ≫
    (zeroSkeletonOrdinaryRelativeHomologyIso C 0).hom) (ULift.up (1 : ℤ))

private theorem zeroCellOrdinaryClassMap_components
    (i : RelCWComplex.cell C 0) :
    zeroCellOrdinaryClassMap C i ≫
        ((zeroSkeletonSpace C).singularHomology₀Iso zeroSkeletonCoefficient).hom =
      Sigma.ι (fun _ : ZerothHomotopy (zeroSkeletonSpace C) => zeroSkeletonCoefficient)
        (ZerothHomotopy.mk (zeroCellPoint C i)) := by
  dsimp only [zeroCellOrdinaryClassMap, TopCat.singularHomology₀Iso, Iso.trans_hom]
  rw [Category.assoc,
    SSet.liftCycles_ιChainComplex_homologyπ_homology₀Iso_hom_assoc]
  simp [sigmaConst, zeroCellVertex, TopCat.zerothHomotopyEquiv_symm_mk]

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
  rfl

/- The standard integer-module Finsupp cofan is transported by the actual
forgetful functor preserving colimits. All indexing types may be empty. -/
private noncomputable def zeroCellIntegerCoproductIso :
    (∐ fun _ : RelCWComplex.cell C 0 => zeroSkeletonCoefficient) ≅
      AddCommGrpCat.of (RelCWComplex.cell C 0 →₀ ULift.{u} ℤ) :=
  let F := forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}
  let cofan := F.mapCocone
    (ModuleCat.finsuppCocone ℤ (ULift.{u} ℤ) (RelCWComplex.cell C 0))
  let hc : IsColimit cofan := isColimitOfPreserves F
    (ModuleCat.finsuppCoconeIsColimit ℤ (ULift.{u} ℤ) (RelCWComplex.cell C 0))
  (colimit.isColimit (Discrete.functor
    (fun _ : RelCWComplex.cell C 0 => zeroSkeletonCoefficient))).coconePointUniqueUpToIso hc

private theorem zeroCellIntegerCoproductIso_single
    (i : RelCWComplex.cell C 0) (a : ULift.{u} ℤ) :
    (zeroCellIntegerCoproductIso C).hom
        (Sigma.ι (fun _ : RelCWComplex.cell C 0 => zeroSkeletonCoefficient) i a) =
      Finsupp.single i a := by
  have h := IsColimit.comp_coconePointUniqueUpToIso_hom
    (colimit.isColimit (Discrete.functor
      (fun _ : RelCWComplex.cell C 0 => zeroSkeletonCoefficient)))
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
    (∐ fun _ : RelCWComplex.cell C 0 => zeroSkeletonCoefficient) ≅
      AddCommGrpCat.of (RelCWComplex.cell C 0 →₀ ℤ) :=
  zeroCellIntegerCoproductIso C ≪≫
    (zeroCellLowerCoefficientEquiv C).toAddCommGrpIso

private theorem zeroCellIntegerFinsuppIso_single
    (i : RelCWComplex.cell C 0) (a : ULift.{u} ℤ) :
    (zeroCellIntegerFinsuppIso C).hom
        (Sigma.ι (fun _ : RelCWComplex.cell C 0 => zeroSkeletonCoefficient) i a) =
      Finsupp.single i a.down := by
  change zeroCellLowerCoefficientEquiv C
    ((zeroCellIntegerCoproductIso C).hom
      (Sigma.ι (fun _ : RelCWComplex.cell C 0 => zeroSkeletonCoefficient) i a)) = _
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
    (Hatcher.Relative.homologyFunctor zeroSkeletonCoefficient 0).obj
        (zeroSkeletonPair C) ≅
      AddCommGrpCat.of (RelCWComplex.cell C 0 →₀ ℤ) :=
  (zeroSkeletonOrdinaryRelativeHomologyIso C 0).symm ≪≫
    (zeroSkeletonSpace C).singularHomology₀Iso zeroSkeletonCoefficient ≪≫
    (sigmaConst.obj zeroSkeletonCoefficient).mapIso
      (zeroSkeletonComponentCellEquiv C).toIso ≪≫
    zeroCellIntegerFinsuppIso C

private theorem zeroCell_relative_class_forward
    (i : RelCWComplex.cell C 0) :
    (zeroSkeletonRelativeHomologyIso C).hom (zeroCellRelativeClass C i) =
      Finsupp.single i 1 := by
  have hcomponent := zeroCellOrdinaryClassMap_components C i
  have hvalue := ConcreteCategory.congr_hom hcomponent (ULift.up (1 : ℤ))
  dsimp only [zeroSkeletonRelativeHomologyIso, Iso.trans_hom, Iso.symm_hom,
    zeroCellRelativeClass, Functor.mapIso_hom]
  change (zeroCellIntegerFinsuppIso C).hom
    (((sigmaConst.obj zeroSkeletonCoefficient).map
      (zeroSkeletonComponentCellEquiv C).toIso.hom)
      (((zeroSkeletonSpace C).singularHomology₀Iso zeroSkeletonCoefficient).hom
        ((zeroSkeletonOrdinaryRelativeHomologyIso C 0).inv
          ((zeroSkeletonOrdinaryRelativeHomologyIso C 0).hom
            (zeroCellOrdinaryClassMap C i (ULift.up (1 : ℤ))))))) = _
  rw [(zeroSkeletonOrdinaryRelativeHomologyIso C 0).hom_inv_id_apply]
  rw [hvalue]
  have hreindex := ConcreteCategory.congr_hom
    (Sigma.ι_comp_map' (zeroSkeletonComponentCellEquiv C) (fun _ => 𝟙 zeroSkeletonCoefficient)
      (ZerothHomotopy.mk (zeroCellPoint C i))) (ULift.up (1 : ℤ))
  change (zeroCellIntegerFinsuppIso C).hom
    ((Sigma.map' (zeroSkeletonComponentCellEquiv C) (fun _ => 𝟙 zeroSkeletonCoefficient))
      (Sigma.ι (fun _ : ZerothHomotopy (zeroSkeletonSpace C) => zeroSkeletonCoefficient)
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
    IsZero ((Hatcher.Relative.homologyFunctor zeroSkeletonCoefficient n).obj
      (zeroSkeletonPair C)) := by
  have h := isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
    AddCommGrpCat.{u} n zeroSkeletonCoefficient (zeroSkeletonSpace C) (Nat.ne_of_gt hn)
  exact h.of_iso (zeroSkeletonOrdinaryRelativeHomologyIso C n)

/-- Hatcher Lemma 2.34(a), degree-zero endpoint with the actual vertex basis.
The proof includes arbitrary and empty cell families. -/
theorem zeroSkeletonRelativeHomology :
    (∀ n : ℕ, 0 < n →
      IsZero ((Hatcher.Relative.homologyFunctor zeroSkeletonCoefficient n).obj
        (zeroSkeletonPair C))) ∧
    ∃ E : (Hatcher.Relative.homologyFunctor zeroSkeletonCoefficient 0).obj
          (zeroSkeletonPair C) ≅
        AddCommGrpCat.of (RelCWComplex.cell C 0 →₀ ℤ),
      ∀ i : RelCWComplex.cell C 0,
        E.inv (Finsupp.single i 1) = zeroCellRelativeClass C i :=
  ⟨zeroSkeletonRelativeHomology_isZero C,
    zeroSkeletonRelativeHomologyIso C, zeroSkeletonRelativeHomologyIso_inv_single C⟩

end Hatcher.ClassicalCW
