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
