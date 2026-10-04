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

variable {ι : Type w} (X : ι → TopCat.{w})

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

section Relative

variable (x₀ : ∀ i, X i)

/-- The canonical map from the coproduct of the relative singular chain
complexes of pointed summands to the relative chains of their sigma pair. -/
noncomputable def relativeChainComplexSigmaMap :
    (∐ fun i ↦
      (chainComplexFunctor R).obj (pointedPair (X i) (x₀ i))) ⟶
      (chainComplexFunctor R).obj (sigmaPointedPair x₀) :=
  Sigma.desc fun i ↦
    (chainComplexFunctor R).map (sigmaPointedPairι x₀ i)

private noncomputable def sigmaPointedPairSourceMap :
    (∐ fun i ↦
      (singularPairFunctor.obj (pointedPair (X i) (x₀ i))).left.chainComplex R) ⟶
      (∐ fun i ↦
        (singularPairFunctor.obj (pointedPair (X i) (x₀ i))).right.chainComplex R) :=
  Limits.Sigma.map fun i ↦
    SSet.chainComplexMap
      (singularPairFunctor.obj (pointedPair (X i) (x₀ i))).hom R

private noncomputable abbrev sigmaPointedPairSummandπ (i : ι) :
    (singularPairFunctor.obj
        (pointedPair (X i) (x₀ i))).right.chainComplex R ⟶
      (chainComplexFunctor R).obj (pointedPair (X i) (x₀ i)) :=
  (singularPairFunctor.obj (pointedPair (X i) (x₀ i))).chainComplexπ R

private noncomputable def sigmaPointedPairSourceπ :
    (∐ fun i ↦
      (singularPairFunctor.obj (pointedPair (X i) (x₀ i))).right.chainComplex R) ⟶
      (∐ fun i ↦
        (chainComplexFunctor R).obj (pointedPair (X i) (x₀ i))) :=
  Limits.Sigma.map fun i ↦
    sigmaPointedPairSummandπ X R x₀ i

private noncomputable abbrev sigmaPointedPairSourceCofork :
    CokernelCofork (sigmaPointedPairSourceMap X R x₀) :=
  sigmaCokernelCofork
    (Q := fun i ↦
      (chainComplexFunctor R).obj (pointedPair (X i) (x₀ i)))
    (fun i ↦ SSet.chainComplexMap
      (singularPairFunctor.obj (pointedPair (X i) (x₀ i))).hom R)
    (fun i ↦
      sigmaPointedPairSummandπ X R x₀ i)
    (fun i ↦
      (singularPairFunctor.obj
        (pointedPair (X i) (x₀ i))).chainComplex_condition R)

private noncomputable def isColimitSigmaPointedPairSourceCofork :
    IsColimit (sigmaPointedPairSourceCofork X R x₀) :=
  isColimitSigmaCokernelCofork
    (Q := fun i ↦
      (chainComplexFunctor R).obj (pointedPair (X i) (x₀ i)))
    (f := fun i ↦ SSet.chainComplexMap
      (singularPairFunctor.obj (pointedPair (X i) (x₀ i))).hom R)
    (p := fun i ↦
      sigmaPointedPairSummandπ X R x₀ i)
    (hp := fun i ↦
      (singularPairFunctor.obj
        (pointedPair (X i) (x₀ i))).chainComplex_condition R)
    (fun i ↦
      (singularPairFunctor.obj
        (pointedPair (X i) (x₀ i))).isColimitCokernelCoforkChainComplex R)

private noncomputable abbrev sigmaPointedPairTargetMap :
    (singularPairFunctor.obj (sigmaPointedPair x₀)).left.chainComplex R ⟶
      (singularPairFunctor.obj (sigmaPointedPair x₀)).right.chainComplex R :=
  SSet.chainComplexMap (singularPairFunctor.obj (sigmaPointedPair x₀)).hom R

private noncomputable def sigmaPointedPairLeftMap :
    (∐ fun i ↦
      (singularPairFunctor.obj (pointedPair (X i) (x₀ i))).left.chainComplex R) ⟶
      (singularPairFunctor.obj (sigmaPointedPair x₀)).left.chainComplex R :=
  Sigma.desc fun i ↦
    SSet.chainComplexMap
      (singularPairFunctor.map (sigmaPointedPairι x₀ i)).left R

private noncomputable def sigmaPointedPairRightMap :
    (∐ fun i ↦
      (singularPairFunctor.obj (pointedPair (X i) (x₀ i))).right.chainComplex R) ⟶
      (singularPairFunctor.obj (sigmaPointedPair x₀)).right.chainComplex R :=
  Sigma.desc fun i ↦
    SSet.chainComplexMap
      (singularPairFunctor.map (sigmaPointedPairι x₀ i)).right R

private noncomputable instance sigmaPointedPairLeftMap_isIso :
    IsIso (sigmaPointedPairLeftMap X R x₀) := by
  change IsIso (singularChainComplexSigmaMap
    (fun i ↦ (pointedPair (X i) (x₀ i)).snd) R)
  infer_instance

private noncomputable instance sigmaPointedPairRightMap_isIso :
    IsIso (sigmaPointedPairRightMap X R x₀) := by
  change IsIso (singularChainComplexSigmaMap
    (fun i ↦ (pointedPair (X i) (x₀ i)).fst) R)
  infer_instance

private noncomputable def sigmaPointedPairArrowIso :
    Arrow.mk (sigmaPointedPairSourceMap X R x₀) ≅
      Arrow.mk (sigmaPointedPairTargetMap X R x₀) :=
  Arrow.isoMk'
    (sigmaPointedPairSourceMap X R x₀)
    (sigmaPointedPairTargetMap X R x₀)
    (asIso (sigmaPointedPairLeftMap X R x₀))
    (asIso (sigmaPointedPairRightMap X R x₀))
    (by
      apply Sigma.hom_ext
      intro i
      simp [sigmaPointedPairLeftMap, sigmaPointedPairRightMap,
        sigmaPointedPairSourceMap, sigmaPointedPairTargetMap,
        Category.assoc, ← Functor.map_comp]
      apply ((SSet.chainComplexFunctor C).obj R).congr_map
      simpa using (singularPairFunctor.map (sigmaPointedPairι x₀ i)).w)

@[simp]
private lemma sigmaPointedPairArrowIso_hom_right :
    (sigmaPointedPairArrowIso X R x₀).hom.right =
      sigmaPointedPairRightMap X R x₀ := rfl

private lemma ι_sigmaPointedPairRightMap_comp_π (i : ι) :
    Sigma.ι
        (fun b ↦ (singularPairFunctor.obj
          (pointedPair (X b) (x₀ b))).right.chainComplex R) i ≫
      ((Sigma.desc fun b ↦ SSet.chainComplexMap
          (singularPairFunctor.map (sigmaPointedPairι x₀ b)).right R) ≫
        (chainComplexFunctorπ R).app (sigmaPointedPair x₀)) =
    SSet.chainComplexMap
        (singularPairFunctor.map (sigmaPointedPairι x₀ i)).right R ≫
      (chainComplexFunctorπ R).app (sigmaPointedPair x₀) := by
  calc
    _ = (Sigma.ι
          (fun b ↦ (singularPairFunctor.obj
            (pointedPair (X b) (x₀ b))).right.chainComplex R) i ≫
        Sigma.desc (fun b ↦ SSet.chainComplexMap
          (singularPairFunctor.map (sigmaPointedPairι x₀ b)).right R)) ≫
        (chainComplexFunctorπ R).app (sigmaPointedPair x₀) :=
      (Category.assoc _ _ _).symm
    _ = _ := congrArg
      (fun k ↦ k ≫ (chainComplexFunctorπ R).app (sigmaPointedPair x₀))
      (Sigma.ι_desc
        (fun b ↦ SSet.chainComplexMap
          (singularPairFunctor.map (sigmaPointedPairι x₀ b)).right R) i)

private noncomputable def sigmaPointedPairSourcePointIso :
    (∐ fun i ↦
      (chainComplexFunctor R).obj (pointedPair (X i) (x₀ i))) ≅
      (sigmaPointedPairSourceCofork X R x₀).pt :=
  Iso.refl _

private noncomputable def sigmaPointedPairTargetPointIso :
    ((singularPairFunctor.obj
      (sigmaPointedPair x₀)).cokernelCoforkChainComplex R).pt ≅
      (chainComplexFunctor R).obj (sigmaPointedPair x₀) :=
  Iso.refl _

@[simp]
private lemma sigmaPointedPairSourcePointIso_hom :
    (sigmaPointedPairSourcePointIso X R x₀).hom = 𝟙 _ := rfl

@[simp]
private lemma sigmaPointedPairTargetPointIso_hom :
    (sigmaPointedPairTargetPointIso X R x₀).hom = 𝟙 _ := rfl

private noncomputable def sigmaPointedPairCokernelIso :
    (sigmaPointedPairSourceCofork X R x₀).pt ≅
      ((singularPairFunctor.obj
        (sigmaPointedPair x₀)).cokernelCoforkChainComplex R).pt :=
  CokernelCofork.mapIsoOfIsColimit
    (isColimitSigmaPointedPairSourceCofork X R x₀)
    ((singularPairFunctor.obj
      (sigmaPointedPair x₀)).isColimitCokernelCoforkChainComplex R)
    (sigmaPointedPairArrowIso X R x₀)

@[reassoc]
private lemma sigmaPointedPairSourceπ_comp_sourcePointIso :
    Limits.Sigma.map (sigmaPointedPairSummandπ X R x₀) ≫
        (sigmaPointedPairSourcePointIso X R x₀).hom =
      Cofork.π (sigmaPointedPairSourceCofork X R x₀) := by
  rw [sigmaPointedPairSourcePointIso_hom]
  rw [Category.comp_id]
  symm
  apply CokernelCofork.π_ofπ
  exact CokernelCofork.condition (sigmaPointedPairSourceCofork X R x₀)

@[reassoc]
private lemma sigmaPointedPairTargetπ_comp_targetPointIso :
    (singularPairFunctor.obj (sigmaPointedPair x₀)).chainComplexπ R ≫
        (sigmaPointedPairTargetPointIso X R x₀).hom =
      (chainComplexFunctorπ R).app (sigmaPointedPair x₀) := by
  rw [sigmaPointedPairTargetPointIso_hom]
  change (chainComplexFunctorπ R).app (sigmaPointedPair x₀) ≫ 𝟙 _ = _
  rw [Category.comp_id]

@[reassoc]
private lemma sigmaPointedPairArrowTarget_fac :
    ((sigmaPointedPairArrowIso X R x₀).hom.right ≫
        (singularPairFunctor.obj (sigmaPointedPair x₀)).chainComplexπ R) ≫
      (sigmaPointedPairTargetPointIso X R x₀).hom =
    (sigmaPointedPairArrowIso X R x₀).hom.right ≫
      (chainComplexFunctorπ R).app (sigmaPointedPair x₀) := by
  calc
    _ = (sigmaPointedPairArrowIso X R x₀).hom.right ≫
        ((singularPairFunctor.obj (sigmaPointedPair x₀)).chainComplexπ R ≫
          (sigmaPointedPairTargetPointIso X R x₀).hom) :=
      Category.assoc _ _ _
    _ = _ := by rw [sigmaPointedPairTargetπ_comp_targetPointIso]

private lemma ι_sigmaPointedPairArrowTarget_fac (i : ι) :
    Sigma.ι
        (fun b ↦ (singularPairFunctor.obj
          (pointedPair (X b) (x₀ b))).right.chainComplex R) i ≫
      (((sigmaPointedPairArrowIso X R x₀).hom.right ≫
          (singularPairFunctor.obj
            (sigmaPointedPair x₀)).chainComplexπ R) ≫
        (sigmaPointedPairTargetPointIso X R x₀).hom) =
    Sigma.ι
        (fun b ↦ (singularPairFunctor.obj
          (pointedPair (X b) (x₀ b))).right.chainComplex R) i ≫
      ((sigmaPointedPairArrowIso X R x₀).hom.right ≫
        (chainComplexFunctorπ R).app (sigmaPointedPair x₀)) :=
  congrArg
    (fun k ↦ Sigma.ι
      (fun b ↦ (singularPairFunctor.obj
        (pointedPair (X b) (x₀ b))).right.chainComplex R) i ≫ k)
    (sigmaPointedPairArrowTarget_fac X R x₀)

@[reassoc]
private lemma sigmaPointedPairCokernelIso_fac :
    Cofork.π (sigmaPointedPairSourceCofork X R x₀) ≫
        (sigmaPointedPairCokernelIso X R x₀).hom =
      (sigmaPointedPairArrowIso X R x₀).hom.right ≫
        (singularPairFunctor.obj (sigmaPointedPair x₀)).chainComplexπ R :=
  CokernelCofork.π_mapOfIsColimit
    (isColimitSigmaPointedPairSourceCofork X R x₀)
    ((singularPairFunctor.obj
      (sigmaPointedPair x₀)).cokernelCoforkChainComplex R)
    (sigmaPointedPairArrowIso X R x₀).hom

/-- Relative singular chains carry the sigma pair of a family of pointed
spaces to the categorical coproduct of the relative chain complexes of the
summands. This includes empty indexing types. -/
noncomputable def relativeChainComplexSigmaIso :
    (∐ fun i ↦
      (chainComplexFunctor R).obj (pointedPair (X i) (x₀ i))) ≅
      (chainComplexFunctor R).obj (sigmaPointedPair x₀) :=
  sigmaPointedPairSourcePointIso X R x₀ ≪≫
    sigmaPointedPairCokernelIso X R x₀ ≪≫
    sigmaPointedPairTargetPointIso X R x₀

/-- The forward map of `relativeChainComplexSigmaIso` is the canonical map
induced by the inclusions of the pointed summands. -/
lemma relativeChainComplexSigmaIso_hom :
    (relativeChainComplexSigmaIso X R x₀).hom =
      relativeChainComplexSigmaMap X R x₀ := by
  apply Sigma.hom_ext
  intro i
  let P := pointedPair (X i) (x₀ i)
  let p := sigmaPointedPairSummandπ X R x₀ i
  letI : Epi p :=
    Cofork.IsColimit.epi
      ((singularPairFunctor.obj P).isColimitCokernelCoforkChainComplex R)
  apply (cancel_epi p).1
  dsimp only [p, P]
  simp only [relativeChainComplexSigmaIso, Iso.trans_hom,
    relativeChainComplexSigmaMap, Category.assoc]
  rw [← Category.assoc, ← Sigma.ι_map]
  rw [Category.assoc]
  rw [sigmaPointedPairSourceπ_comp_sourcePointIso_assoc]
  rw [sigmaPointedPairCokernelIso_fac_assoc]
  refine (ι_sigmaPointedPairArrowTarget_fac X R x₀ i).trans ?_
  rw [sigmaPointedPairArrowIso_hom_right]
  unfold sigmaPointedPairRightMap
  refine (ι_sigmaPointedPairRightMap_comp_π X R x₀ i).trans ?_
  rw [Sigma.ι_desc]
  exact ((SSetPair.chainComplexFunctorπ C).app R).naturality
    (singularPairFunctor.map (sigmaPointedPairι x₀ i))

/-- On every coproduct summand, the forward isomorphism is exactly the
relative-chain map induced by the canonical sigma inclusion. -/
@[reassoc (attr := simp)]
lemma ι_relativeChainComplexSigmaIso_hom (i : ι) :
    Sigma.ι
        (fun i ↦ (chainComplexFunctor R).obj
          (pointedPair (X i) (x₀ i))) i ≫
      (relativeChainComplexSigmaIso X R x₀).hom =
    (chainComplexFunctor R).map (sigmaPointedPairι x₀ i) := by
  rw [relativeChainComplexSigmaIso_hom]
  simp [relativeChainComplexSigmaMap]

end Relative

end Coefficients

end Hatcher.Relative
