import Hatcher.Singular.SigmaRelativeChains
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Homology.Functor
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic

/-!
# Relative homology of a topological coproduct
-/

noncomputable section

open AlgebraicTopology CategoryTheory Limits

namespace Hatcher.Relative

universe w v u d c

section HomologyCoproduct

variable {ι : Type w} {C : Type c} [Category.{d} C] [Abelian C]
  [HasCoproducts.{w} C] [AB4OfSize.{w} C]

private noncomputable def familyChainComplex
    (K : ι → ChainComplex C ℕ) :
    ChainComplex (Discrete ι ⥤ C) ℕ where
  X n := Discrete.functor fun i ↦ (K i).X n
  d n m :=
    { app := fun i ↦ (K i.as).d n m
      naturality := fun _ _ f ↦ by
        obtain rfl := Discrete.ext (Discrete.eq_of_hom f)
        simp }
  shape n m h := by
    ext i
    exact (K i.as).shape n m h
  d_comp_d' n m k hnm hmk := by
    ext i
    exact (K i.as).d_comp_d n m k

private noncomputable def evaluationToColim (i : Discrete ι) :
    (evaluation (Discrete ι) C).obj i ⟶
      colim (J := Discrete ι) (C := C) where
  app F := colimit.ι F i
  naturality _ _ f := (colimit.ι_map f i).symm

private noncomputable def familyChainComplexι
    (K : ι → ChainComplex C ℕ) (i : ι) :
    K i ⟶
      ((colim (J := Discrete ι) (C := C)).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (familyChainComplex K) :=
  (NatTrans.mapHomologicalComplex
    (evaluationToColim (C := C) ⟨i⟩) (ComplexShape.down ℕ)).app
      (familyChainComplex K)

private noncomputable def familyChainComplexColimitIsoX
    (K : ι → ChainComplex C ℕ) (n : ℕ) :
    (colim (J := Discrete ι) (C := C)).obj
        ((familyChainComplex K).X n) ≅
      (∐ K).X n :=
  IsColimit.coconePointUniqueUpToIso
    (colimit.isColimit ((familyChainComplex K).X n))
    (isColimitOfHasCoproductOfPreservesColimit
      (HomologicalComplex.eval C (ComplexShape.down ℕ) n) K)

omit [AB4OfSize.{w} C] in
@[reassoc]
private lemma familyChainComplex_colimit_ι_isoX_hom
    (K : ι → ChainComplex C ℕ) (n : ℕ) (i : ι) :
    colimit.ι ((familyChainComplex K).X n) ⟨i⟩ ≫
        (familyChainComplexColimitIsoX K n).hom =
      (Sigma.ι K i).f n :=
  IsColimit.comp_coconePointUniqueUpToIso_hom
    (colimit.isColimit ((familyChainComplex K).X n))
    (isColimitOfHasCoproductOfPreservesColimit
      (HomologicalComplex.eval C (ComplexShape.down ℕ) n) K) ⟨i⟩

private noncomputable def familyChainComplexColimitIso
    (K : ι → ChainComplex C ℕ) :
    ((colim (J := Discrete ι) (C := C)).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (familyChainComplex K) ≅
      ∐ K :=
  HomologicalComplex.Hom.isoOfComponents
    (familyChainComplexColimitIsoX K)
    (by
      intro n m h
      apply (colimit.isColimit ((familyChainComplex K).X n)).hom_ext
      intro i
      rcases i with ⟨i⟩
      change
        colimit.ι ((familyChainComplex K).X n) ⟨i⟩ ≫
            (familyChainComplexColimitIsoX K n).hom ≫ (∐ K).d n m =
          colimit.ι ((familyChainComplex K).X n) ⟨i⟩ ≫
            colim.map ((familyChainComplex K).d n m) ≫
              (familyChainComplexColimitIsoX K m).hom
      have hι :
          colimit.ι ((familyChainComplex K).X n) ⟨i⟩ ≫
              colim.map ((familyChainComplex K).d n m) =
            (K i).d n m ≫
              colimit.ι ((familyChainComplex K).X m) ⟨i⟩ := by
        simpa only [familyChainComplex] using
          colimit.ι_map ((familyChainComplex K).d n m) ⟨i⟩
      have htail :
          (K i).d n m ≫ (Sigma.ι K i).f m =
            colimit.ι ((familyChainComplex K).X n) ⟨i⟩ ≫
              colim.map ((familyChainComplex K).d n m) ≫
                (familyChainComplexColimitIsoX K m).hom := by
        rw [← familyChainComplex_colimit_ι_isoX_hom]
        exact (Category.assoc ((K i).d n m)
          (colimit.ι ((familyChainComplex K).X m) ⟨i⟩)
          (familyChainComplexColimitIsoX K m).hom).symm.trans <|
            ((reassoc_of% hι)
              (familyChainComplexColimitIsoX K m).hom).symm
      have hhead :
          colimit.ι ((familyChainComplex K).X n) ⟨i⟩ ≫
              (familyChainComplexColimitIsoX K n).hom ≫ (∐ K).d n m =
            (Sigma.ι K i).f n ≫ (∐ K).d n m := by
        rw [← Category.assoc,
          familyChainComplex_colimit_ι_isoX_hom]
        rfl
      exact hhead.trans (((Sigma.ι K i).comm n m).trans htail))

omit [AB4OfSize.{w} C] in
private lemma familyChainComplexι_comp_colimitIso_hom
    (K : ι → ChainComplex C ℕ) (i : ι) :
    familyChainComplexι K i ≫ (familyChainComplexColimitIso K).hom =
      Sigma.ι K i := by
  ext n
  exact familyChainComplex_colimit_ι_isoX_hom K n i

private noncomputable def homologyCoproductComparisonIso
    (K : ι → ChainComplex C ℕ) (n : ℕ) :
    (∐ fun i ↦ (K i).homology n) ≅
      (((colim (J := Discrete ι) (C := C)).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (familyChainComplex K)).homology n :=
  Sigma.mapIso (fun i ↦
      ((familyChainComplex K).sc n).mapHomologyIso
        ((evaluation (Discrete ι) C).obj ⟨i⟩)) ≪≫
    ((colim (J := Discrete ι) (C := C)).mapIso
      (Discrete.natIsoFunctor
        (F := ((familyChainComplex K).sc n).homology))).symm ≪≫
    (((familyChainComplex K).sc n).mapHomologyIso
      (colim (J := Discrete ι) (C := C))).symm

private noncomputable def homologyCoproductIso
    (K : ι → ChainComplex C ℕ) (n : ℕ) :
    (∐ fun i ↦ (K i).homology n) ≅ (∐ K).homology n :=
  homologyCoproductComparisonIso K n ≪≫
    HomologicalComplex.homologyMapIso
      (familyChainComplexColimitIso K) n

@[reassoc]
private lemma ι_homologyCoproductComparisonIso_hom
    (K : ι → ChainComplex C ℕ) (n : ℕ) (i : ι) :
    Sigma.ι (fun i ↦ (K i).homology n) i ≫
        (homologyCoproductComparisonIso K n).hom =
      HomologicalComplex.homologyMap (familyChainComplexι K i) n := by
  let S := (familyChainComplex K).sc n
  let e (j : ι) : (K j).homology n ≅ S.homology.obj ⟨j⟩ :=
    S.mapHomologyIso ((evaluation (Discrete ι) C).obj ⟨j⟩)
  have hfirst :
      Sigma.ι (fun j ↦ (K j).homology n) i ≫
          (Sigma.mapIso e).hom ≫
            (colim (J := Discrete ι) (C := C)).map
              (Discrete.natIsoFunctor (F := S.homology)).inv =
        (e i).hom ≫ colimit.ι S.homology ⟨i⟩ := by
    rw [← Category.assoc, Sigma.ι_mapIso_hom]
    rw [Category.assoc, colimit.ι_map]
    simp [e]
  have hmap :
      HomologicalComplex.homologyMap (familyChainComplexι K i) n =
        (e i).hom ≫ colimit.ι S.homology ⟨i⟩ ≫
          (S.mapHomologyIso
            (colim (J := Discrete ι) (C := C))).inv := by
    change ShortComplex.homologyMap
        (S.mapNatTrans (evaluationToColim (C := C) ⟨i⟩)) =
      (S.mapHomologyIso
          ((evaluation (Discrete ι) C).obj ⟨i⟩)).hom ≫
        (evaluationToColim (C := C) ⟨i⟩).app S.homology ≫
          (S.mapHomologyIso
            (colim (J := Discrete ι) (C := C))).inv
    exact S.homologyMap_mapNatTrans
      (evaluationToColim (C := C) ⟨i⟩)
  dsimp only [homologyCoproductComparisonIso, Iso.trans_hom,
    Iso.symm_hom, Functor.mapIso_inv]
  change
    Sigma.ι (fun j ↦ (K j).homology n) i ≫
        (Sigma.mapIso e).hom ≫
          (colim (J := Discrete ι) (C := C)).map
            (Discrete.natIsoFunctor (F := S.homology)).inv ≫
              (S.mapHomologyIso
                (colim (J := Discrete ι) (C := C))).inv =
      HomologicalComplex.homologyMap (familyChainComplexι K i) n
  exact ((reassoc_of% hfirst)
    (S.mapHomologyIso
      (colim (J := Discrete ι) (C := C))).inv).trans hmap.symm

@[reassoc]
private lemma ι_homologyCoproductIso_hom
    (K : ι → ChainComplex C ℕ) (n : ℕ) (i : ι) :
    Sigma.ι (fun i ↦ (K i).homology n) i ≫
        (homologyCoproductIso K n).hom =
      HomologicalComplex.homologyMap (Sigma.ι K i) n := by
  rw [homologyCoproductIso, Iso.trans_hom, ← Category.assoc,
    ι_homologyCoproductComparisonIso_hom]
  change
    HomologicalComplex.homologyMap (familyChainComplexι K i) n ≫
        HomologicalComplex.homologyMap
          (familyChainComplexColimitIso K).hom n =
      HomologicalComplex.homologyMap (Sigma.ι K i) n
  rw [← HomologicalComplex.homologyMap_comp,
    familyChainComplexι_comp_colimitIso_hom]

end HomologyCoproduct

section RelativeHomology

variable {ι : Type w} (X : ι → TopCat.{w})
  {C : Type c} [Category.{d} C] [Abelian C]
  [HasCoproducts.{w} C] [AB4OfSize.{w} C]
  (R : C) (x₀ : ∀ i, X i) (n : ℕ)

/-- The canonical map from the coproduct of the relative homology objects of
the pointed summands to the relative homology of their topological sigma. -/
noncomputable def relativeHomologySigmaMap :
    (∐ fun i ↦ (homologyFunctor R n).obj (pointedPair (X i) (x₀ i))) ⟶
      (homologyFunctor R n).obj (sigmaPointedPair x₀) :=
  Sigma.desc fun i ↦ (homologyFunctor R n).map (sigmaPointedPairι x₀ i)

private noncomputable def relativeHomologyObjIso (P : TopPair.{w}) :
    (homologyFunctor R n).obj P ≅
      ((chainComplexFunctor R).obj P).homology n :=
  Iso.refl _

omit [AB4OfSize.{w} C] in
private lemma relativeHomologyObjIso_map {P Q : TopPair.{w}}
    (f : P ⟶ Q) :
    (relativeHomologyObjIso R n P).hom ≫
        HomologicalComplex.homologyMap
          ((chainComplexFunctor R).map f) n ≫
          (relativeHomologyObjIso R n Q).inv =
      (homologyFunctor R n).map f := by
  change
    𝟙 _ ≫ HomologicalComplex.homologyMap
        ((chainComplexFunctor R).map f) n ≫ 𝟙 _ = _
  rw [Category.id_comp, Category.comp_id]
  rfl

private noncomputable def relativeHomologySigmaChainIso :
    (∐ fun i ↦
      ((chainComplexFunctor R).obj
        (pointedPair (X i) (x₀ i))).homology n) ≅
      ((chainComplexFunctor R).obj (sigmaPointedPair x₀)).homology n :=
  homologyCoproductIso
      (fun i ↦ (chainComplexFunctor R).obj (pointedPair (X i) (x₀ i))) n ≪≫
    HomologicalComplex.homologyMapIso
      (relativeChainComplexSigmaIso X R x₀) n

@[reassoc]
private lemma ι_relativeHomologySigmaChainIso_hom (i : ι) :
    Sigma.ι
        (fun i ↦ ((chainComplexFunctor R).obj
          (pointedPair (X i) (x₀ i))).homology n) i ≫
      (relativeHomologySigmaChainIso X R x₀ n).hom =
    HomologicalComplex.homologyMap
      ((chainComplexFunctor R).map (sigmaPointedPairι x₀ i)) n := by
  dsimp only [relativeHomologySigmaChainIso, Iso.trans_hom]
  rw [← Category.assoc, ι_homologyCoproductIso_hom]
  change
    HomologicalComplex.homologyMap
        (Sigma.ι
          (fun i ↦ (chainComplexFunctor R).obj
            (pointedPair (X i) (x₀ i))) i) n ≫
      HomologicalComplex.homologyMap
        (relativeChainComplexSigmaIso X R x₀).hom n = _
  rw [← HomologicalComplex.homologyMap_comp,
    ι_relativeChainComplexSigmaIso_hom]

/-- Relative homology commutes with topological coproducts when coproducts in
the coefficient category are exact. This statement includes an empty index
type. -/
noncomputable def relativeHomologySigmaIso :
    (∐ fun i ↦ (homologyFunctor R n).obj (pointedPair (X i) (x₀ i))) ≅
      (homologyFunctor R n).obj (sigmaPointedPair x₀) :=
  Sigma.mapIso (fun i ↦
      relativeHomologyObjIso R n (pointedPair (X i) (x₀ i))) ≪≫
    relativeHomologySigmaChainIso X R x₀ n ≪≫
    (relativeHomologyObjIso R n (sigmaPointedPair x₀)).symm

/-- On each coproduct summand, the forward relative-homology comparison is
the map induced by the canonical inclusion into the topological sigma. -/
@[reassoc (attr := simp)]
lemma ι_relativeHomologySigmaIso_hom (i : ι) :
    Sigma.ι
        (fun i ↦ (homologyFunctor R n).obj
          (pointedPair (X i) (x₀ i))) i ≫
      (relativeHomologySigmaIso X R x₀ n).hom =
    (homologyFunctor R n).map (sigmaPointedPairι x₀ i) := by
  dsimp only [relativeHomologySigmaIso, Iso.trans_hom]
  rw [← Category.assoc, Sigma.ι_mapIso_hom]
  simp only [Category.assoc]
  rw [ι_relativeHomologySigmaChainIso_hom_assoc]
  simpa only [Iso.symm_hom] using
    relativeHomologyObjIso_map R n (sigmaPointedPairι x₀ i)

/-- The forward map of `relativeHomologySigmaIso` is the canonical coproduct
map induced by the summand inclusions. -/
lemma relativeHomologySigmaIso_hom :
    (relativeHomologySigmaIso X R x₀ n).hom =
      relativeHomologySigmaMap X R x₀ n := by
  apply Sigma.hom_ext
  intro i
  simp [relativeHomologySigmaMap]

end RelativeHomology

section Integral

variable {ι : Type} (X : ι → TopCat.{0}) (x₀ : ∀ i, X i) (n : ℕ)

/-- The integral specialization of the relative-homology coproduct
comparison. Mathlib's `AB4 AddCommGrpCat` instance supplies exactness. -/
noncomputable def relativeIntegralHomologySigmaIso :
    (∐ fun i ↦
      (homologyFunctor (AddCommGrpCat.of ℤ) n).obj
        (pointedPair (X i) (x₀ i))) ≅
      (homologyFunctor (AddCommGrpCat.of ℤ) n).obj
        (sigmaPointedPair x₀) :=
  relativeHomologySigmaIso X (AddCommGrpCat.of ℤ) x₀ n

end Integral

end Hatcher.Relative
