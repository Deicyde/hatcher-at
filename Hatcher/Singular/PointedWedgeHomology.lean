/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Hatcher.Sphere.Homology
import Hatcher.Singular.DoubleSimplexSphere
import Hatcher.Sphere.PuncturedStereographic
import Hatcher.Singular.GoodPairPointQuotientNaturality
import Hatcher.Singular.PointedWedgePointQuotient
import Hatcher.Singular.SigmaGoodPair
import Hatcher.Singular.SigmaRelativeHomology
import Hatcher.VanKampen.WellPointedWedgeCover

/-!
# Reduced homology of a pointed wedge

This file proves the canonical form of Hatcher's wedge axiom: the morphism
from the coproduct of the reduced homology objects of the summands, whose
components are induced by the summand inclusions, is an isomorphism when the
basepoints form good pairs.  The empty family is handled separately from the
good-pair argument.
-/

noncomputable section

open AlgebraicTopology CategoryTheory Limits

namespace Hatcher.PointedWedge

universe w v u

variable {ι : Type w} (X : ι → TopCat.{w}) (x₀ : ∀ i, X i)
variable {C : Type u} [Category.{v} C] [Abelian C]
  [HasCoproducts.{w} C]

/-- The canonical map from the coproduct of the reduced homology objects of
the summands to reduced homology of their pointed wedge.  Its components are
the maps induced by the canonical summand inclusions. -/
noncomputable def reducedHomologyCoproductMap (R : C) (n : ℕ) :
    (∐ fun i ↦ (Hatcher.Reduced.homologyFunctor R n).obj (X i)) ⟶
      (Hatcher.Reduced.homologyFunctor R n).obj
        (TopCat.of (Hatcher.PointedWedge (fun i ↦ X i) x₀)) :=
  Sigma.desc fun i ↦
    (Hatcher.Reduced.homologyFunctor R n).map
      (Hatcher.Relative.pointedWedgeSummandInclusion x₀ i)

/-- The restriction of the canonical wedge map to a summand is the map on
reduced homology induced by that summand's inclusion. -/
@[reassoc (attr := simp)]
lemma ι_reducedHomologyCoproductMap (R : C) (n : ℕ) (i : ι) :
    Sigma.ι
        (fun i ↦ (Hatcher.Reduced.homologyFunctor R n).obj (X i)) i ≫
      reducedHomologyCoproductMap X x₀ R n =
    (Hatcher.Reduced.homologyFunctor R n).map
      (Hatcher.Relative.pointedWedgeSummandInclusion x₀ i) := by
  simp [reducedHomologyCoproductMap]

section Nonempty

variable [AB4OfSize.{w} C] [Nonempty ι]

/-- The comparison isomorphism assembled through relative homology of the
sigma pointed pair and the good-pair point quotient. -/
private noncomputable def reducedHomologyCoproductIso
    (h : ∀ i, Hatcher.Relative.IsGoodPair
      (Hatcher.Relative.pointedPair (X i) (x₀ i)))
    (R : C) (n : ℕ) :
    (∐ fun i ↦ (Hatcher.Reduced.homologyFunctor R n).obj (X i)) ≅
      (Hatcher.Reduced.homologyFunctor R n).obj
        (TopCat.of (Hatcher.PointedWedge (fun i ↦ X i) x₀)) :=
  (Sigma.mapIso fun i ↦
      Hatcher.Relative.pointedPairHomologyIso (X i) (x₀ i) R n).symm ≪≫
    Hatcher.Relative.relativeHomologySigmaIso X R x₀ n ≪≫
    Hatcher.Relative.goodPairRelativeHomologyIsoReducedPointQuotient
      (Hatcher.Relative.sigmaPointedPair x₀)
      (Hatcher.Relative.sigmaPointedPair_isGoodPair x₀ h) R n ≪≫
    (Hatcher.Reduced.homologyFunctor R n).mapIso
      (Hatcher.Relative.pointQuotientSigmaPointedPairIsoPointedWedge x₀)

set_option backward.isDefEq.respectTransparency false in
private lemma reducedHomologyCoproductIso_hom
    (h : ∀ i, Hatcher.Relative.IsGoodPair
      (Hatcher.Relative.pointedPair (X i) (x₀ i)))
    (R : C) (n : ℕ) :
    (reducedHomologyCoproductIso X x₀ h R n).hom =
      reducedHomologyCoproductMap X x₀ R n := by
  apply Sigma.hom_ext
  intro i
  let P : Hatcher.Relative.GoodPair.{w} :=
    ⟨Hatcher.Relative.sigmaPointedPair x₀,
      Hatcher.Relative.sigmaPointedPair_isGoodPair x₀ h⟩
  have hnatural :=
    Hatcher.Relative.reducedPairProjection_naturality
      (Hatcher.Relative.sigmaPointedPairι x₀ i) R n
  have hquotient :=
    Hatcher.Relative.reducedPairProjection_comp_goodPairPointQuotientRelativeHomologyNatIso_hom_app
      P R n
  change
    Hatcher.Relative.reducedPairProjection
          (Hatcher.Relative.sigmaPointedPair x₀) R n ≫
        (Hatcher.Relative.goodPairRelativeHomologyIsoReducedPointQuotient
          (Hatcher.Relative.sigmaPointedPair x₀)
          (Hatcher.Relative.sigmaPointedPair_isGoodPair x₀ h) R n).hom =
      (Hatcher.Reduced.homologyFunctor R n).map
        (Hatcher.Relative.pointQuotientProjection
          (Hatcher.Relative.sigmaPointedPair x₀)) at hquotient
  have htop :
      (TopPair.Hom.fst (Hatcher.Relative.sigmaPointedPairι x₀ i) ≫
          Hatcher.Relative.pointQuotientProjection
            (Hatcher.Relative.sigmaPointedPair x₀)) ≫
          (Hatcher.Relative.pointQuotientSigmaPointedPairIsoPointedWedge
            x₀).hom =
        Hatcher.Relative.pointedWedgeSummandInclusion x₀ i := by
    simpa only [Hatcher.Relative.sigmaPointedPairι_fst] using
      Hatcher.Relative.sigmaι_pointQuotientProjection_pointQuotientSigmaPointedPairIsoPointedWedge_hom
        x₀ i
  have hcomponent :
      (Hatcher.Relative.pointedPairHomologyIso
          (X i) (x₀ i) R n).inv ≫
          (Hatcher.Relative.homologyFunctor R n).map
            (Hatcher.Relative.sigmaPointedPairι x₀ i) ≫
          (Hatcher.Relative.goodPairRelativeHomologyIsoReducedPointQuotient
            (Hatcher.Relative.sigmaPointedPair x₀)
            (Hatcher.Relative.sigmaPointedPair_isGoodPair x₀ h) R n).hom ≫
          (Hatcher.Reduced.homologyFunctor R n).map
            (Hatcher.Relative.pointQuotientSigmaPointedPairIsoPointedWedge
              x₀).hom =
        (Hatcher.Reduced.homologyFunctor R n).map
          (Hatcher.Relative.pointedWedgeSummandInclusion x₀ i) := by
    let g :=
      (Hatcher.Relative.goodPairRelativeHomologyIsoReducedPointQuotient
        (Hatcher.Relative.sigmaPointedPair x₀)
        (Hatcher.Relative.sigmaPointedPair_isGoodPair x₀ h) R n).hom
    let e :=
      (Hatcher.Reduced.homologyFunctor R n).map
        (Hatcher.Relative.pointQuotientSigmaPointedPairIsoPointedWedge x₀).hom
    have hnaturalAssoc := (reassoc_of% hnatural) (g ≫ e)
    have hquotientAssoc := (reassoc_of% hquotient) e
    have hmiddle := congrArg
      (fun k ↦
        (Hatcher.Reduced.homologyFunctor R n).map
            (TopPair.Hom.fst (Hatcher.Relative.sigmaPointedPairι x₀ i)) ≫ k)
      hquotientAssoc
    have hmap := congrArg
      (Hatcher.Reduced.homologyFunctor R n).map htop
    simp only [Functor.map_comp] at hmap
    have hmapAssoc :
        (Hatcher.Reduced.homologyFunctor R n).map
            (TopPair.Hom.fst (Hatcher.Relative.sigmaPointedPairι x₀ i)) ≫
          (Hatcher.Reduced.homologyFunctor R n).map
              (Hatcher.Relative.pointQuotientProjection
                (Hatcher.Relative.sigmaPointedPair x₀)) ≫ e =
        (Hatcher.Reduced.homologyFunctor R n).map
          (Hatcher.Relative.pointedWedgeSummandInclusion x₀ i) := by
      simpa only [e, Category.assoc] using hmap
    have hinv :
        (Hatcher.Relative.pointedPairHomologyIso
            (X i) (x₀ i) R n).inv =
          Hatcher.Relative.reducedPairProjection
            (Hatcher.Relative.pointedPair (X i) (x₀ i)) R n := by
      rw [Hatcher.Relative.pointedPairHomologyIso_inv]
      exact Hatcher.Relative.pointedPairProjection_eq_reducedPairProjection
        (X i) (x₀ i) R n
    have hinvAssoc := (reassoc_of% hinv)
      ((Hatcher.Relative.homologyFunctor R n).map
          (Hatcher.Relative.sigmaPointedPairι x₀ i) ≫ g ≫ e)
    exact hinvAssoc.trans
      (hnaturalAssoc.trans (hmiddle.trans hmapAssoc))
  rw [ι_reducedHomologyCoproductMap]
  dsimp only [reducedHomologyCoproductIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom]
  rw [← Category.assoc, Sigma.ι_mapIso_inv]
  simp only [Category.assoc]
  rw [Hatcher.Relative.ι_relativeHomologySigmaIso_hom_assoc]
  exact hcomponent

end Nonempty

/-- **Hatcher, Corollary 2.25 (page 126).** If each chosen basepoint forms a
good pair with its summand, then the canonical map from the coproduct of the
summands' reduced homology objects to the reduced homology of their pointed
wedge is an isomorphism.  Exactness of coproducts is used only in the
nonempty-family case. -/
theorem reducedHomologyCoproductMap_isIso [AB4OfSize.{w} C]
    (h : ∀ i, Hatcher.Relative.IsGoodPair
      (Hatcher.Relative.pointedPair (X i) (x₀ i)))
    (R : C) (n : ℕ) :
    IsIso (reducedHomologyCoproductMap X x₀ R n) := by
  cases isEmpty_or_nonempty ι with
  | inl hι =>
      let _ : IsEmpty ι := hι
      let F : Discrete ι ⥤ C := Discrete.functor fun i ↦
        (Hatcher.Reduced.homologyFunctor R n).obj (X i)
      have hsource : IsZero
          (∐ fun i ↦ (Hatcher.Reduced.homologyFunctor R n).obj (X i)) := by
        change IsZero (colimit F)
        exact ((isColimitEquivIsInitialOfIsEmpty C (colimit.cocone F))
          (colimit.isColimit F)).isZero
      have htarget : IsZero
          ((Hatcher.Reduced.homologyFunctor R n).obj
            (TopCat.of (Hatcher.PointedWedge (fun i ↦ X i) x₀))) :=
        Hatcher.Reduced.isZero_homology_of_contractible R n
      exact hsource.isIso htarget _
  | inr hι =>
      let _ : Nonempty ι := hι
      rw [← reducedHomologyCoproductIso_hom X x₀ h R n]
      infer_instance

section Integral

variable {ι₀ : Type} (X₀ : ι₀ → TopCat.{0}) (x₀₀ : ∀ i, X₀ i)

/-- Integral reduced homology of a pointed wedge is the direct sum of the
reduced homology groups of its summands.  Mathlib's `AB4 AddCommGrpCat`
instance supplies the exact-coproduct hypothesis. -/
theorem reducedIntegralHomologyCoproductMap_isIso
    (h : ∀ i, Hatcher.Relative.IsGoodPair
      (Hatcher.Relative.pointedPair (X₀ i) (x₀₀ i)))
    (n : ℕ) :
    IsIso (reducedHomologyCoproductMap X₀ x₀₀ (AddCommGrpCat.of ℤ) n) :=
  reducedHomologyCoproductMap_isIso X₀ x₀₀ h (AddCommGrpCat.of ℤ) n

end Integral

end Hatcher.PointedWedge


noncomputable section

open AlgebraicTopology CategoryTheory Limits _root_.Topology
open Hatcher.Relative
open scoped Simplicial

namespace Hatcher.ClassicalCW

universe u

private abbrev positiveCellCoefficient : AddCommGrpCat.{u} :=
  AddCommGrpCat.of.{u} (ULift.{u} ℤ)

section Skeleta

variable {X : Type u} [TopologicalSpace X] [T2Space X]
  (C : Set X) [CWComplex C]

private theorem positiveRestrictedSkeletonCarrier (m : ℕ) :
    (CWComplex.skeletonLT
        (CWComplex.skeletonLT C ((m + 1 : ℕ) : ℕ∞) : Set X) (m : ℕ∞) : Set X) =
      (CWComplex.skeletonLT C (m : ℕ∞) : Set X) := by
  classical
  let B : CWComplex.Subcomplex C := CWComplex.skeletonLT C ((m + 1 : ℕ) : ℕ∞)
  let _ : CWComplex (B : Set X) := CWComplex.Subcomplex.instCWComplex B
  change (CWComplex.skeletonLT (B : Set X) (m : ℕ∞) : Set X) = _
  ext x
  constructor
  · intro hx
    obtain ⟨d, hd, i, hi⟩ :=
      (CWComplex.mem_skeletonLT_iff (C := (B : Set X))).mp hx
    let ib : B.I d := i
    refine (CWComplex.mem_skeletonLT_iff (C := C)).mpr ⟨d, hd, ib.1, ?_⟩
    simpa only [RelCWComplex.Subcomplex.openCell_eq] using hi
  · intro hx
    obtain ⟨d, hd, i, hi⟩ := (CWComplex.mem_skeletonLT_iff (C := C)).mp hx
    have hib : i ∈ B.I d := by
      dsimp only [B]
      unfold _root_.Topology.RelCWComplex.skeletonLT
      change (d : ℕ∞) < ((m + 1 : ℕ) : ℕ∞)
      exact hd.trans_le (by exact_mod_cast Nat.le_succ m)
    let ib : B.I d := ⟨i, hib⟩
    refine (CWComplex.mem_skeletonLT_iff (C := (B : Set X))).mpr
      ⟨d, hd, ib, ?_⟩
    simpa only [RelCWComplex.Subcomplex.openCell_eq] using hi

private theorem positiveSkeletalPair_isGoodPair (k : ℕ)
    (hA : Nonempty (skeletalStagePair C (k + 1)).snd) :
    IsGoodPair (skeletalStagePair C (k + 1)) := by
  classical
  let m := k + 1
  let B : CWComplex.Subcomplex C := CWComplex.skeletonLT C ((m + 1 : ℕ) : ℕ∞)
  let _ : CWComplex (B : Set X) := CWComplex.Subcomplex.instCWComplex B
  let A : CWComplex.Subcomplex (B : Set X) := CWComplex.skeletonLT (B : Set X) (m : ℕ∞)
  have hcarrier : (A : Set X) = (CWComplex.skeletonLT C (m : ℕ∞) : Set X) :=
    positiveRestrictedSkeletonCarrier C m
  let Acopy : CWComplex.Subcomplex (B : Set X) :=
    A.copy (CWComplex.skeletonLT C (m : ℕ∞) : Set X) hcarrier.symm A.I rfl
  have hne : (Acopy : Set X).Nonempty := by
    obtain ⟨a⟩ := hA
    exact ⟨a.1, a.2⟩
  have hgood := subcomplex_isGoodPair (B : Set X) Acopy hne
  let f : TopCat.of ↑(CWComplex.skeletonLT C (m : ℕ∞) : Set X) ⟶
      TopCat.of ↑(CWComplex.skeletonLT C ((m + 1 : ℕ) : ℕ∞) : Set X) :=
    TopCat.ofHom (ContinuousMap.inclusion Acopy.subset_complex)
  have hf : f = skeletonLTInclusion C m := by
    apply TopCat.ext
    intro x
    apply Subtype.ext
    rfl
  let hF : IsEmbedding f := IsEmbedding.inclusion Acopy.subset_complex
  have hG : IsEmbedding (skeletonLTInclusion C m) :=
    (skeletalStagePair C m).isEmbedding_map
  have hpairof : ∀ (a b : TopCat.of ↑(CWComplex.skeletonLT C (m : ℕ∞) : Set X) ⟶
      TopCat.of ↑(CWComplex.skeletonLT C ((m + 1 : ℕ) : ℕ∞) : Set X))
      (h₁ : IsEmbedding a) (h₂ : IsEmbedding b),
      a = b → TopPair.of a h₁ = TopPair.of b h₂ := by
    intro a b h₁ h₂ hab
    cases hab
    rfl
  have hpair := hpairof f (skeletonLTInclusion C m) hF hG hf
  change TopPair.of f hF = skeletalStagePair C m at hpair
  change IsGoodPair (TopPair.of f hF) at hgood
  exact hpair ▸ hgood

end Skeleta

/- The accepted sphere witness uses the singleton subtype. The existing wedge
API uses PUnit. Transfer the same witness, leaving its ambient space fixed. -/
private theorem positiveSphereBasedPair_isGoodPair (k : ℕ) :
    IsGoodPair (pointedPair (TopCat.sphere.{u} (k + 1)) (Hatcher.Sphere.northPole.{u} k)) := by
  classical
  let S : TopCat.{u} := TopCat.sphere.{u} (k + 1)
  let b : S := Hatcher.Sphere.northPole.{u} k
  let P : TopPair.{u} := pointedPair S b
  let Q : TopPair.{u} := TopPair.ofSubset ({b} : Set S)
  let h : GoodPairData Q := Hatcher.Sphere.sphereSingletonGoodPairData (k + 1) b
  let V : Set S := h.V
  have hrange : Set.range P.map = Set.range Q.map := by
    ext x
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨⟨b, by simp⟩, rfl⟩
    · rintro ⟨q, rfl⟩
      refine ⟨PUnit.unit, ?_⟩
      change b = q.1
      exact (Set.mem_singleton_iff.mp q.2).symm
  have hV : Set.range P.map ⊆ interior V := by
    rw [hrange]
    exact h.range_subset_interior
  let i : C(P.snd, V) :=
    goodPairNeighborhoodInclusion P V (hV.trans interior_subset)
  let j : C(Q.snd, V) :=
    goodPairNeighborhoodInclusion Q V
      (h.range_subset_interior.trans interior_subset)
  let d : Hatcher.StrongDeformationRetract j := h.strongDeformationRetract
  have hpoint (p : P.snd) : i p = j ⟨b, by simp⟩ := by
    apply Subtype.ext
    rfl
  refine ⟨{ nonempty := ?_
            isClosed_range := ?_
            V := V
            range_subset_interior := hV
            strongDeformationRetract := ?_ }⟩
  · change Nonempty PUnit
    infer_instance
  · rw [hrange]
    exact h.isClosed_range
  · refine
      { retract := ⟨fun _ => PUnit.unit, continuous_const⟩
        retract_inclusion := by
          ext p
          cases p
          rfl
        deformation :=
          { toFun := d.deformation
            continuous_toFun := d.deformation.continuous
            map_zero_left := by
              intro x
              exact d.deformation.apply_zero x
            map_one_left := by
              intro x
              change d.deformation (1, x) = i PUnit.unit
              have hlimit : d.deformation (1, x) = j (d.retract x) :=
                d.deformation.apply_one x
              have htarget : j (d.retract x) = i PUnit.unit := by
                apply Subtype.ext
                exact Set.mem_singleton_iff.mp (d.retract x).2
              exact hlimit.trans htarget
            prop' := by
              intro t x hx
              rcases hx with ⟨p, rfl⟩
              change d.deformation (t, i p) = i p
              have hp : i p = j ⟨b, by simp⟩ := hpoint p
              have hfixed : d.deformation (t, j ⟨b, by simp⟩) = j ⟨b, by simp⟩ :=
                d.deformation.eq_fst t ⟨⟨b, by simp⟩, rfl⟩
              exact (congrArg (fun z : V => d.deformation (t, z)) hp).trans
                (hfixed.trans hp.symm) } }

private noncomputable def positiveSpherePositiveIso (k : ℕ) :
    (Hatcher.Reduced.homologyFunctor.{u} positiveCellCoefficient.{u} (k + 1)).obj
        (TopCat.sphere.{u} (k + 1)) ≅
      ((singularHomologyFunctor.{u} AddCommGrpCat.{u} (k + 1)).obj
        positiveCellCoefficient.{u}).obj (TopCat.sphere.{u} (k + 1)) :=
  (Hatcher.Reduced.homologyIsoOfPositiveDegree.{u}
    positiveCellCoefficient.{u} (k + 1) (Nat.succ_pos k)).app
      (TopCat.sphere.{u} (k + 1))

private noncomputable def positiveSphereOrdinaryFundamentalClass (k : ℕ) :
    positiveCellCoefficient.{u} ⟶
      ((singularHomologyFunctor.{u} AddCommGrpCat.{u} (k + 1)).obj
        positiveCellCoefficient.{u}).obj (TopCat.sphere.{u} (k + 1)) :=
  Hatcher.Sphere.liftedOrderedSphereFundamentalClass.{u} k ≫ (positiveSpherePositiveIso.{u} k).hom

private noncomputable def positiveConeGoodPair (k : ℕ) : GoodPair.{u} :=
  ⟨Hatcher.Sphere.sphereConePair.{u} k, (Hatcher.Sphere.sphere_cone_geometry k).1⟩

private noncomputable def positiveConeQuotientIso (k j : ℕ) :
    (homologyFunctor positiveCellCoefficient.{u} j).obj
        (Hatcher.Sphere.sphereConePair.{u} k) ≅
      (Hatcher.Reduced.homologyFunctor.{u} positiveCellCoefficient.{u} j).obj
        (pointQuotient (Hatcher.Sphere.sphereConePair.{u} k)) :=
  (goodPairPointQuotientRelativeHomologyNatIso positiveCellCoefficient.{u} j).app
    (positiveConeGoodPair.{u} k)

private noncomputable def positiveDiskSphereOrdinaryIso (k : ℕ) :
    (homologyFunctor positiveCellCoefficient.{u} (k + 1)).obj
        (standardDiskBoundaryPair.{u} (k + 1)) ≅
      ((singularHomologyFunctor.{u} AddCommGrpCat.{u} (k + 1)).obj
        positiveCellCoefficient.{u}).obj (TopCat.sphere.{u} (k + 1)) :=
  (homologyFunctor positiveCellCoefficient.{u} (k + 1)).mapIso
      (diskBoundaryPairIsoCone.{u} k) ≪≫
    positiveConeQuotientIso.{u} k (k + 1) ≪≫
    (Hatcher.Reduced.homologyFunctor.{u} positiveCellCoefficient.{u} (k + 1)).mapIso
      (TopCat.isoOfHomeo (Hatcher.Sphere.sphereConeQuotientHomeomorph.{u} k)) ≪≫
    positiveSpherePositiveIso.{u} k

/-- The actual standard disk relative fundamental class with fixed orientation. -/
noncomputable def positiveStandardDiskFundamentalClass (k : ℕ) :
    (AddCommGrpCat.of.{u} (ULift.{u} ℤ)) ⟶
      (homologyFunctor (AddCommGrpCat.of.{u} (ULift.{u} ℤ)) (k + 1)).obj
        (standardDiskBoundaryPair.{u} (k + 1)) :=
  positiveSphereOrdinaryFundamentalClass.{u} k ≫
    (positiveDiskSphereOrdinaryIso.{u} k).inv

private theorem positiveStandardDiskFundamentalClass_cone_formula (k : ℕ) :
    positiveStandardDiskFundamentalClass.{u} k =
      Hatcher.Sphere.liftedOrderedSphereFundamentalClass.{u} k ≫
        (Hatcher.Reduced.homologyFunctor.{u} positiveCellCoefficient.{u} (k + 1)).map
          (TopCat.isoOfHomeo (Hatcher.Sphere.sphereConeQuotientHomeomorph.{u} k)).inv ≫
        (positiveConeQuotientIso.{u} k (k + 1)).inv ≫
        (homologyFunctor positiveCellCoefficient.{u} (k + 1)).map
          (diskBoundaryPairIsoCone.{u} k).inv := by
  dsimp only [positiveStandardDiskFundamentalClass,
    positiveSphereOrdinaryFundamentalClass, positiveDiskSphereOrdinaryIso,
    Iso.trans_inv, Iso.trans_hom, Functor.mapIso_inv]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

section SkeletalHomology

variable {X : Type u} [TopologicalSpace X] [T2Space X]
  (C : Set X) [CWComplex C]

private abbrev positiveSkeletalPair (k : ℕ) : TopPair.{u} := skeletalStagePair C (k + 1)
private abbrev positiveSkeletalCell (k : ℕ) : Type u := RelCWComplex.cell C (k + 1)
private abbrev positiveSkeletalSphereFamily (k : ℕ) : positiveSkeletalCell C k → TopCat.{u} :=
  fun _ => TopCat.sphere.{u} (k + 1)
private abbrev positiveSkeletalSphereBasepoint (k : ℕ) :
    ∀ i : positiveSkeletalCell C k, positiveSkeletalSphereFamily C k i :=
  fun _ => Hatcher.Sphere.northPole.{u} k
private abbrev positiveSkeletalWedge (k : ℕ) : TopCat.{u} :=
  TopCat.of (Hatcher.PointedWedge (fun i => positiveSkeletalSphereFamily C k i)
    (positiveSkeletalSphereBasepoint C k))

private noncomputable def positiveSkeletalGoodPair (k : ℕ)
    (hA : Nonempty (positiveSkeletalPair C k).snd) : GoodPair.{u} :=
  ⟨positiveSkeletalPair C k, positiveSkeletalPair_isGoodPair C k hA⟩

private noncomputable def positiveSkeletalQuotientIso (k : ℕ)
    (hA : Nonempty (positiveSkeletalPair C k).snd) (j : ℕ) :
    (homologyFunctor positiveCellCoefficient.{u} j).obj (positiveSkeletalPair C k) ≅
      (Hatcher.Reduced.homologyFunctor.{u} positiveCellCoefficient.{u} j).obj
        (pointQuotient (positiveSkeletalPair C k)) :=
  (goodPairPointQuotientRelativeHomologyNatIso positiveCellCoefficient.{u} j).app
    (positiveSkeletalGoodPair C k hA)

private noncomputable def positiveSkeletalWedgeComparison (k : ℕ)
    (hA : Nonempty (positiveSkeletalPair C k).snd) (j : ℕ) :
    (homologyFunctor positiveCellCoefficient.{u} j).obj (positiveSkeletalPair C k) ≅
      (Hatcher.Reduced.homologyFunctor.{u} positiveCellCoefficient.{u} j).obj
        (positiveSkeletalWedge C k) :=
  positiveSkeletalQuotientIso C k hA j ≪≫
    (Hatcher.Reduced.homologyFunctor.{u} positiveCellCoefficient.{u} j).mapIso
      (skeletonPointQuotientIsoWedge C k)

private noncomputable def positiveWedgeHomologyIso (k j : ℕ) :
    (∐ fun i : positiveSkeletalCell C k =>
      (Hatcher.Reduced.homologyFunctor.{u} positiveCellCoefficient.{u} j).obj
        (positiveSkeletalSphereFamily C k i)) ≅
      (Hatcher.Reduced.homologyFunctor.{u} positiveCellCoefficient.{u} j).obj
        (positiveSkeletalWedge C k) := by
  let f := Hatcher.PointedWedge.reducedHomologyCoproductMap
    (positiveSkeletalSphereFamily C k) (positiveSkeletalSphereBasepoint C k)
    positiveCellCoefficient.{u} j
  let hf : IsIso f := Hatcher.PointedWedge.reducedHomologyCoproductMap_isIso
    (positiveSkeletalSphereFamily C k) (positiveSkeletalSphereBasepoint C k)
    (fun _ => positiveSphereBasedPair_isGoodPair.{u} k) positiveCellCoefficient.{u} j
  exact @asIso AddCommGrpCat.{u} _ _ _ f hf

omit [T2Space X] in
private theorem positiveWedgeHomologyIso_hom (k j : ℕ) :
    (positiveWedgeHomologyIso C k j).hom =
      Hatcher.PointedWedge.reducedHomologyCoproductMap
        (positiveSkeletalSphereFamily C k) (positiveSkeletalSphereBasepoint C k)
        positiveCellCoefficient.{u} j := rfl

private noncomputable def positiveWedgeCellBasisIso (k : ℕ) :
    (∐ fun _ : positiveSkeletalCell C k => positiveCellCoefficient.{u}) ≅
      (Hatcher.Reduced.homologyFunctor.{u} positiveCellCoefficient.{u} (k + 1)).obj
        (positiveSkeletalWedge C k) :=
  (Sigma.mapIso fun _ : positiveSkeletalCell C k =>
    @asIso AddCommGrpCat.{u} _ _ _ (Hatcher.Sphere.liftedOrderedSphereFundamentalClass.{u} k)
      (Hatcher.Sphere.liftedOrderedSphereFundamentalClass_isIso.{u} k)) ≪≫
    positiveWedgeHomologyIso C k (k + 1)

omit [T2Space X] in
private theorem positiveWedgeCellBasisIso_ι (k : ℕ) (i : positiveSkeletalCell C k) :
    Sigma.ι (fun _ : positiveSkeletalCell C k => positiveCellCoefficient.{u}) i ≫
        (positiveWedgeCellBasisIso C k).hom =
      Hatcher.Sphere.liftedOrderedSphereFundamentalClass.{u} k ≫
        (Hatcher.Reduced.homologyFunctor.{u} positiveCellCoefficient.{u} (k + 1)).map
          (pointedWedgeSummandInclusion (positiveSkeletalSphereBasepoint C k) i) := by
  dsimp only [positiveWedgeCellBasisIso, Iso.trans_hom]
  rw [← Category.assoc, Sigma.ι_mapIso_hom]
  rw [Category.assoc, positiveWedgeHomologyIso_hom]
  rw [Hatcher.PointedWedge.ι_reducedHomologyCoproductMap]
  rfl

/-- The relative class induced by the actual standardized characteristic map. -/
noncomputable def positiveSkeletonCellFundamentalClass (k : ℕ)
    (i : RelCWComplex.cell C (k + 1)) :
    (homologyFunctor (AddCommGrpCat.of.{u} (ULift.{u} ℤ)) (k + 1)).obj (skeletalStagePair C (k + 1)) :=
  (positiveStandardDiskFundamentalClass.{u} k ≫
    (homologyFunctor positiveCellCoefficient.{u} (k + 1)).map
      (skeletalStageCellPairMap C (k + 1) i)) (ULift.up (1 : ℤ))

private theorem positiveConeCellQuotient_square (k : ℕ) (i : positiveSkeletalCell C k) :
    pointQuotientMap ((diskBoundaryPairIsoCone.{u} k).inv ≫
        skeletalStageCellPairMap C (k + 1) i) ≫
        (skeletonPointQuotientIsoWedge C k).hom =
      (TopCat.isoOfHomeo (Hatcher.Sphere.sphereConeQuotientHomeomorph.{u} k)).hom ≫
        pointedWedgeSummandInclusion (positiveSkeletalSphereBasepoint C k) i := by
  let e := diskBoundaryPairIsoCone.{u} k
  have hinv : pointQuotientMap e.inv ≫ pointQuotientMap e.hom = 𝟙 _ := by
    rw [← pointQuotientMap_comp, e.inv_hom_id, pointQuotientMap_id]
  rw [pointQuotientMap_comp, Category.assoc,
    skeletonPointQuotientIsoWedge_pairMap, diskBoundaryPointQuotientIsoSphere_hom]
  change pointQuotientMap e.inv ≫
    (pointQuotientMap e.hom ≫
      (TopCat.isoOfHomeo (Hatcher.Sphere.sphereConeQuotientHomeomorph.{u} k)).hom) ≫ _ = _
  simp only [Category.assoc]
  rw [← Category.assoc (pointQuotientMap e.inv) (pointQuotientMap e.hom)
    ((TopCat.isoOfHomeo (Hatcher.Sphere.sphereConeQuotientHomeomorph.{u} k)).hom ≫
      pointedWedgeSummandInclusion (positiveSkeletalSphereBasepoint C k) i),
    hinv, Category.id_comp]

private theorem positiveSkeletonCell_class_to_wedge (k : ℕ)
    (hA : Nonempty (positiveSkeletalPair C k).snd) (i : positiveSkeletalCell C k) :
    positiveStandardDiskFundamentalClass.{u} k ≫
        (homologyFunctor positiveCellCoefficient.{u} (k + 1)).map
          (skeletalStageCellPairMap C (k + 1) i) ≫
        (positiveSkeletalWedgeComparison C k hA (k + 1)).hom =
      Hatcher.Sphere.liftedOrderedSphereFundamentalClass.{u} k ≫
        (Hatcher.Reduced.homologyFunctor.{u} positiveCellCoefficient.{u} (k + 1)).map
          (pointedWedgeSummandInclusion (positiveSkeletalSphereBasepoint C k) i) := by
  let F := homologyFunctor positiveCellCoefficient.{u} (k + 1)
  let H := Hatcher.Reduced.homologyFunctor.{u} positiveCellCoefficient.{u} (k + 1)
  let g : Hatcher.Sphere.sphereConePair.{u} k ⟶ positiveSkeletalPair C k :=
    (diskBoundaryPairIsoCone.{u} k).inv ≫ skeletalStageCellPairMap C (k + 1) i
  let f : positiveConeGoodPair.{u} k ⟶ positiveSkeletalGoodPair C k hA :=
    ObjectProperty.homMk g
  have hn := (goodPairPointQuotientRelativeHomologyNatIso
    positiveCellCoefficient.{u} (k + 1)).hom.naturality f
  change F.map g ≫ (positiveSkeletalQuotientIso C k hA (k + 1)).hom =
    (positiveConeQuotientIso.{u} k (k + 1)).hom ≫ H.map (pointQuotientMap g) at hn
  have htop := positiveConeCellQuotient_square C k i
  let A := positiveConeQuotientIso.{u} k (k + 1)
  let B := positiveSkeletalQuotientIso C k hA (k + 1)
  let e := TopCat.isoOfHomeo (Hatcher.Sphere.sphereConeQuotientHomeomorph.{u} k)
  let v := pointedWedgeSummandInclusion (positiveSkeletalSphereBasepoint C k) i
  have hp : F.map (diskBoundaryPairIsoCone.{u} k).inv ≫
      F.map (skeletalStageCellPairMap C (k + 1) i) ≫ B.hom =
      A.hom ≫ H.map (pointQuotientMap g) := by
    calc
      _ = (F.map (diskBoundaryPairIsoCone.{u} k).inv ≫
          F.map (skeletalStageCellPairMap C (k + 1) i)) ≫ B.hom :=
        (Category.assoc _ _ _).symm
      _ = F.map g ≫ B.hom := by rw [← F.map_comp]
      _ = _ := hn
  have hp' : A.inv ≫ (F.map (diskBoundaryPairIsoCone.{u} k).inv ≫
      F.map (skeletalStageCellPairMap C (k + 1) i) ≫ B.hom) =
      H.map (pointQuotientMap g) := by
    rw [hp]
    exact A.inv_hom_id_assoc _
  have hm : H.map (pointQuotientMap g) ≫
      H.map (skeletonPointQuotientIsoWedge C k).hom =
      H.map e.hom ≫ H.map v := by
    calc
      _ = H.map (pointQuotientMap g ≫ (skeletonPointQuotientIsoWedge C k).hom) :=
        (H.map_comp _ _).symm
      _ = H.map (e.hom ≫ v) := H.congr_map htop
      _ = _ := H.map_comp _ _
  have hm' : H.map e.inv ≫ H.map (pointQuotientMap g) ≫
      H.map (skeletonPointQuotientIsoWedge C k).hom = H.map v := by
    rw [hm]
    rw [← Category.assoc, ← H.map_comp, e.inv_hom_id, H.map_id, Category.id_comp]
  rw [positiveStandardDiskFundamentalClass_cone_formula]
  change Hatcher.Sphere.liftedOrderedSphereFundamentalClass.{u} k ≫ H.map e.inv ≫ A.inv ≫
      F.map (diskBoundaryPairIsoCone.{u} k).inv ≫
      F.map (skeletalStageCellPairMap C (k + 1) i) ≫ B.hom ≫
      H.map (skeletonPointQuotientIsoWedge C k).hom = _
  calc
    _ = Hatcher.Sphere.liftedOrderedSphereFundamentalClass.{u} k ≫ H.map e.inv ≫
        (A.inv ≫ (F.map (diskBoundaryPairIsoCone.{u} k).inv ≫
          F.map (skeletalStageCellPairMap C (k + 1) i) ≫ B.hom)) ≫
        H.map (skeletonPointQuotientIsoWedge C k).hom := by
      simp only [Category.assoc]
    _ = Hatcher.Sphere.liftedOrderedSphereFundamentalClass.{u} k ≫ H.map e.inv ≫
        H.map (pointQuotientMap g) ≫
        H.map (skeletonPointQuotientIsoWedge C k).hom := by rw [hp']
    _ = Hatcher.Sphere.liftedOrderedSphereFundamentalClass.{u} k ≫ H.map v := by rw [hm']

private noncomputable def positiveIntegerCoproductIso (k : ℕ) :
    (∐ fun _ : positiveSkeletalCell C k => positiveCellCoefficient.{u}) ≅
      AddCommGrpCat.of.{u} (positiveSkeletalCell C k →₀ ULift.{u} ℤ) :=
  let F := forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}
  let cofan := F.mapCocone
    (ModuleCat.finsuppCocone ℤ (ULift.{u} ℤ) (positiveSkeletalCell C k))
  let hc : IsColimit cofan := isColimitOfPreserves F
    (ModuleCat.finsuppCoconeIsColimit ℤ (ULift.{u} ℤ) (positiveSkeletalCell C k))
  (colimit.isColimit (Discrete.functor
    (fun _ : positiveSkeletalCell C k => positiveCellCoefficient.{u}))).coconePointUniqueUpToIso hc

omit [T2Space X] in
private theorem positiveIntegerCoproductIso_ι (k : ℕ) (i : positiveSkeletalCell C k)
    (a : ULift.{u} ℤ) :
    (positiveIntegerCoproductIso C k).hom
        (Sigma.ι (fun _ : positiveSkeletalCell C k => positiveCellCoefficient.{u}) i a) =
      Finsupp.single i a := by
  have h := IsColimit.comp_coconePointUniqueUpToIso_hom
    (colimit.isColimit (Discrete.functor
      (fun _ : positiveSkeletalCell C k => positiveCellCoefficient.{u})))
    (isColimitOfPreserves (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u})
      (ModuleCat.finsuppCoconeIsColimit ℤ (ULift.{u} ℤ)
        (positiveSkeletalCell C k))) (Discrete.mk i)
  exact ConcreteCategory.congr_hom h a

private noncomputable def positiveCellLowerEquiv (k : ℕ) :
    (positiveSkeletalCell C k →₀ ULift.{u} ℤ) ≃+
      (positiveSkeletalCell C k →₀ ℤ) where
  toFun := Finsupp.mapRange ULift.down rfl
  invFun := Finsupp.mapRange ULift.up rfl
  left_inv := by intro a; ext i; rfl
  right_inv := by intro a; ext i; rfl
  map_add' := by intro a b; ext i; rfl

private noncomputable def positiveIntegerFinsuppIso (k : ℕ) :
    (∐ fun _ : positiveSkeletalCell C k => positiveCellCoefficient.{u}) ≅
      AddCommGrpCat.of.{u} (positiveSkeletalCell C k →₀ ℤ) :=
  positiveIntegerCoproductIso C k ≪≫ (positiveCellLowerEquiv C k).toAddCommGrpIso

omit [T2Space X] in
private theorem positiveIntegerFinsuppIso_ι (k : ℕ) (i : positiveSkeletalCell C k)
    (a : ULift.{u} ℤ) :
    (positiveIntegerFinsuppIso C k).hom
        (Sigma.ι (fun _ : positiveSkeletalCell C k => positiveCellCoefficient.{u}) i a) =
      Finsupp.single i a.down := by
  change positiveCellLowerEquiv C k
    ((positiveIntegerCoproductIso C k).hom
      (Sigma.ι (fun _ : positiveSkeletalCell C k => positiveCellCoefficient.{u}) i a)) = _
  rw [positiveIntegerCoproductIso_ι]
  change Finsupp.mapRange ULift.down rfl (Finsupp.single i a) = Finsupp.single i a.down
  classical
  ext j
  by_cases h : i = j
  · subst j
    simp
  · simp [h]

private noncomputable def positiveSkeletonCellBasisIso (k : ℕ)
    (hA : Nonempty (positiveSkeletalPair C k).snd) :
    (homologyFunctor positiveCellCoefficient.{u} (k + 1)).obj (positiveSkeletalPair C k) ≅
      AddCommGrpCat.of.{u} (positiveSkeletalCell C k →₀ ℤ) :=
  positiveSkeletalWedgeComparison C k hA (k + 1) ≪≫
    (positiveWedgeCellBasisIso C k).symm ≪≫ positiveIntegerFinsuppIso C k

private theorem positiveSkeletonCellBasisIso_class (k : ℕ)
    (hA : Nonempty (positiveSkeletalPair C k).snd) (i : positiveSkeletalCell C k) :
    (positiveSkeletonCellBasisIso C k hA).hom (positiveSkeletonCellFundamentalClass C k i) =
      Finsupp.single i 1 := by
  let R : AddCommGrpCat.{u} := positiveCellCoefficient.{u}
  let T := positiveSkeletalWedgeComparison C k hA (k + 1)
  let B := positiveWedgeCellBasisIso C k
  let A := positiveIntegerFinsuppIso C k
  let c : R ⟶ (homologyFunctor R (k + 1)).obj (positiveSkeletalPair C k) :=
    positiveStandardDiskFundamentalClass.{u} k ≫
      (homologyFunctor R (k + 1)).map (skeletalStageCellPairMap C (k + 1) i)
  let ι : R ⟶ (∐ fun _ : positiveSkeletalCell C k => R) := Sigma.ι (fun _ => R) i
  have hcell : c ≫ T.hom = ι ≫ B.hom :=
    (positiveSkeletonCell_class_to_wedge C k hA i).trans
      (positiveWedgeCellBasisIso_ι C k i).symm
  have hpost := congrArg (fun f => f ≫ B.inv ≫ A.hom) hcell
  have hassoc : c ≫ T.hom ≫ B.inv ≫ A.hom = ι ≫ B.hom ≫ B.inv ≫ A.hom := by
    simpa only [Category.assoc] using hpost
  have hcancel : B.hom ≫ B.inv ≫ A.hom = A.hom := B.hom_inv_id_assoc A.hom
  have h : c ≫ T.hom ≫ B.inv ≫ A.hom = ι ≫ A.hom :=
    hassoc.trans (congrArg (fun f => ι ≫ f) hcancel)
  have hv := ConcreteCategory.congr_hom h (ULift.up (1 : ℤ))
  change (positiveSkeletonCellBasisIso C k hA).hom
      (positiveSkeletonCellFundamentalClass C k i) =
    (positiveIntegerFinsuppIso C k).hom
      (Sigma.ι (fun _ : positiveSkeletalCell C k => positiveCellCoefficient.{u}) i
        (ULift.up (1 : ℤ))) at hv
  exact hv.trans (positiveIntegerFinsuppIso_ι C k i (ULift.up (1 : ℤ)))

private theorem positiveSkeletonCellBasisIso_inv_single (k : ℕ)
    (hA : Nonempty (positiveSkeletalPair C k).snd) (i : positiveSkeletalCell C k) :
    (positiveSkeletonCellBasisIso C k hA).inv (Finsupp.single i 1) =
      positiveSkeletonCellFundamentalClass C k i := by
  rw [← positiveSkeletonCellBasisIso_class C k hA i]
  exact (positiveSkeletonCellBasisIso C k hA).hom_inv_id_apply _

private theorem positiveSkeleton_offDiagonal_isZero (k : ℕ)
    (hA : Nonempty (positiveSkeletalPair C k).snd) (j : ℕ) (hj : j ≠ k + 1) :
    IsZero ((homologyFunctor positiveCellCoefficient.{u} j).obj (positiveSkeletalPair C k)) := by
  let Z : positiveSkeletalCell C k → AddCommGrpCat.{u} :=
    fun i => (Hatcher.Reduced.homologyFunctor.{u} positiveCellCoefficient.{u} j).obj
      (positiveSkeletalSphereFamily C k i)
  have hz : ∀ i, IsZero (Z i) := fun _ =>
    (Hatcher.Sphere.reducedHomology_sphere positiveCellCoefficient.{u} (k + 1)).2 j hj
  have hsum : IsZero (∐ Z) := by
    apply (IsZero.iff_id_eq_zero (∐ Z)).mpr
    apply Sigma.hom_ext
    intro i
    rw [Category.comp_id, comp_zero]
    exact (hz i).eq_of_src _ _
  have hw : IsZero
      ((Hatcher.Reduced.homologyFunctor.{u} positiveCellCoefficient.{u} j).obj
        (positiveSkeletalWedge C k)) :=
    hsum.of_iso (positiveWedgeHomologyIso C k j).symm
  exact hw.of_iso (positiveSkeletalWedgeComparison C k hA j)

private theorem positiveSkeletalCells_isEmpty (k : ℕ)
    [IsEmpty (positiveSkeletalPair C k).snd] : IsEmpty (positiveSkeletalCell C k) := by
  classical
  refine ⟨fun i => ?_⟩
  let h : GoodPairData (Hatcher.Sphere.sphereConePair.{u} k) :=
    Classical.choice (Hatcher.Sphere.sphere_cone_geometry k).1
  let b : (Hatcher.Sphere.sphereConePair.{u} k).snd := Classical.choice h.nonempty
  let bd : (standardDiskBoundaryPair.{u} (k + 1)).snd :=
    TopPair.Hom.snd (diskBoundaryPairIsoCone.{u} k).inv b
  exact IsEmpty.false (TopPair.Hom.snd (skeletalStageCellPairMap C (k + 1) i) bd)

private theorem positiveSkeletalSuccessor_isEmpty (k : ℕ)
    [IsEmpty (positiveSkeletalPair C k).snd] [IsEmpty (positiveSkeletalCell C k)] :
    IsEmpty (positiveSkeletalPair C k).fst := by
  have hOld : IsEmpty ↑(RelCWComplex.skeletonLT C ((k + 1 : ℕ) : ℕ∞) : Set X) := by
    change IsEmpty (positiveSkeletalPair C k).snd
    infer_instance
  refine ⟨fun x => ?_⟩
  obtain ⟨z, hz⟩ := (skeletonLTStepJointMap_isQuotient C (k + 1)).surjective x
  rcases z with a | ⟨i, z⟩
  · exact @IsEmpty.false _ hOld a
  · exact IsEmpty.false i

private theorem positiveEmptySkeletalHomology_isZero (k j : ℕ)
    [IsEmpty (positiveSkeletalPair C k).fst] :
    IsZero ((homologyFunctor positiveCellCoefficient.{u} j).obj (positiveSkeletalPair C k)) := by
  let P : TopPair.{u} := positiveSkeletalPair C k
  have hEmpty : IsEmpty P.fst := by
    change IsEmpty (positiveSkeletalPair C k).fst
    infer_instance
  let f : P.fst → P.snd := fun x => (@IsEmpty.false _ hEmpty x).elim
  have hf : Continuous f := by
    apply continuous_def.mpr
    intro U _hU
    have he : f ⁻¹' U = ∅ := by
      ext x
      exact (@IsEmpty.false _ hEmpty x).elim
    rw [he]
    exact isOpen_empty
  let g : P.fst ⟶ P.snd := TopCat.ofHom ⟨f, hf⟩
  have hg : TopPair.Hom.fst (𝟙 P) = g ≫ P.map := by
    ext x
    exact (@IsEmpty.false _ hEmpty x).elim
  let F : TopPair.{u} ⥤ AddCommGrpCat.{u} := homologyFunctor positiveCellCoefficient.{u} j
  have h : F.map (𝟙 P) = 0 :=
    Hatcher.Relative.homologyFunctor_map_eq_zero_of_factors_through_subspace
      (𝟙 P) g hg positiveCellCoefficient.{u} j
  apply (IsZero.iff_id_eq_zero (F.obj P)).mpr
  exact (F.map_id P).symm.trans h

omit [T2Space X] in
private theorem positiveEmptyFinsupp_isZero (k : ℕ) [IsEmpty (positiveSkeletalCell C k)] :
    IsZero (AddCommGrpCat.of.{u} (positiveSkeletalCell C k →₀ ℤ)) := by
  apply (IsZero.iff_id_eq_zero
    (AddCommGrpCat.of.{u} (positiveSkeletalCell C k →₀ ℤ))).mpr
  ext a i
  exact (IsEmpty.false i).elim

/-- Hatcher Lemma 2.34(a), positive-dimensional ordinary relative groups with
their actual characteristic-map generators; arbitrary and empty CW complexes. -/
theorem positiveSkeletonRelativeHomology (k : ℕ) :
    (∀ j : ℕ, j ≠ k + 1 →
      IsZero ((homologyFunctor (AddCommGrpCat.of.{u} (ULift.{u} ℤ)) j).obj
        (skeletalStagePair C (k + 1)))) ∧
    ∃ E : (homologyFunctor (AddCommGrpCat.of.{u} (ULift.{u} ℤ)) (k + 1)).obj
          (skeletalStagePair C (k + 1)) ≅
        AddCommGrpCat.of.{u} (RelCWComplex.cell C (k + 1) →₀ ℤ),
      ∀ i : RelCWComplex.cell C (k + 1),
        E.inv (Finsupp.single i 1) = positiveSkeletonCellFundamentalClass C k i := by
  classical
  rcases isEmpty_or_nonempty (positiveSkeletalPair C k).snd with he | hn
  · let _ : IsEmpty (positiveSkeletalPair C k).snd := he
    let _ : IsEmpty (positiveSkeletalCell C k) := positiveSkeletalCells_isEmpty C k
    let _ : IsEmpty (positiveSkeletalPair C k).fst := positiveSkeletalSuccessor_isEmpty C k
    have hsource := positiveEmptySkeletalHomology_isZero C k (k + 1)
    have htarget := positiveEmptyFinsupp_isZero C k
    let f : (homologyFunctor positiveCellCoefficient.{u} (k + 1)).obj
        (positiveSkeletalPair C k) ⟶
        AddCommGrpCat.of.{u} (positiveSkeletalCell C k →₀ ℤ) := 0
    let hf : IsIso f := hsource.isIso htarget f
    refine ⟨fun j _ => positiveEmptySkeletalHomology_isZero C k j,
      @asIso AddCommGrpCat.{u} _ _ _ f hf, ?_⟩
    intro i
    exact (IsEmpty.false i).elim
  · exact ⟨positiveSkeleton_offDiagonal_isZero C k hn,
      positiveSkeletonCellBasisIso C k hn,
      positiveSkeletonCellBasisIso_inv_single C k hn⟩

end SkeletalHomology

end Hatcher.ClassicalCW

noncomputable section

namespace Hatcher.ClassicalCW

open CategoryTheory CategoryTheory.Limits _root_.Topology
open Hatcher.Relative

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X]
  (C : Set X) [CWComplex C]

/-- The actual characteristic class in every cell dimension, including the
ordinary characteristic-point class in dimension zero. -/
noncomputable def skeletalCellFundamentalClass (n : ℕ)
    (i : RelCWComplex.cell C n) :
    (homologyFunctor (AddCommGrpCat.of.{u} (ULift.{u} ℤ)) n).obj
      (skeletalStagePair C n) := by
  cases n with
  | zero =>
      change (homologyFunctor (AddCommGrpCat.of.{u} (ULift.{u} ℤ)) 0).obj
        (zeroSkeletonPair C)
      exact zeroCellRelativeClass C i
  | succ k => exact positiveSkeletonCellFundamentalClass C k i

@[simp]
theorem skeletalCellFundamentalClass_zero (i : RelCWComplex.cell C 0) :
    skeletalCellFundamentalClass C 0 i = zeroCellRelativeClass C i := rfl

@[simp]
theorem skeletalCellFundamentalClass_succ (k : ℕ)
    (i : RelCWComplex.cell C (k + 1)) :
    skeletalCellFundamentalClass C (k + 1) i =
      positiveSkeletonCellFundamentalClass C k i := rfl

/-- Hatcher Lemma 2.34(a): ordinary skeletal relative homology in all degrees,
with the standard vectors sent to the actual characteristic classes. -/
theorem skeletonRelativeHomology (n : ℕ) :
    (∀ k : ℕ, k ≠ n →
      IsZero ((homologyFunctor (AddCommGrpCat.of.{u} (ULift.{u} ℤ)) k).obj
        (skeletalStagePair C n))) ∧
    ∃ E : (homologyFunctor (AddCommGrpCat.of.{u} (ULift.{u} ℤ)) n).obj
          (skeletalStagePair C n) ≅
        AddCommGrpCat.of.{u} (RelCWComplex.cell C n →₀ ℤ),
      ∀ i : RelCWComplex.cell C n,
        E.inv (Finsupp.single i 1) = skeletalCellFundamentalClass C n i := by
  cases n with
  | zero =>
      obtain ⟨hz, E, hE⟩ := zeroSkeletonRelativeHomology C
      refine ⟨?_, E, ?_⟩
      · intro k hk
        have hpos : 0 < k := by
          cases k with
          | zero => exact (hk rfl).elim
          | succ k => exact Nat.zero_lt_succ k
        exact hz k hpos
      · intro i
        exact hE i
  | succ k => exact positiveSkeletonRelativeHomology C k

end Hatcher.ClassicalCW

noncomputable section

namespace Hatcher.ClassicalCW

open CategoryTheory CategoryTheory.Limits _root_.Topology

universe u

/-- Hatcher Lemma 2.34(c), one-stage form, for the actual skeleton inclusion.
The ordinary degree-zero window and the empty initial stage are included. -/
theorem skeletonStepHomologyStability
    {X : Type u} [TopologicalSpace X] [T2Space X]
    (C : Set X) [CWComplex C] (p k : ℕ) :
    let P : TopPair.{u} := skeletalStagePair C p
    let R : AddCommGrpCat.{u} := AddCommGrpCat.of.{u} (ULift.{u} ℤ)
    let H : TopCat.{u} ⥤ AddCommGrpCat.{u} :=
      (AlgebraicTopology.singularHomologyFunctor AddCommGrpCat.{u} k).obj R
    let i := H.map P.map
    (k ≠ p → Function.Surjective i) ∧
    (k + 1 ≠ p → Function.Injective i) ∧
    (k ≠ p → k + 1 ≠ p → IsIso i) := by
  let P : TopPair.{u} := skeletalStagePair C p
  let R : AddCommGrpCat.{u} := AddCommGrpCat.of.{u} (ULift.{u} ℤ)
  let H : TopCat.{u} ⥤ AddCommGrpCat.{u} :=
    (AlgebraicTopology.singularHomologyFunctor AddCommGrpCat.{u} k).obj R
  let i : H.obj P.snd ⟶ H.obj P.fst := H.map P.map
  change (k ≠ p → Function.Surjective i) ∧
    (k + 1 ≠ p → Function.Injective i) ∧
    (k ≠ p → k + 1 ≠ p → IsIso i)
  let Q : SSetPair.{u} := Hatcher.Relative.singularPairFunctor.obj P
  let δ : (Hatcher.Relative.homologyFunctor R (k + 1)).obj P ⟶ H.obj P.snd :=
    Hatcher.Relative.pairConnecting P R (k + 1) k rfl
  let π : H.obj P.fst ⟶ (Hatcher.Relative.homologyFunctor R k).obj P :=
    Q.homologyπ R k
  let L : ComposableArrows AddCommGrpCat.{u} 5 :=
    Hatcher.Relative.pairSequence P R (k + 1) k rfl
  have hL : L.Exact := Hatcher.Relative.pairSequence_exact P R (k + 1) k rfl
  have hiL : L.map' 3 4 = i := by
    rfl
  have hrel (q : ℕ) (hq : q ≠ p) :
      IsZero ((Hatcher.Relative.homologyFunctor R q).obj P) :=
    (skeletonRelativeHomology C p).1 q hq
  have hmono (hk : k + 1 ≠ p) : Mono i := by
    have hδ : δ = 0 := (hrel (k + 1) hk).eq_zero_of_src δ
    have hδL : L.map' 2 3 = 0 := by
      change δ = 0
      exact hδ
    have hm : Mono (L.map' 3 4) := (hL.exact 2 (by decide)).mono_g hδL
    rw [hiL] at hm
    exact hm
  have hepi (hk : k ≠ p) : Epi i := by
    have hπ : π = 0 := (hrel k hk).eq_zero_of_tgt π
    have hπL : L.map' 4 5 = 0 := by
      change π = 0
      exact hπ
    have he : Epi (L.map' 3 4) := (hL.exact 3 (by decide)).epi_f hπL
    rw [hiL] at he
    exact he
  refine ⟨?_, ?_, ?_⟩
  · intro hk
    exact (AddCommGrpCat.epi_iff_surjective i).mp (hepi hk)
  · intro hk
    exact (AddCommGrpCat.mono_iff_injective i).mp (hmono hk)
  · intro hk hk'
    letI : Mono i := hmono hk'
    letI : Epi i := hepi hk
    exact isIso_of_mono_of_epi i

end Hatcher.ClassicalCW

end

noncomputable section

namespace Hatcher.ClassicalCW

open AlgebraicTopology CategoryTheory CategoryTheory.Limits _root_.Topology

universe u

private abbrev skeletonVanishingCoefficient : AddCommGrpCat.{u} :=
  AddCommGrpCat.of.{u} (ULift.{u} ℤ)

private abbrev skeletonVanishingHomology (k : ℕ) : TopCat.{u} ⥤ AddCommGrpCat.{u} :=
  (singularHomologyFunctor AddCommGrpCat.{u} k).obj skeletonVanishingCoefficient.{u}

variable {X : Type u} [TopologicalSpace X] [T2Space X]
  (C : Set X) [CWComplex C]

private abbrev skeletonVanishingTop (n : ℕ) : TopCat.{u} :=
  TopCat.of ↑(CWComplex.skeleton C (n : ℕ∞) : Set X)

private theorem skeletonVanishing_standard_strict (n : ℕ) :
    (CWComplex.skeleton C (n : ℕ∞) : Set X) =
      (RelCWComplex.skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X) := by
  change (RelCWComplex.skeletonLT C ((n : ℕ∞) + 1) : Set X) =
    (RelCWComplex.skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X)
  exact congrArg (fun p : ℕ∞ ↦ (RelCWComplex.skeletonLT C p : Set X))
    (by simp only [Nat.cast_add, Nat.cast_one])

private noncomputable def skeletonVanishingStepSourceIso (n : ℕ) :
    skeletonVanishingTop C n ≅ (skeletalStagePair C (n + 1)).snd :=
  TopCat.isoOfHomeo (Homeomorph.setCongr (skeletonVanishing_standard_strict C n))

/- The pinned skeleton constructor requires T2Space X even in its carrier
statements, so this helper retains that genuinely used instance. -/
private noncomputable def skeletonVanishingStepTargetIso (n : ℕ) :
    (skeletalStagePair C (n + 1)).fst ≅ skeletonVanishingTop C (n + 1) := by
  have hcast : (((n + 1 : ℕ) : ℕ∞) + 1) = (((n + 1) + 1 : ℕ) : ℕ∞) := by
    simp only [Nat.cast_add, Nat.cast_one]
  have h : (RelCWComplex.skeletonLT C (((n + 1 : ℕ) : ℕ∞) + 1) : Set X) =
      (CWComplex.skeleton C ((n + 1 : ℕ) : ℕ∞) : Set X) :=
    (congrArg (fun p : ℕ∞ ↦ (RelCWComplex.skeletonLT C p : Set X)) hcast).trans
      (skeletonVanishing_standard_strict C (n + 1)).symm
  exact TopCat.isoOfHomeo (Homeomorph.setCongr h)

/-- Ordinary integral homology of the actual n-skeleton vanishes strictly
above n, without any bound on its number of cells. -/
theorem skeletonHomologyVanishing (n k : ℕ) (hnk : n < k) :
    IsZero (((singularHomologyFunctor AddCommGrpCat.{u} k).obj
      (AddCommGrpCat.of.{u} (ULift.{u} ℤ))).obj
        (TopCat.of ↑(CWComplex.skeleton C (n : ℕ∞) : Set X))) := by
  induction n generalizing k with
  | zero =>
      let R : AddCommGrpCat.{u} := skeletonVanishingCoefficient.{u}
      let H : TopCat.{u} ⥤ AddCommGrpCat.{u} := skeletonVanishingHomology.{u} k
      let Z : TopCat.{u} := TopCat.of (WithDiscreteTopology (RelCWComplex.cell C 0))
      let e : Z ≅ skeletonVanishingTop C 0 :=
        TopCat.isoOfHomeo (zeroSkeletonHomeomorphCells C)
      let _ : TotallyDisconnectedSpace Z := inferInstance
      have hz : IsZero (H.obj Z) :=
        isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
          AddCommGrpCat.{u} k R Z (Nat.ne_of_gt hnk)
      exact hz.of_iso (H.mapIso e).symm
  | succ n ih =>
      let R : AddCommGrpCat.{u} := skeletonVanishingCoefficient.{u}
      let H : TopCat.{u} ⥤ AddCommGrpCat.{u} := skeletonVanishingHomology.{u} k
      let P : TopPair.{u} := skeletalStagePair C (n + 1)
      let a : skeletonVanishingTop C n ≅ P.snd := skeletonVanishingStepSourceIso C n
      let i : H.obj P.snd ⟶ H.obj P.fst := H.map P.map
      have hk : k ≠ n + 1 := Nat.ne_of_gt hnk
      have hk' : k + 1 ≠ n + 1 :=
        Nat.ne_of_gt (Nat.lt_trans hnk (Nat.lt_succ_self k))
      have hi : IsIso i := (skeletonStepHomologyStability C (n + 1) k).2.2 hk hk'
      let _ : IsIso i := hi
      let b : P.fst ≅ skeletonVanishingTop C (n + 1) :=
        skeletonVanishingStepTargetIso C n
      let e : H.obj (skeletonVanishingTop C n) ≅
          H.obj (skeletonVanishingTop C (n + 1)) :=
        H.mapIso a ≪≫ asIso i ≪≫ H.mapIso b
      have hz : IsZero (H.obj (skeletonVanishingTop C n)) :=
        ih k (Nat.lt_trans (Nat.lt_succ_self n) hnk)
      exact hz.of_iso e.symm

/-- A genuine equality of the actual skeleton with the complex transfers the
same ordinary vanishing result to the whole space. -/
theorem homologyVanishingOfSkeletonEq (n k : ℕ)
    (hbound : (CWComplex.skeleton C (n : ℕ∞) : Set X) = C) (hnk : n < k) :
    IsZero (((singularHomologyFunctor AddCommGrpCat.{u} k).obj
      (AddCommGrpCat.of.{u} (ULift.{u} ℤ))).obj (TopCat.of ↑C)) := by
  let H : TopCat.{u} ⥤ AddCommGrpCat.{u} := skeletonVanishingHomology.{u} k
  let e : skeletonVanishingTop C n ≅ TopCat.of ↑C :=
    TopCat.isoOfHomeo (Homeomorph.setCongr hbound)
  exact (skeletonHomologyVanishing C n k hnk).of_iso (H.mapIso e).symm

private theorem skeletonEqOfCellDimensionBound (n : ℕ)
    (hbound : ∀ m : ℕ, n < m → IsEmpty (RelCWComplex.cell C m)) :
    (CWComplex.skeleton C (n : ℕ∞) : Set X) = C := by
  apply Set.Subset.antisymm (CWComplex.skeleton C (n : ℕ∞)).subset_complex
  intro x hx
  rw [← CWComplex.iUnion_openCell_eq_complex (C := C)] at hx
  obtain ⟨m, hx⟩ := Set.mem_iUnion.mp hx
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
  by_cases hm : m ≤ n
  · exact (CWComplex.skeleton_mono (C := C) (Nat.cast_le.mpr hm))
      (CWComplex.openCell_subset_skeleton (C := C) m i hxi)
  · let _ : IsEmpty (RelCWComplex.cell C m) := hbound m (Nat.lt_of_not_ge hm)
    exact (IsEmpty.false i).elim

/-- Every genuine bound on the cell dimensions yields the asserted vanishing;
no surviving cell family is required to be finite. -/
theorem homologyVanishingOfCellDimensionBound (n : ℕ)
    (hbound : ∀ m : ℕ, n < m → IsEmpty (RelCWComplex.cell C m)) :
    ∀ k : ℕ, n < k →
      IsZero (((singularHomologyFunctor AddCommGrpCat.{u} k).obj
        (AddCommGrpCat.of.{u} (ULift.{u} ℤ))).obj (TopCat.of ↑C)) := by
  intro k hk
  exact homologyVanishingOfSkeletonEq C n k
    (skeletonEqOfCellDimensionBound C n hbound) hk

/-- Finite dimension supplies an actual skeleton bound; finite cell counts
and finite type are not hypotheses. -/
theorem finiteDimensionalHomologyVanishing [CWComplex.FiniteDimensional C] :
    ∃ n : ℕ, (CWComplex.skeleton C (n : ℕ∞) : Set X) = C ∧
      ∀ k : ℕ, n < k →
        IsZero (((singularHomologyFunctor AddCommGrpCat.{u} k).obj
          (AddCommGrpCat.of.{u} (ULift.{u} ℤ))).obj (TopCat.of ↑C)) := by
  let hRel : RelCWComplex C (∅ : Set X) := CWComplex.instRelCWComplex C
  let hFinite : @RelCWComplex.FiniteDimensional X inferInstance C (∅ : Set X) hRel :=
    inferInstance
  have h : ∀ᶠ m : ℕ in Filter.atTop,
      IsEmpty (@RelCWComplex.cell X inferInstance C (∅ : Set X) hRel m) :=
    @RelCWComplex.FiniteDimensional.eventually_isEmpty_cell
      X inferInstance C (∅ : Set X) hRel hFinite
  rw [Filter.eventually_atTop] at h
  obtain ⟨N, hN⟩ := h
  have hbound : ∀ m : ℕ, N < m → IsEmpty (RelCWComplex.cell C m) :=
    fun m hm ↦ hN m hm.le
  exact ⟨N, skeletonEqOfCellDimensionBound C N hbound,
    homologyVanishingOfCellDimensionBound C N hbound⟩

end Hatcher.ClassicalCW

noncomputable section

namespace Hatcher.ClassicalCW

open AlgebraicTopology CategoryTheory CategoryTheory.Limits _root_.Topology

universe u

private abbrev finiteStageCoefficient : AddCommGrpCat.{u} :=
  AddCommGrpCat.of.{u} (ULift.{u} ℤ)

private abbrev finiteStageHomology (k : ℕ) : TopCat.{u} ⥤ AddCommGrpCat.{u} :=
  (singularHomologyFunctor AddCommGrpCat.{u} k).obj finiteStageCoefficient.{u}

variable {X : Type u} [TopologicalSpace X] [T2Space X]
  (C : Set X) [CWComplex C]

private abbrev finiteStageTop (n : ℕ) : TopCat.{u} :=
  TopCat.of ↑(CWComplex.skeleton C (n : ℕ∞) : Set X)

private noncomputable def finiteStageInclusion (n m : ℕ) (hnm : n ≤ m) :
    finiteStageTop C n ⟶ finiteStageTop C m :=
  TopCat.ofHom (ContinuousMap.inclusion
    (CWComplex.skeleton_mono (C := C) (Nat.cast_le.mpr hnm)))

private theorem finiteStageInclusion_id (n : ℕ) :
    finiteStageInclusion C n n (Nat.le_refl n) = 𝟙 (finiteStageTop C n) := by
  apply TopCat.ext
  intro x
  apply Subtype.ext
  rfl

private theorem finiteStageInclusion_comp (n m l : ℕ)
    (hnm : n ≤ m) (hml : m ≤ l) :
    finiteStageInclusion C n m hnm ≫ finiteStageInclusion C m l hml =
      finiteStageInclusion C n l (Nat.le_trans hnm hml) := by
  apply TopCat.ext
  intro x
  apply Subtype.ext
  rfl

private theorem finiteStage_standard_strict (n : ℕ) :
    (CWComplex.skeleton C (n : ℕ∞) : Set X) =
      (RelCWComplex.skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X) := by
  change (RelCWComplex.skeletonLT C ((n : ℕ∞) + 1) : Set X) =
    (RelCWComplex.skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X)
  exact congrArg (fun p : ℕ∞ ↦ (RelCWComplex.skeletonLT C p : Set X))
    (by simp only [Nat.cast_add, Nat.cast_one])

private noncomputable def finiteStageStepSourceIso (n : ℕ) :
    finiteStageTop C n ≅ (skeletalStagePair C (n + 1)).snd :=
  TopCat.isoOfHomeo (Homeomorph.setCongr (finiteStage_standard_strict C n))

/- Carrier and inclusion wrappers retain T2Space X because the pinned
skeleton objects themselves require it; no unused pure binder is added. -/
private noncomputable def finiteStageStepTargetIso (n : ℕ) :
    (skeletalStagePair C (n + 1)).fst ≅ finiteStageTop C (n + 1) := by
  have hcast : (((n + 1 : ℕ) : ℕ∞) + 1) = (((n + 1) + 1 : ℕ) : ℕ∞) := by
    simp only [Nat.cast_add, Nat.cast_one]
  have h : (RelCWComplex.skeletonLT C (((n + 1 : ℕ) : ℕ∞) + 1) : Set X) =
      (CWComplex.skeleton C ((n + 1 : ℕ) : ℕ∞) : Set X) :=
    (congrArg (fun p : ℕ∞ ↦ (RelCWComplex.skeletonLT C p : Set X)) hcast).trans
      (finiteStage_standard_strict C (n + 1)).symm
  exact TopCat.isoOfHomeo (Homeomorph.setCongr h)

private theorem finiteStageInclusion_step (n : ℕ) :
    finiteStageInclusion C n (n + 1) (Nat.le_succ n) =
      (finiteStageStepSourceIso C n).hom ≫ (skeletalStagePair C (n + 1)).map ≫
        (finiteStageStepTargetIso C n).hom := by
  apply TopCat.ext
  intro x
  apply Subtype.ext
  rfl

private theorem finiteStageIdentityHomology (n k : ℕ) :
    let H : TopCat.{u} ⥤ AddCommGrpCat.{u} := finiteStageHomology.{u} k
    let i := H.map (finiteStageInclusion C n n (Nat.le_refl n))
    Function.Surjective i ∧ IsIso i := by
  let H : TopCat.{u} ⥤ AddCommGrpCat.{u} := finiteStageHomology.{u} k
  let i : H.obj (finiteStageTop C n) ⟶ H.obj (finiteStageTop C n) :=
    H.map (finiteStageInclusion C n n (Nat.le_refl n))
  have hi : i = 𝟙 (H.obj (finiteStageTop C n)) :=
    (congrArg (fun f : finiteStageTop C n ⟶ finiteStageTop C n ↦ H.map f)
      (finiteStageInclusion_id C n)).trans (H.map_id (finiteStageTop C n))
  have hs : Function.Surjective i := by
    intro y
    exact ⟨y, ConcreteCategory.congr_hom hi y⟩
  have he : IsIso i :=
    Eq.mpr (congrArg (fun f : H.obj (finiteStageTop C n) ⟶
      H.obj (finiteStageTop C n) ↦ IsIso f) hi) inferInstance
  exact ⟨hs, he⟩

private theorem finiteStageOneStep (n k : ℕ) :
    let H : TopCat.{u} ⥤ AddCommGrpCat.{u} := finiteStageHomology.{u} k
    let i := H.map (finiteStageInclusion C n (n + 1) (Nat.le_succ n))
    (k ≤ n → Function.Surjective i) ∧ (k < n → IsIso i) := by
  let H : TopCat.{u} ⥤ AddCommGrpCat.{u} := finiteStageHomology.{u} k
  let P : TopPair.{u} := skeletalStagePair C (n + 1)
  let a : finiteStageTop C n ≅ P.snd := finiteStageStepSourceIso C n
  let b : P.fst ≅ finiteStageTop C (n + 1) := finiteStageStepTargetIso C n
  let E := H.mapIso a
  let E₂ := H.mapIso b
  let p : H.obj (finiteStageTop C n) ⟶ H.obj P.snd := E.hom
  let q₀ : H.obj P.snd ⟶ H.obj P.fst := H.map P.map
  let q : H.obj P.snd ⟶ H.obj (finiteStageTop C (n + 1)) :=
    H.map (P.map ≫ b.hom)
  have hpost : q₀ ≫ E₂.hom = q := (H.map_comp P.map b.hom).symm
  let i : H.obj (finiteStageTop C n) ⟶ H.obj (finiteStageTop C (n + 1)) :=
    H.map (finiteStageInclusion C n (n + 1) (Nat.le_succ n))
  have hmap : p ≫ q = i :=
    (H.map_comp a.hom (P.map ≫ b.hom)).symm.trans
      (congrArg (fun f : finiteStageTop C n ⟶ finiteStageTop C (n + 1) ↦ H.map f)
        (finiteStageInclusion_step C n).symm)
  refine ⟨?_, ?_⟩
  · intro hk
    have hq₀ : Function.Surjective q₀ :=
      (skeletonStepHomologyStability C (n + 1) k).1
        (Nat.ne_of_lt (Nat.lt_succ_of_le hk))
    have hq : Function.Surjective q := by
      intro y
      obtain ⟨z, hz⟩ := hq₀ (E₂.inv y)
      have he : E₂.hom (E₂.inv y) = y := ConcreteCategory.congr_hom E₂.inv_hom_id y
      have h := ConcreteCategory.congr_hom hpost z
      change E₂.hom (q₀ z) = q z at h
      exact ⟨z, h.symm.trans ((congrArg E₂.hom hz).trans he)⟩
    intro y
    obtain ⟨z, hz⟩ := hq y
    let x := E.inv z
    have hp : p x = z := ConcreteCategory.congr_hom E.inv_hom_id z
    have h := ConcreteCategory.congr_hom hmap x
    change q (p x) = i x at h
    exact ⟨x, h.symm.trans ((congrArg q hp).trans hz)⟩
  · intro hk
    have hp : IsIso p := inferInstance
    have hq₀ : IsIso q₀ := (skeletonStepHomologyStability C (n + 1) k).2.2
      (Nat.ne_of_lt (Nat.lt_succ_of_le hk.le))
      (Nat.ne_of_lt (Nat.lt_succ_of_le (Nat.succ_le_of_lt hk)))
    have he : IsIso E₂.hom := inferInstance
    have hq : IsIso q := Eq.mp (congrArg
      (fun f : H.obj P.snd ⟶ H.obj (finiteStageTop C (n + 1)) ↦ IsIso f) hpost)
        (IsIso.comp_isIso' hq₀ he)
    exact Eq.mp (congrArg
      (fun f : H.obj (finiteStageTop C n) ⟶ H.obj (finiteStageTop C (n + 1)) ↦ IsIso f)
      hmap) (IsIso.comp_isIso' hp hq)

/-- The actual finite-to-finite skeleton inclusion is surjective on ordinary
integral homology in degrees at most n and an isomorphism in degrees below n.
The identity and empty cases use the same literal maps. -/
theorem finiteStageHomologyStability (n m : ℕ) (hnm : n ≤ m) (k : ℕ) :
    let R : AddCommGrpCat.{u} := AddCommGrpCat.of.{u} (ULift.{u} ℤ)
    let H : TopCat.{u} ⥤ AddCommGrpCat.{u} :=
      (singularHomologyFunctor AddCommGrpCat.{u} k).obj R
    let A : Set X := CWComplex.skeleton C (n : ℕ∞)
    let B : Set X := CWComplex.skeleton C (m : ℕ∞)
    let hAB : A ⊆ B := CWComplex.skeleton_mono (C := C) (Nat.cast_le.mpr hnm)
    let i := H.map (TopCat.ofHom (ContinuousMap.inclusion hAB))
    (k ≤ n → Function.Surjective i) ∧ (k < n → IsIso i) := by
  let H : TopCat.{u} ⥤ AddCommGrpCat.{u} := finiteStageHomology.{u} k
  change (k ≤ n → Function.Surjective (H.map (finiteStageInclusion C n m hnm))) ∧
    (k < n → IsIso (H.map (finiteStageInclusion C n m hnm)))
  induction m generalizing n with
  | zero =>
      have hn : n = 0 := Nat.eq_zero_of_le_zero hnm
      subst n
      exact ⟨fun _ ↦ (finiteStageIdentityHomology C 0 k).1,
        fun _ ↦ (finiteStageIdentityHomology C 0 k).2⟩
  | succ m ih =>
      by_cases hn : n = m + 1
      · subst n
        exact ⟨fun _ ↦ (finiteStageIdentityHomology C (m + 1) k).1,
          fun _ ↦ (finiteStageIdentityHomology C (m + 1) k).2⟩
      · have hnm' : n ≤ m := Nat.le_of_lt_succ (lt_of_le_of_ne hnm hn)
        let i₀ : H.obj (finiteStageTop C n) ⟶ H.obj (finiteStageTop C m) :=
          H.map (finiteStageInclusion C n m hnm')
        let i₁ : H.obj (finiteStageTop C m) ⟶ H.obj (finiteStageTop C (m + 1)) :=
          H.map (finiteStageInclusion C m (m + 1) (Nat.le_succ m))
        let i : H.obj (finiteStageTop C n) ⟶ H.obj (finiteStageTop C (m + 1)) :=
          H.map (finiteStageInclusion C n (m + 1) hnm)
        have hcomp : i₀ ≫ i₁ = i :=
          (H.map_comp (finiteStageInclusion C n m hnm')
            (finiteStageInclusion C m (m + 1) (Nat.le_succ m))).symm.trans
              (congrArg
                (fun f : finiteStageTop C n ⟶ finiteStageTop C (m + 1) ↦ H.map f)
                (finiteStageInclusion_comp C n m (m + 1) hnm' (Nat.le_succ m)))
        have hold := ih n hnm'
        have hlast := finiteStageOneStep C m k
        refine ⟨?_, ?_⟩
        · intro hk
          have h₀ : Function.Surjective i₀ := hold.1 hk
          have h₁ : Function.Surjective i₁ := hlast.1 (Nat.le_trans hk hnm')
          intro y
          obtain ⟨z, hz⟩ := h₁ y
          obtain ⟨x, hx⟩ := h₀ z
          have h := ConcreteCategory.congr_hom hcomp x
          change i₁ (i₀ x) = i x at h
          exact ⟨x, h.symm.trans ((congrArg i₁ hx).trans hz)⟩
        · intro hk
          have h₀ : IsIso i₀ := hold.2 hk
          have h₁ : IsIso i₁ := hlast.2 (lt_of_lt_of_le hk hnm')
          exact Eq.mp (congrArg
            (fun f : H.obj (finiteStageTop C n) ⟶ H.obj (finiteStageTop C (m + 1)) ↦ IsIso f)
            hcomp) (IsIso.comp_isIso' h₀ h₁)

end Hatcher.ClassicalCW

noncomputable section

namespace Hatcher.ClassicalCW

open AlgebraicTopology CategoryTheory CategoryTheory.Limits _root_.Topology

universe u

private theorem skeletonSpaceClassMap
    (K L : ChainComplex AddCommGrpCat.{u} ℕ) (φ : K ⟶ L) (k : ℕ)
    (c : K.cycles k) (d : L.cycles k)
    (h : φ.f k (K.iCycles k c) = L.iCycles k d) :
    HomologicalComplex.homologyMap φ k (K.homologyπ k c) = L.homologyπ k d := by
  have hc : HomologicalComplex.cyclesMap φ k c = d := by
    apply (AddCommGrpCat.mono_iff_injective (L.iCycles k)).mp inferInstance
    have hi := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i φ k) c
    change L.iCycles k (HomologicalComplex.cyclesMap φ k c) =
      φ.f k (K.iCycles k c) at hi
    exact hi.trans h
  have hπ := ConcreteCategory.congr_hom
    (HomologicalComplex.homologyπ_naturality φ k) c
  change HomologicalComplex.homologyMap φ k (K.homologyπ k c) =
    L.homologyπ k (HomologicalComplex.cyclesMap φ k c) at hπ
  exact hπ.trans (congrArg (L.homologyπ k) hc)

private theorem skeletonSpaceClassBoundary_iff
    (K : ChainComplex AddCommGrpCat.{u} ℕ) (k : ℕ) (c : K.cycles k) :
    K.homologyπ k c = 0 ↔
      ∃ w : K.X (k + 1), K.d (k + 1) k w = K.iCycles k c := by
  let B : ShortComplex AddCommGrpCat.{u} :=
    ShortComplex.mk (K.toCycles (k + 1) k) (K.homologyπ k)
      (K.toCycles_comp_homologyπ (k + 1) k)
  have hB : B.Exact :=
    B.exact_of_g_is_cokernel (K.homologyIsCokernel (k + 1) k
      ((ComplexShape.down ℕ).prev_eq'
        (show (ComplexShape.down ℕ).Rel (k + 1) k from rfl)))
  constructor
  · intro hc
    obtain ⟨w, hw⟩ := (B.ab_exact_iff).mp hB c hc
    refine ⟨w, ?_⟩
    have hi := ConcreteCategory.congr_hom (K.toCycles_i (k + 1) k) w
    change K.iCycles k (K.toCycles (k + 1) k w) = K.d (k + 1) k w at hi
    exact hi.symm.trans (congrArg (K.iCycles k) hw)
  · rintro ⟨w, hw⟩
    have hc : K.toCycles (k + 1) k w = c := by
      apply (AddCommGrpCat.mono_iff_injective (K.iCycles k)).mp inferInstance
      have hi := ConcreteCategory.congr_hom (K.toCycles_i (k + 1) k) w
      change K.iCycles k (K.toCycles (k + 1) k w) = K.d (k + 1) k w at hi
      exact hi.trans hw
    have hz := ConcreteCategory.congr_hom
      (K.toCycles_comp_homologyπ (k + 1) k) w
    change K.homologyπ k (K.toCycles (k + 1) k w) = 0 at hz
    exact (congrArg (K.homologyπ k) hc).symm.trans hz

/-- Hatcher Lemma 2.34(c): the actual skeleton-to-space inclusion on ordinary
integral homology, including H0, empty and unbounded CW complexes. -/
theorem skeletonToSpaceHomologyStability
    {X : Type u} [TopologicalSpace X] [T2Space X]
    (C : Set X) [CWComplex C] (n k : ℕ) :
    let R : AddCommGrpCat.{u} := AddCommGrpCat.of.{u} (ULift.{u} ℤ)
    let H : TopCat.{u} ⥤ AddCommGrpCat.{u} :=
      (singularHomologyFunctor AddCommGrpCat.{u} k).obj R
    let i := H.map (singularSkeletonInclusion C n)
    (k ≤ n → Function.Surjective i) ∧ (k < n → IsIso i) := by
  let R : AddCommGrpCat.{u} := AddCommGrpCat.of.{u} (ULift.{u} ℤ)
  let F : TopCat.{u} ⥤ ChainComplex AddCommGrpCat.{u} ℕ :=
    (singularChainComplexFunctor AddCommGrpCat.{u}).obj R
  let H : TopCat.{u} ⥤ AddCommGrpCat.{u} :=
    (singularHomologyFunctor AddCommGrpCat.{u} k).obj R
  let T : TopCat.{u} := TopCat.of ↑C
  let T₀ : TopCat.{u} := TopCat.of ↑(CWComplex.skeleton C (n : ℕ∞) : Set X)
  let K : ChainComplex AddCommGrpCat.{u} ℕ := F.obj T
  let K₀ : ChainComplex AddCommGrpCat.{u} ℕ := F.obj T₀
  let φ : K₀ ⟶ K := singularSkeletonChainMap C n
  let i : K₀.homology k ⟶ K.homology k := H.map (singularSkeletonInclusion C n)
  change (k ≤ n → Function.Surjective i) ∧ (k < n → IsIso i)
  have hsurj (hk : k ≤ n) : Function.Surjective i := by
    intro y
    obtain ⟨c, hc⟩ :=
      ((AddCommGrpCat.epi_iff_surjective (K.homologyπ k)).mp inferInstance) y
    let z : K.X k := K.iCycles k c
    let l : ℕ := (ComplexShape.down ℕ).next k
    have hz : K.d k l z = 0 := by
      have h := ConcreteCategory.congr_hom (K.iCycles_d k l) c
      change K.d k l z = 0 at h
      exact h
    obtain ⟨N, hN, _, _, _, _, lift, hLift⟩ :=
      singularChain_exists_boundedSkeletonLift C (fun _ : Unit ↦ k) (fun _ : Unit ↦ z) n
    let Tₙ : TopCat.{u} := TopCat.of ↑(CWComplex.skeleton C (N : ℕ∞) : Set X)
    let Kₙ : ChainComplex AddCommGrpCat.{u} ℕ := F.obj Tₙ
    let φₙ : Kₙ ⟶ K := singularSkeletonChainMap C N
    let zₙ : Kₙ.X k := lift ()
    have hLiftz : φₙ.f k zₙ = z := hLift ()
    have hzₙ : Kₙ.d k l zₙ = 0 :=
      (singularSkeletonChainMap_cycle_iff C N k l zₙ).mp
        ((congrArg (K.d k l) hLiftz).trans hz)
    let cₙ : Kₙ.cycles k := (Kₙ.sc k).abCyclesIso.inv ⟨zₙ, hzₙ⟩
    have hcₙ : Kₙ.iCycles k cₙ = zₙ :=
      (Kₙ.sc k).abCyclesIso_inv_apply_iCycles ⟨zₙ, hzₙ⟩
    have himage : H.map (singularSkeletonInclusion C N) (Kₙ.homologyπ k cₙ) = y := by
      have h := skeletonSpaceClassMap Kₙ K φₙ k cₙ c
        ((congrArg (φₙ.f k) hcₙ).trans hLiftz)
      change H.map (singularSkeletonInclusion C N) (Kₙ.homologyπ k cₙ) =
        K.homologyπ k c at h
      exact h.trans hc
    let f : T₀ ⟶ Tₙ := TopCat.ofHom (ContinuousMap.inclusion
      (CWComplex.skeleton_mono (C := C) (Nat.cast_le.mpr hN)))
    have hs : Function.Surjective (H.map f) :=
      (finiteStageHomologyStability C n N hN k).1 hk
    obtain ⟨x, hx⟩ := hs (Kₙ.homologyπ k cₙ)
    have hinc : f ≫ singularSkeletonInclusion C N = singularSkeletonInclusion C n := by
      apply TopCat.ext
      intro x
      apply Subtype.ext
      rfl
    have hcomp : H.map f ≫ H.map (singularSkeletonInclusion C N) = i :=
      (H.map_comp f (singularSkeletonInclusion C N)).symm.trans
        (congrArg (fun g : T₀ ⟶ T ↦ H.map g) hinc)
    have h := ConcreteCategory.congr_hom hcomp x
    change H.map (singularSkeletonInclusion C N) (H.map f x) = i x at h
    exact ⟨x, h.symm.trans
      ((congrArg (H.map (singularSkeletonInclusion C N)) hx).trans himage)⟩
  refine ⟨hsurj, ?_⟩
  intro hk
  have hzero (x : K₀.homology k) (hx : i x = 0) : x = 0 := by
    obtain ⟨c, hc⟩ :=
      ((AddCommGrpCat.epi_iff_surjective (K₀.homologyπ k)).mp inferInstance) x
    let ca : K.cycles k := HomologicalComplex.cyclesMap φ k c
    have hm := ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality φ k) c
    change i (K₀.homologyπ k c) = K.homologyπ k ca at hm
    have hnull : K.homologyπ k ca = 0 :=
      hm.symm.trans ((congrArg i hc).trans hx)
    obtain ⟨w, hw⟩ := (skeletonSpaceClassBoundary_iff K k ca).mp hnull
    let z₀ : K₀.X k := K₀.iCycles k c
    have hca := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i φ k) c
    change K.iCycles k ca = φ.f k z₀ at hca
    have hbound : K.d (k + 1) k w = φ.f k z₀ := hw.trans hca
    obtain ⟨N, hN, _, _, _, _, lift, hLift⟩ :=
      singularChain_exists_boundedSkeletonLift C
        (fun _ : Unit ↦ k + 1) (fun _ : Unit ↦ w) n
    let Tₙ : TopCat.{u} := TopCat.of ↑(CWComplex.skeleton C (N : ℕ∞) : Set X)
    let Kₙ : ChainComplex AddCommGrpCat.{u} ℕ := F.obj Tₙ
    let φₙ : Kₙ ⟶ K := singularSkeletonChainMap C N
    let wₙ : Kₙ.X (k + 1) := lift ()
    have hLiftw : φₙ.f (k + 1) wₙ = w := hLift ()
    let f : T₀ ⟶ Tₙ := TopCat.ofHom (ContinuousMap.inclusion
      (CWComplex.skeleton_mono (C := C) (Nat.cast_le.mpr hN)))
    let ψ : K₀ ⟶ Kₙ := F.map f
    let zₙ : Kₙ.X k := ψ.f k z₀
    have hinc : f ≫ singularSkeletonInclusion C N = singularSkeletonInclusion C n := by
      apply TopCat.ext
      intro x
      apply Subtype.ext
      rfl
    have hchain : ψ ≫ φₙ = φ :=
      (F.map_comp f (singularSkeletonInclusion C N)).symm.trans
        (congrArg (fun g : T₀ ⟶ T ↦ F.map g) hinc)
    have hzmap : φₙ.f k zₙ = φ.f k z₀ := by
      have h := ConcreteCategory.congr_hom
        (congrArg (fun g : K₀ ⟶ K ↦ g.f k) hchain) z₀
      change φₙ.f k zₙ = φ.f k z₀ at h
      exact h
    have hreflect : K.d (k + 1) k (φₙ.f (k + 1) wₙ) = φₙ.f k zₙ :=
      (congrArg (K.d (k + 1) k) hLiftw).trans (hbound.trans hzmap.symm)
    have hwₙ : Kₙ.d (k + 1) k wₙ = zₙ :=
      (singularSkeletonChainMap_boundary_iff C N (k + 1) k wₙ zₙ).mp hreflect
    let cₙ : Kₙ.cycles k := HomologicalComplex.cyclesMap ψ k c
    have hcₙ := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i ψ k) c
    change Kₙ.iCycles k cₙ = zₙ at hcₙ
    have hnullₙ : Kₙ.homologyπ k cₙ = 0 :=
      (skeletonSpaceClassBoundary_iff Kₙ k cₙ).mpr ⟨wₙ, hwₙ.trans hcₙ.symm⟩
    have hmap := ConcreteCategory.congr_hom
      (HomologicalComplex.homologyπ_naturality ψ k) c
    change H.map f (K₀.homologyπ k c) = Kₙ.homologyπ k cₙ at hmap
    have hfx : H.map f x = 0 :=
      (congrArg (H.map f) hc).symm.trans (hmap.trans hnullₙ)
    let _ : IsIso (H.map f) := (finiteStageHomologyStability C n N hN k).2 hk
    have hinj : Function.Injective (H.map f) :=
      (AddCommGrpCat.mono_iff_injective (H.map f)).mp inferInstance
    exact hinj (hfx.trans (map_zero (H.map f).hom).symm)
  have hinj : Function.Injective i := by
    intro x y hxy
    have hz : i (x - y) = 0 :=
      (map_sub i.hom x y).trans (sub_eq_zero.mpr hxy)
    exact sub_eq_zero.mp (hzero (x - y) hz)
  let _ : Mono i := (AddCommGrpCat.mono_iff_injective i).mpr hinj
  let _ : Epi i := (AddCommGrpCat.epi_iff_surjective i).mpr (hsurj hk.le)
  exact isIso_of_mono_of_epi i

end Hatcher.ClassicalCW

end

noncomputable section

namespace Hatcher.ClassicalCW

open AlgebraicTopology CategoryTheory CategoryTheory.Limits _root_.Topology

universe u

private abbrev cellularComparisonCoefficient : AddCommGrpCat.{u} :=
  AddCommGrpCat.of.{u} (ULift.{u} ℤ)

private abbrev cellularComparisonHomology (k : ℕ) : TopCat.{u} ⥤ AddCommGrpCat.{u} :=
  (singularHomologyFunctor AddCommGrpCat.{u} k).obj cellularComparisonCoefficient.{u}

variable {X : Type u} [TopologicalSpace X] [T2Space X]
  (C : Set X) [CWComplex C]

private abbrev cellularComparisonOrdinary (n : ℕ) : AddCommGrpCat.{u} :=
  (cellularComparisonHomology.{u} n).obj (cellularSkeletonPair C n).fst

private noncomputable def cellularComparisonProjection (n : ℕ) :
    cellularComparisonOrdinary C n ⟶ (cellularChainComplex C).X n :=
  (Hatcher.Relative.singularPairFunctor.obj (cellularSkeletonPair C n)).homologyπ
    cellularComparisonCoefficient.{u} n

private noncomputable def cellularComparisonIncoming (n : ℕ) :
    (cellularChainComplex C).X (n + 1) ⟶ cellularComparisonOrdinary C n :=
  Hatcher.Relative.pairConnecting (cellularSkeletonPair C (n + 1))
    cellularComparisonCoefficient.{u} (n + 1) n rfl

private noncomputable def cellularComparisonSkeletonIso (n : ℕ) :
    TopCat.of ↑(CWComplex.skeleton C (n : ℕ∞) : Set X) ≅
      (cellularSkeletonPair C n).fst := by
  have h : (CWComplex.skeleton C (n : ℕ∞) : Set X) =
      (CWComplex.skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X) := by
    change (RelCWComplex.skeletonLT C ((n : ℕ∞) + 1) : Set X) =
      (RelCWComplex.skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X)
    exact congrArg (fun p : ℕ∞ ↦ (RelCWComplex.skeletonLT C p : Set X))
      (by simp only [Nat.cast_add, Nat.cast_one])
  exact TopCat.isoOfHomeo (Homeomorph.setCongr h)

private noncomputable def cellularComparisonInclusion (n : ℕ) :
    (cellularSkeletonPair C n).fst ⟶ TopCat.of ↑C :=
  TopCat.ofHom (ContinuousMap.inclusion
    (CWComplex.skeletonLT C ((n + 1 : ℕ) : ℕ∞)).subset_complex)

private theorem cellularComparisonStandardInclusion (n : ℕ) :
    (cellularComparisonSkeletonIso C n).inv ≫ singularSkeletonInclusion C n =
      cellularComparisonInclusion C n := by
  apply TopCat.ext
  intro x
  apply Subtype.ext
  rfl

private theorem cellularComparisonInclusion_isIso (n k : ℕ) (hk : k < n) :
    IsIso ((cellularComparisonHomology.{u} k).map (cellularComparisonInclusion C n)) := by
  let H : TopCat.{u} ⥤ AddCommGrpCat.{u} := cellularComparisonHomology.{u} k
  let e := H.mapIso (cellularComparisonSkeletonIso C n)
  let q := H.map (singularSkeletonInclusion C n)
  let i := H.map (cellularComparisonInclusion C n)
  have hcomp : e.inv ≫ q = i :=
    (H.map_comp (cellularComparisonSkeletonIso C n).inv
      (singularSkeletonInclusion C n)).symm.trans
        (congrArg (fun f ↦ H.map f) (cellularComparisonStandardInclusion C n))
  have hq : IsIso q := (skeletonToSpaceHomologyStability C n k).2 hk
  exact Eq.mp (congrArg (fun f ↦ IsIso f) hcomp)
    (IsIso.comp_isIso' (show IsIso e.inv from inferInstance) hq)

private theorem cellularComparisonInclusion_epi (n k : ℕ) (hk : k ≤ n) :
    Epi ((cellularComparisonHomology.{u} k).map (cellularComparisonInclusion C n)) := by
  let H : TopCat.{u} ⥤ AddCommGrpCat.{u} := cellularComparisonHomology.{u} k
  let e := H.mapIso (cellularComparisonSkeletonIso C n)
  let q := H.map (singularSkeletonInclusion C n)
  let i := H.map (cellularComparisonInclusion C n)
  let _ : Epi q := (AddCommGrpCat.epi_iff_surjective q).mpr
    ((skeletonToSpaceHomologyStability C n k).1 hk)
  have hcomp : e.inv ≫ q = i :=
    (H.map_comp (cellularComparisonSkeletonIso C n).inv
      (singularSkeletonInclusion C n)).symm.trans
        (congrArg (fun f ↦ H.map f) (cellularComparisonStandardInclusion C n))
  exact Eq.mp (congrArg (fun f ↦ Epi f) hcomp)
    (show Epi (e.inv ≫ q) from inferInstance)

private theorem cellularComparisonProjection_zero_isIso :
    IsIso (cellularComparisonProjection C 0) := by
  let R : AddCommGrpCat.{u} := AddCommGrpCat.of.{u} (ULift.{u} ℤ)
  let P : TopPair.{u} := zeroSkeletonPair C
  let π : ((singularHomologyFunctor AddCommGrpCat.{u} 0).obj R).obj P.fst ⟶
      (Hatcher.Relative.homologyFunctor R 0).obj P :=
    (Hatcher.Relative.singularPairFunctor.obj P).homologyπ R 0
  have hπ : π = cellularComparisonProjection C 0 := by
    change (Hatcher.Relative.singularPairFunctor.obj (zeroSkeletonPair C)).homologyπ R 0 =
      (Hatcher.Relative.singularPairFunctor.obj (cellularSkeletonPair C 0)).homologyπ R 0
    rfl
  have hE : (zeroSkeletonOrdinaryRelativeHomologyIso C 0).hom = π :=
    zeroSkeletonOrdinaryRelativeHomologyIso_hom C 0
  exact Eq.mp (congrArg (fun f ↦ IsIso f) (hE.trans hπ))
    (show IsIso (zeroSkeletonOrdinaryRelativeHomologyIso C 0).hom from inferInstance)

private theorem cellularComparisonProjection_mono (n : ℕ) :
    Mono (cellularComparisonProjection C n) := by
  cases n with
  | zero =>
      let _ : IsIso (cellularComparisonProjection C 0) :=
        cellularComparisonProjection_zero_isIso C
      infer_instance
  | succ r =>
      let P : TopPair.{u} := cellularSkeletonPair C (r + 1)
      let H : TopCat.{u} ⥤ AddCommGrpCat.{u} := cellularComparisonHomology.{u} (r + 1)
      let e : TopCat.of ↑(CWComplex.skeleton C (r : ℕ∞) : Set X) ≅ P.snd :=
        cellularComparisonSkeletonIso C r
      have hz₀ : IsZero (H.obj (TopCat.of ↑(CWComplex.skeleton C (r : ℕ∞) : Set X))) :=
        skeletonHomologyVanishing C r (r + 1) (Nat.lt_succ_self r)
      have hz : IsZero (H.obj P.snd) := hz₀.of_iso (H.mapIso e).symm
      let Q : SSetPair.{u} := Hatcher.Relative.singularPairFunctor.obj P
      have hzero : H.map P.map = 0 := hz.eq_zero_of_src (H.map P.map)
      exact (Q.homology_exact₂ cellularComparisonCoefficient.{u} (r + 1)).mono_g hzero

private noncomputable def cellularComparisonCycleSequence (n : ℕ) :
    ShortComplex AddCommGrpCat.{u} :=
  ShortComplex.mk (cellularComparisonProjection C n)
    ((cellularChainComplex C).sc' (n + 1) n (Nat.pred n)).g
    (by
      cases n with
      | zero =>
          let D : ChainComplex AddCommGrpCat.{u} ℕ := cellularChainComplex C
          let j : cellularComparisonOrdinary C 0 ⟶ D.X 0 :=
            cellularComparisonProjection C 0
          change j ≫ D.d 0 0 = 0
          have h : D.d 0 0 = 0 := cellularChainComplex_d_zero C 0
          exact (congrArg (fun f : D.X 0 ⟶ D.X 0 ↦ j ≫ f) h).trans
            (by simp only [comp_zero])
      | succ r =>
          let D : ChainComplex AddCommGrpCat.{u} ℕ := cellularChainComplex C
          let A : AddCommGrpCat.{u} := cellularComparisonOrdinary C (r + 1)
          let U : AddCommGrpCat.{u} := cellularComparisonOrdinary C r
          let j : A ⟶ D.X (r + 1) := cellularComparisonProjection C (r + 1)
          let δ : D.X (r + 1) ⟶ U := cellularComparisonIncoming C r
          let q : U ⟶ D.X r := cellularComparisonProjection C r
          let g : D.X (r + 1) ⟶ D.X r := D.d (r + 1) r
          change j ≫ g = 0
          have hz : j ≫ δ = 0 :=
            (Hatcher.Relative.singularPairFunctor.obj (cellularSkeletonPair C (r + 1))).comp_homologyδ cellularComparisonCoefficient.{u} (r + 1) r rfl
          have hd : g = δ ≫ q := cellularChainComplex_d_succ C r
          have h₁ : j ≫ g = j ≫ (δ ≫ q) :=
            congrArg (fun f : D.X (r + 1) ⟶ D.X r ↦ j ≫ f) hd
          have h₂ : j ≫ (δ ≫ q) = (j ≫ δ) ≫ q := (Category.assoc j δ q).symm
          have h₃ : (j ≫ δ) ≫ q = 0 :=
            (congrArg (fun f : A ⟶ U ↦ f ≫ q) hz).trans (by simp only [zero_comp])
          exact h₁.trans (h₂.trans h₃))

private theorem cellularComparisonCycleSequence_exact (n : ℕ) :
    (cellularComparisonCycleSequence C n).Exact := by
  cases n with
  | zero =>
      let e : cellularComparisonOrdinary C 0 ≅ (cellularChainComplex C).X 0 :=
        @asIso _ _ _ _ (cellularComparisonProjection C 0)
          (cellularComparisonProjection_zero_isIso C)
      apply ((cellularComparisonCycleSequence C 0).ab_exact_iff).mpr
      intro x _
      exact ⟨e.inv x, ConcreteCategory.congr_hom e.inv_hom_id x⟩
  | succ r =>
      let δ := cellularComparisonIncoming C r
      let j := cellularComparisonProjection C r
      let Q : SSetPair.{u} :=
        Hatcher.Relative.singularPairFunctor.obj (cellularSkeletonPair C (r + 1))
      let B : ShortComplex AddCommGrpCat.{u} := ShortComplex.mk
        (cellularComparisonProjection C (r + 1)) δ
        (Q.comp_homologyδ cellularComparisonCoefficient.{u} (r + 1) r rfl)
      have hB : B.Exact := Q.homology_exact₃ cellularComparisonCoefficient.{u} (r + 1) r rfl
      have hd : ((cellularChainComplex C).sc' (r + 1 + 1) (r + 1) r).g = δ ≫ j := by
        change (cellularChainComplex C).d (r + 1) r = _
        exact cellularChainComplex_d_succ C r
      have hj : Function.Injective j :=
        (AddCommGrpCat.mono_iff_injective j).mp (cellularComparisonProjection_mono C r)
      apply ((cellularComparisonCycleSequence C (r + 1)).ab_exact_iff).mpr
      intro x hx
      have h := ConcreteCategory.congr_hom hd x
      change ((cellularChainComplex C).sc' (r + 1 + 1) (r + 1) r).g x = j (δ x) at h
      have hδ : δ x = 0 := hj
        ((h.symm.trans hx).trans (map_zero j.hom).symm)
      exact (B.ab_exact_iff).mp hB x hδ

private theorem cellularComparisonInclusion_succ (n : ℕ) :
    (cellularSkeletonPair C (n + 1)).map ≫ cellularComparisonInclusion C (n + 1) =
      cellularComparisonInclusion C n := by
  apply TopCat.ext
  intro x
  apply Subtype.ext
  rfl

private noncomputable def cellularComparisonSpaceSequence (n : ℕ) :
    ShortComplex AddCommGrpCat.{u} :=
  ShortComplex.mk (cellularComparisonIncoming C n)
    ((cellularComparisonHomology.{u} n).map (cellularComparisonInclusion C n))
    (by
      let H : TopCat.{u} ⥤ AddCommGrpCat.{u} := cellularComparisonHomology.{u} n
      let P : TopPair.{u} := cellularSkeletonPair C (n + 1)
      let a := H.map P.map
      let b := H.map (cellularComparisonInclusion C (n + 1))
      have hf : a ≫ b = H.map (cellularComparisonInclusion C n) :=
        (H.map_comp P.map (cellularComparisonInclusion C (n + 1))).symm.trans
          (congrArg (fun f ↦ H.map f) (cellularComparisonInclusion_succ C n))
      have hz : cellularComparisonIncoming C n ≫ a = 0 :=
        (Hatcher.Relative.singularPairFunctor.obj P).homologyδ_comp
          cellularComparisonCoefficient.{u} (n + 1) n rfl
      calc
        cellularComparisonIncoming C n ≫ H.map (cellularComparisonInclusion C n) =
            cellularComparisonIncoming C n ≫ (a ≫ b) :=
          congrArg (fun f ↦ cellularComparisonIncoming C n ≫ f) hf.symm
        _ = (cellularComparisonIncoming C n ≫ a) ≫ b := (Category.assoc _ _ _).symm
        _ = 0 := by rw [hz, zero_comp])

private theorem cellularComparisonSpaceSequence_exact (n : ℕ) :
    (cellularComparisonSpaceSequence C n).Exact := by
  let H : TopCat.{u} ⥤ AddCommGrpCat.{u} := cellularComparisonHomology.{u} n
  let P : TopPair.{u} := cellularSkeletonPair C (n + 1)
  let Q : SSetPair.{u} := Hatcher.Relative.singularPairFunctor.obj P
  let a := H.map P.map
  let b := H.map (cellularComparisonInclusion C (n + 1))
  let B : ShortComplex AddCommGrpCat.{u} := ShortComplex.mk
    (cellularComparisonIncoming C n) a
    (Q.homologyδ_comp cellularComparisonCoefficient.{u} (n + 1) n rfl)
  have hB : B.Exact := Q.homology_exact₁ cellularComparisonCoefficient.{u} (n + 1) n rfl
  let _ : IsIso b := cellularComparisonInclusion_isIso C (n + 1) n (Nat.lt_succ_self n)
  have hb : Function.Injective b := (AddCommGrpCat.mono_iff_injective b).mp inferInstance
  have hf : a ≫ b = H.map (cellularComparisonInclusion C n) :=
    (H.map_comp P.map (cellularComparisonInclusion C (n + 1))).symm.trans
      (congrArg (fun f ↦ H.map f) (cellularComparisonInclusion_succ C n))
  apply ((cellularComparisonSpaceSequence C n).ab_exact_iff).mpr
  intro x hx
  have h := ConcreteCategory.congr_hom hf x
  change b (a x) = H.map (cellularComparisonInclusion C n) x at h
  have ha : a x = 0 := hb ((h.trans hx).trans (map_zero b.hom).symm)
  exact (B.ab_exact_iff).mp hB x ha

private noncomputable def cellularComparisonData (n : ℕ) :
    ((cellularChainComplex C).sc' (n + 1) n (Nat.pred n)).LeftHomologyData := by
  let S : ShortComplex AddCommGrpCat.{u} := (cellularChainComplex C).sc' (n + 1) n (Nat.pred n)
  let B : ShortComplex AddCommGrpCat.{u} := cellularComparisonCycleSequence C n
  let W : ShortComplex AddCommGrpCat.{u} := cellularComparisonSpaceSequence C n
  let j := cellularComparisonProjection C n
  let π := (cellularComparisonHomology.{u} n).map (cellularComparisonInclusion C n)
  letI : Mono j := cellularComparisonProjection_mono C n
  letI : Epi π := cellularComparisonInclusion_epi C n n (Nat.le_refl n)
  have hB : B.Exact := cellularComparisonCycleSequence_exact C n
  letI : Mono B.f := cellularComparisonProjection_mono C n
  let hi : IsLimit (KernelFork.ofι j B.zero) := hB.fIsKernel
  let f' := hi.lift (KernelFork.ofι S.f S.zero)
  have hfi : f' ≫ j = S.f := hi.fac (KernelFork.ofι S.f S.zero) WalkingParallelPair.zero
  have hδ : cellularComparisonIncoming C n ≫ j = S.f := by
    change _ = (cellularChainComplex C).d (n + 1) n
    exact (cellularChainComplex_d_succ C n).symm
  have hf : f' = cellularComparisonIncoming C n :=
    (cancel_mono j).mp (hfi.trans hδ.symm)
  have wπ : f' ≫ π = 0 :=
    (congrArg (fun f ↦ f ≫ π) hf).trans W.zero
  have hW : W.Exact := cellularComparisonSpaceSequence_exact C n
  letI : Epi W.g := cellularComparisonInclusion_epi C n n (Nat.le_refl n)
  let hcoker : IsColimit (CokernelCofork.ofπ π W.zero) := hW.gIsCokernel
  have hπ : IsColimit (CokernelCofork.ofπ π wπ) :=
    CokernelCofork.IsColimit.ofπ' π wπ (fun k hk ↦
      ⟨hcoker.desc (CokernelCofork.ofπ k
          ((congrArg (fun f ↦ f ≫ k) hf).symm.trans hk)),
        Cofork.IsColimit.π_desc hcoker⟩)
  exact
    { K := cellularComparisonOrdinary C n
      H := (cellularComparisonHomology.{u} n).obj (TopCat.of ↑C)
      i := j
      π := π
      wi := B.zero
      hi := hi
      wπ := wπ
      hπ := hπ }

/-- The actual skeletal relative projection identifies ordinary skeleton
homology with the canonical cycles of the constructed cellular complex. -/
noncomputable def cellularCyclesIso (n : ℕ) :
    ((singularHomologyFunctor AddCommGrpCat.{u} n).obj
      (AddCommGrpCat.of.{u} (ULift.{u} ℤ))).obj (cellularSkeletonPair C n).fst ≅
        (cellularChainComplex C).cycles n :=
  (cellularComparisonData C n).cyclesIso.symm ≪≫
    ((cellularChainComplex C).cyclesIsoSc' (n + 1) n (Nat.pred n)
      (ChainComplex.prev ℕ n)
      (by cases n with
          | zero => exact ChainComplex.next_nat_zero
          | succ r => exact ChainComplex.next_nat_succ r)).symm

theorem cellularCyclesIso_hom_iCycles (n : ℕ) :
    (cellularCyclesIso C n).hom ≫ (cellularChainComplex C).iCycles n =
      (Hatcher.Relative.singularPairFunctor.obj (cellularSkeletonPair C n)).homologyπ
        (AddCommGrpCat.of.{u} (ULift.{u} ℤ)) n := by
  let D : ChainComplex AddCommGrpCat.{u} ℕ := cellularChainComplex C
  let S : ShortComplex AddCommGrpCat.{u} := D.sc' (n + 1) n (Nat.pred n)
  have hp : (ComplexShape.down ℕ).prev n = n + 1 := ChainComplex.prev ℕ n
  have hn : (ComplexShape.down ℕ).next n = Nat.pred n := by
    cases n with
    | zero => exact ChainComplex.next_nat_zero
    | succ r => exact ChainComplex.next_nat_succ r
  let e : D.cycles n ≅ S.cycles := D.cyclesIsoSc' (n + 1) n (Nat.pred n) hp hn
  let data : S.LeftHomologyData := cellularComparisonData C n
  let a : data.K ⟶ S.cycles := data.cyclesIso.inv
  let b : S.cycles ⟶ D.cycles n := e.inv
  let q : D.cycles n ⟶ S.X₂ := D.iCycles n
  change (a ≫ b) ≫ q = data.i
  have h₁ : (a ≫ b) ≫ q = a ≫ (b ≫ q) := Category.assoc a b q
  have hb : b ≫ q = S.iCycles :=
    D.cyclesIsoSc'_inv_iCycles (n + 1) n (Nat.pred n) hp hn
  have h₂ : a ≫ (b ≫ q) = a ≫ S.iCycles :=
    congrArg (fun f : S.cycles ⟶ S.X₂ ↦ a ≫ f) hb
  have h₃ : a ≫ S.iCycles = data.i := data.cyclesIso_inv_comp_iCycles
  exact h₁.trans (h₂.trans h₃)

/-- Hatcher Theorem 2.35: cellular homology of the actual complex agrees
with ordinary integral singular homology of the whole CW carrier. -/
noncomputable def cellularHomologyComparison (n : ℕ) :
    (cellularChainComplex C).homology n ≅
      ((singularHomologyFunctor AddCommGrpCat.{u} n).obj
        (AddCommGrpCat.of.{u} (ULift.{u} ℤ))).obj (TopCat.of ↑C) :=
  (cellularChainComplex C).homologyIsoSc' (n + 1) n (Nat.pred n)
      (ChainComplex.prev ℕ n)
      (by cases n with
          | zero => exact ChainComplex.next_nat_zero
          | succ r => exact ChainComplex.next_nat_succ r) ≪≫
    (cellularComparisonData C n).homologyIso

theorem cellularHomologyComparison_forward (n : ℕ) :
    let R : AddCommGrpCat.{u} := AddCommGrpCat.of.{u} (ULift.{u} ℤ)
    let H : TopCat.{u} ⥤ AddCommGrpCat.{u} :=
      (singularHomologyFunctor AddCommGrpCat.{u} n).obj R
    let f : (cellularSkeletonPair C n).fst ⟶ TopCat.of ↑C :=
      TopCat.ofHom (ContinuousMap.inclusion
        (CWComplex.skeletonLT C ((n + 1 : ℕ) : ℕ∞)).subset_complex)
    (cellularCyclesIso C n).hom ≫ (cellularChainComplex C).homologyπ n ≫
        (cellularHomologyComparison C n).hom = H.map f := by
  let D : ChainComplex AddCommGrpCat.{u} ℕ := cellularChainComplex C
  let S : ShortComplex AddCommGrpCat.{u} := D.sc' (n + 1) n (Nat.pred n)
  have hp : (ComplexShape.down ℕ).prev n = n + 1 := ChainComplex.prev ℕ n
  have hn : (ComplexShape.down ℕ).next n = Nat.pred n := by
    cases n with
    | zero => exact ChainComplex.next_nat_zero
    | succ r => exact ChainComplex.next_nat_succ r
  let e : D.cycles n ≅ S.cycles := D.cyclesIsoSc' (n + 1) n (Nat.pred n) hp hn
  let E : D.homology n ≅ S.homology := D.homologyIsoSc' (n + 1) n (Nat.pred n) hp hn
  let data : S.LeftHomologyData := cellularComparisonData C n
  have hq : D.homologyπ n ≫ E.hom = e.hom ≫ S.homologyπ :=
    D.π_homologyIsoSc'_hom (n + 1) n (Nat.pred n) hp hn
  change (data.cyclesIso.inv ≫ e.inv) ≫ D.homologyπ n ≫
    (E.hom ≫ data.homologyIso.hom) = data.π
  calc
    (data.cyclesIso.inv ≫ e.inv) ≫ D.homologyπ n ≫
        (E.hom ≫ data.homologyIso.hom) =
        data.cyclesIso.inv ≫ (e.inv ≫
          ((D.homologyπ n ≫ E.hom) ≫ data.homologyIso.hom)) :=
      by simp only [Category.assoc]
    _ = data.cyclesIso.inv ≫ (e.inv ≫
        ((e.hom ≫ S.homologyπ) ≫ data.homologyIso.hom)) := congrArg
      (fun f ↦ data.cyclesIso.inv ≫ (e.inv ≫ (f ≫ data.homologyIso.hom))) hq
    _ = data.cyclesIso.inv ≫ (S.homologyπ ≫ data.homologyIso.hom) :=
      by simp only [Category.assoc, Iso.inv_hom_id_assoc]
    _ = data.cyclesIso.inv ≫ (data.cyclesIso.hom ≫ data.π) :=
      congrArg (fun f ↦ data.cyclesIso.inv ≫ f) data.homologyπ_comp_homologyIso_hom
    _ = data.π := by simp only [Iso.inv_hom_id_assoc]

end Hatcher.ClassicalCW

end

namespace Hatcher.ClassicalCW

open AlgebraicTopology CategoryTheory CategoryTheory.Limits _root_.Topology

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X]
  (C : Set X) [CWComplex C]

/-- Hatcher's first immediate cellular application: no cells in degree n
implies vanishing of ordinary integral homology in that degree. -/
theorem homologyVanishingOfNoCells (n : ℕ)
    (h : IsEmpty (RelCWComplex.cell C n)) :
    IsZero (((singularHomologyFunctor AddCommGrpCat.{u} n).obj
      (AddCommGrpCat.of.{u} (ULift.{u} ℤ))).obj (TopCat.of ↑C)) := by
  letI : IsEmpty (RelCWComplex.cell C n) := h
  let D : ChainComplex AddCommGrpCat.{u} ℕ := cellularChainComplex C
  obtain ⟨_, e, _⟩ := skeletonRelativeHomology C n
  have hPair : cellularSkeletonPair C n = skeletalStagePair C n := by
    rfl
  have hFree : IsZero
      (AddCommGrpCat.of.{u} (RelCWComplex.cell C n →₀ ℤ)) := by
    apply (IsZero.iff_id_eq_zero
      (AddCommGrpCat.of.{u} (RelCWComplex.cell C n →₀ ℤ))).mpr
    ext a i
    exact (IsEmpty.false i).elim
  have hMiddle : IsZero (D.X n) := by
    change IsZero ((cellularChainComplex C).X n)
    rw [cellularChainComplex_X C n, hPair]
    exact hFree.of_iso e
  let S : ShortComplex AddCommGrpCat.{u} := D.sc' (n + 1) n (Nat.pred n)
  have hSc : IsZero S.homology :=
    S.isZero_homology_of_isZero_X₂ (show IsZero S.X₂ from hMiddle)
  have hn : (ComplexShape.down ℕ).next n = Nat.pred n := by
    cases n with
    | zero => exact ChainComplex.next_nat_zero
    | succ r => exact ChainComplex.next_nat_succ r
  have hCellHomology : IsZero (D.homology n) :=
    hSc.of_iso (D.homologyIsoSc' (n + 1) n (Nat.pred n)
      (ChainComplex.prev ℕ n) hn)
  exact hCellHomology.of_iso (cellularHomologyComparison C n).symm

end Hatcher.ClassicalCW

namespace Hatcher.ClassicalCW

open AlgebraicTopology CategoryTheory CategoryTheory.Limits _root_.Topology

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X]
  (C : Set X) [CWComplex C]

/-- If no two occupied cell dimensions are adjacent, every differential of
the actual ordinary integral cellular complex is zero. -/
theorem cellularDifferentialsZeroOfSparseCells
    (hSparse : ∀ n : ℕ,
      ¬ (Nonempty (RelCWComplex.cell C n) ∧
        Nonempty (RelCWComplex.cell C (n + 1))))
    (i j : ℕ) : (cellularChainComplex C).d i j = 0 := by
  let D : ChainComplex AddCommGrpCat.{u} ℕ := cellularChainComplex C
  have hEmptyChain : ∀ k : ℕ, IsEmpty (RelCWComplex.cell C k) → IsZero (D.X k) := by
    intro k hk
    letI : IsEmpty (RelCWComplex.cell C k) := hk
    obtain ⟨_, e, _⟩ := skeletonRelativeHomology C k
    have hPair : cellularSkeletonPair C k = skeletalStagePair C k := by
      rfl
    have hFree : IsZero
        (AddCommGrpCat.of.{u} (RelCWComplex.cell C k →₀ ℤ)) := by
      apply (IsZero.iff_id_eq_zero
        (AddCommGrpCat.of.{u} (RelCWComplex.cell C k →₀ ℤ))).mpr
      ext a c
      exact (IsEmpty.false c).elim
    change IsZero ((cellularChainComplex C).X k)
    rw [cellularChainComplex_X C k, hPair]
    exact hFree.of_iso e
  change D.d i j = 0
  by_cases hij : i = j + 1
  · subst i
    rcases isEmpty_or_nonempty (RelCWComplex.cell C j) with hTargetEmpty | hTargetNonempty
    · exact (hEmptyChain j hTargetEmpty).eq_of_tgt (D.d (j + 1) j) 0
    · have hSourceEmpty : IsEmpty (RelCWComplex.cell C (j + 1)) :=
        ⟨fun c => hSparse j ⟨hTargetNonempty, ⟨c⟩⟩⟩
      exact (hEmptyChain (j + 1) hSourceEmpty).eq_of_src (D.d (j + 1) j) 0
  · exact cellularChainComplex_d_eq_zero C hij

end Hatcher.ClassicalCW

namespace Hatcher.ClassicalCW

open AlgebraicTopology CategoryTheory CategoryTheory.Limits _root_.Topology

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X]
  (C : Set X) [CWComplex C]

/-- With no adjacent occupied cell dimensions, the actual cells give a basis
of ordinary integral singular homology through the canonical cellular quotient
and the cellular/singular comparison. -/
theorem homologyCellBasisOfSparseCells
    (hSparse : ∀ n : ℕ,
      ¬ (Nonempty (RelCWComplex.cell C n) ∧
        Nonempty (RelCWComplex.cell C (n + 1))))
    (n : ℕ) :
    let D : ChainComplex AddCommGrpCat.{u} ℕ := cellularChainComplex C
    ∃ q : D.X n ≅ D.homology n,
      D.iCycles n ≫ q.hom = D.homologyπ n ∧
      ∃ E : AddCommGrpCat.of.{u} (RelCWComplex.cell C n →₀ ℤ) ≅
          (((singularHomologyFunctor AddCommGrpCat.{u} n).obj
            (AddCommGrpCat.of.{u} (ULift.{u} ℤ))).obj (TopCat.of ↑C)),
        ∀ i : RelCWComplex.cell C n,
          E.hom (Finsupp.single i 1) =
            (q.hom ≫ (cellularHomologyComparison C n).hom)
              (skeletalCellFundamentalClass C n i) := by
  let D : ChainComplex AddCommGrpCat.{u} ℕ := cellularChainComplex C
  have hD (i j : ℕ) : D.d i j = 0 :=
    cellularDifferentialsZeroOfSparseCells C hSparse i j
  let eCycles : D.cycles n ≅ D.X n :=
    D.iCyclesIso n ((ComplexShape.down ℕ).next n) rfl
      (hD n ((ComplexShape.down ℕ).next n))
  let eHomology : D.cycles n ≅ D.homology n :=
    D.isoHomologyπ ((ComplexShape.down ℕ).prev n) n rfl
      (hD ((ComplexShape.down ℕ).prev n) n)
  let q : D.X n ≅ D.homology n := eCycles.symm ≪≫ eHomology
  have hq : D.iCycles n ≫ q.hom = D.homologyπ n := by
    change eCycles.hom ≫ (eCycles.inv ≫ eHomology.hom) = eHomology.hom
    rw [← Category.assoc, eCycles.hom_inv_id, Category.id_comp]
  obtain ⟨_, e, he⟩ := skeletonRelativeHomology C n
  have hPair : cellularSkeletonPair C n = skeletalStagePair C n := by
    rfl
  let eCell : D.X n ≅ AddCommGrpCat.of.{u} (RelCWComplex.cell C n →₀ ℤ) := by
    change (cellularChainComplex C).X n ≅
      AddCommGrpCat.of.{u} (RelCWComplex.cell C n →₀ ℤ)
    rw [cellularChainComplex_X C n, hPair]
    exact e
  have hCell (i : RelCWComplex.cell C n) :
      eCell.inv (Finsupp.single i 1) = skeletalCellFundamentalClass C n i := by
    change e.inv (Finsupp.single i 1) = skeletalCellFundamentalClass C n i
    exact he i
  refine ⟨q, hq, eCell.symm ≪≫ q ≪≫ cellularHomologyComparison C n, ?_⟩
  intro i
  change (q.hom ≫ (cellularHomologyComparison C n).hom)
    (eCell.inv (Finsupp.single i 1)) =
      (q.hom ≫ (cellularHomologyComparison C n).hom)
        (skeletalCellFundamentalClass C n i)
  rw [hCell i]

end Hatcher.ClassicalCW
