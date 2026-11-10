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
    [IsEmpty (positiveSkeletalPair C k).snd] [IsEmpty (positiveSkeletalPair C k).fst] :
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
