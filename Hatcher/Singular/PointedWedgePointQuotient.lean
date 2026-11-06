/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Jack McCarthy
-/
import Hatcher.Singular.PointQuotient
import Hatcher.Singular.SigmaPointedPair
import Hatcher.VanKampen.PointedWedgeUniversal
import Hatcher.Singular.PointQuotientTopology

/-!
# The pointed wedge as a point quotient

The pointed wedge of a family is the pushout of the sigma of its spaces along
the sigma of its chosen basepoints to a point.  Consequently it is canonically
isomorphic to the point quotient of the corresponding sigma pointed pair.

The construction also covers an empty family.  In that case the sigma is empty
and the extra point in `Hatcher.PointedWedge` is the whole wedge.
-/

noncomputable section

open CategoryTheory Limits

namespace Hatcher.Relative

universe u v w

variable {ι : Type u} {X : ι → TopCat.{max u v}}

/-- The inclusion of one summand into the pointed wedge, as a morphism in
`TopCat`. -/
def pointedWedgeSummandInclusion (x₀ : ∀ i, X i) (i : ι) :
    X i ⟶ TopCat.of (Hatcher.PointedWedge (fun i ↦ X i) x₀) :=
  TopCat.ofHom
    ⟨Hatcher.PointedWedge.inclusion x₀ i,
      Hatcher.PointedWedge.continuous_inclusion x₀ i⟩

@[simp]
theorem pointedWedgeSummandInclusion_apply (x₀ : ∀ i, X i) (i : ι)
    (x : X i) :
    pointedWedgeSummandInclusion x₀ i x =
      Hatcher.PointedWedge.inclusion x₀ i x :=
  rfl

/-- The map from the sigma of the spaces to their pointed wedge. -/
def sigmaToPointedWedge (x₀ : ∀ i, X i) :
    (sigmaPointedPair x₀).fst ⟶
      TopCat.of (Hatcher.PointedWedge (fun i ↦ X i) x₀) :=
  TopCat.ofHom
    { toFun := fun z ↦ Hatcher.PointedWedge.inclusion x₀ z.1 z.2
      continuous_toFun :=
        continuous_sigma fun i ↦
          Hatcher.PointedWedge.continuous_inclusion x₀ i }

@[simp]
theorem sigmaToPointedWedge_apply (x₀ : ∀ i, X i) (i : ι) (x : X i) :
    sigmaToPointedWedge x₀ ⟨i, x⟩ =
      Hatcher.PointedWedge.inclusion x₀ i x :=
  rfl

@[reassoc (attr := simp)]
theorem sigmaPointedPairι_fst_sigmaToPointedWedge
    (x₀ : ∀ i, X i) (i : ι) :
    TopPair.Hom.fst (sigmaPointedPairι x₀ i) ≫ sigmaToPointedWedge x₀ =
      pointedWedgeSummandInclusion x₀ i := by
  ext x
  rfl

/-- The map from a point to the distinguished point of a pointed wedge. -/
def pointedWedgePointInclusion (x₀ : ∀ i, X i) :
    (TopCat.of PUnit : TopCat.{max u v}) ⟶
      TopCat.of (Hatcher.PointedWedge (fun i ↦ X i) x₀) :=
  TopCat.ofHom ⟨fun _ ↦ Hatcher.PointedWedge.basepoint x₀, continuous_const⟩

@[simp]
theorem pointedWedgePointInclusion_apply (x₀ : ∀ i, X i) (z : PUnit) :
    (pointedWedgePointInclusion x₀).hom z =
      Hatcher.PointedWedge.basepoint x₀ :=
  rfl

/-- Controlled unfolding of the distinguished point of a point quotient.
This formulation lets callers expose the point inclusion without unfolding
the pushout itself. -/
theorem pointQuotientPoint_eq_pointQuotientPointInclusion (P : TopPair.{w}) :
    pointQuotientPoint P = pointQuotientPointInclusion P PUnit.unit :=
  rfl

/-- The sigma of the spaces and the common point exhibit the pointed wedge as
the pushout of the sigma pointed pair.  The proof uses the extra wedge point
separately, so it remains valid when the index type is empty. -/
theorem sigmaPointedPair_pointedWedge_isPushout (x₀ : ∀ i, X i) :
    IsPushout
      (sigmaPointedPair x₀).map
      (pointQuotientCollapse (sigmaPointedPair x₀))
      (sigmaToPointedWedge x₀)
      (pointedWedgePointInclusion x₀) := by
  apply IsPushout.mk'
  · ext z
    rcases z with ⟨i, ⟨⟩⟩
    change Hatcher.PointedWedge.inclusion x₀ i (x₀ i) =
      Hatcher.PointedWedge.basepoint x₀
    exact Hatcher.PointedWedge.inclusion_basepoint x₀ i
  · intro T φ ψ hφ hψ
    ext q
    induction q using Quotient.inductionOn with
    | _ q =>
        cases q with
        | none =>
            have h := ConcreteCategory.congr_hom hψ PUnit.unit
            change φ (Hatcher.PointedWedge.basepoint x₀) =
              ψ (Hatcher.PointedWedge.basepoint x₀) at h
            change φ (Hatcher.PointedWedge.basepoint x₀) =
              ψ (Hatcher.PointedWedge.basepoint x₀)
            exact h
        | some z =>
            have h := ConcreteCategory.congr_hom hφ z
            change φ (Hatcher.PointedWedge.inclusion x₀ z.1 z.2) =
              ψ (Hatcher.PointedWedge.inclusion x₀ z.1 z.2) at h
            change φ (Hatcher.PointedWedge.inclusion x₀ z.1 z.2) =
              ψ (Hatcher.PointedWedge.inclusion x₀ z.1 z.2)
            exact h
  · intro T a b hab
    let f : ∀ i, C(X i, T) := fun i ↦
      { toFun := fun x ↦ a ⟨i, x⟩
        continuous_toFun := a.hom.continuous.comp continuous_sigmaMk }
    have hf : ∀ i, f i (x₀ i) = b PUnit.unit := by
      intro i
      have h := ConcreteCategory.congr_hom hab
        (⟨i, PUnit.unit⟩ : (sigmaPointedPair x₀).snd)
      change a ⟨i, x₀ i⟩ = b PUnit.unit at h
      exact h
    let d : C(Hatcher.PointedWedge (fun i ↦ X i) x₀, T) :=
      Hatcher.PointedWedge.desc x₀ (b PUnit.unit) f hf
    refine ⟨TopCat.ofHom d, ?_, ?_⟩
    · ext z
      rcases z with ⟨i, x⟩
      change X i at x
      change d (Hatcher.PointedWedge.inclusion x₀ i x) = a ⟨i, x⟩
      simp [d, f]
    · ext z
      rcases z with ⟨⟩
      change d (Hatcher.PointedWedge.basepoint x₀) = b PUnit.unit
      simp [d]

/-- The point quotient of the sigma pointed pair is canonically the existing
project model of the pointed wedge. -/
noncomputable def pointQuotientSigmaPointedPairIsoPointedWedge
    (x₀ : ∀ i, X i) :
    pointQuotient (sigmaPointedPair x₀) ≅
      TopCat.of (Hatcher.PointedWedge (fun i ↦ X i) x₀) :=
  (IsPushout.of_hasPushout
      (sigmaPointedPair x₀).map
      (pointQuotientCollapse (sigmaPointedPair x₀))).isoIsPushout
    _ _ (sigmaPointedPair_pointedWedge_isPushout x₀)

@[reassoc (attr := simp)]
theorem pointQuotientProjection_pointQuotientSigmaPointedPairIsoPointedWedge_hom
    (x₀ : ∀ i, X i) :
    pointQuotientProjection (sigmaPointedPair x₀) ≫
        (pointQuotientSigmaPointedPairIsoPointedWedge x₀).hom =
      sigmaToPointedWedge x₀ := by
  unfold pointQuotientSigmaPointedPairIsoPointedWedge
  apply IsPushout.inl_isoIsPushout_hom

@[reassoc (attr := simp)]
theorem pointQuotientPointInclusion_pointQuotientSigmaPointedPairIsoPointedWedge_hom
    (x₀ : ∀ i, X i) :
    pointQuotientPointInclusion (sigmaPointedPair x₀) ≫
        (pointQuotientSigmaPointedPairIsoPointedWedge x₀).hom =
      pointedWedgePointInclusion x₀ := by
  unfold pointQuotientSigmaPointedPairIsoPointedWedge
  apply IsPushout.inr_isoIsPushout_hom

/-- The distinguished representative of the point summand maps to the wedge
basepoint.  This Unit-specialized post-simp rule supports clients that expose
the collapsed point through its point inclusion. -/
@[simp↓]
theorem pointQuotientSigmaPointedPairIsoPointedWedge_hom_pointInclusion_unit
    (x₀ : ∀ i, X i) :
    ((pointQuotientSigmaPointedPairIsoPointedWedge x₀).hom).hom
        (ConcreteCategory.hom
          (pointQuotientPointInclusion (sigmaPointedPair x₀)) PUnit.unit) =
      Hatcher.PointedWedge.basepoint x₀ := by
  have h := ConcreteCategory.congr_hom
    (pointQuotientPointInclusion_pointQuotientSigmaPointedPairIsoPointedWedge_hom
      x₀) PUnit.unit
  change ((pointQuotientSigmaPointedPairIsoPointedWedge x₀).hom).hom
      (ConcreteCategory.hom
        (pointQuotientPointInclusion (sigmaPointedPair x₀)) PUnit.unit) =
    Hatcher.PointedWedge.basepoint x₀ at h
  exact h

/-- Under the canonical isomorphism, the collapsed point is the wedge
basepoint. -/
@[simp↓]
theorem pointQuotientSigmaPointedPairIsoPointedWedge_hom_point
    (x₀ : ∀ i, X i) :
    ((pointQuotientSigmaPointedPairIsoPointedWedge x₀).hom).hom
        (pointQuotientPoint (sigmaPointedPair x₀)) =
      Hatcher.PointedWedge.basepoint x₀ := by
  rw [pointQuotientPoint_eq_pointQuotientPointInclusion]
  exact pointQuotientSigmaPointedPairIsoPointedWedge_hom_pointInclusion_unit x₀

/-- Restricting the quotient projection to a summand gives its canonical
inclusion in the pointed wedge. -/
@[reassoc (attr := simp)]
theorem sigmaι_pointQuotientProjection_pointQuotientSigmaPointedPairIsoPointedWedge_hom
    (x₀ : ∀ i, X i) (i : ι) :
    (TopCat.sigmaι X i ≫
        pointQuotientProjection (sigmaPointedPair x₀)) ≫
        (pointQuotientSigmaPointedPairIsoPointedWedge x₀).hom =
      pointedWedgeSummandInclusion x₀ i := by
  change (TopPair.Hom.fst (sigmaPointedPairι x₀ i) ≫
      pointQuotientProjection (sigmaPointedPair x₀)) ≫
      (pointQuotientSigmaPointedPairIsoPointedWedge x₀).hom =
    pointedWedgeSummandInclusion x₀ i
  simpa only [Category.assoc,
    pointQuotientProjection_pointQuotientSigmaPointedPairIsoPointedWedge_hom]
    using sigmaPointedPairι_fst_sigmaToPointedWedge x₀ i

@[simp]
theorem pointQuotientSigmaPointedPairIsoPointedWedge_hom_projection_apply
    (x₀ : ∀ i, X i) (i : ι) (x : X i) :
    (pointQuotientSigmaPointedPairIsoPointedWedge x₀).hom
        (pointQuotientProjection (sigmaPointedPair x₀) ⟨i, x⟩) =
      Hatcher.PointedWedge.inclusion x₀ i x := by
  have h := ConcreteCategory.congr_hom
    (pointQuotientProjection_pointQuotientSigmaPointedPairIsoPointedWedge_hom
      x₀) ⟨i, x⟩
  change (pointQuotientSigmaPointedPairIsoPointedWedge x₀).hom
      (pointQuotientProjection (sigmaPointedPair x₀) ⟨i, x⟩) =
    Hatcher.PointedWedge.inclusion x₀ i x at h
  exact h

section FiniteOnePointSigma

open scoped OnePoint

variable (X)

private noncomputable def finiteOnePointSigmaWedgeData
    [Finite ι] [∀ i, LocallyCompactSpace (X i)] [∀ i, T2Space (X i)] :
    {e : OnePoint (Σ i, X i) ≃ₜ
        Hatcher.PointedWedge (fun i ↦ OnePoint (X i))
          (fun i ↦ (∞ : OnePoint (X i))) //
      e (∞ : OnePoint (Σ i, X i)) =
          Hatcher.PointedWedge.basepoint (fun i ↦ (∞ : OnePoint (X i))) ∧
      ∀ (i : ι) (x : X i),
        e ((⟨i, x⟩ : Σ j, X j) : OnePoint (Σ j, X j)) =
          Hatcher.PointedWedge.inclusion (fun j ↦ (∞ : OnePoint (X j))) i
            (x : OnePoint (X i))} := by
  classical
  refine if hι : Nonempty ι then ?_ else ?_
  · letI : Nonempty ι := hι
    let T : ι → TopCat.{max u v} := fun i ↦ TopCat.of (OnePoint (X i))
    let x₀ : ∀ i, T i := fun i ↦ (∞ : OnePoint (X i))
    let P : TopPair.{max u v} := sigmaPointedPair (X := T) x₀
    let Z : TopCat.{max u v} := P.fst
    let V : Set Z := {z | z.2 ≠ (∞ : OnePoint (X z.1))}
    letI : CompactSpace Z := by
      change CompactSpace (Σ i, OnePoint (X i))
      infer_instance
    letI : T2Space Z := by
      change T2Space (Σ i, OnePoint (X i))
      infer_instance
    let a : (Σ i, X i) → Z :=
      Sigma.map (fun i ↦ i) fun i x ↦ (x : OnePoint (X i))
    have ha : Topology.IsOpenEmbedding a := by
      change Topology.IsOpenEmbedding
        (Sigma.map (fun i : ι ↦ i) fun i (x : X i) ↦ (x : OnePoint (X i)))
      exact (Topology.isOpenEmbedding_sigmaMap Function.injective_id).2 fun i ↦
        OnePoint.isOpenEmbedding_coe
    have haRange : Set.range a = V := by
      ext z
      constructor
      · rintro ⟨⟨i, x⟩, rfl⟩
        change (x : OnePoint (X i)) ≠ ∞
        exact OnePoint.coe_ne_infty x
      · intro hz
        rcases z with ⟨i, y⟩
        change y ≠ (∞ : OnePoint (X i)) at hz
        induction y using OnePoint.rec with
        | infty => exact (hz rfl).elim
        | coe x => exact ⟨⟨i, x⟩, rfl⟩
    have hV : IsOpen V := haRange ▸ ha.isOpen_range
    let eV : (Σ i, X i) ≃ₜ V :=
      ha.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr haRange)
    have hPRange : Set.range P.map = Vᶜ := by
      ext z
      constructor
      · rintro ⟨b, rfl⟩
        rcases b with ⟨i, ⟨⟩⟩
        change ¬ ((∞ : OnePoint (X i)) ≠ ∞)
        simp
      · intro hz
        have hzi : z.2 = (∞ : OnePoint (X z.1)) := by
          simpa only [V, Set.mem_compl_iff, Set.mem_setOf_eq, not_not] using hz
        rcases z with ⟨i, y⟩
        change y = (∞ : OnePoint (X i)) at hzi
        subst y
        exact ⟨⟨i, PUnit.unit⟩, rfl⟩
    let Q : TopPair.{max u v} := TopPair.ofSubset Vᶜ
    let eA : P.snd ≃ₜ Q.snd :=
      (TopPair.isEmbedding_map P).toHomeomorph.trans (Homeomorph.setCongr hPRange)
    let eAi : P.snd ≅ Q.snd := TopCat.isoOfHomeo eA
    let p : P ≅ Q :=
      { hom := TopPair.ofHom (𝟙 Z) eAi.hom (by
          ext b
          rfl)
        inv := TopPair.ofHom (𝟙 Z) eAi.inv (by
          ext b
          change P.map (eA.symm b) = b.1
          exact congrArg Subtype.val (eA.apply_symm_apply b))
        hom_inv_id := by
          apply MorphismProperty.Arrow.Hom.ext
          · change eAi.hom ≫ eAi.inv = 𝟙 _
            exact eAi.hom_inv_id
          · change (𝟙 Z) ≫ (𝟙 Z) = 𝟙 Z
            simp
        inv_hom_id := by
          apply MorphismProperty.Arrow.Hom.ext
          · change eAi.inv ≫ eAi.hom = 𝟙 _
            exact eAi.inv_hom_id
          · change (𝟙 Z) ≫ (𝟙 Z) = 𝟙 Z
            simp }
    let q : pointQuotient P ≅ pointQuotient Q :=
      { hom := pointQuotientMap p.hom
        inv := pointQuotientMap p.inv
        hom_inv_id := by
          rw [← pointQuotientMap_comp, p.hom_inv_id, pointQuotientMap_id]
        inv_hom_id := by
          rw [← pointQuotientMap_comp, p.inv_hom_id, pointQuotientMap_id] }
    let eQ := TopCat.homeoOfIso q
    have heQ_projection (z : Z) :
        eQ (pointQuotientProjection P z) = pointQuotientProjection Q z := by
      have heq := ConcreteCategory.congr_hom
        (pointQuotientProjection_naturality p.hom) z
      change eQ (pointQuotientProjection P z) = pointQuotientProjection Q z at heq
      exact heq
    have heQ_point : eQ (pointQuotientPoint P) = pointQuotientPoint Q := by
      have heq := ConcreteCategory.congr_hom
        (pointQuotientPointInclusion_naturality p.hom) PUnit.unit
      change eQ (pointQuotientPoint P) = pointQuotientPoint Q at heq
      exact heq
    have heQ_symm_projection (z : Z) :
        eQ.symm (pointQuotientProjection Q z) = pointQuotientProjection P z := by
      apply eQ.injective
      rw [eQ.apply_symm_apply]
      exact (heQ_projection z).symm
    have heQ_symm_point : eQ.symm (pointQuotientPoint Q) = pointQuotientPoint P := by
      apply eQ.injective
      rw [eQ.apply_symm_apply]
      exact heQ_point.symm
    have hVc : (Vᶜ).Nonempty := by
      rcases hι with ⟨i⟩
      refine ⟨⟨i, (∞ : OnePoint (X i))⟩, ?_⟩
      change ¬ ((∞ : OnePoint (X i)) ≠ ∞)
      simp
    let C := compactComplementQuotientOnePointHomeomorph Z V hV hVc
    have hC_point : C.symm (∞ : OnePoint V) = pointQuotientPoint Q := by
      apply C.injective
      rw [C.apply_symm_apply]
      exact (compactComplementQuotientOnePointHomeomorph_apply_point Z V hV hVc).symm
    have hC_projection (z : V) :
        C.symm (z : OnePoint V) = pointQuotientProjection Q z.1 := by
      apply C.injective
      rw [C.apply_symm_apply]
      exact (compactComplementQuotientOnePointHomeomorph_apply_projection
        Z V hV hVc z).symm
    let w := TopCat.homeoOfIso
      (pointQuotientSigmaPointedPairIsoPointedWedge (X := T) x₀)
    let e := eV.onePointCongr.trans (C.symm.trans (eQ.symm.trans w))
    refine ⟨e, ?_, ?_⟩
    · change w (eQ.symm (C.symm (∞ : OnePoint V))) =
        Hatcher.PointedWedge.basepoint x₀
      rw [hC_point, heQ_symm_point]
      exact pointQuotientSigmaPointedPairIsoPointedWedge_hom_point (X := T) x₀
    · intro i x
      let z : V := eV (⟨i, x⟩ : Σ j, X j)
      have hz : z.1 = (⟨i, (x : OnePoint (X i))⟩ : Z) := rfl
      change w (eQ.symm (C.symm (z : OnePoint V))) =
        Hatcher.PointedWedge.inclusion x₀ i (x : OnePoint (X i))
      rw [hC_projection z, heQ_symm_projection, hz]
      exact pointQuotientSigmaPointedPairIsoPointedWedge_hom_projection_apply
        (X := T) x₀ i (x : OnePoint (X i))
  · letI : IsEmpty ι := ⟨fun i ↦ hι ⟨i⟩⟩
    let e : OnePoint (Σ i, X i) ≃ₜ
        Hatcher.PointedWedge (fun i ↦ OnePoint (X i))
          (fun i ↦ (∞ : OnePoint (X i))) :=
      { toEquiv :=
          { toFun := fun _ ↦
              Hatcher.PointedWedge.basepoint (fun i ↦ (∞ : OnePoint (X i)))
            invFun := fun _ ↦ (∞ : OnePoint (Σ i, X i))
            left_inv := by
              intro z
              induction z using OnePoint.rec with
              | infty => rfl
              | coe z => exact isEmptyElim z.1
            right_inv := by
              intro z
              induction z using Quotient.inductionOn with
              | _ z =>
                cases z with
                | none => rfl
                | some z => exact isEmptyElim z.1 }
        continuous_toFun := continuous_const
        continuous_invFun := continuous_const }
    refine ⟨e, rfl, ?_⟩
    intro i x
    exact isEmptyElim i

/-- Compactifying a finite topological disjoint union gives the actual
pointed wedge of the compactified summands, each based at infinity.
The empty family is included. -/
noncomputable def finiteOnePointSigmaWedgeHomeomorph
    [Finite ι] [∀ i, LocallyCompactSpace (X i)] [∀ i, T2Space (X i)] :
    OnePoint (Σ i, X i) ≃ₜ
      Hatcher.PointedWedge (fun i ↦ OnePoint (X i))
        (fun i ↦ (∞ : OnePoint (X i))) :=
  (finiteOnePointSigmaWedgeData X).1

/-- A finite point maps to its canonical compactified-summand inclusion. -/
@[simp]
theorem finite_one_point_sigma_wedge_homeomorph_apply_coe
    [Finite ι] [∀ i, LocallyCompactSpace (X i)] [∀ i, T2Space (X i)]
    (i : ι) (x : X i) :
    finiteOnePointSigmaWedgeHomeomorph X
        ((⟨i, x⟩ : Σ j, X j) : OnePoint (Σ j, X j)) =
      Hatcher.PointedWedge.inclusion (fun j ↦ (∞ : OnePoint (X j))) i
        (x : OnePoint (X i)) :=
  (finiteOnePointSigmaWedgeData X).2.2 i x

/-- Infinity maps to the existing wedge's common basepoint. -/
@[simp]
theorem finite_one_point_sigma_wedge_homeomorph_apply_infty
    [Finite ι] [∀ i, LocallyCompactSpace (X i)] [∀ i, T2Space (X i)] :
    finiteOnePointSigmaWedgeHomeomorph X (∞ : OnePoint (Σ i, X i)) =
      Hatcher.PointedWedge.basepoint (fun i ↦ (∞ : OnePoint (X i))) :=
  (finiteOnePointSigmaWedgeData X).2.1

end FiniteOnePointSigma

end Hatcher.Relative
