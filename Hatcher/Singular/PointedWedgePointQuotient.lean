/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Jack McCarthy
-/
import Hatcher.Singular.PointQuotient
import Hatcher.Singular.SigmaPointedPair
import Hatcher.VanKampen.PointedWedgeUniversal

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

end Hatcher.Relative
