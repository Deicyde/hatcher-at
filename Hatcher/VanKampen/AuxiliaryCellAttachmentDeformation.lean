import Hatcher.VanKampen.AuxiliaryCellAttachmentCover
import Hatcher.VanKampen.ConeAttachmentDeformation

/-!
# Deformation of Hatcher's auxiliary cell attachment

The strip-enlarged auxiliary space strongly deformation-retracts onto its
canonical indexed cone attachment. Each square is folded onto its bottom and
right edges while its left edge collapses compatibly with the common spine.
-/

noncomputable section

open Set Topology
open scoped unitInterval ContinuousMap

namespace Hatcher.VanKampen.AuxiliaryCellAttachment

universe u

variable {X J : Type u} {S : J → Type u}
variable [TopologicalSpace X] [∀ j, TopologicalSpace (S j)]
variable (f : ∀ j, S j → X) (s₀ : ∀ j, S j) (x₀ : X)
variable (γ : ∀ j, Path x₀ (f j (s₀ j)))

/-- The scalar that runs once along the bottom and then once up the right edge. -/
private def foldParameter (p : I × I) : ℝ :=
  (p.1 : ℝ) * (1 + (p.2 : ℝ))

private theorem foldParameter_nonneg (p : I × I) : 0 ≤ foldParameter p := by
  exact mul_nonneg p.1.property.1 (by nlinarith [p.2.property.1])

private theorem foldParameter_le_two (p : I × I) : foldParameter p ≤ 2 := by
  dsimp [foldParameter]
  have hmul : 0 ≤ (1 - (p.1 : ℝ)) * (p.2 : ℝ) :=
    mul_nonneg (by linarith [p.1.property.2]) p.2.property.1
  nlinarith [p.1.property.2, p.2.property.1, p.2.property.2, hmul]

private def foldBottom (p : I × I) : I :=
  ⟨min 1 (foldParameter p), by
    constructor
    · exact le_min zero_le_one (foldParameter_nonneg p)
    · exact min_le_left _ _⟩

private def foldRight (p : I × I) : I :=
  ⟨max 0 (foldParameter p - 1), by
    constructor
    · exact le_max_left _ _
    · exact max_le zero_le_one (by linarith [foldParameter_le_two p])⟩

private def foldSquare (p : I × I) : I × I :=
  (foldBottom p, foldRight p)

private theorem continuous_foldParameter : Continuous foldParameter := by
  unfold foldParameter
  fun_prop

private theorem continuous_foldBottom : Continuous foldBottom := by
  apply Continuous.subtype_mk
  exact continuous_const.min continuous_foldParameter

private theorem continuous_foldRight : Continuous foldRight := by
  apply Continuous.subtype_mk
  exact continuous_const.max (continuous_foldParameter.sub continuous_const)

private theorem continuous_foldSquare : Continuous foldSquare := by
  exact continuous_foldBottom.prodMk continuous_foldRight

@[simp] private theorem foldSquare_bottom (a : I) :
    foldSquare (a, 0) = (a, 0) := by
  apply Prod.ext <;> apply Subtype.ext
  · change min 1 ((a : ℝ) * (1 + 0)) = a
    simpa using min_eq_right a.property.2
  · change max 0 ((a : ℝ) * (1 + 0) - 1) = 0
    rw [max_eq_left]
    linarith [a.property.2]

@[simp] private theorem foldSquare_right (t : I) :
    foldSquare (1, t) = (1, t) := by
  apply Prod.ext <;> apply Subtype.ext
  · change min 1 ((1 : ℝ) * (1 + t)) = 1
    rw [min_eq_left]
    linarith [t.property.1]
  · change max 0 ((1 : ℝ) * (1 + t) - 1) = t
    rw [max_eq_right]
    · ring
    · linarith [t.property.1]

@[simp] private theorem foldSquare_left (t : I) :
    foldSquare (0, t) = (0, 0) := by
  apply Prod.ext <;> apply Subtype.ext <;>
    simp [foldSquare, foldBottom, foldRight, foldParameter]

private def squareDeformation (p : I × (I × I)) : I × I :=
  (Set.Icc.convexComb p.2.1 (foldSquare p.2).1 p.1,
    Set.Icc.convexComb p.2.2 (foldSquare p.2).2 p.1)

private theorem continuous_squareDeformation : Continuous squareDeformation := by
  have hu : Continuous (fun p : I × (I × I) ↦ p.1) := continuous_fst
  have hxa : Continuous (fun p : I × (I × I) ↦ p.2.1) :=
    continuous_fst.comp continuous_snd
  have hya : Continuous (fun p : I × (I × I) ↦ (foldSquare p.2).1) :=
    continuous_fst.comp (continuous_foldSquare.comp continuous_snd)
  have hxt : Continuous (fun p : I × (I × I) ↦ p.2.2) :=
    continuous_snd.comp continuous_snd
  have hyt : Continuous (fun p : I × (I × I) ↦ (foldSquare p.2).2) :=
    continuous_snd.comp (continuous_foldSquare.comp continuous_snd)
  exact (Set.Icc.continuous_convexComb_prod.comp
      (hxa.prodMk (hya.prodMk hu))).prodMk
    (Set.Icc.continuous_convexComb_prod.comp
      (hxt.prodMk (hyt.prodMk hu)))

@[simp] private theorem squareDeformation_zero (p : I × I) :
    squareDeformation (0, p) = p := by
  simp [squareDeformation]

@[simp] private theorem squareDeformation_one (p : I × I) :
    squareDeformation (1, p) = foldSquare p := by
  simp [squareDeformation]

@[simp] private theorem squareDeformation_bottom (u a : I) :
    squareDeformation (u, (a, 0)) = (a, 0) := by
  simp [squareDeformation]

@[simp] private theorem squareDeformation_right (u t : I) :
    squareDeformation (u, (1, t)) = (1, t) := by
  simp [squareDeformation]

@[simp] private theorem squareDeformation_left (u t : I) :
    squareDeformation (u, (0, t)) =
      (0, Set.Icc.convexComb t 0 u) := by
  simp [squareDeformation]

private def stripRetraction (j : J) (p : I × I) :
    Hatcher.VanKampen.IndexedConeAttachment f :=
  if foldParameter p ≤ 1 then
    IndexedConeAttachment.base f (γ j (foldBottom p))
  else
    IndexedConeAttachment.cylinder f j (s₀ j)
      (truncatedRadialHeight (foldRight p))

private theorem continuous_stripRetraction (j : J) :
    Continuous (stripRetraction f s₀ x₀ γ j) := by
  apply Continuous.if_le
  · exact (IndexedConeAttachment.continuous_base f).comp
      ((γ j).continuous.comp continuous_foldBottom)
  · exact (IndexedConeAttachment.continuous_cylinder f j).comp
      (continuous_const.prodMk
        (truncatedRadialHeight.continuous.comp continuous_foldRight))
  · exact continuous_foldParameter
  · exact continuous_const
  · intro p hp
    have hb : foldBottom p = 1 := by
      apply Subtype.ext
      simp [foldBottom, hp]
    have hr : foldRight p = 0 := by
      apply Subtype.ext
      simp [foldRight, hp]
    simp [hb, hr, (γ j).target]

omit [∀ j, TopologicalSpace (S j)] in
@[simp] private theorem stripRetraction_left (j : J) (t : I) :
    stripRetraction f s₀ x₀ γ j (0, t) = IndexedConeAttachment.base f x₀ := by
  simp [stripRetraction, foldParameter, foldBottom, (γ j).source]

omit [∀ j, TopologicalSpace (S j)] in
@[simp] private theorem stripRetraction_bottom (j : J) (a : I) :
    stripRetraction f s₀ x₀ γ j (a, 0) =
      IndexedConeAttachment.base f (γ j a) := by
  simp [stripRetraction, foldParameter, foldBottom, a.property.2]

omit [∀ j, TopologicalSpace (S j)] in
@[simp] private theorem stripRetraction_right (j : J) (t : I) :
    stripRetraction f s₀ x₀ γ j (1, t) =
      IndexedConeAttachment.cylinder f j (s₀ j) (truncatedRadialHeight t) := by
  by_cases ht : t = 0
  · subst t
    simp [stripRetraction, foldParameter, foldBottom, (γ j).target]
  · have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1 (Ne.symm (Subtype.coe_ne_coe.mpr ht))
    have hnle : ¬ foldParameter ((1 : I), t) ≤ 1 := by
      dsimp [foldParameter]
      linarith
    rw [stripRetraction, if_neg hnle]
    congr 2
    apply Subtype.ext
    change max 0 ((1 : ℝ) * (1 + t) - 1) = t
    rw [max_eq_right] <;> linarith

private theorem strip_foldSquare (j : J) (p : I × I) :
    strip f s₀ x₀ γ j (foldSquare p) =
      attachment f s₀ x₀ γ (stripRetraction f s₀ x₀ γ j p) := by
  by_cases hp : foldParameter p ≤ 1
  · have hr : foldRight p = 0 := by
      apply Subtype.ext
      change max 0 (foldParameter p - 1) = 0
      rw [max_eq_left]; linarith
    rw [show foldSquare p = (foldBottom p, 0) by simp [foldSquare, hr]]
    rw [strip_bottom]
    change attachment f s₀ x₀ γ
        (IndexedConeAttachment.base f (γ j (foldBottom p))) = _
    rw [stripRetraction, if_pos hp]
  · have hb : foldBottom p = 1 := by
      apply Subtype.ext
      change min 1 (foldParameter p) = 1
      rw [min_eq_left]
      exact le_of_not_ge hp
    rw [show foldSquare p = (1, foldRight p) by simp [foldSquare, hb]]
    rw [strip_right]
    simp [stripRetraction, hp]

private def retractionRaw : Prequotient f →
    Hatcher.VanKampen.IndexedConeAttachment f
  | Sum.inl y => y
  | Sum.inr (Sum.inl _) => IndexedConeAttachment.base f x₀
  | Sum.inr (Sum.inr ⟨j, p⟩) => stripRetraction f s₀ x₀ γ j p

private theorem continuous_retractionRaw :
    Continuous (retractionRaw f s₀ x₀ γ) := by
  rw [continuous_sum_dom]
  constructor
  · exact continuous_id
  · rw [continuous_sum_dom]
    constructor
    · exact continuous_const
    · rw [continuous_sigma_iff]
      intro j
      exact continuous_stripRetraction f s₀ x₀ γ j

omit [∀ j, TopologicalSpace (S j)] in
private theorem retractionRaw_normalForm (z : Prequotient f) :
    retractionRaw f s₀ x₀ γ (normalForm f s₀ x₀ γ z) =
      retractionRaw f s₀ x₀ γ z := by
  rcases z with y | (t | ⟨j, a, t⟩)
  · rfl
  · by_cases ht : t = 0
    · subst t
      simp [normalForm, retractionRaw]
    · simp [normalForm, retractionRaw, ht]
  · by_cases ht : t = 0
    · subst t
      simp [normalForm, retractionRaw]
    · by_cases ha0 : a = 0
      · subst a
        simp [normalForm, retractionRaw, ht]
      · by_cases ha1 : a = 1
        · subst a
          simp [normalForm, retractionRaw, ht]
        · simp [normalForm, retractionRaw, ht, ha0, ha1]

private def retractionMap :
    Hatcher.VanKampen.AuxiliaryCellAttachment f s₀ x₀ γ →
      Hatcher.VanKampen.IndexedConeAttachment f :=
  Quotient.lift (retractionRaw f s₀ x₀ γ) (by
    intro a b hab
    change normalForm f s₀ x₀ γ a = normalForm f s₀ x₀ γ b at hab
    rw [← retractionRaw_normalForm f s₀ x₀ γ a,
      ← retractionRaw_normalForm f s₀ x₀ γ b, hab])

private theorem continuous_retractionMap :
    Continuous (retractionMap f s₀ x₀ γ) := by
  apply Continuous.quotient_lift
  exact continuous_retractionRaw f s₀ x₀ γ

private def retraction : C(
    Hatcher.VanKampen.AuxiliaryCellAttachment f s₀ x₀ γ,
    Hatcher.VanKampen.IndexedConeAttachment f) where
  toFun := retractionMap f s₀ x₀ γ
  continuous_toFun := continuous_retractionMap f s₀ x₀ γ

@[simp] private theorem retraction_quotientMk (z : Prequotient f) :
    retraction f s₀ x₀ γ (quotientMk f s₀ x₀ γ z) =
      retractionRaw f s₀ x₀ γ z :=
  rfl

@[simp] private theorem retraction_attachment
    (y : Hatcher.VanKampen.IndexedConeAttachment f) :
    retraction f s₀ x₀ γ (attachment f s₀ x₀ γ y) = y :=
  rfl

private theorem retraction_comp_attachment :
    (retraction f s₀ x₀ γ).comp (attachment f s₀ x₀ γ) =
      ContinuousMap.id _ := by
  ext y
  exact retraction_attachment f s₀ x₀ γ y

private def deformationRaw :
    I × Prequotient f →
      Hatcher.VanKampen.AuxiliaryCellAttachment f s₀ x₀ γ
  | (_, Sum.inl y) => attachment f s₀ x₀ γ y
  | (u, Sum.inr (Sum.inl t)) =>
      spine f s₀ x₀ γ (Set.Icc.convexComb t 0 u)
  | (u, Sum.inr (Sum.inr ⟨j, p⟩)) =>
      strip f s₀ x₀ γ j (squareDeformation (u, p))

private theorem continuous_deformationRaw :
    Continuous (deformationRaw f s₀ x₀ γ) := by
  let gstrip : (Σ j : J, (I × I) × I) →
      Hatcher.VanKampen.AuxiliaryCellAttachment f s₀ x₀ γ
    | ⟨j, p, u⟩ => strip f s₀ x₀ γ j (squareDeformation (u, p))
  have hgstrip : Continuous gstrip := by
    rw [continuous_sigma_iff]
    intro j
    exact (strip f s₀ x₀ γ j).continuous.comp
      (continuous_squareDeformation.comp continuous_swap)
  let gright : (I × I) ⊕ (I × (Σ _j : J, I × I)) →
      Hatcher.VanKampen.AuxiliaryCellAttachment f s₀ x₀ γ
    | Sum.inl (u, t) =>
        spine f s₀ x₀ γ (Set.Icc.convexComb t 0 u)
    | Sum.inr p => gstrip
        ((Homeomorph.sigmaProdDistrib :
          (Σ _j : J, I × I) × I ≃ₜ Σ _j : J, (I × I) × I)
          (Prod.swap p))
  have hgright : Continuous gright := by
    rw [continuous_sum_dom]
    constructor
    · exact (spine f s₀ x₀ γ).continuous.comp
        (Set.Icc.continuous_convexComb_prod.comp
          ((continuous_snd).prodMk (continuous_const.prodMk continuous_fst)))
    · exact hgstrip.comp
        ((Homeomorph.sigmaProdDistrib :
          (Σ _j : J, I × I) × I ≃ₜ Σ _j : J, (I × I) × I).continuous.comp
          continuous_swap)
  let g : (I × Hatcher.VanKampen.IndexedConeAttachment f) ⊕
      (I × (I ⊕ (Σ _j : J, I × I))) →
      Hatcher.VanKampen.AuxiliaryCellAttachment f s₀ x₀ γ
    | Sum.inl (_, y) => attachment f s₀ x₀ γ y
    | Sum.inr p => gright
        ((Homeomorph.prodSumDistrib :
          I × (I ⊕ (Σ _j : J, I × I)) ≃ₜ
            (I × I) ⊕ (I × (Σ _j : J, I × I))) p)
  have hg : Continuous g := by
    rw [continuous_sum_dom]
    constructor
    · exact (attachment f s₀ x₀ γ).continuous.comp continuous_snd
    · exact hgright.comp
        (Homeomorph.prodSumDistrib :
          I × (I ⊕ (Σ _j : J, I × I)) ≃ₜ
            (I × I) ⊕ (I × (Σ _j : J, I × I))).continuous
  apply (hg.comp
    (Homeomorph.prodSumDistrib :
      I × Prequotient f ≃ₜ
        (I × Hatcher.VanKampen.IndexedConeAttachment f) ⊕
          (I × (I ⊕ (Σ _j : J, I × I)))).continuous).congr
  rintro ⟨u, z⟩
  rcases z with y | (t | ⟨j, p⟩) <;> rfl

private theorem deformationRaw_normalForm (u : I) (z : Prequotient f) :
    deformationRaw f s₀ x₀ γ (u, normalForm f s₀ x₀ γ z) =
      deformationRaw f s₀ x₀ γ (u, z) := by
  rcases z with y | (t | ⟨j, a, t⟩)
  · rfl
  · by_cases ht : t = 0
    · subst t
      simp [normalForm, deformationRaw]
    · simp [normalForm, deformationRaw, ht]
  · by_cases ht : t = 0
    · subst t
      simp [normalForm, deformationRaw]
    · by_cases ha0 : a = 0
      · subst a
        simp [normalForm, deformationRaw, ht]
      · by_cases ha1 : a = 1
        · subst a
          simp [normalForm, deformationRaw, ht]
        · simp [normalForm, deformationRaw, ht, ha0, ha1]

private theorem deformationRaw_eq_of_quotient_eq (u : I)
    {a b : Prequotient f}
    (h : quotientMk f s₀ x₀ γ a = quotientMk f s₀ x₀ γ b) :
    deformationRaw f s₀ x₀ γ (u, a) =
      deformationRaw f s₀ x₀ γ (u, b) := by
  have hrel := Quotient.exact h
  change normalForm f s₀ x₀ γ a = normalForm f s₀ x₀ γ b at hrel
  rw [← deformationRaw_normalForm f s₀ x₀ γ u a,
    ← deformationRaw_normalForm f s₀ x₀ γ u b, hrel]

private noncomputable def deformationMap :
    I × Hatcher.VanKampen.AuxiliaryCellAttachment f s₀ x₀ γ →
      Hatcher.VanKampen.AuxiliaryCellAttachment f s₀ x₀ γ := fun p =>
  deformationRaw f s₀ x₀ γ
    (p.1, Function.surjInv
      (isQuotientMap_quotientMk f s₀ x₀ γ).surjective p.2)

private theorem deformationMap_quotientMk (u : I) (z : Prequotient f) :
    deformationMap f s₀ x₀ γ (u, quotientMk f s₀ x₀ γ z) =
      deformationRaw f s₀ x₀ γ (u, z) := by
  apply deformationRaw_eq_of_quotient_eq f s₀ x₀ γ u
  exact Function.surjInv_eq
    (isQuotientMap_quotientMk f s₀ x₀ γ).surjective _

private theorem continuous_deformationMap :
    Continuous (deformationMap f s₀ x₀ γ) := by
  apply (isQuotientMap_quotientMk f s₀ x₀ γ).continuous_lift_prod_right
  apply (continuous_deformationRaw f s₀ x₀ γ).congr
  rintro ⟨u, z⟩
  exact (deformationMap_quotientMk f s₀ x₀ γ u z).symm

@[simp] private theorem deformationMap_zero
    (z : Hatcher.VanKampen.AuxiliaryCellAttachment f s₀ x₀ γ) :
    deformationMap f s₀ x₀ γ (0, z) = z := by
  obtain ⟨a, rfl⟩ := (isQuotientMap_quotientMk f s₀ x₀ γ).surjective z
  rw [deformationMap_quotientMk]
  rcases a with y | (t | ⟨j, p⟩)
  · rfl
  · simp [deformationRaw, spine, quotientMk]
  · simp [deformationRaw, strip, quotientMk]

@[simp] private theorem deformationMap_one
    (z : Hatcher.VanKampen.AuxiliaryCellAttachment f s₀ x₀ γ) :
    deformationMap f s₀ x₀ γ (1, z) =
      attachment f s₀ x₀ γ (retraction f s₀ x₀ γ z) := by
  obtain ⟨a, rfl⟩ := (isQuotientMap_quotientMk f s₀ x₀ γ).surjective z
  rw [deformationMap_quotientMk]
  rcases a with y | (t | ⟨j, p⟩)
  · rfl
  · rw [retraction_quotientMk]
    change spine f s₀ x₀ γ (Set.Icc.convexComb t 0 1) =
      attachment f s₀ x₀ γ (IndexedConeAttachment.base f x₀)
    rw [Set.Icc.convexComb_one, spine_zero]
    rfl
  · rw [retraction_quotientMk]
    simpa [deformationRaw, retractionRaw] using
      strip_foldSquare f s₀ x₀ γ j p

@[simp] private theorem deformationMap_attachment (u : I)
    (y : Hatcher.VanKampen.IndexedConeAttachment f) :
    deformationMap f s₀ x₀ γ (u, attachment f s₀ x₀ γ y) =
      attachment f s₀ x₀ γ y := by
  change deformationMap f s₀ x₀ γ
      (u, quotientMk f s₀ x₀ γ (Sum.inl y)) = _
  rw [deformationMap_quotientMk]
  rfl

private def deformation :
    (ContinuousMap.id
      (Hatcher.VanKampen.AuxiliaryCellAttachment f s₀ x₀ γ)).HomotopyRel
      ((attachment f s₀ x₀ γ).comp (retraction f s₀ x₀ γ))
      (Set.range (attachment f s₀ x₀ γ)) where
  toFun := deformationMap f s₀ x₀ γ
  continuous_toFun := continuous_deformationMap f s₀ x₀ γ
  map_zero_left := deformationMap_zero f s₀ x₀ γ
  map_one_left := deformationMap_one f s₀ x₀ γ
  prop' u z hz := by
    obtain ⟨y, rfl⟩ := hz
    exact deformationMap_attachment f s₀ x₀ γ u y

/-- The canonical indexed attachment is a strong deformation retract of the
auxiliary strip enlargement. -/
def attachmentStrongDeformationRetract :
    Hatcher.StrongDeformationRetract (attachment f s₀ x₀ γ) where
  retract := retraction f s₀ x₀ γ
  retract_inclusion := retraction_comp_attachment f s₀ x₀ γ
  deformation := deformation f s₀ x₀ γ

/-!
## Retraction of the base-side auxiliary cover

The indexed lower cone cover retracts radially onto the original base.  The
existing strip deformation restricts to the auxiliary base-side member, and
composition gives Hatcher's base-side strong deformation retraction.
-/

private def indexedLowerRaw :
    I × IndexedConeAttachment.Prequotient X S →
      Hatcher.VanKampen.IndexedConeAttachment f
  | (_, Sum.inl x) => IndexedConeAttachment.base f x
  | (_, Sum.inr ⟨j, Sum.inl _⟩) => IndexedConeAttachment.apex f j
  | (u, Sum.inr ⟨j, Sum.inr (s, t)⟩) =>
      IndexedConeAttachment.cylinder f j s
        (Set.Icc.convexComb t 1 u)

private theorem continuous_indexedLowerRaw :
    Continuous (indexedLowerRaw f) := by
  let gsigma : (Σ j : J, (Unit ⊕ (S j × I)) × I) →
      Hatcher.VanKampen.IndexedConeAttachment f
    | ⟨j, Sum.inl _, _⟩ => IndexedConeAttachment.apex f j
    | ⟨j, Sum.inr (s, t), u⟩ =>
        IndexedConeAttachment.cylinder f j s
          (Set.Icc.convexComb t 1 u)
  have hgsigma : Continuous gsigma := by
    rw [continuous_sigma_iff]
    intro j
    let gj : (Unit × I) ⊕ ((S j × I) × I) →
        Hatcher.VanKampen.IndexedConeAttachment f
      | Sum.inl _ => IndexedConeAttachment.apex f j
      | Sum.inr ((s, t), u) => IndexedConeAttachment.cylinder f j s
          (Set.Icc.convexComb t 1 u)
    have hgj : Continuous gj := by
      rw [continuous_sum_dom]
      constructor
      · exact continuous_const
      · exact (IndexedConeAttachment.continuous_cylinder f j).comp
          ((continuous_fst.comp continuous_fst).prodMk
            (Set.Icc.continuous_convexComb_prod.comp
              ((continuous_snd.comp continuous_fst).prodMk
                (continuous_const.prodMk continuous_snd))))
    apply (hgj.comp
      (Homeomorph.sumProdDistrib :
        (Unit ⊕ (S j × I)) × I ≃ₜ
          (Unit × I) ⊕ ((S j × I) × I)).continuous).congr
    rintro ⟨_ | ⟨s, t⟩, u⟩ <;> rfl
  let g : (I × X) ⊕ (I × (Σ j : J, Unit ⊕ (S j × I))) →
      Hatcher.VanKampen.IndexedConeAttachment f
    | Sum.inl (_, x) => IndexedConeAttachment.base f x
    | Sum.inr p => gsigma
        ((Homeomorph.sigmaProdDistrib :
          (Σ j : J, Unit ⊕ (S j × I)) × I ≃ₜ
            Σ j : J, (Unit ⊕ (S j × I)) × I)
          (Prod.swap p))
  have hg : Continuous g := by
    rw [continuous_sum_dom]
    constructor
    · exact (IndexedConeAttachment.continuous_base f).comp continuous_snd
    · exact hgsigma.comp
        ((Homeomorph.sigmaProdDistrib :
          (Σ j : J, Unit ⊕ (S j × I)) × I ≃ₜ
            Σ j : J, (Unit ⊕ (S j × I)) × I).continuous.comp
          continuous_swap)
  apply (hg.comp
    (Homeomorph.prodSumDistrib :
      I × IndexedConeAttachment.Prequotient X S ≃ₜ
        (I × X) ⊕ (I × (Σ j : J, Unit ⊕ (S j × I)))).continuous).congr
  rintro ⟨u, x | ⟨j, (_ | ⟨s, t⟩)⟩⟩ <;> rfl

omit [TopologicalSpace X] [∀ j, TopologicalSpace (S j)] in
private theorem indexedLowerSource_mem (z :
    IndexedConeAttachment.quotientMk f ⁻¹'
      IndexedConeAttachment.lowerCover f) :
    z.1 ∈ IndexedConeAttachment.lowerPreimage := by
  exact Set.ext_iff.mp
    (IndexedConeAttachment.quotientMk_preimage_lowerCover f) z.1 |>.mp z.2

omit [TopologicalSpace X] [∀ j, TopologicalSpace (S j)] in
private theorem indexedLowerRaw_mem (u : I)
    (z : IndexedConeAttachment.quotientMk f ⁻¹'
      IndexedConeAttachment.lowerCover f) :
    indexedLowerRaw f (u, z.1) ∈ IndexedConeAttachment.lowerCover f := by
  have hz := indexedLowerSource_mem f z
  rcases z with ⟨x | ⟨j, (_ | ⟨s, t⟩)⟩, hz'⟩
  · exact IndexedConeAttachment.base_mem_lowerCover f x
  · contradiction
  · simp only [indexedLowerRaw]
    rw [IndexedConeAttachment.cylinder_mem_lowerCover_iff]
    change 0 < t at hz
    exact hz.trans_le (Set.Icc.le_convexComb unitInterval.le_one' u)

private def indexedLowerRawRestricted :
    I × (IndexedConeAttachment.quotientMk f ⁻¹'
      IndexedConeAttachment.lowerCover f) →
        IndexedConeAttachment.lowerCover f :=
  fun p => ⟨indexedLowerRaw f (p.1, p.2.1),
    indexedLowerRaw_mem f p.1 p.2⟩

private theorem continuous_indexedLowerRawRestricted :
    Continuous (indexedLowerRawRestricted f) := by
  apply Continuous.subtype_mk
  exact (continuous_indexedLowerRaw f).comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))

omit [TopologicalSpace X] [∀ j, TopologicalSpace (S j)] in
private theorem indexedLowerRaw_eq_of_normalForm_eq (u : I)
    {a b : IndexedConeAttachment.Prequotient X S}
    (ha : a ∈ IndexedConeAttachment.lowerPreimage)
    (hb : b ∈ IndexedConeAttachment.lowerPreimage)
    (h : IndexedConeAttachment.normalForm f a =
      IndexedConeAttachment.normalForm f b) :
    indexedLowerRaw f (u, a) = indexedLowerRaw f (u, b) := by
  rcases a with x | ⟨j, a⟩
  · rcases b with y | ⟨k, b⟩
    · simp_all [IndexedConeAttachment.normalForm, indexedLowerRaw]
    · rcases b with _ | ⟨r, v⟩
      · change False at hb
        contradiction
      · change 0 < v at hb
        simp only [IndexedConeAttachment.normalForm] at h
        split_ifs at h
        all_goals simp_all [indexedLowerRaw]
  · rcases a with _ | ⟨s, t⟩
    · change False at ha
      contradiction
    · change 0 < t at ha
      rcases b with y | ⟨k, b⟩
      · simp only [IndexedConeAttachment.normalForm] at h
        split_ifs at h
        all_goals simp_all [indexedLowerRaw]
      · rcases b with _ | ⟨r, v⟩
        · change False at hb
          contradiction
        · change 0 < v at hb
          simp only [IndexedConeAttachment.normalForm] at h
          split_ifs at h
          all_goals try simp_all [indexedLowerRaw]
          obtain ⟨rfl, hsr⟩ := h
          cases hsr
          rfl

omit [TopologicalSpace X] [∀ j, TopologicalSpace (S j)] in
private theorem indexedLowerRawRestricted_eq_of_quotient_eq (u : I)
    {a b : IndexedConeAttachment.quotientMk f ⁻¹'
      IndexedConeAttachment.lowerCover f}
    (h : (IndexedConeAttachment.lowerCover f).restrictPreimage
        (IndexedConeAttachment.quotientMk f) a =
      (IndexedConeAttachment.lowerCover f).restrictPreimage
        (IndexedConeAttachment.quotientMk f) b) :
    indexedLowerRawRestricted f (u, a) =
      indexedLowerRawRestricted f (u, b) := by
  apply Subtype.ext
  apply indexedLowerRaw_eq_of_normalForm_eq f u
  · exact indexedLowerSource_mem f a
  · exact indexedLowerSource_mem f b
  · have hrel := Quotient.exact (congrArg Subtype.val h)
    change IndexedConeAttachment.normalForm f a.1 =
      IndexedConeAttachment.normalForm f b.1 at hrel
    exact hrel

private noncomputable def indexedLowerDeformationMap :
    I × IndexedConeAttachment.lowerCover f →
      IndexedConeAttachment.lowerCover f := fun p =>
  indexedLowerRawRestricted f
    (p.1, Function.surjInv
      (IndexedConeAttachment.isQuotientMap_restrictPreimage_lowerCover f).surjective p.2)

private theorem indexedLowerDeformationMap_quotientMap (u : I)
    (z : IndexedConeAttachment.quotientMk f ⁻¹'
      IndexedConeAttachment.lowerCover f) :
    indexedLowerDeformationMap f
        (u, (IndexedConeAttachment.lowerCover f).restrictPreimage
          (IndexedConeAttachment.quotientMk f) z) =
      indexedLowerRawRestricted f (u, z) := by
  apply indexedLowerRawRestricted_eq_of_quotient_eq f u
  exact Function.surjInv_eq
    (IndexedConeAttachment.isQuotientMap_restrictPreimage_lowerCover f).surjective _

private theorem continuous_indexedLowerDeformationMap :
    Continuous (indexedLowerDeformationMap f) := by
  apply (IndexedConeAttachment.isQuotientMap_restrictPreimage_lowerCover f).continuous_lift_prod_right
  apply (continuous_indexedLowerRawRestricted f).congr
  rintro ⟨u, z⟩
  exact (indexedLowerDeformationMap_quotientMap f u z).symm

private def indexedLowerRetractionPre :
    (IndexedConeAttachment.quotientMk f ⁻¹'
      IndexedConeAttachment.lowerCover f) → X
  | ⟨Sum.inl x, _⟩ => x
  | ⟨Sum.inr ⟨_, Sum.inl _⟩, h⟩ => False.elim <| by
      have hz : (Sum.inr ⟨_, Sum.inl ()⟩ :
          IndexedConeAttachment.Prequotient X S) ∈
          IndexedConeAttachment.lowerPreimage :=
        Set.ext_iff.mp
          (IndexedConeAttachment.quotientMk_preimage_lowerCover f) _ |>.mp h
      exact hz
  | ⟨Sum.inr ⟨j, Sum.inr (s, _)⟩, _⟩ => f j s

private theorem continuous_indexedLowerRetractionPre
    (hf : ∀ j, Continuous (f j)) :
    Continuous (indexedLowerRetractionPre f) := by
  cases isEmpty_or_nonempty X with
  | inl hX =>
      letI : IsEmpty X := hX
      exact continuous_empty_function _
  | inr hX =>
      let x₀' : X := Classical.choice hX
      let g : IndexedConeAttachment.Prequotient X S → X
        | Sum.inl x => x
        | Sum.inr ⟨_, Sum.inl _⟩ => x₀'
        | Sum.inr ⟨j, Sum.inr (s, _)⟩ => f j s
      have hg : Continuous g := by
        rw [continuous_sum_dom]
        constructor
        · exact continuous_id
        · rw [continuous_sigma_iff]
          intro j
          rw [continuous_sum_dom]
          exact ⟨continuous_const, (hf j).comp continuous_fst⟩
      apply (hg.comp continuous_subtype_val).congr
      intro z
      have hz := indexedLowerSource_mem f z
      rcases z with ⟨x | ⟨j, (_ | ⟨s, t⟩)⟩, hz'⟩
      · rfl
      · contradiction
      · rfl

omit [TopologicalSpace X] [∀ j, TopologicalSpace (S j)] in
private theorem indexedLowerRetractionPre_eq_of_quotient_eq
    {a b : IndexedConeAttachment.quotientMk f ⁻¹'
      IndexedConeAttachment.lowerCover f}
    (h : (IndexedConeAttachment.lowerCover f).restrictPreimage
        (IndexedConeAttachment.quotientMk f) a =
      (IndexedConeAttachment.lowerCover f).restrictPreimage
        (IndexedConeAttachment.quotientMk f) b) :
    indexedLowerRetractionPre f a = indexedLowerRetractionPre f b := by
  have ha := indexedLowerSource_mem f a
  have hb := indexedLowerSource_mem f b
  have hrel := Quotient.exact (congrArg Subtype.val h)
  change IndexedConeAttachment.normalForm f a.1 =
    IndexedConeAttachment.normalForm f b.1 at hrel
  obtain ⟨a, ha'⟩ := a
  obtain ⟨b, hb'⟩ := b
  rcases a with x | ⟨j, a⟩
  · rcases b with y | ⟨k, b⟩
    · simp_all [IndexedConeAttachment.normalForm, indexedLowerRetractionPre]
    · rcases b with _ | ⟨r, v⟩
      · change False at hb
        contradiction
      · change 0 < v at hb
        simp only [IndexedConeAttachment.normalForm] at hrel
        split_ifs at hrel
        all_goals simp_all [indexedLowerRetractionPre]
  · rcases a with _ | ⟨s, t⟩
    · change False at ha
      contradiction
    · change 0 < t at ha
      rcases b with y | ⟨k, b⟩
      · simp only [IndexedConeAttachment.normalForm] at hrel
        split_ifs at hrel
        all_goals simp_all [indexedLowerRetractionPre]
      · rcases b with _ | ⟨r, v⟩
        · change False at hb
          contradiction
        · change 0 < v at hb
          simp only [IndexedConeAttachment.normalForm] at hrel
          split_ifs at hrel
          all_goals try simp_all [indexedLowerRetractionPre]
          obtain ⟨rfl, hsr⟩ := hrel
          cases hsr
          rfl

private noncomputable def indexedLowerRetractionMap :
    IndexedConeAttachment.lowerCover f → X := fun z =>
  indexedLowerRetractionPre f
    (Function.surjInv
      (IndexedConeAttachment.isQuotientMap_restrictPreimage_lowerCover f).surjective z)

private theorem indexedLowerRetractionMap_quotientMap
    (z : IndexedConeAttachment.quotientMk f ⁻¹'
      IndexedConeAttachment.lowerCover f) :
    indexedLowerRetractionMap f
        ((IndexedConeAttachment.lowerCover f).restrictPreimage
          (IndexedConeAttachment.quotientMk f) z) =
      indexedLowerRetractionPre f z := by
  apply indexedLowerRetractionPre_eq_of_quotient_eq f
  exact Function.surjInv_eq
    (IndexedConeAttachment.isQuotientMap_restrictPreimage_lowerCover f).surjective _

private theorem continuous_indexedLowerRetractionMap
    (hf : ∀ j, Continuous (f j)) :
    Continuous (indexedLowerRetractionMap f) := by
  apply (IndexedConeAttachment.isQuotientMap_restrictPreimage_lowerCover f).continuous_iff.mpr
  apply (continuous_indexedLowerRetractionPre f hf).congr
  intro z
  exact (indexedLowerRetractionMap_quotientMap f z).symm

private def indexedLowerBaseInclusion :
    C(X, IndexedConeAttachment.lowerCover f) where
  toFun x := ⟨IndexedConeAttachment.base f x,
    IndexedConeAttachment.base_mem_lowerCover f x⟩
  continuous_toFun := (IndexedConeAttachment.continuous_base f).subtype_mk _

private noncomputable def indexedLowerRetraction
    (hf : ∀ j, Continuous (f j)) :
    C(IndexedConeAttachment.lowerCover f, X) where
  toFun := indexedLowerRetractionMap f
  continuous_toFun := continuous_indexedLowerRetractionMap f hf

@[simp] private theorem indexedLowerRetraction_apply_base
    (hf : ∀ j, Continuous (f j)) (x : X) :
    indexedLowerRetraction f hf (indexedLowerBaseInclusion f x) = x := by
  let a : IndexedConeAttachment.quotientMk f ⁻¹'
      IndexedConeAttachment.lowerCover f :=
    ⟨Sum.inl x, IndexedConeAttachment.base_mem_lowerCover f x⟩
  have ha : (IndexedConeAttachment.lowerCover f).restrictPreimage
      (IndexedConeAttachment.quotientMk f) a =
      indexedLowerBaseInclusion f x := rfl
  change indexedLowerRetractionMap f (indexedLowerBaseInclusion f x) = x
  rw [← ha, indexedLowerRetractionMap_quotientMap f]
  rfl

private theorem indexedLowerDeformationMap_zero
    (z : IndexedConeAttachment.lowerCover f) :
    indexedLowerDeformationMap f (0, z) = z := by
  obtain ⟨a, rfl⟩ :=
    (IndexedConeAttachment.isQuotientMap_restrictPreimage_lowerCover f).surjective z
  rw [indexedLowerDeformationMap_quotientMap]
  apply Subtype.ext
  rcases a with ⟨x | ⟨j, (_ | ⟨s, t⟩)⟩, ha⟩ <;>
    simp [indexedLowerRawRestricted, indexedLowerRaw,
      IndexedConeAttachment.base, IndexedConeAttachment.apex,
      IndexedConeAttachment.cylinder]

private theorem indexedLowerDeformationMap_one
    (hf : ∀ j, Continuous (f j))
    (z : IndexedConeAttachment.lowerCover f) :
    indexedLowerDeformationMap f (1, z) =
      indexedLowerBaseInclusion f (indexedLowerRetraction f hf z) := by
  obtain ⟨a, rfl⟩ :=
    (IndexedConeAttachment.isQuotientMap_restrictPreimage_lowerCover f).surjective z
  rw [indexedLowerDeformationMap_quotientMap]
  change indexedLowerRawRestricted f (1, a) =
    indexedLowerBaseInclusion f
      (indexedLowerRetractionMap f
        ((IndexedConeAttachment.lowerCover f).restrictPreimage
          (IndexedConeAttachment.quotientMk f) a))
  rw [indexedLowerRetractionMap_quotientMap f]
  apply Subtype.ext
  have ha := indexedLowerSource_mem f a
  rcases a with ⟨x | ⟨j, (_ | ⟨s, t⟩)⟩, ha'⟩
  · rfl
  · contradiction
  · simp [indexedLowerRawRestricted, indexedLowerRaw,
      indexedLowerBaseInclusion, indexedLowerRetractionPre]

private theorem indexedLowerDeformationMap_base (u : I) (x : X) :
    indexedLowerDeformationMap f (u, indexedLowerBaseInclusion f x) =
      indexedLowerBaseInclusion f x := by
  let a : IndexedConeAttachment.quotientMk f ⁻¹'
      IndexedConeAttachment.lowerCover f :=
    ⟨Sum.inl x, IndexedConeAttachment.base_mem_lowerCover f x⟩
  have ha : (IndexedConeAttachment.lowerCover f).restrictPreimage
      (IndexedConeAttachment.quotientMk f) a =
      indexedLowerBaseInclusion f x := rfl
  rw [← ha, indexedLowerDeformationMap_quotientMap]
  rfl

private def indexedLowerDeformation
    (hf : ∀ j, Continuous (f j)) :
    (ContinuousMap.id (IndexedConeAttachment.lowerCover f)).HomotopyRel
      ((indexedLowerBaseInclusion f).comp (indexedLowerRetraction f hf))
      (Set.range (indexedLowerBaseInclusion f)) where
  toFun := indexedLowerDeformationMap f
  continuous_toFun := continuous_indexedLowerDeformationMap f
  map_zero_left := indexedLowerDeformationMap_zero f
  map_one_left := indexedLowerDeformationMap_one f hf
  prop' u z hz := by
    obtain ⟨x, rfl⟩ := hz
    exact indexedLowerDeformationMap_base f u x

private def indexedLowerStrongDeformationRetract
    (hf : ∀ j, Continuous (f j)) :
    Hatcher.StrongDeformationRetract (indexedLowerBaseInclusion f) where
  retract := indexedLowerRetraction f hf
  retract_inclusion := by
    ext x
    exact indexedLowerRetraction_apply_base f hf x
  deformation := indexedLowerDeformation f hf

/-- The indexed lower cover included into the auxiliary base cover. -/
private def indexedLowerToBaseCover :
    C(IndexedConeAttachment.lowerCover f, baseCover f s₀ x₀ γ) where
  toFun y := ⟨attachment f s₀ x₀ γ y,
    (attachment_mem_baseCover_iff f s₀ x₀ γ y).2 y.2⟩
  continuous_toFun := (attachment f s₀ x₀ γ).continuous.comp
    continuous_subtype_val |>.subtype_mk _

private theorem auxiliaryRetraction_mem_indexedLower
    (z : baseCover f s₀ x₀ γ) :
    retraction f s₀ x₀ γ z.1 ∈ IndexedConeAttachment.lowerCover f := by
  obtain ⟨a, ha⟩ :=
    (isQuotientMap_restrictPreimage_baseCover f s₀ x₀ γ).surjective z
  have haval : quotientMk f s₀ x₀ γ a.1 = z.1 :=
    congrArg Subtype.val ha
  rw [← haval, retraction_quotientMk]
  rcases a with ⟨y | (t | ⟨j, p⟩), hmem⟩
  · change attachment f s₀ x₀ γ y ∈ baseCover f s₀ x₀ γ at hmem
    exact (attachment_mem_baseCover_iff f s₀ x₀ γ y).1 hmem
  · exact IndexedConeAttachment.base_mem_lowerCover f x₀
  · simp only [retractionRaw]
    unfold stripRetraction
    split_ifs
    · exact IndexedConeAttachment.base_mem_lowerCover f _
    · exact (IndexedConeAttachment.cylinder_mem_lowerCover_iff f j
        (s₀ j) _).2 (truncatedRadialHeight_pos _)

private noncomputable def baseCoverToIndexedLower :
    C(baseCover f s₀ x₀ γ, IndexedConeAttachment.lowerCover f) where
  toFun z := ⟨retraction f s₀ x₀ γ z.1,
    auxiliaryRetraction_mem_indexedLower f s₀ x₀ γ z⟩
  continuous_toFun := (retraction f s₀ x₀ γ).continuous.comp
    continuous_subtype_val |>.subtype_mk _

private theorem auxiliaryDeformation_mem_baseCover (u : I)
    (z : baseCover f s₀ x₀ γ) :
    deformationMap f s₀ x₀ γ (u, z.1) ∈ baseCover f s₀ x₀ γ := by
  obtain ⟨a, ha⟩ :=
    (isQuotientMap_restrictPreimage_baseCover f s₀ x₀ γ).surjective z
  have haval : quotientMk f s₀ x₀ γ a.1 = z.1 :=
    congrArg Subtype.val ha
  rw [← haval, deformationMap_quotientMk]
  rcases a with ⟨y | (t | ⟨j, p⟩), hmem⟩
  · change attachment f s₀ x₀ γ y ∈ baseCover f s₀ x₀ γ at hmem
    exact hmem
  · exact spine_mem_baseCover f s₀ x₀ γ _
  · exact strip_mem_baseCover f s₀ x₀ γ j _

private noncomputable def auxiliaryBaseCoverDeformationMap :
    I × baseCover f s₀ x₀ γ → baseCover f s₀ x₀ γ :=
  fun p => ⟨deformationMap f s₀ x₀ γ (p.1, p.2.1),
    auxiliaryDeformation_mem_baseCover f s₀ x₀ γ p.1 p.2⟩

private theorem continuous_auxiliaryBaseCoverDeformationMap :
    Continuous (auxiliaryBaseCoverDeformationMap f s₀ x₀ γ) := by
  apply Continuous.subtype_mk
  exact (continuous_deformationMap f s₀ x₀ γ).comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))

private theorem auxiliaryBaseCoverDeformationMap_zero
    (z : baseCover f s₀ x₀ γ) :
    auxiliaryBaseCoverDeformationMap f s₀ x₀ γ (0, z) = z := by
  apply Subtype.ext
  exact deformationMap_zero f s₀ x₀ γ z.1

private theorem auxiliaryBaseCoverDeformationMap_one
    (z : baseCover f s₀ x₀ γ) :
    auxiliaryBaseCoverDeformationMap f s₀ x₀ γ (1, z) =
      indexedLowerToBaseCover f s₀ x₀ γ
        (baseCoverToIndexedLower f s₀ x₀ γ z) := by
  apply Subtype.ext
  exact deformationMap_one f s₀ x₀ γ z.1

private theorem auxiliaryBaseCoverDeformationMap_indexedLower
    (u : I) (y : IndexedConeAttachment.lowerCover f) :
    auxiliaryBaseCoverDeformationMap f s₀ x₀ γ
        (u, indexedLowerToBaseCover f s₀ x₀ γ y) =
      indexedLowerToBaseCover f s₀ x₀ γ y := by
  apply Subtype.ext
  exact deformationMap_attachment f s₀ x₀ γ u y.1

private def auxiliaryBaseCoverDeformation :
    (ContinuousMap.id (baseCover f s₀ x₀ γ)).HomotopyRel
      ((indexedLowerToBaseCover f s₀ x₀ γ).comp
        (baseCoverToIndexedLower f s₀ x₀ γ))
      (Set.range (indexedLowerToBaseCover f s₀ x₀ γ)) where
  toFun := auxiliaryBaseCoverDeformationMap f s₀ x₀ γ
  continuous_toFun := continuous_auxiliaryBaseCoverDeformationMap f s₀ x₀ γ
  map_zero_left := auxiliaryBaseCoverDeformationMap_zero f s₀ x₀ γ
  map_one_left := auxiliaryBaseCoverDeformationMap_one f s₀ x₀ γ
  prop' u z hz := by
    obtain ⟨y, rfl⟩ := hz
    exact auxiliaryBaseCoverDeformationMap_indexedLower f s₀ x₀ γ u y

private def indexedLowerToBaseCoverStrongDeformationRetract :
    Hatcher.StrongDeformationRetract
      (indexedLowerToBaseCover f s₀ x₀ γ) where
  retract := baseCoverToIndexedLower f s₀ x₀ γ
  retract_inclusion := by
    ext y
    exact retraction_attachment f s₀ x₀ γ y.1
  deformation := auxiliaryBaseCoverDeformation f s₀ x₀ γ

private def strongDeformationRetractTrans
    {A B Y : Type u} [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalSpace Y] {i : C(A, B)} {j : C(B, Y)}
    (hAB : Hatcher.StrongDeformationRetract i)
    (hBY : Hatcher.StrongDeformationRetract j) :
    Hatcher.StrongDeformationRetract (j.comp i) where
  retract := hAB.retract.comp hBY.retract
  retract_inclusion := by
    ext a
    have houter := congrArg (fun g : C(B, B) => g (i a))
      hBY.retract_inclusion
    have hinner := congrArg (fun g : C(A, A) => g a)
      hAB.retract_inclusion
    exact (congrArg hAB.retract houter).trans hinner
  deformation := by
    let F : (ContinuousMap.id Y).HomotopyRel
        (j.comp hBY.retract) (Set.range (j.comp i)) := {
      toFun := hBY.deformation
      continuous_toFun := hBY.deformation.continuous
      map_zero_left := hBY.deformation.apply_zero
      map_one_left := hBY.deformation.apply_one
      prop' t y hy := by
        apply hBY.deformation.eq_fst
        rcases hy with ⟨a, rfl⟩
        exact ⟨i a, rfl⟩ }
    let G : (j.comp hBY.retract).HomotopyRel
        ((j.comp i).comp (hAB.retract.comp hBY.retract))
        (Set.range (j.comp i)) := {
      toFun p := j (hAB.deformation (p.1, hBY.retract p.2))
      continuous_toFun := j.continuous.comp
        (hAB.deformation.continuous.comp
          (continuous_fst.prodMk (hBY.retract.continuous.comp continuous_snd)))
      map_zero_left y := by
        simp only [hAB.deformation.apply_zero]
        rfl
      map_one_left y := by
        simp only [hAB.deformation.apply_one]
        rfl
      prop' t y hy := by
        rcases hy with ⟨a, rfl⟩
        have houter := congrArg (fun g : C(B, B) => g (i a))
          hBY.retract_inclusion
        change j (hAB.deformation (t, hBY.retract (j (i a)))) =
          j (hBY.retract (j (i a)))
        rw [show hBY.retract (j (i a)) = i a by exact houter]
        exact congrArg j (hAB.deformation.eq_fst t ⟨a, rfl⟩) }
    exact F.trans G

/-- The base-side member of the auxiliary cover strongly deformation-retracts
onto the canonical copy of the original base. -/
def baseCoverStrongDeformationRetract
    (hf : ∀ j, Continuous (f j)) :
    Hatcher.StrongDeformationRetract (baseToBaseCover f s₀ x₀ γ) := by
  have hcomp :
      (indexedLowerToBaseCover f s₀ x₀ γ).comp
          (indexedLowerBaseInclusion f) =
        baseToBaseCover f s₀ x₀ γ := by
    ext x
    rfl
  rw [← hcomp]
  exact strongDeformationRetractTrans
    (indexedLowerStrongDeformationRetract f hf)
    (indexedLowerToBaseCoverStrongDeformationRetract f s₀ x₀ γ)

/-- The base-side retraction collapses the common auxiliary spine to the
chosen basepoint of the original space. -/
@[simp] theorem baseCoverStrongDeformationRetract_retract_spine
    (hf : ∀ j, Continuous (f j)) (t : I) :
    (baseCoverStrongDeformationRetract f s₀ x₀ γ hf).retract
        ⟨spine f s₀ x₀ γ t, spine_mem_baseCover f s₀ x₀ γ t⟩ = x₀ := by
  change indexedLowerRetraction f hf
    (baseCoverToIndexedLower f s₀ x₀ γ
      ⟨spine f s₀ x₀ γ t, spine_mem_baseCover f s₀ x₀ γ t⟩) = x₀
  have hr : retraction f s₀ x₀ γ (spine f s₀ x₀ γ t) =
      IndexedConeAttachment.base f x₀ := by
    change retraction f s₀ x₀ γ
      (quotientMk f s₀ x₀ γ (Sum.inr (Sum.inl t))) = _
    rw [retraction_quotientMk]
    rfl
  rw [show baseCoverToIndexedLower f s₀ x₀ γ
      ⟨spine f s₀ x₀ γ t, spine_mem_baseCover f s₀ x₀ γ t⟩ =
      indexedLowerBaseInclusion f x₀ by
    apply Subtype.ext
    exact hr]
  exact indexedLowerRetraction_apply_base f hf x₀

/-- In particular, the chosen binary-cover basepoint retracts to `x₀`. -/
@[simp] theorem baseCoverStrongDeformationRetract_retract_overlapBasepoint
    (hf : ∀ j, Continuous (f j)) :
    (baseCoverStrongDeformationRetract f s₀ x₀ γ hf).retract
        ⟨overlapBasepoint f s₀ x₀ γ,
          overlapBasepoint_mem_baseCover f s₀ x₀ γ⟩ = x₀ := by
  simp [overlapBasepoint]

end Hatcher.VanKampen.AuxiliaryCellAttachment
