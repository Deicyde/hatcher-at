import Hatcher.VanKampen.AuxiliaryCellAttachment
import Hatcher.VanKampen.WellPointedWedgeCover
import Mathlib.Topology.CompactOpen

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

end Hatcher.VanKampen.AuxiliaryCellAttachment
