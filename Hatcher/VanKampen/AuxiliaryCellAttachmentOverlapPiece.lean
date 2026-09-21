import Hatcher.VanKampen.AuxiliaryCellAttachmentBasepoint
import Hatcher.VanKampen.AuxiliaryCellAttachmentOverlapCover
import Hatcher.VanKampen.ConeAttachmentIntersection

/-!
# The homotopy type of an auxiliary overlap piece

Each member of the indexed overlap cover strongly deformation-retracts onto
the open cylinder in its selected cone. This identifies the piece with its
attaching space; for a cell attachment, that space is the corresponding disk
boundary.
-/

noncomputable section

open Set Topology
open scoped unitInterval ContinuousMap

namespace Hatcher.VanKampen.IndexedConeAttachment

universe u

variable {X J : Type u} {S : J → Type u}
variable [TopologicalSpace X] [∀ j, TopologicalSpace (S j)]

private def interiorRaw (j : J) :
    S j × Set.Ioo (0 : I) 1 → Prequotient X S :=
  fun p ↦ Sum.inr ⟨j, Sum.inr (p.1, p.2.1)⟩

private theorem isEmbedding_interiorRaw (j : J) :
    IsEmbedding (interiorRaw (X := X) (S := S) j) := by
  exact IsEmbedding.inr.comp <| IsEmbedding.sigmaMk.comp <|
    IsEmbedding.inr.comp <| IsEmbedding.id.prodMap IsEmbedding.subtypeVal

omit [TopologicalSpace X] [∀ j, TopologicalSpace (S j)] in
private theorem range_interiorRaw (f : ∀ j, S j → X) (j : J) :
    Set.range (interiorRaw (X := X) (S := S) j) =
      quotientMk f ⁻¹' interiorPiece f j := by
  ext z
  constructor
  · rintro ⟨⟨s, t⟩, rfl⟩
    rw [quotientMk_preimage_interiorPiece]
    exact ⟨rfl, t.2.1, t.2.2⟩
  · intro hz
    rw [quotientMk_preimage_interiorPiece] at hz
    rcases z with x | ⟨k, star | ⟨s, t⟩⟩
    · exact False.elim hz
    · exact False.elim hz
    · rcases hz with ⟨rfl, ht0, ht1⟩
      exact ⟨⟨s, ⟨t, ht0, ht1⟩⟩, rfl⟩

private noncomputable def interiorPreimageHomeomorph
    (f : ∀ j, S j → X) (j : J) :
    S j × Set.Ioo (0 : I) 1 ≃ₜ quotientMk f ⁻¹' interiorPiece f j :=
  (isEmbedding_interiorRaw (X := X) (S := S) j).toHomeomorph.trans
    (Homeomorph.setCongr (range_interiorRaw f j))

private theorem isQuotientMap_restrictPreimage_interiorPiece
    (f : ∀ j, S j → X) (j : J) :
    IsQuotientMap ((interiorPiece f j).restrictPreimage (quotientMk f)) :=
  (isQuotientMap_quot_mk : IsQuotientMap (quotientMk f)).restrictPreimage_isOpen
    (isOpen_interiorPiece f j)

omit [TopologicalSpace X] [∀ j, TopologicalSpace (S j)] in
private theorem injective_restrictPreimage_interiorPiece
    (f : ∀ j, S j → X) (j : J) :
    Function.Injective ((interiorPiece f j).restrictPreimage (quotientMk f)) := by
  intro a b hab
  have ha : a.1 ∈ Set.range (interiorRaw (X := X) (S := S) j) := by
    rw [range_interiorRaw f j]
    exact a.2
  have hb : b.1 ∈ Set.range (interiorRaw (X := X) (S := S) j) := by
    rw [range_interiorRaw f j]
    exact b.2
  obtain ⟨p, hp⟩ := ha
  obtain ⟨q, hq⟩ := hb
  apply Subtype.ext
  rw [← hp, ← hq]
  have hrel := Quotient.exact (congrArg Subtype.val hab)
  change normalForm f a.1 = normalForm f b.1 at hrel
  rw [← hp, ← hq] at hrel
  have hpq : p.1 = q.1 ∧ (p.2 : I) = q.2 := by
    simpa [interiorRaw, normalForm, ne_of_gt p.2.2.1,
      ne_of_lt p.2.2.2, ne_of_gt q.2.2.1,
      ne_of_lt q.2.2.2] using hrel
  exact congrArg (interiorRaw (X := X) (S := S) j)
    (Prod.ext hpq.1 (Subtype.ext hpq.2))

private noncomputable def homeomorphOfQuotientInjective
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {g : A → B} (hg : IsQuotientMap g) (hinj : Function.Injective g) :
    A ≃ₜ B := by
  let e : A ≃ B := Equiv.ofBijective g ⟨hinj, hg.surjective⟩
  exact
    { toEquiv := e
      continuous_toFun := hg.continuous
      continuous_invFun := hg.continuous_iff.mpr <| by
        convert continuous_id using 1
        funext a
        exact e.symm_apply_apply a }

private noncomputable def preimageHomeomorphInteriorPiece
    (f : ∀ j, S j → X) (j : J) :
    (quotientMk f ⁻¹' interiorPiece f j) ≃ₜ ↑(interiorPiece f j) :=
  homeomorphOfQuotientInjective
    (isQuotientMap_restrictPreimage_interiorPiece f j)
    (injective_restrictPreimage_interiorPiece f j)

/-- The selected indexed cone interior has the expected open-cylinder chart. -/
noncomputable def interiorCylinderHomeomorphInteriorPiece
    (f : ∀ j, S j → X) (j : J) :
    S j × Set.Ioo (0 : I) 1 ≃ₜ ↑(interiorPiece f j) :=
  (interiorPreimageHomeomorph f j).trans
    (preimageHomeomorphInteriorPiece f j)

@[simp] theorem interiorCylinderHomeomorphInteriorPiece_apply
    (f : ∀ j, S j → X) (j : J) (s : S j) (t : Set.Ioo (0 : I) 1) :
    interiorCylinderHomeomorphInteriorPiece f j (s, t) =
      (⟨cylinder f j s t.1,
        (cylinder_mem_interiorPiece_iff f j j s t.1).mpr
          ⟨rfl, t.2.1, t.2.2⟩⟩ : ↑(interiorPiece f j)) := by
  rfl

@[simp] theorem interiorCylinderHomeomorphInteriorPiece_symm_apply_cylinder
    (f : ∀ j, S j → X) (j : J) (s : S j) (t : I)
    (ht0 : 0 < t) (ht1 : t < 1) :
    (interiorCylinderHomeomorphInteriorPiece f j).symm
        ⟨cylinder f j s t,
          (cylinder_mem_interiorPiece_iff f j j s t).mpr ⟨rfl, ht0, ht1⟩⟩ =
      (s, ⟨t, ht0, ht1⟩) := by
  apply (interiorCylinderHomeomorphInteriorPiece f j).injective
  rw [(interiorCylinderHomeomorphInteriorPiece f j).apply_symm_apply]
  rfl

end Hatcher.VanKampen.IndexedConeAttachment

namespace Hatcher.VanKampen.AuxiliaryCellAttachment

universe u

variable {X J : Type u} {S : J → Type u}
variable [TopologicalSpace X] [∀ j, TopologicalSpace (S j)]
variable (f : ∀ j, S j → X) (s₀ : ∀ j, S j) (x₀ : X)
variable (γ : ∀ j, Path x₀ (f j (s₀ j)))

local instance : DecidableEq J := Classical.decEq J

private theorem truncatedRadialHeight_lt_one_iff' (t : I) :
    truncatedRadialHeight t < 1 ↔ 0 < t := by
  change 1 - (t : ℝ) / 2 < 1 ↔ 0 < (t : ℝ)
  constructor <;> intro h <;> linarith

private def phaseAHorizontal (u a : I) : I :=
  Set.Icc.convexComb a 0 u

private def phaseBHorizontal (u a : I) : I :=
  Set.Icc.convexComb a 1 u

private theorem continuous_phaseAHorizontal :
    Continuous fun p : I × I ↦ phaseAHorizontal p.1 p.2 := by
  unfold phaseAHorizontal
  fun_prop

private theorem continuous_phaseBHorizontal :
    Continuous fun p : I × I ↦ phaseBHorizontal p.1 p.2 := by
  unfold phaseBHorizontal
  fun_prop

private theorem phaseAHorizontal_lt_one (u a : I) (ha : a < 1) :
    phaseAHorizontal u a < 1 := by
  change Set.Icc.convexComb a 0 u < 1
  have h : Set.Icc.convexComb (0 : I) a (unitInterval.symm u) ≤ a :=
    Set.Icc.convexComb_le a.property.1 (unitInterval.symm u)
  rw [Set.Icc.convexComb_symm] at h
  exact lt_of_le_of_lt h ha

private def phaseARaw (j : J) :
    I × Prequotient f →
      Hatcher.VanKampen.AuxiliaryCellAttachment f s₀ x₀ γ
  | (_, Sum.inl y) => attachment f s₀ x₀ γ y
  | (_, Sum.inr (Sum.inl t)) => spine f s₀ x₀ γ t
  | (u, Sum.inr (Sum.inr ⟨k, (a, t)⟩)) =>
      if k = j then strip f s₀ x₀ γ k (a, t)
      else strip f s₀ x₀ γ k (phaseAHorizontal u a, t)

private theorem continuous_phaseARaw (j : J) :
    Continuous (phaseARaw f s₀ x₀ γ j) := by
  let gstrip : (Σ k : J, (I × I) × I) →
      Hatcher.VanKampen.AuxiliaryCellAttachment f s₀ x₀ γ
    | ⟨k, (a, t), u⟩ =>
        if k = j then strip f s₀ x₀ γ k (a, t)
        else strip f s₀ x₀ γ k (phaseAHorizontal u a, t)
  have hgstrip : Continuous gstrip := by
    rw [continuous_sigma_iff]
    intro k
    by_cases hkj : k = j
    · simp only [gstrip, hkj, if_true]
      fun_prop
    · simp only [gstrip, hkj, if_false]
      exact (strip f s₀ x₀ γ k).continuous.comp
        ((continuous_phaseAHorizontal.comp
            (continuous_snd.prodMk (continuous_fst.comp continuous_fst))).prodMk
          (continuous_snd.comp continuous_fst))
  let gright : (I × I) ⊕ (I × (Σ _k : J, I × I)) →
      Hatcher.VanKampen.AuxiliaryCellAttachment f s₀ x₀ γ
    | Sum.inl (_, t) => spine f s₀ x₀ γ t
    | Sum.inr p => gstrip
        ((Homeomorph.sigmaProdDistrib :
          (Σ _k : J, I × I) × I ≃ₜ Σ _k : J, (I × I) × I)
          (Prod.swap p))
  have hgright : Continuous gright := by
    rw [continuous_sum_dom]
    constructor
    · exact (spine f s₀ x₀ γ).continuous.comp continuous_snd
    · exact hgstrip.comp
        ((Homeomorph.sigmaProdDistrib :
          (Σ _k : J, I × I) × I ≃ₜ Σ _k : J, (I × I) × I).continuous.comp
            continuous_swap)
  let g : (I × Hatcher.VanKampen.IndexedConeAttachment f) ⊕
      (I × (I ⊕ (Σ _k : J, I × I))) →
      Hatcher.VanKampen.AuxiliaryCellAttachment f s₀ x₀ γ
    | Sum.inl (_, y) => attachment f s₀ x₀ γ y
    | Sum.inr p => gright
        ((Homeomorph.prodSumDistrib :
          I × (I ⊕ (Σ _k : J, I × I)) ≃ₜ
            (I × I) ⊕ (I × (Σ _k : J, I × I))) p)
  have hg : Continuous g := by
    rw [continuous_sum_dom]
    constructor
    · exact (attachment f s₀ x₀ γ).continuous.comp continuous_snd
    · exact hgright.comp
        (Homeomorph.prodSumDistrib :
          I × (I ⊕ (Σ _k : J, I × I)) ≃ₜ
            (I × I) ⊕ (I × (Σ _k : J, I × I))).continuous
  apply (hg.comp
    (Homeomorph.prodSumDistrib :
      I × Prequotient f ≃ₜ
        (I × Hatcher.VanKampen.IndexedConeAttachment f) ⊕
          (I × (I ⊕ (Σ _k : J, I × I)))).continuous).congr
  rintro ⟨u, y | (t | ⟨k, a, t⟩)⟩ <;> rfl

private def phaseBRaw (j : J) :
    I × Prequotient f →
      Hatcher.VanKampen.AuxiliaryCellAttachment f s₀ x₀ γ
  | (_, Sum.inl y) => attachment f s₀ x₀ γ y
  | (u, Sum.inr (Sum.inl t)) => strip f s₀ x₀ γ j (u, t)
  | (u, Sum.inr (Sum.inr ⟨k, (a, t)⟩)) =>
      if k = j then strip f s₀ x₀ γ j (phaseBHorizontal u a, t)
      else strip f s₀ x₀ γ j (u, t)

private theorem continuous_phaseBRaw (j : J) :
    Continuous (phaseBRaw f s₀ x₀ γ j) := by
  let gstrip : (Σ k : J, (I × I) × I) →
      Hatcher.VanKampen.AuxiliaryCellAttachment f s₀ x₀ γ
    | ⟨k, (a, t), u⟩ =>
        if k = j then strip f s₀ x₀ γ j (phaseBHorizontal u a, t)
        else strip f s₀ x₀ γ j (u, t)
  have hgstrip : Continuous gstrip := by
    rw [continuous_sigma_iff]
    intro k
    by_cases hkj : k = j
    · simp only [gstrip, hkj, if_true]
      exact (strip f s₀ x₀ γ j).continuous.comp
        ((continuous_phaseBHorizontal.comp
            (continuous_snd.prodMk (continuous_fst.comp continuous_fst))).prodMk
          (continuous_snd.comp continuous_fst))
    · simp only [gstrip, hkj, if_false]
      fun_prop
  let gright : (I × I) ⊕ (I × (Σ _k : J, I × I)) →
      Hatcher.VanKampen.AuxiliaryCellAttachment f s₀ x₀ γ
    | Sum.inl (u, t) => strip f s₀ x₀ γ j (u, t)
    | Sum.inr p => gstrip
        ((Homeomorph.sigmaProdDistrib :
          (Σ _k : J, I × I) × I ≃ₜ Σ _k : J, (I × I) × I)
          (Prod.swap p))
  have hgright : Continuous gright := by
    rw [continuous_sum_dom]
    constructor
    · exact (strip f s₀ x₀ γ j).continuous.comp
        (continuous_fst.prodMk continuous_snd)
    · exact hgstrip.comp
        ((Homeomorph.sigmaProdDistrib :
          (Σ _k : J, I × I) × I ≃ₜ Σ _k : J, (I × I) × I).continuous.comp
            continuous_swap)
  let g : (I × Hatcher.VanKampen.IndexedConeAttachment f) ⊕
      (I × (I ⊕ (Σ _k : J, I × I))) →
      Hatcher.VanKampen.AuxiliaryCellAttachment f s₀ x₀ γ
    | Sum.inl (_, y) => attachment f s₀ x₀ γ y
    | Sum.inr p => gright
        ((Homeomorph.prodSumDistrib :
          I × (I ⊕ (Σ _k : J, I × I)) ≃ₜ
            (I × I) ⊕ (I × (Σ _k : J, I × I))) p)
  have hg : Continuous g := by
    rw [continuous_sum_dom]
    constructor
    · exact (attachment f s₀ x₀ γ).continuous.comp continuous_snd
    · exact hgright.comp
        (Homeomorph.prodSumDistrib :
          I × (I ⊕ (Σ _k : J, I × I)) ≃ₜ
            (I × I) ⊕ (I × (Σ _k : J, I × I))).continuous
  apply (hg.comp
    (Homeomorph.prodSumDistrib :
      I × Prequotient f ≃ₜ
        (I × Hatcher.VanKampen.IndexedConeAttachment f) ⊕
          (I × (I ⊕ (Σ _k : J, I × I)))).continuous).congr
  rintro ⟨u, y | (t | ⟨k, a, t⟩)⟩ <;> rfl

private theorem phaseARaw_mem (j : J) (u : I)
    (z : quotientMk f s₀ x₀ γ ⁻¹' intersectionPieceAmbient f s₀ x₀ γ j) :
    phaseARaw f s₀ x₀ γ j (u, z.1) ∈
      intersectionPieceAmbient f s₀ x₀ γ j := by
  rcases z with ⟨y | (t | ⟨k, a, t⟩), hmem⟩
  · change attachment f s₀ x₀ γ y ∈
      intersectionPieceAmbient f s₀ x₀ γ j at hmem ⊢
    exact hmem
  · change spine f s₀ x₀ γ t ∈
      intersectionPieceAmbient f s₀ x₀ γ j at hmem ⊢
    exact hmem
  · have hraw : 0 < t ∧ (k = j ∨ a < 1) := by
      exact (strip_mem_intersectionPieceAmbient_iff
        f s₀ x₀ γ j k a t).mp hmem
    by_cases hkj : k = j
    · subst k
      simp only [phaseARaw]
      exact (strip_mem_intersectionPieceAmbient_iff
        f s₀ x₀ γ j j a t).mpr hraw
    · simp only [phaseARaw, hkj, if_false]
      apply (strip_mem_intersectionPieceAmbient_iff
        f s₀ x₀ γ j k (phaseAHorizontal u a) t).mpr
      exact ⟨hraw.1, Or.inr (phaseAHorizontal_lt_one u a
        (hraw.2.resolve_left hkj))⟩

private theorem phaseBRaw_mem (j : J) (u : I)
    (z : quotientMk f s₀ x₀ γ ⁻¹' intersectionPieceAmbient f s₀ x₀ γ j) :
    phaseBRaw f s₀ x₀ γ j (u, z.1) ∈
      intersectionPieceAmbient f s₀ x₀ γ j := by
  rcases z with ⟨y | (t | ⟨k, a, t⟩), hmem⟩
  · change attachment f s₀ x₀ γ y ∈
      intersectionPieceAmbient f s₀ x₀ γ j at hmem ⊢
    exact hmem
  · have ht := (spine_mem_intersectionPieceAmbient_iff
      f s₀ x₀ γ j t).mp hmem
    exact (strip_mem_intersectionPieceAmbient_iff
      f s₀ x₀ γ j j u t).mpr ⟨ht, Or.inl rfl⟩
  · have ht := (strip_mem_intersectionPieceAmbient_iff
      f s₀ x₀ γ j k a t).mp hmem |>.1
    by_cases hkj : k = j
    · subst k
      simp only [phaseBRaw]
      exact (strip_mem_intersectionPieceAmbient_iff
        f s₀ x₀ γ j j (phaseBHorizontal u a) t).mpr
          ⟨ht, Or.inl rfl⟩
    · simp only [phaseBRaw, hkj, if_false]
      exact (strip_mem_intersectionPieceAmbient_iff
        f s₀ x₀ γ j j u t).mpr ⟨ht, Or.inl rfl⟩

private def phaseARawRestricted (j : J) :
    I × (quotientMk f s₀ x₀ γ ⁻¹'
      intersectionPieceAmbient f s₀ x₀ γ j) →
      ↑(intersectionPieceAmbient f s₀ x₀ γ j) :=
  fun p ↦ ⟨phaseARaw f s₀ x₀ γ j (p.1, p.2.1),
    phaseARaw_mem f s₀ x₀ γ j p.1 p.2⟩

private theorem continuous_phaseARawRestricted (j : J) :
    Continuous (phaseARawRestricted f s₀ x₀ γ j) := by
  apply Continuous.subtype_mk
  exact (continuous_phaseARaw f s₀ x₀ γ j).comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))

private def phaseBRawRestricted (j : J) :
    I × (quotientMk f s₀ x₀ γ ⁻¹'
      intersectionPieceAmbient f s₀ x₀ γ j) →
      ↑(intersectionPieceAmbient f s₀ x₀ γ j) :=
  fun p ↦ ⟨phaseBRaw f s₀ x₀ γ j (p.1, p.2.1),
    phaseBRaw_mem f s₀ x₀ γ j p.1 p.2⟩

private theorem continuous_phaseBRawRestricted (j : J) :
    Continuous (phaseBRawRestricted f s₀ x₀ γ j) := by
  apply Continuous.subtype_mk
  exact (continuous_phaseBRaw f s₀ x₀ γ j).comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))

private theorem phaseARaw_normalForm (j : J) (u : I) (z : Prequotient f)
    (hz : quotientMk f s₀ x₀ γ z ∈
      intersectionPieceAmbient f s₀ x₀ γ j) :
    phaseARaw f s₀ x₀ γ j (u, normalForm f s₀ x₀ γ z) =
      phaseARaw f s₀ x₀ γ j (u, z) := by
  rcases z with y | (t | ⟨k, a, t⟩)
  · rfl
  · have ht := (spine_mem_intersectionPieceAmbient_iff
      f s₀ x₀ γ j t).mp hz
    simp [normalForm, phaseARaw, ne_of_gt ht]
  · have hm := (strip_mem_intersectionPieceAmbient_iff
      f s₀ x₀ γ j k a t).mp hz
    have ht0 : t ≠ 0 := ne_of_gt hm.1
    by_cases ha0 : a = 0
    · subst a
      by_cases hkj : k = j
      · subst k
        simp [normalForm, phaseARaw, ht0]
      · simp [normalForm, phaseARaw, ht0, hkj, phaseAHorizontal]
    · by_cases ha1 : a = 1
      · subst a
        have hkj : k = j := hm.2.resolve_right (lt_irrefl 1)
        subst k
        simp [normalForm, phaseARaw, ht0]
      · simp [normalForm, phaseARaw, ht0, ha0, ha1]

private theorem phaseBRaw_normalForm (j : J) (u : I) (z : Prequotient f)
    (hz : quotientMk f s₀ x₀ γ z ∈
      intersectionPieceAmbient f s₀ x₀ γ j) :
    phaseBRaw f s₀ x₀ γ j (u, normalForm f s₀ x₀ γ z) =
      phaseBRaw f s₀ x₀ γ j (u, z) := by
  rcases z with y | (t | ⟨k, a, t⟩)
  · rfl
  · have ht := (spine_mem_intersectionPieceAmbient_iff
      f s₀ x₀ γ j t).mp hz
    simp [normalForm, phaseBRaw, ne_of_gt ht]
  · have hm := (strip_mem_intersectionPieceAmbient_iff
      f s₀ x₀ γ j k a t).mp hz
    have ht0 : t ≠ 0 := ne_of_gt hm.1
    by_cases ha0 : a = 0
    · subst a
      by_cases hkj : k = j
      · subst k
        simp [normalForm, phaseBRaw, ht0, phaseBHorizontal]
      · simp [normalForm, phaseBRaw, ht0, hkj]
    · by_cases ha1 : a = 1
      · subst a
        have hkj : k = j := hm.2.resolve_right (lt_irrefl 1)
        subst k
        simp [normalForm, phaseBRaw, ht0, phaseBHorizontal]
      · simp [normalForm, phaseBRaw, ht0, ha0, ha1]

private theorem phaseARawRestricted_eq_of_quotient_eq (j : J) (u : I)
    {a b : quotientMk f s₀ x₀ γ ⁻¹'
      intersectionPieceAmbient f s₀ x₀ γ j}
    (h : (intersectionPieceAmbient f s₀ x₀ γ j).restrictPreimage
        (quotientMk f s₀ x₀ γ) a =
      (intersectionPieceAmbient f s₀ x₀ γ j).restrictPreimage
        (quotientMk f s₀ x₀ γ) b) :
    phaseARawRestricted f s₀ x₀ γ j (u, a) =
      phaseARawRestricted f s₀ x₀ γ j (u, b) := by
  apply Subtype.ext
  change phaseARaw f s₀ x₀ γ j (u, a.1) =
    phaseARaw f s₀ x₀ γ j (u, b.1)
  rw [← phaseARaw_normalForm f s₀ x₀ γ j u a.1 a.2,
    ← phaseARaw_normalForm f s₀ x₀ γ j u b.1 b.2]
  have hrel := Quotient.exact (congrArg Subtype.val h)
  change normalForm f s₀ x₀ γ a.1 = normalForm f s₀ x₀ γ b.1 at hrel
  rw [hrel]

private theorem phaseBRawRestricted_eq_of_quotient_eq (j : J) (u : I)
    {a b : quotientMk f s₀ x₀ γ ⁻¹'
      intersectionPieceAmbient f s₀ x₀ γ j}
    (h : (intersectionPieceAmbient f s₀ x₀ γ j).restrictPreimage
        (quotientMk f s₀ x₀ γ) a =
      (intersectionPieceAmbient f s₀ x₀ γ j).restrictPreimage
        (quotientMk f s₀ x₀ γ) b) :
    phaseBRawRestricted f s₀ x₀ γ j (u, a) =
      phaseBRawRestricted f s₀ x₀ γ j (u, b) := by
  apply Subtype.ext
  change phaseBRaw f s₀ x₀ γ j (u, a.1) =
    phaseBRaw f s₀ x₀ γ j (u, b.1)
  rw [← phaseBRaw_normalForm f s₀ x₀ γ j u a.1 a.2,
    ← phaseBRaw_normalForm f s₀ x₀ γ j u b.1 b.2]
  have hrel := Quotient.exact (congrArg Subtype.val h)
  change normalForm f s₀ x₀ γ a.1 = normalForm f s₀ x₀ γ b.1 at hrel
  rw [hrel]

private noncomputable def phaseAMap (j : J) :
    I × ↑(intersectionPieceAmbient f s₀ x₀ γ j) →
      ↑(intersectionPieceAmbient f s₀ x₀ γ j) := fun p ↦
  phaseARawRestricted f s₀ x₀ γ j
    (p.1, Function.surjInv
      (isQuotientMap_restrictPreimage_intersectionPieceAmbient
        f s₀ x₀ γ j).surjective p.2)

private theorem phaseAMap_quotientMap (j : J) (u : I)
    (z : quotientMk f s₀ x₀ γ ⁻¹'
      intersectionPieceAmbient f s₀ x₀ γ j) :
    phaseAMap f s₀ x₀ γ j
        (u, (intersectionPieceAmbient f s₀ x₀ γ j).restrictPreimage
          (quotientMk f s₀ x₀ γ) z) =
      phaseARawRestricted f s₀ x₀ γ j (u, z) :=
  phaseARawRestricted_eq_of_quotient_eq f s₀ x₀ γ j u
    (Function.surjInv_eq
      (isQuotientMap_restrictPreimage_intersectionPieceAmbient
        f s₀ x₀ γ j).surjective _)

private theorem continuous_phaseAMap (j : J) :
    Continuous (phaseAMap f s₀ x₀ γ j) := by
  apply (isQuotientMap_restrictPreimage_intersectionPieceAmbient
    f s₀ x₀ γ j).continuous_lift_prod_right
  apply (continuous_phaseARawRestricted f s₀ x₀ γ j).congr
  rintro ⟨u, z⟩
  exact (phaseAMap_quotientMap f s₀ x₀ γ j u z).symm

private noncomputable def phaseBMap (j : J) :
    I × ↑(intersectionPieceAmbient f s₀ x₀ γ j) →
      ↑(intersectionPieceAmbient f s₀ x₀ γ j) := fun p ↦
  phaseBRawRestricted f s₀ x₀ γ j
    (p.1, Function.surjInv
      (isQuotientMap_restrictPreimage_intersectionPieceAmbient
        f s₀ x₀ γ j).surjective p.2)

private theorem phaseBMap_quotientMap (j : J) (u : I)
    (z : quotientMk f s₀ x₀ γ ⁻¹'
      intersectionPieceAmbient f s₀ x₀ γ j) :
    phaseBMap f s₀ x₀ γ j
        (u, (intersectionPieceAmbient f s₀ x₀ γ j).restrictPreimage
          (quotientMk f s₀ x₀ γ) z) =
      phaseBRawRestricted f s₀ x₀ γ j (u, z) :=
  phaseBRawRestricted_eq_of_quotient_eq f s₀ x₀ γ j u
    (Function.surjInv_eq
      (isQuotientMap_restrictPreimage_intersectionPieceAmbient
        f s₀ x₀ γ j).surjective _)

private theorem continuous_phaseBMap (j : J) :
    Continuous (phaseBMap f s₀ x₀ γ j) := by
  apply (isQuotientMap_restrictPreimage_intersectionPieceAmbient
    f s₀ x₀ γ j).continuous_lift_prod_right
  apply (continuous_phaseBRawRestricted f s₀ x₀ γ j).congr
  rintro ⟨u, z⟩
  exact (phaseBMap_quotientMap f s₀ x₀ γ j u z).symm

private def pieceRetractionRaw (j : J) :
    Prequotient f → Hatcher.VanKampen.IndexedConeAttachment f
  | Sum.inl y => y
  | Sum.inr (Sum.inl t) =>
      IndexedConeAttachment.cylinder f j (s₀ j) (truncatedRadialHeight t)
  | Sum.inr (Sum.inr ⟨_, (_, t)⟩) =>
      IndexedConeAttachment.cylinder f j (s₀ j) (truncatedRadialHeight t)

private theorem continuous_pieceRetractionRaw (j : J) :
    Continuous (pieceRetractionRaw f s₀ j) := by
  rw [continuous_sum_dom]
  constructor
  · exact continuous_id
  · rw [continuous_sum_dom]
    constructor
    · exact (IndexedConeAttachment.continuous_cylinder f j).comp
        (continuous_const.prodMk truncatedRadialHeight.continuous)
    · rw [continuous_sigma_iff]
      intro k
      exact (IndexedConeAttachment.continuous_cylinder f j).comp
        (continuous_const.prodMk
          (truncatedRadialHeight.continuous.comp continuous_snd))

private theorem pieceRetractionRaw_mem (j : J)
    (z : quotientMk f s₀ x₀ γ ⁻¹'
      intersectionPieceAmbient f s₀ x₀ γ j) :
    pieceRetractionRaw f s₀ j z.1 ∈
      IndexedConeAttachment.interiorPiece f j := by
  rcases z with ⟨y | (t | ⟨k, a, t⟩), hmem⟩
  · exact (attachment_mem_intersectionPieceAmbient_iff
      f s₀ x₀ γ j y).mp hmem
  · have ht := (spine_mem_intersectionPieceAmbient_iff
      f s₀ x₀ γ j t).mp hmem
    exact (IndexedConeAttachment.cylinder_mem_interiorPiece_iff
      f j j (s₀ j) (truncatedRadialHeight t)).mpr
        ⟨rfl, truncatedRadialHeight_pos t,
          (truncatedRadialHeight_lt_one_iff' t).mpr ht⟩
  · have ht := (strip_mem_intersectionPieceAmbient_iff
      f s₀ x₀ γ j k a t).mp hmem |>.1
    exact (IndexedConeAttachment.cylinder_mem_interiorPiece_iff
      f j j (s₀ j) (truncatedRadialHeight t)).mpr
        ⟨rfl, truncatedRadialHeight_pos t,
          (truncatedRadialHeight_lt_one_iff' t).mpr ht⟩

private def pieceRetractionRawRestricted (j : J) :
    (quotientMk f s₀ x₀ γ ⁻¹'
      intersectionPieceAmbient f s₀ x₀ γ j) →
      ↑(IndexedConeAttachment.interiorPiece f j) :=
  fun z ↦ ⟨pieceRetractionRaw f s₀ j z.1,
    pieceRetractionRaw_mem f s₀ x₀ γ j z⟩

private theorem continuous_pieceRetractionRawRestricted (j : J) :
    Continuous (pieceRetractionRawRestricted f s₀ x₀ γ j) :=
  (continuous_pieceRetractionRaw f s₀ j).comp continuous_subtype_val |>.subtype_mk _

private theorem pieceRetractionRaw_normalForm (j : J) (z : Prequotient f)
    (hz : quotientMk f s₀ x₀ γ z ∈
      intersectionPieceAmbient f s₀ x₀ γ j) :
    pieceRetractionRaw f s₀ j (normalForm f s₀ x₀ γ z) =
      pieceRetractionRaw f s₀ j z := by
  rcases z with y | (t | ⟨k, a, t⟩)
  · rfl
  · have ht := (spine_mem_intersectionPieceAmbient_iff
      f s₀ x₀ γ j t).mp hz
    simp [normalForm, pieceRetractionRaw, ne_of_gt ht]
  · have hm := (strip_mem_intersectionPieceAmbient_iff
      f s₀ x₀ γ j k a t).mp hz
    have ht0 : t ≠ 0 := ne_of_gt hm.1
    by_cases ha0 : a = 0
    · subst a
      simp [normalForm, pieceRetractionRaw, ht0]
    · by_cases ha1 : a = 1
      · subst a
        have hkj : k = j := hm.2.resolve_right (lt_irrefl 1)
        subst k
        simp [normalForm, pieceRetractionRaw, ht0]
      · simp [normalForm, pieceRetractionRaw, ht0, ha0, ha1]

private theorem pieceRetractionRawRestricted_eq_of_quotient_eq (j : J)
    {a b : quotientMk f s₀ x₀ γ ⁻¹'
      intersectionPieceAmbient f s₀ x₀ γ j}
    (h : (intersectionPieceAmbient f s₀ x₀ γ j).restrictPreimage
        (quotientMk f s₀ x₀ γ) a =
      (intersectionPieceAmbient f s₀ x₀ γ j).restrictPreimage
        (quotientMk f s₀ x₀ γ) b) :
    pieceRetractionRawRestricted f s₀ x₀ γ j a =
      pieceRetractionRawRestricted f s₀ x₀ γ j b := by
  apply Subtype.ext
  change pieceRetractionRaw f s₀ j a.1 = pieceRetractionRaw f s₀ j b.1
  rw [← pieceRetractionRaw_normalForm f s₀ x₀ γ j a.1 a.2,
    ← pieceRetractionRaw_normalForm f s₀ x₀ γ j b.1 b.2]
  have hrel := Quotient.exact (congrArg Subtype.val h)
  change normalForm f s₀ x₀ γ a.1 = normalForm f s₀ x₀ γ b.1 at hrel
  rw [hrel]

private noncomputable def pieceRetraction (j : J) :
    C(↑(intersectionPieceAmbient f s₀ x₀ γ j),
      ↑(IndexedConeAttachment.interiorPiece f j)) where
  toFun z := pieceRetractionRawRestricted f s₀ x₀ γ j
    (Function.surjInv
      (isQuotientMap_restrictPreimage_intersectionPieceAmbient
        f s₀ x₀ γ j).surjective z)
  continuous_toFun := by
    apply (isQuotientMap_restrictPreimage_intersectionPieceAmbient
      f s₀ x₀ γ j).continuous_iff.mpr
    apply (continuous_pieceRetractionRawRestricted f s₀ x₀ γ j).congr
    intro z
    exact (pieceRetractionRawRestricted_eq_of_quotient_eq
      f s₀ x₀ γ j (Function.surjInv_eq
        (isQuotientMap_restrictPreimage_intersectionPieceAmbient
          f s₀ x₀ γ j).surjective _)).symm

private theorem pieceRetraction_quotientMap (j : J)
    (z : quotientMk f s₀ x₀ γ ⁻¹'
      intersectionPieceAmbient f s₀ x₀ γ j) :
    pieceRetraction f s₀ x₀ γ j
        ((intersectionPieceAmbient f s₀ x₀ γ j).restrictPreimage
          (quotientMk f s₀ x₀ γ) z) =
      pieceRetractionRawRestricted f s₀ x₀ γ j z :=
  pieceRetractionRawRestricted_eq_of_quotient_eq f s₀ x₀ γ j
    (Function.surjInv_eq
      (isQuotientMap_restrictPreimage_intersectionPieceAmbient
        f s₀ x₀ γ j).surjective _)

private def interiorPieceInclusion (j : J) :
    C(↑(IndexedConeAttachment.interiorPiece f j),
      ↑(intersectionPieceAmbient f s₀ x₀ γ j)) where
  toFun y := ⟨attachment f s₀ x₀ γ y.1,
    (attachment_mem_intersectionPieceAmbient_iff f s₀ x₀ γ j y.1).mpr y.2⟩
  continuous_toFun := (attachment f s₀ x₀ γ).continuous.comp
    continuous_subtype_val |>.subtype_mk _

private theorem pieceRetraction_comp_interiorPieceInclusion (j : J) :
    (pieceRetraction f s₀ x₀ γ j).comp
        (interiorPieceInclusion f s₀ x₀ γ j) =
      ContinuousMap.id ↑(IndexedConeAttachment.interiorPiece f j) := by
  ext y
  let z : quotientMk f s₀ x₀ γ ⁻¹'
      intersectionPieceAmbient f s₀ x₀ γ j :=
    ⟨Sum.inl y.1,
      (attachment_mem_intersectionPieceAmbient_iff
        f s₀ x₀ γ j y.1).mpr y.2⟩
  have hz :
      (intersectionPieceAmbient f s₀ x₀ γ j).restrictPreimage
          (quotientMk f s₀ x₀ γ) z =
        interiorPieceInclusion f s₀ x₀ γ j y := by
    apply Subtype.ext
    rfl
  change (pieceRetraction f s₀ x₀ γ j
      (interiorPieceInclusion f s₀ x₀ γ j y)).1 = y.1
  rw [← hz, pieceRetraction_quotientMap]
  rfl

private theorem phaseARaw_zero (j : J) (z : Prequotient f) :
    phaseARaw f s₀ x₀ γ j (0, z) = quotientMk f s₀ x₀ γ z := by
  rcases z with y | (t | ⟨k, a, t⟩)
  · rfl
  · rfl
  · by_cases hkj : k = j
    · subst k
      simp only [phaseARaw]
      rfl
    · simp only [phaseARaw, hkj, if_false, phaseAHorizontal,
        Set.Icc.convexComb_zero]
      rfl

private theorem phaseBRaw_zero_eq_phaseARaw_one (j : J) (z : Prequotient f) :
    phaseBRaw f s₀ x₀ γ j (0, z) =
      phaseARaw f s₀ x₀ γ j (1, z) := by
  rcases z with y | (t | ⟨k, a, t⟩)
  · rfl
  · simp [phaseARaw, phaseBRaw]
  · by_cases hkj : k = j
    · subst k
      simp [phaseARaw, phaseBRaw, phaseBHorizontal]
    · simp [phaseARaw, phaseBRaw, hkj, phaseAHorizontal]

private theorem phaseBRaw_one (j : J) (z : Prequotient f) :
    phaseBRaw f s₀ x₀ γ j (1, z) =
      attachment f s₀ x₀ γ (pieceRetractionRaw f s₀ j z) := by
  rcases z with y | (t | ⟨k, a, t⟩)
  · rfl
  · simp [phaseBRaw, pieceRetractionRaw]
  · by_cases hkj : k = j
    · subst k
      simp [phaseBRaw, phaseBHorizontal, pieceRetractionRaw]
    · simp [phaseBRaw, hkj, pieceRetractionRaw]

private theorem phaseAMap_zero (j : J)
    (z : ↑(intersectionPieceAmbient f s₀ x₀ γ j)) :
    phaseAMap f s₀ x₀ γ j (0, z) = z := by
  obtain ⟨raw, rfl⟩ :=
    (isQuotientMap_restrictPreimage_intersectionPieceAmbient
      f s₀ x₀ γ j).surjective z
  rw [phaseAMap_quotientMap]
  apply Subtype.ext
  exact phaseARaw_zero f s₀ x₀ γ j raw.1

private theorem phaseBMap_zero_eq_phaseAMap_one (j : J)
    (z : ↑(intersectionPieceAmbient f s₀ x₀ γ j)) :
    phaseBMap f s₀ x₀ γ j (0, z) =
      phaseAMap f s₀ x₀ γ j (1, z) := by
  obtain ⟨raw, rfl⟩ :=
    (isQuotientMap_restrictPreimage_intersectionPieceAmbient
      f s₀ x₀ γ j).surjective z
  rw [phaseAMap_quotientMap, phaseBMap_quotientMap]
  apply Subtype.ext
  exact phaseBRaw_zero_eq_phaseARaw_one f s₀ x₀ γ j raw.1

private theorem phaseBMap_one (j : J)
    (z : ↑(intersectionPieceAmbient f s₀ x₀ γ j)) :
    phaseBMap f s₀ x₀ γ j (1, z) =
      interiorPieceInclusion f s₀ x₀ γ j
        (pieceRetraction f s₀ x₀ γ j z) := by
  obtain ⟨raw, rfl⟩ :=
    (isQuotientMap_restrictPreimage_intersectionPieceAmbient
      f s₀ x₀ γ j).surjective z
  rw [phaseBMap_quotientMap, pieceRetraction_quotientMap]
  apply Subtype.ext
  exact phaseBRaw_one f s₀ x₀ γ j raw.1

private theorem phaseAMap_interiorPiece (j : J) (u : I)
    (y : ↑(IndexedConeAttachment.interiorPiece f j)) :
    phaseAMap f s₀ x₀ γ j
        (u, interiorPieceInclusion f s₀ x₀ γ j y) =
      interiorPieceInclusion f s₀ x₀ γ j y := by
  let raw : quotientMk f s₀ x₀ γ ⁻¹'
      intersectionPieceAmbient f s₀ x₀ γ j :=
    ⟨Sum.inl y.1,
      (attachment_mem_intersectionPieceAmbient_iff
        f s₀ x₀ γ j y.1).mpr y.2⟩
  have hraw :
      (intersectionPieceAmbient f s₀ x₀ γ j).restrictPreimage
          (quotientMk f s₀ x₀ γ) raw =
        interiorPieceInclusion f s₀ x₀ γ j y := by
    apply Subtype.ext
    rfl
  rw [← hraw, phaseAMap_quotientMap]
  rfl

private theorem phaseBMap_interiorPiece (j : J) (u : I)
    (y : ↑(IndexedConeAttachment.interiorPiece f j)) :
    phaseBMap f s₀ x₀ γ j
        (u, interiorPieceInclusion f s₀ x₀ γ j y) =
      interiorPieceInclusion f s₀ x₀ γ j y := by
  let raw : quotientMk f s₀ x₀ γ ⁻¹'
      intersectionPieceAmbient f s₀ x₀ γ j :=
    ⟨Sum.inl y.1,
      (attachment_mem_intersectionPieceAmbient_iff
        f s₀ x₀ γ j y.1).mpr y.2⟩
  have hraw :
      (intersectionPieceAmbient f s₀ x₀ γ j).restrictPreimage
          (quotientMk f s₀ x₀ γ) raw =
        interiorPieceInclusion f s₀ x₀ γ j y := by
    apply Subtype.ext
    rfl
  rw [← hraw, phaseBMap_quotientMap]
  rfl

private def phaseAEnd (j : J) :
    C(↑(intersectionPieceAmbient f s₀ x₀ γ j),
      ↑(intersectionPieceAmbient f s₀ x₀ γ j)) where
  toFun z := phaseAMap f s₀ x₀ γ j (1, z)
  continuous_toFun := (continuous_phaseAMap f s₀ x₀ γ j).comp
    (continuous_const.prodMk continuous_id)

private def phaseADeformation (j : J) :
    (ContinuousMap.id ↑(intersectionPieceAmbient f s₀ x₀ γ j)).HomotopyRel
      (phaseAEnd f s₀ x₀ γ j)
      (Set.range (interiorPieceInclusion f s₀ x₀ γ j)) where
  toFun := phaseAMap f s₀ x₀ γ j
  continuous_toFun := continuous_phaseAMap f s₀ x₀ γ j
  map_zero_left := phaseAMap_zero f s₀ x₀ γ j
  map_one_left _ := rfl
  prop' u z hz := by
    obtain ⟨y, rfl⟩ := hz
    exact phaseAMap_interiorPiece f s₀ x₀ γ j u y

private def phaseBDeformation (j : J) :
    (phaseAEnd f s₀ x₀ γ j).HomotopyRel
      ((interiorPieceInclusion f s₀ x₀ γ j).comp
        (pieceRetraction f s₀ x₀ γ j))
      (Set.range (interiorPieceInclusion f s₀ x₀ γ j)) where
  toFun := phaseBMap f s₀ x₀ γ j
  continuous_toFun := continuous_phaseBMap f s₀ x₀ γ j
  map_zero_left := phaseBMap_zero_eq_phaseAMap_one f s₀ x₀ γ j
  map_one_left := phaseBMap_one f s₀ x₀ γ j
  prop' u z hz := by
    obtain ⟨y, rfl⟩ := hz
    exact (phaseBMap_interiorPiece f s₀ x₀ γ j u y).trans
      (phaseAMap_interiorPiece f s₀ x₀ γ j 1 y).symm

private def ambientPieceDeformation (j : J) :
    (ContinuousMap.id ↑(intersectionPieceAmbient f s₀ x₀ γ j)).HomotopyRel
      ((interiorPieceInclusion f s₀ x₀ γ j).comp
        (pieceRetraction f s₀ x₀ γ j))
      (Set.range (interiorPieceInclusion f s₀ x₀ γ j)) :=
  (phaseADeformation f s₀ x₀ γ j).trans
    (phaseBDeformation f s₀ x₀ γ j)

private def ambientPieceHomotopyEquivInterior (j : J) :
    ↑(intersectionPieceAmbient f s₀ x₀ γ j) ≃ₕ
      ↑(IndexedConeAttachment.interiorPiece f j) where
  toFun := pieceRetraction f s₀ x₀ γ j
  invFun := interiorPieceInclusion f s₀ x₀ γ j
  left_inv := ⟨(ambientPieceDeformation f s₀ x₀ γ j).toHomotopy.symm⟩
  right_inv := by
    rw [pieceRetraction_comp_interiorPieceInclusion]

private def radialMidpoint : I := ⟨(1 : ℝ) / 2, by norm_num⟩

private theorem radialMidpoint_pos : 0 < radialMidpoint := by
  change (0 : ℝ) < 1 / 2
  norm_num

private theorem radialMidpoint_lt_one : radialMidpoint < 1 := by
  change (1 : ℝ) / 2 < 1
  norm_num

private def interiorRadialMidpoint : Set.Ioo (0 : I) 1 :=
  ⟨radialMidpoint, radialMidpoint_pos, radialMidpoint_lt_one⟩

private theorem convexComb_pos' {a b : I} (ha : 0 < a) (hb : 0 < b)
    (u : I) : 0 < Set.Icc.convexComb a b u := by
  rcases le_total a b with hab | hba
  · exact lt_of_lt_of_le ha (Set.Icc.le_convexComb hab u)
  · have h := Set.Icc.le_convexComb hba (unitInterval.symm u)
    rw [Set.Icc.convexComb_symm] at h
    exact lt_of_lt_of_le hb h

private theorem convexComb_lt_one' {a b : I} (ha : a < 1) (hb : b < 1)
    (u : I) : Set.Icc.convexComb a b u < 1 := by
  rcases le_total a b with hab | hba
  · exact lt_of_le_of_lt (Set.Icc.convexComb_le hab u) hb
  · have h := Set.Icc.convexComb_le hba (unitInterval.symm u)
    rw [Set.Icc.convexComb_symm] at h
    exact lt_of_le_of_lt h ha

private def contractInteriorInterval (u : I) (t : Set.Ioo (0 : I) 1) :
    Set.Ioo (0 : I) 1 :=
  ⟨Set.Icc.convexComb radialMidpoint t.1 u,
    convexComb_pos' radialMidpoint_pos t.2.1 u,
    convexComb_lt_one' radialMidpoint_lt_one t.2.2 u⟩

private theorem continuous_contractInteriorInterval :
    Continuous fun p : I × Set.Ioo (0 : I) 1 ↦
      contractInteriorInterval p.1 p.2 := by
  apply Continuous.subtype_mk
  exact Set.Icc.continuous_convexComb_prod.comp
    (continuous_const.prodMk
      ((continuous_subtype_val.comp continuous_snd).prodMk continuous_fst))

private def interiorCylinderProjection (T : Type*) [TopologicalSpace T] :
    C(T × Set.Ioo (0 : I) 1, T) :=
  ⟨Prod.fst, continuous_fst⟩

private def interiorCylinderMidpointInclusion (T : Type*) [TopologicalSpace T] :
    C(T, T × Set.Ioo (0 : I) 1) :=
  ⟨fun x ↦ (x, interiorRadialMidpoint), continuous_id.prodMk continuous_const⟩

private def interiorCylinderContraction (T : Type*) [TopologicalSpace T] :
    ((interiorCylinderMidpointInclusion T).comp
        (interiorCylinderProjection T)).Homotopy
      (ContinuousMap.id (T × Set.Ioo (0 : I) 1)) where
  toFun p := (p.2.1, contractInteriorInterval p.1 p.2.2)
  continuous_toFun :=
    (continuous_fst.comp continuous_snd).prodMk
      (continuous_contractInteriorInterval.comp
        (continuous_fst.prodMk (continuous_snd.comp continuous_snd)))
  map_zero_left p := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      simp [contractInteriorInterval, interiorCylinderMidpointInclusion,
        interiorCylinderProjection, interiorRadialMidpoint]
  map_one_left p := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      simp [contractInteriorInterval]

private def interiorCylinderHomotopyEquivBase
    (T : Type*) [TopologicalSpace T] :
    T × Set.Ioo (0 : I) 1 ≃ₕ T where
  toFun := interiorCylinderProjection T
  invFun := interiorCylinderMidpointInclusion T
  left_inv := ⟨interiorCylinderContraction T⟩
  right_inv := by
    have h : (interiorCylinderProjection T).comp
        (interiorCylinderMidpointInclusion T) = ContinuousMap.id T := by
      ext x
      rfl
    rw [h]

private noncomputable def interiorPieceHomotopyEquivBase (j : J) :
    ↑(IndexedConeAttachment.interiorPiece f j) ≃ₕ S j :=
  (IndexedConeAttachment.interiorCylinderHomeomorphInteriorPiece f j).symm.toHomotopyEquiv.trans
    (interiorCylinderHomotopyEquivBase (S j))

/-- The `j`-th overlap piece has the homotopy type of its attaching space.
For cell attachments this attaching space is the relevant disk boundary. -/
noncomputable def intersectionPieceHomotopyEquivBoundary (j : J) :
    ↑(intersectionPiece f s₀ x₀ γ j) ≃ₕ S j :=
  (intersectionPieceAmbientHomeomorphIntersectionPiece f s₀ x₀ γ j).symm.toHomotopyEquiv.trans
    ((ambientPieceHomotopyEquivInterior f s₀ x₀ γ j).trans
      (interiorPieceHomotopyEquivBase f j))

/-- The common overlap basepoint, regarded as a point of the `j`-th overlap
piece. -/
def intersectionPieceBasepoint (j : J) :
    ↑(intersectionPiece f s₀ x₀ γ j) :=
  ⟨coverIntersectionBasepoint f s₀ x₀ γ,
    coverIntersectionBasepoint_mem_intersectionPiece f s₀ x₀ γ j⟩

private def ambientIntersectionPieceBasepoint (j : J) :
    ↑(intersectionPieceAmbient f s₀ x₀ γ j) :=
  ⟨overlapBasepoint f s₀ x₀ γ, by simp [overlapBasepoint]⟩

private def selectedInteriorMidpoint (j : J) :
    ↑(IndexedConeAttachment.interiorPiece f j) :=
  ⟨IndexedConeAttachment.cylinder f j (s₀ j) radialMidpoint,
    (IndexedConeAttachment.cylinder_mem_interiorPiece_iff
      f j j (s₀ j) radialMidpoint).mpr
        ⟨rfl, radialMidpoint_pos, radialMidpoint_lt_one⟩⟩

private theorem pieceRetraction_ambientIntersectionPieceBasepoint (j : J) :
    pieceRetraction f s₀ x₀ γ j
        (ambientIntersectionPieceBasepoint f s₀ x₀ γ j) =
      selectedInteriorMidpoint f s₀ j := by
  let raw : quotientMk f s₀ x₀ γ ⁻¹'
      intersectionPieceAmbient f s₀ x₀ γ j :=
    ⟨Sum.inr (Sum.inl (1 : I)),
      (spine_mem_intersectionPieceAmbient_iff f s₀ x₀ γ j 1).mpr
        zero_lt_one⟩
  have hraw :
      (intersectionPieceAmbient f s₀ x₀ γ j).restrictPreimage
          (quotientMk f s₀ x₀ γ) raw =
        ambientIntersectionPieceBasepoint f s₀ x₀ γ j := by
    apply Subtype.ext
    rfl
  rw [← hraw, pieceRetraction_quotientMap]
  apply Subtype.ext
  change IndexedConeAttachment.cylinder f j (s₀ j)
      (truncatedRadialHeight 1) =
    IndexedConeAttachment.cylinder f j (s₀ j) radialMidpoint
  rw [truncatedRadialHeight_one]
  rfl

private theorem interiorPieceHomotopyEquivBase_selectedInteriorMidpoint (j : J) :
    interiorPieceHomotopyEquivBase f j (selectedInteriorMidpoint f s₀ j) =
      s₀ j := by
  change (interiorCylinderProjection (S j))
      ((IndexedConeAttachment.interiorCylinderHomeomorphInteriorPiece f j).symm
        (selectedInteriorMidpoint f s₀ j)) = s₀ j
  rw [show selectedInteriorMidpoint f s₀ j =
      ⟨IndexedConeAttachment.cylinder f j (s₀ j) radialMidpoint,
        (IndexedConeAttachment.cylinder_mem_interiorPiece_iff
          f j j (s₀ j) radialMidpoint).mpr
            ⟨rfl, radialMidpoint_pos, radialMidpoint_lt_one⟩⟩ by rfl]
  rw [IndexedConeAttachment.interiorCylinderHomeomorphInteriorPiece_symm_apply_cylinder
    f j (s₀ j) radialMidpoint radialMidpoint_pos radialMidpoint_lt_one]
  rfl

/-- The overlap-piece equivalence sends the common cover basepoint to the
chosen point of the selected attaching space. -/
@[simp] theorem intersectionPieceHomotopyEquivBoundary_basepoint (j : J) :
    intersectionPieceHomotopyEquivBoundary f s₀ x₀ γ j
        (intersectionPieceBasepoint f s₀ x₀ γ j) =
      s₀ j := by
  change interiorPieceHomotopyEquivBase f j
      (pieceRetraction f s₀ x₀ γ j
        ((intersectionPieceAmbientHomeomorphIntersectionPiece
          f s₀ x₀ γ j).symm
            (intersectionPieceBasepoint f s₀ x₀ γ j))) = s₀ j
  have hbase :
      (intersectionPieceAmbientHomeomorphIntersectionPiece
        f s₀ x₀ γ j).symm
          (intersectionPieceBasepoint f s₀ x₀ γ j) =
        ambientIntersectionPieceBasepoint f s₀ x₀ γ j := by
    apply Subtype.ext
    rfl
  rw [hbase, pieceRetraction_ambientIntersectionPieceBasepoint,
    interiorPieceHomotopyEquivBase_selectedInteriorMidpoint]

/-!
## Compatibility with the attaching map

The equivalence above is used with the inclusion of an overlap piece into the
base-side cover.  The following maps keep that inclusion and its retraction
canonical; in particular, downstream statements do not have to choose a
second model of the overlap piece.
-/

/-- Inclusion of one indexed overlap piece into the base-side cover. -/
def intersectionPieceToBaseCover (j : J) :
    C(↑(intersectionPiece f s₀ x₀ γ j), baseCover f s₀ x₀ γ) where
  toFun z := ⟨z.1.1, z.1.2.1⟩
  continuous_toFun :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

/-- The map from an overlap piece to the original base supplied by the
base-side deformation retraction. -/
def intersectionPieceToBase (hf : ∀ j, Continuous (f j)) (j : J) :
    C(↑(intersectionPiece f s₀ x₀ γ j), X) :=
  (baseCoverRetraction f s₀ x₀ γ hf).comp
    (intersectionPieceToBaseCover f s₀ x₀ γ j)

@[simp] theorem intersectionPieceToBaseCover_basepoint (j : J) :
    intersectionPieceToBaseCover f s₀ x₀ γ j
        (intersectionPieceBasepoint f s₀ x₀ γ j) =
      baseCoverBasepoint f s₀ x₀ γ := by
  apply Subtype.ext
  rfl

@[simp] theorem intersectionPieceToBase_basepoint
    (hf : ∀ j, Continuous (f j)) (j : J) :
    intersectionPieceToBase f s₀ x₀ γ hf j
        (intersectionPieceBasepoint f s₀ x₀ γ j) = x₀ := by
  exact baseCoverRetraction_overlapBasepoint f s₀ x₀ γ hf

private def ambientPieceToBaseCover (j : J) :
    C(↑(intersectionPieceAmbient f s₀ x₀ γ j),
      baseCover f s₀ x₀ γ) where
  toFun z :=
    ⟨z.1, (intersectionPieceAmbient_subset_coverIntersection
      f s₀ x₀ γ j z.2).1⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

private def intersectionPieceToAmbientPiece (j : J) :
    C(↑(intersectionPiece f s₀ x₀ γ j),
      ↑(intersectionPieceAmbient f s₀ x₀ γ j)) where
  toFun :=
    (intersectionPieceAmbientHomeomorphIntersectionPiece
      f s₀ x₀ γ j).symm
  continuous_toFun :=
    (intersectionPieceAmbientHomeomorphIntersectionPiece
      f s₀ x₀ γ j).symm.continuous

private def ambientPieceToBase (hf : ∀ j, Continuous (f j)) (j : J) :
    C(↑(intersectionPieceAmbient f s₀ x₀ γ j), X) :=
  (baseCoverRetraction f s₀ x₀ γ hf).comp
    (ambientPieceToBaseCover f s₀ x₀ γ j)

private theorem phaseAMap_ambientIntersectionPieceBasepoint
    (j : J) (u : I) :
    phaseAMap f s₀ x₀ γ j
        (u, ambientIntersectionPieceBasepoint f s₀ x₀ γ j) =
      ambientIntersectionPieceBasepoint f s₀ x₀ γ j := by
  let raw : quotientMk f s₀ x₀ γ ⁻¹'
      intersectionPieceAmbient f s₀ x₀ γ j :=
    ⟨Sum.inr (Sum.inl (1 : I)),
      (spine_mem_intersectionPieceAmbient_iff
        f s₀ x₀ γ j 1).mpr zero_lt_one⟩
  have hraw :
      (intersectionPieceAmbient f s₀ x₀ γ j).restrictPreimage
          (quotientMk f s₀ x₀ γ) raw =
        ambientIntersectionPieceBasepoint f s₀ x₀ γ j := by
    apply Subtype.ext
    rfl
  rw [← hraw, phaseAMap_quotientMap]
  apply Subtype.ext
  rfl

private theorem phaseBMap_ambientIntersectionPieceBasepoint
    (j : J) (u : I) :
    phaseBMap f s₀ x₀ γ j
        (u, ambientIntersectionPieceBasepoint f s₀ x₀ γ j) =
      ⟨strip f s₀ x₀ γ j (u, 1),
        (strip_mem_intersectionPieceAmbient_iff
          f s₀ x₀ γ j j u 1).mpr
            ⟨zero_lt_one, Or.inl rfl⟩⟩ := by
  let raw : quotientMk f s₀ x₀ γ ⁻¹'
      intersectionPieceAmbient f s₀ x₀ γ j :=
    ⟨Sum.inr (Sum.inl (1 : I)),
      (spine_mem_intersectionPieceAmbient_iff
        f s₀ x₀ γ j 1).mpr zero_lt_one⟩
  have hraw :
      (intersectionPieceAmbient f s₀ x₀ γ j).restrictPreimage
          (quotientMk f s₀ x₀ γ) raw =
        ambientIntersectionPieceBasepoint f s₀ x₀ γ j := by
    apply Subtype.ext
    rfl
  rw [← hraw, phaseBMap_quotientMap]
  apply Subtype.ext
  rfl

private theorem ambientPieceToBase_interiorPiece
    (hf : ∀ j, Continuous (f j)) (j : J)
    (y : ↑(IndexedConeAttachment.interiorPiece f j)) :
    ambientPieceToBase f s₀ x₀ γ hf j
        (interiorPieceInclusion f s₀ x₀ γ j y) =
      f j (interiorPieceHomotopyEquivBase f j y) := by
  let e := IndexedConeAttachment.interiorCylinderHomeomorphInteriorPiece f j
  rcases hst : e.symm y with ⟨s, t⟩
  have hy : y = e (s, t) := by
    calc
      y = e (e.symm y) := (e.apply_symm_apply y).symm
      _ = e (s, t) := congrArg e hst
  rw [hy]
  change baseCoverRetraction f s₀ x₀ γ hf
      ⟨attachment f s₀ x₀ γ (e (s, t)).1, _⟩ =
    f j ((interiorCylinderProjection (S j)) (e.symm (e (s, t))))
  rw [e.symm_apply_apply]
  change baseCoverRetraction f s₀ x₀ γ hf
      ⟨attachment f s₀ x₀ γ
          (IndexedConeAttachment.cylinder f j s t.1), _⟩ = f j s
  exact baseCoverRetraction_attachment_cylinder
    f s₀ x₀ γ hf j s t.1 t.2.1

private noncomputable def intersectionPieceAttachingHomotopyRaw
    (hf : ∀ j, Continuous (f j)) (j : J) := by
  let toAmbient := intersectionPieceToAmbientPiece f s₀ x₀ γ j
  let toBase := ambientPieceToBase f s₀ x₀ γ hf j
  let D := (ambientPieceDeformation f s₀ x₀ γ j).compContinuousMap toBase
  exact D.toHomotopy.compContinuousMap toAmbient

private theorem intersectionPieceAttachingHomotopyRaw_zero
    (hf : ∀ j, Continuous (f j)) (j : J) :
    (ambientPieceToBase f s₀ x₀ γ hf j).comp
        (intersectionPieceToAmbientPiece f s₀ x₀ γ j) =
      intersectionPieceToBase f s₀ x₀ γ hf j := by
  ext z
  rfl

private theorem intersectionPieceAttachingHomotopyRaw_one
    (hf : ∀ j, Continuous (f j)) (j : J) :
    (ambientPieceToBase f s₀ x₀ γ hf j).comp
        ((interiorPieceInclusion f s₀ x₀ γ j).comp
          ((pieceRetraction f s₀ x₀ γ j).comp
            (intersectionPieceToAmbientPiece f s₀ x₀ γ j))) =
      (⟨f j, hf j⟩ : C(S j, X)).comp
        (intersectionPieceHomotopyEquivBoundary f s₀ x₀ γ j).toFun := by
  ext z
  change ambientPieceToBase f s₀ x₀ γ hf j
      (interiorPieceInclusion f s₀ x₀ γ j
        (pieceRetraction f s₀ x₀ γ j
          ((intersectionPieceAmbientHomeomorphIntersectionPiece
            f s₀ x₀ γ j).symm z))) =
    f j (interiorPieceHomotopyEquivBase f j
      (pieceRetraction f s₀ x₀ γ j
        ((intersectionPieceAmbientHomeomorphIntersectionPiece
          f s₀ x₀ γ j).symm z)))
  exact ambientPieceToBase_interiorPiece f s₀ x₀ γ hf j _

/-- The canonical homotopy comparing an overlap piece followed by the
base-side retraction with its attaching map. -/
noncomputable def intersectionPieceAttachingHomotopy
    (hf : ∀ j, Continuous (f j)) (j : J) :
    (intersectionPieceToBase f s₀ x₀ γ hf j).Homotopy
      ((⟨f j, hf j⟩ : C(S j, X)).comp
        (intersectionPieceHomotopyEquivBoundary f s₀ x₀ γ j).toFun) := by
  apply (intersectionPieceAttachingHomotopyRaw f s₀ x₀ γ hf j).cast
  · ext z
    exact DFunLike.congr_fun
      (intersectionPieceAttachingHomotopyRaw_zero f s₀ x₀ γ hf j) z
  · ext z
    exact DFunLike.congr_fun
      (intersectionPieceAttachingHomotopyRaw_one f s₀ x₀ γ hf j) z

@[simp] private theorem intersectionPieceAttachingHomotopy_apply
    (hf : ∀ j, Continuous (f j)) (j : J) (u : I)
    (z : ↑(intersectionPiece f s₀ x₀ γ j)) :
    intersectionPieceAttachingHomotopy f s₀ x₀ γ hf j (u, z) =
      ambientPieceToBase f s₀ x₀ γ hf j
        (ambientPieceDeformation f s₀ x₀ γ j
          (u, intersectionPieceToAmbientPiece f s₀ x₀ γ j z)) := by
  rfl

private def secondPhaseParameter (u : I) : I :=
  ⟨max 0 (2 * (u : ℝ) - 1), by
    constructor
    · exact le_max_left _ _
    · exact max_le zero_le_one (by nlinarith [u.property.2])⟩

private theorem continuous_secondPhaseParameter :
    Continuous secondPhaseParameter := by
  apply Continuous.subtype_mk
  fun_prop

private theorem secondPhaseParameter_eq_zero {u : I}
    (hu : (u : ℝ) ≤ 1 / 2) : secondPhaseParameter u = 0 := by
  apply Subtype.ext
  change max 0 (2 * (u : ℝ) - 1) = 0
  rw [max_eq_left]
  linarith

private theorem secondPhaseParameter_eq_of_not_le {u : I}
    (hu : ¬(u : ℝ) ≤ 1 / 2) :
    secondPhaseParameter u =
      ⟨2 * (u : ℝ) - 1,
        unitInterval.two_mul_sub_one_mem_iff.mpr
          ⟨(not_le.mp hu).le, u.property.2⟩⟩ := by
  apply Subtype.ext
  change max 0 (2 * (u : ℝ) - 1) = 2 * (u : ℝ) - 1
  rw [max_eq_right]
  linarith [not_le.mp hu]

/-- Reparameterization of `γ j` traced by the basepoint during the canonical
overlap-piece deformation. -/
def intersectionPieceAttachingTraceParameter (u : I) : I :=
  topStripRetractionParameter (secondPhaseParameter u)

theorem continuous_intersectionPieceAttachingTraceParameter :
    Continuous intersectionPieceAttachingTraceParameter :=
  continuous_topStripRetractionParameter.comp
    continuous_secondPhaseParameter

@[simp] theorem intersectionPieceAttachingTraceParameter_zero :
    intersectionPieceAttachingTraceParameter 0 = 0 := by
  rw [intersectionPieceAttachingTraceParameter,
    secondPhaseParameter_eq_zero (by norm_num),
    topStripRetractionParameter_zero]

@[simp] theorem intersectionPieceAttachingTraceParameter_one :
    intersectionPieceAttachingTraceParameter 1 = 1 := by
  have hsecond : secondPhaseParameter (1 : I) = 1 := by
    apply Subtype.ext
    norm_num [secondPhaseParameter]
  rw [intersectionPieceAttachingTraceParameter, hsecond]
  rw [topStripRetractionParameter_one]

/-- The path traced by the common basepoint during
`intersectionPieceAttachingHomotopy`, with endpoints expressed in the
original base space. -/
noncomputable def intersectionPieceAttachingTrace
    (hf : ∀ j, Continuous (f j)) (j : J) :
    Path x₀ (f j (s₀ j)) :=
  ((intersectionPieceAttachingHomotopy f s₀ x₀ γ hf j).evalAt
      (intersectionPieceBasepoint f s₀ x₀ γ j)).cast
    (intersectionPieceToBase_basepoint f s₀ x₀ γ hf j).symm
    (congrArg (f j)
      (intersectionPieceHomotopyEquivBoundary_basepoint
        f s₀ x₀ γ j)).symm

@[simp] theorem intersectionPieceAttachingTrace_apply
    (hf : ∀ j, Continuous (f j)) (j : J) (u : I) :
    intersectionPieceAttachingTrace f s₀ x₀ γ hf j u =
      γ j (intersectionPieceAttachingTraceParameter u) := by
  have hambient :
      intersectionPieceToAmbientPiece f s₀ x₀ γ j
          (intersectionPieceBasepoint f s₀ x₀ γ j) =
        ambientIntersectionPieceBasepoint f s₀ x₀ γ j := by
    apply Subtype.ext
    rfl
  change ambientPieceToBase f s₀ x₀ γ hf j
      (ambientPieceDeformation f s₀ x₀ γ j
        (u, intersectionPieceToAmbientPiece f s₀ x₀ γ j
          (intersectionPieceBasepoint f s₀ x₀ γ j))) = _
  rw [hambient, ambientPieceDeformation,
    ContinuousMap.HomotopyRel.trans_apply]
  split_ifs with hu
  · let v : I :=
      ⟨2 * (u : ℝ),
        (unitInterval.mul_pos_mem_iff zero_lt_two).mpr
          ⟨u.property.1, hu⟩⟩
    change ambientPieceToBase f s₀ x₀ γ hf j
      (phaseAMap f s₀ x₀ γ j
        (v, ambientIntersectionPieceBasepoint f s₀ x₀ γ j)) = _
    rw [phaseAMap_ambientIntersectionPieceBasepoint]
    rw [intersectionPieceAttachingTraceParameter,
      secondPhaseParameter_eq_zero hu,
      topStripRetractionParameter_zero, (γ j).source]
    exact baseCoverRetraction_overlapBasepoint f s₀ x₀ γ hf
  · let v : I :=
      ⟨2 * (u : ℝ) - 1,
        unitInterval.two_mul_sub_one_mem_iff.mpr
          ⟨(not_le.mp hu).le, u.property.2⟩⟩
    change ambientPieceToBase f s₀ x₀ γ hf j
      (phaseBMap f s₀ x₀ γ j
        (v, ambientIntersectionPieceBasepoint f s₀ x₀ γ j)) = _
    rw [phaseBMap_ambientIntersectionPieceBasepoint]
    change baseCoverRetraction f s₀ x₀ γ hf
      ⟨strip f s₀ x₀ γ j (v, 1), _⟩ = _
    rw [baseCoverRetraction_strip_top]
    rw [intersectionPieceAttachingTraceParameter,
      secondPhaseParameter_eq_of_not_le hu]

/-- The basepoint track of the overlap-piece deformation is the prescribed
path `γ j`, up to its explicit endpoint-preserving reparameterization. -/
theorem intersectionPieceAttachingTrace_homotopic
    (hf : ∀ j, Continuous (f j)) (j : J) :
    Path.Homotopic (intersectionPieceAttachingTrace f s₀ x₀ γ hf j) (γ j) := by
  have hpath : intersectionPieceAttachingTrace f s₀ x₀ γ hf j =
      (γ j).reparam intersectionPieceAttachingTraceParameter
        continuous_intersectionPieceAttachingTraceParameter
        intersectionPieceAttachingTraceParameter_zero
        intersectionPieceAttachingTraceParameter_one := by
    ext u
    simp
  rw [hpath]
  exact ⟨(Path.Homotopy.reparam (γ j)
    intersectionPieceAttachingTraceParameter
    continuous_intersectionPieceAttachingTraceParameter
    intersectionPieceAttachingTraceParameter_zero
    intersectionPieceAttachingTraceParameter_one).symm⟩

end Hatcher.VanKampen.AuxiliaryCellAttachment
