import Hatcher.VanKampen.AuxiliaryCellAttachmentDeformation

noncomputable section

open Set Topology
open scoped unitInterval ContinuousMap

namespace Hatcher.VanKampen.AuxiliaryCellAttachment

universe u

variable {X J : Type u} {S : J → Type u}
variable [TopologicalSpace X] [∀ j, TopologicalSpace (S j)]
variable (f : ∀ j, S j → X) (s₀ : ∀ j, S j) (x₀ : X)
variable (γ : ∀ j, Path x₀ (f j (s₀ j)))

private def half : I := ⟨(1 : ℝ) / 2, by norm_num⟩

private def bridgeHorizontal (q : I) : I :=
  ⟨min 1 (2 * (q : ℝ)), by
    constructor
    · exact le_min zero_le_one (mul_nonneg (by norm_num) q.property.1)
    · exact min_le_left _ _⟩

private def bridgeRadialTime (q : I) : I :=
  ⟨max 0 (2 * (q : ℝ) - 1), by
    constructor
    · exact le_max_left _ _
    · apply max_le zero_le_one
      nlinarith [q.property.2]⟩

private theorem continuous_bridgeHorizontal : Continuous bridgeHorizontal := by
  apply Continuous.subtype_mk
  exact continuous_const.min
    (continuous_const.mul continuous_subtype_val)

private theorem continuous_bridgeRadialTime : Continuous bridgeRadialTime := by
  apply Continuous.subtype_mk
  exact continuous_const.max
    ((continuous_const.mul continuous_subtype_val).sub continuous_const)

private def halfParameter (a : I) : I :=
  ⟨(a : ℝ) / 2, by constructor <;> nlinarith [a.property.1, a.property.2]⟩

private def stretchParameter (u a : I) : I :=
  ⟨(a : ℝ) * (1 + (u : ℝ)) / 2, by
    constructor
    · exact div_nonneg (mul_nonneg a.property.1 (by nlinarith [u.property.1]))
        (by norm_num)
    · have hmul : 0 ≤ (1 - (a : ℝ)) * (u : ℝ) :=
        mul_nonneg (by linarith [a.property.2]) u.property.1
      nlinarith [a.property.2, u.property.1, u.property.2, hmul]⟩

private theorem continuous_stretchParameter :
    Continuous (fun p : I × I => stretchParameter p.1 p.2) := by
  apply Continuous.subtype_mk
  fun_prop

private def shrinkParameter (u a : I) : I :=
  Set.Icc.convexComb a 0 u

private def raisedVertical (u t : I) : I :=
  Set.Icc.convexComb t 1 u

private def phaseAParameter (u a : I) : ℝ :=
  (a : ℝ) * (1 + (u : ℝ))

private theorem phaseAParameter_nonneg (u a : I) :
    0 ≤ phaseAParameter u a := by
  exact mul_nonneg a.property.1 (by nlinarith [u.property.1])

private theorem phaseAParameter_le_two (u a : I) :
    phaseAParameter u a ≤ 2 := by
  have hmul : 0 ≤ (1 - (a : ℝ)) * (1 + (u : ℝ)) :=
    mul_nonneg (by linarith [a.property.2]) (by nlinarith [u.property.1])
  dsimp [phaseAParameter]
  nlinarith [u.property.2, hmul]

private def phaseAHorizontal (u a : I) : I :=
  ⟨min 1 (phaseAParameter u a), by
    constructor
    · exact le_min zero_le_one (phaseAParameter_nonneg u a)
    · exact min_le_left _ _⟩

private def phaseAOffset (u a : I) : I :=
  ⟨max 0 (phaseAParameter u a - 1), by
    constructor
    · exact le_max_left _ _
    · exact max_le zero_le_one (by linarith [phaseAParameter_le_two u a])⟩

private theorem phaseAOffset_le_time (u a : I) : phaseAOffset u a ≤ u := by
  change max 0 (phaseAParameter u a - 1) ≤ (u : ℝ)
  apply max_le u.property.1
  have hmul : 0 ≤ (1 - (a : ℝ)) * (1 + (u : ℝ)) :=
    mul_nonneg (by linarith [a.property.2]) (by nlinarith [u.property.1])
  dsimp [phaseAParameter]
  nlinarith

private def phaseAHeight (u a t : I) : I :=
  ⟨(truncatedRadialHeight (raisedVertical u t) : ℝ) -
      (phaseAOffset u a : ℝ) / 2, by
    have hTlo := (raisedVertical u t).property.1
    have hThi := (raisedVertical u t).property.2
    have hofflo := (phaseAOffset u a).property.1
    have hoffu := phaseAOffset_le_time u a
    change (phaseAOffset u a : ℝ) ≤ (u : ℝ) at hoffu
    have huhi := u.property.2
    change 0 ≤ 1 - (raisedVertical u t : ℝ) / 2 -
        (phaseAOffset u a : ℝ) / 2 ∧
      1 - (raisedVertical u t : ℝ) / 2 -
        (phaseAOffset u a : ℝ) / 2 ≤ 1
    constructor <;> nlinarith⟩

private theorem continuous_phaseAHorizontal :
    Continuous (fun p : I × I => phaseAHorizontal p.1 p.2) := by
  apply Continuous.subtype_mk
  exact continuous_const.min
    ((continuous_subtype_val.comp continuous_snd).mul
      (continuous_const.add (continuous_subtype_val.comp continuous_fst)))

private theorem continuous_phaseAOffset :
    Continuous (fun p : I × I => phaseAOffset p.1 p.2) := by
  apply Continuous.subtype_mk
  exact continuous_const.max
    (((continuous_subtype_val.comp continuous_snd).mul
      (continuous_const.add (continuous_subtype_val.comp continuous_fst))).sub
        continuous_const)

private theorem continuous_raisedVertical :
    Continuous (fun p : I × I => raisedVertical p.1 p.2) := by
  exact Set.Icc.continuous_convexComb_prod.comp
    (continuous_snd.prodMk (continuous_const.prodMk continuous_fst))

private theorem continuous_phaseAHeight :
    Continuous (fun p : I × I × I => phaseAHeight p.1 p.2.1 p.2.2) := by
  apply Continuous.subtype_mk
  exact ((continuous_subtype_val.comp
      (truncatedRadialHeight.continuous.comp
        (continuous_raisedVertical.comp
          (continuous_fst.prodMk (continuous_snd.comp continuous_snd))))).sub
    ((continuous_subtype_val.comp
      (continuous_phaseAOffset.comp
        (continuous_fst.prodMk (continuous_fst.comp continuous_snd)))).div_const 2))

private def bridgePoint (j : J) (t q : I) :
    Hatcher.VanKampen.AuxiliaryCellAttachment f s₀ x₀ γ :=
  if (q : ℝ) ≤ 1 / 2 then
    strip f s₀ x₀ γ j (bridgeHorizontal q, t)
  else
    attachment f s₀ x₀ γ
      (IndexedConeAttachment.cylinder f j (s₀ j)
        (Set.Icc.convexComb (truncatedRadialHeight t) 0
          (bridgeRadialTime q)))

private theorem continuous_bridgePoint (j : J) :
    Continuous (fun p : I × I => bridgePoint f s₀ x₀ γ j p.1 p.2) := by
  apply Continuous.if_le
  · exact (strip f s₀ x₀ γ j).continuous.comp
      ((continuous_bridgeHorizontal.comp continuous_snd).prodMk continuous_fst)
  · exact (attachment f s₀ x₀ γ).continuous.comp
      ((IndexedConeAttachment.continuous_cylinder f j).comp
        (continuous_const.prodMk
          (Set.Icc.continuous_convexComb_prod.comp
            ((truncatedRadialHeight.continuous.comp continuous_fst).prodMk
              (continuous_const.prodMk
                (continuous_bridgeRadialTime.comp continuous_snd))))))
  · exact continuous_subtype_val.comp continuous_snd
  · exact continuous_const
  · intro p hp
    have hh : bridgeHorizontal p.2 = 1 := by
      apply Subtype.ext
      change min 1 (2 * (p.2 : ℝ)) = 1
      rw [min_eq_left]
      linarith
    have hr : bridgeRadialTime p.2 = 0 := by
      apply Subtype.ext
      change max 0 (2 * (p.2 : ℝ) - 1) = 0
      rw [max_eq_left]; linarith
    simp [hh, hr]

omit [∀ j, TopologicalSpace (S j)] in
private theorem truncatedRadialHeight_lt_one_of_pos (t : I) (ht : 0 < t) :
    truncatedRadialHeight t < 1 := by
  change 0 < (t : ℝ) at ht
  change 1 - (t : ℝ) / 2 < 1
  linarith

private theorem bridgePoint_mem_upperCover (j : J) (t q : I) (ht : 0 < t) :
    bridgePoint f s₀ x₀ γ j t q ∈ upperCover f s₀ x₀ γ := by
  unfold bridgePoint
  split_ifs
  · rw [strip_mem_upperCover_iff]
    exact ht
  · rw [attachment_mem_upperCover_iff,
      IndexedConeAttachment.cylinder_mem_upperCover_iff]
    have hheight : truncatedRadialHeight t < 1 :=
      truncatedRadialHeight_lt_one_of_pos t ht
    change (Set.Icc.convexComb (truncatedRadialHeight t) 0
      (bridgeRadialTime q) : ℝ) < 1
    simp only [Set.Icc.coe_convexComb]
    norm_num
    have htrnonneg : 0 ≤ (truncatedRadialHeight t : ℝ) :=
      (truncatedRadialHeight t).property.1
    have hurange := (bridgeRadialTime q).property
    have hprod : 0 ≤ (bridgeRadialTime q : ℝ) *
        (truncatedRadialHeight t : ℝ) :=
      mul_nonneg hurange.1 htrnonneg
    exact lt_of_le_of_lt (by nlinarith) hheight

@[simp] private theorem bridgePoint_zero (j : J) (t : I) :
    bridgePoint f s₀ x₀ γ j t 0 = spine f s₀ x₀ γ t := by
  simp [bridgePoint, bridgeHorizontal]

@[simp] private theorem bridgePoint_one (j : J) (t : I) :
    bridgePoint f s₀ x₀ γ j t 1 = apex f s₀ x₀ γ j := by
  norm_num [bridgePoint, bridgeRadialTime, apex]

@[simp] private theorem bridgePoint_halfParameter (j : J) (a t : I) :
    bridgePoint f s₀ x₀ γ j t (halfParameter a) =
      strip f s₀ x₀ γ j (a, t) := by
  have hle : ((halfParameter a : I) : ℝ) ≤ 1 / 2 := by
    dsimp [halfParameter]
    linarith [a.property.2]
  rw [bridgePoint, if_pos hle]
  congr 2
  apply Subtype.ext
  change min 1 (2 * ((a : ℝ) / 2)) = a
  rw [min_eq_right] <;> nlinarith [a.property.2]

@[simp] private theorem stretchParameter_zero (a : I) :
    stretchParameter 0 a = halfParameter a := by
  apply Subtype.ext
  simp [stretchParameter, halfParameter]

@[simp] private theorem stretchParameter_one (a : I) :
    stretchParameter 1 a = a := by
  apply Subtype.ext
  change (a : ℝ) * (1 + 1) / 2 = a
  ring

@[simp] private theorem stretchParameter_left (u : I) :
    stretchParameter u 0 = 0 := by
  apply Subtype.ext
  simp [stretchParameter]

private theorem bridgePoint_stretch_right (j : J) (u t : I) :
    bridgePoint f s₀ x₀ γ j t (stretchParameter u 1) =
      attachment f s₀ x₀ γ
        (IndexedConeAttachment.cylinder f j (s₀ j)
          (Set.Icc.convexComb (truncatedRadialHeight t) 0 u)) := by
  by_cases hu : u = 0
  · subst u
    simp [bridgePoint_halfParameter]
  · have hupos : 0 < (u : ℝ) :=
      lt_of_le_of_ne u.property.1 (Ne.symm (Subtype.coe_ne_coe.mpr hu))
    have hnot : ¬ ((stretchParameter u 1 : I) : ℝ) ≤ 1 / 2 := by
      dsimp [stretchParameter]
      linarith
    rw [bridgePoint, if_neg hnot]
    congr 3
    apply Subtype.ext
    change max 0 (2 * (((1 : ℝ) * (1 + u)) / 2) - 1) = u
    rw [max_eq_right] <;> nlinarith

private def phaseAStrip (j : J) (u a t : I) :
    Hatcher.VanKampen.AuxiliaryCellAttachment f s₀ x₀ γ :=
  if phaseAParameter u a ≤ 1 then
    strip f s₀ x₀ γ j
      (phaseAHorizontal u a, raisedVertical u t)
  else
    attachment f s₀ x₀ γ
      (IndexedConeAttachment.cylinder f j (s₀ j) (phaseAHeight u a t))

private theorem continuous_phaseAStrip (j : J) :
    Continuous (fun p : I × I × I =>
      phaseAStrip f s₀ x₀ γ j p.1 p.2.1 p.2.2) := by
  apply Continuous.if_le
  · exact (strip f s₀ x₀ γ j).continuous.comp
      ((continuous_phaseAHorizontal.comp
          (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).prodMk
        (continuous_raisedVertical.comp
          (continuous_fst.prodMk (continuous_snd.comp continuous_snd))))
  · exact (attachment f s₀ x₀ γ).continuous.comp
      ((IndexedConeAttachment.continuous_cylinder f j).comp
        (continuous_const.prodMk continuous_phaseAHeight))
  · exact (continuous_subtype_val.comp (continuous_fst.comp continuous_snd)).mul
      (continuous_const.add (continuous_subtype_val.comp continuous_fst))
  · exact continuous_const
  · intro p hp
    have hh : phaseAHorizontal p.1 p.2.1 = 1 := by
      apply Subtype.ext
      change min 1 (phaseAParameter p.1 p.2.1) = 1
      rw [min_eq_left]
      exact le_of_eq hp.symm
    have ho : phaseAOffset p.1 p.2.1 = 0 := by
      apply Subtype.ext
      change max 0 (phaseAParameter p.1 p.2.1 - 1) = 0
      rw [max_eq_left]; linarith
    rw [hh, strip_right]
    congr 3
    apply Subtype.ext
    simp [phaseAHeight, ho]

omit [∀ j, TopologicalSpace (S j)] in
private theorem raisedVertical_pos (u t : I) (ht : 0 < t) :
    0 < raisedVertical u t := by
  exact ht.trans_le (Set.Icc.le_convexComb t.property.2 u)

private theorem phaseAStrip_mem_upperCover (j : J) (u a t : I)
    (ht : 0 < t) :
    phaseAStrip f s₀ x₀ γ j u a t ∈ upperCover f s₀ x₀ γ := by
  unfold phaseAStrip
  split_ifs with h
  · rw [strip_mem_upperCover_iff]
    exact raisedVertical_pos u t ht
  · rw [attachment_mem_upperCover_iff,
      IndexedConeAttachment.cylinder_mem_upperCover_iff]
    change (phaseAHeight u a t : ℝ) < 1
    have hTpos := raisedVertical_pos u t ht
    change 0 < (raisedVertical u t : ℝ) at hTpos
    have hoff := (phaseAOffset u a).property.1
    change 0 ≤ (phaseAOffset u a : ℝ) at hoff
    change 1 - (raisedVertical u t : ℝ) / 2 -
          (phaseAOffset u a : ℝ) / 2 < 1
    linarith

@[simp] private theorem phaseAStrip_zero (j : J) (a t : I) :
    phaseAStrip f s₀ x₀ γ j 0 a t = strip f s₀ x₀ γ j (a, t) := by
  have hp : phaseAParameter 0 a ≤ 1 := by
    simpa [phaseAParameter] using a.property.2
  rw [phaseAStrip, if_pos hp]
  congr 2
  · apply Subtype.ext
    change min 1 ((a : ℝ) * (1 + 0)) = a
    simpa using min_eq_right a.property.2
  · simp [raisedVertical]

@[simp] private theorem phaseAStrip_left (j : J) (u t : I) :
    phaseAStrip f s₀ x₀ γ j u 0 t =
      spine f s₀ x₀ γ (raisedVertical u t) := by
  have hp : phaseAParameter u 0 ≤ 1 := by simp [phaseAParameter]
  rw [phaseAStrip, if_pos hp]
  have hh : phaseAHorizontal u 0 = 0 := by
    apply Subtype.ext
    simp [phaseAHorizontal, phaseAParameter]
  rw [hh, strip_left]

private theorem phaseAHeight_right (u t : I) :
    phaseAHeight u 1 t =
      Set.Icc.convexComb (truncatedRadialHeight t) 0 u := by
  apply Subtype.ext
  simp only [phaseAHeight, Set.Icc.coe_convexComb]
  have ho : phaseAOffset u 1 = u := by
    apply Subtype.ext
    change max 0 ((1 : ℝ) * (1 + u) - 1) = u
    rw [max_eq_right] <;> nlinarith [u.property.1]
  rw [ho]
  change 1 - (Set.Icc.convexComb t 1 u : I) / 2 - (u : ℝ) / 2 =
    (1 - (u : ℝ)) * (1 - (t : ℝ) / 2) + (u : ℝ) * 0
  simp only [Set.Icc.coe_convexComb]
  norm_num
  ring

private theorem phaseAStrip_right (j : J) (u t : I) :
    phaseAStrip f s₀ x₀ γ j u 1 t =
      attachment f s₀ x₀ γ
        (IndexedConeAttachment.cylinder f j (s₀ j)
          (Set.Icc.convexComb (truncatedRadialHeight t) 0 u)) := by
  by_cases hu : u = 0
  · subst u
    simp [phaseAStrip_zero]
  · have hupos : 0 < (u : ℝ) :=
      lt_of_le_of_ne u.property.1 (Ne.symm (Subtype.coe_ne_coe.mpr hu))
    have hp : ¬ phaseAParameter u 1 ≤ 1 := by
      dsimp [phaseAParameter]
      linarith
    rw [phaseAStrip, if_neg hp, phaseAHeight_right]

private theorem phaseAStrip_one (j : J) (a t : I) :
    phaseAStrip f s₀ x₀ γ j 1 a t = bridgePoint f s₀ x₀ γ j 1 a := by
  by_cases ha : (a : ℝ) ≤ 1 / 2
  · have hp : phaseAParameter 1 a ≤ 1 := by
      dsimp [phaseAParameter]
      nlinarith
    rw [phaseAStrip, if_pos hp, bridgePoint, if_pos ha]
    congr 2
    · apply Subtype.ext
      simp only [phaseAHorizontal, phaseAParameter, bridgeHorizontal]
      congr 1
      norm_num
      ring
    · simp [raisedVertical]
  · have hp : ¬ phaseAParameter 1 a ≤ 1 := by
      dsimp [phaseAParameter]
      nlinarith
    rw [phaseAStrip, if_neg hp, bridgePoint, if_neg ha]
    congr 3
    apply Subtype.ext
    simp only [phaseAHeight, raisedVertical, Set.Icc.coe_convexComb,
      truncatedRadialHeight]
    have ho : phaseAOffset 1 a = bridgeRadialTime a := by
      apply Subtype.ext
      simp only [phaseAOffset, phaseAParameter, bridgeRadialTime]
      congr 1
      norm_num
      ring
    rw [ho]
    simp only [bridgeRadialTime]
    norm_num
    ring

def upperOverlapBasepoint : upperCover f s₀ x₀ γ :=
  ⟨overlapBasepoint f s₀ x₀ γ,
    overlapBasepoint_mem_upperCover f s₀ x₀ γ⟩

/-! A flattened quotient chart, replacing the nested indexed attachment quotient
by its own prequotient.  This makes continuity on the upper member branchwise. -/

private abbrev FlatPrequotient :=
  IndexedConeAttachment.Prequotient X S ⊕
    (I ⊕ Sigma (fun _j : J => I × I))

private theorem isQuotientMap_sumMap
    {A B C D : Type*} [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalSpace C] [TopologicalSpace D]
    {g : A → B} {h : C → D} (hg : IsQuotientMap g) (hh : IsQuotientMap h) :
    IsQuotientMap (Sum.map g h) := by
  refine ⟨?_, hg.surjective.sumMap hh.surjective⟩
  rw [isCoinducing_iff]
  intro s
  rw [isOpen_sum_iff, isOpen_sum_iff]
  change (IsOpen (g ⁻¹' (Sum.inl ⁻¹' s)) ∧
      IsOpen (h ⁻¹' (Sum.inr ⁻¹' s))) ↔ _
  rw [hg.isCoinducing.isOpen_preimage, hh.isCoinducing.isOpen_preimage]

private def flatToPrequotient : FlatPrequotient (X := X) (S := S) →
    Prequotient f :=
  Sum.map (IndexedConeAttachment.quotientMk f) id

private def flatMk : FlatPrequotient (X := X) (S := S) →
    Hatcher.VanKampen.AuxiliaryCellAttachment f s₀ x₀ γ :=
  quotientMk f s₀ x₀ γ ∘ flatToPrequotient f

private theorem isQuotientMap_flatToPrequotient :
    IsQuotientMap (flatToPrequotient f) :=
  isQuotientMap_sumMap
    isQuotientMap_quot_mk
    IsQuotientMap.id

private theorem isQuotientMap_flatMk :
    IsQuotientMap (flatMk f s₀ x₀ γ) := by
  exact (isQuotientMap_quotientMk f s₀ x₀ γ).comp
    (isQuotientMap_flatToPrequotient f)

private theorem isQuotientMap_flatMk_restrictUpper :
    IsQuotientMap ((upperCover f s₀ x₀ γ).restrictPreimage
      (flatMk f s₀ x₀ γ)) :=
  (isQuotientMap_flatMk f s₀ x₀ γ).restrictPreimage_isOpen
    (isOpen_upperCover f s₀ x₀ γ)

private def indexedRadialRaw :
    I × IndexedConeAttachment.Prequotient X S →
      Hatcher.VanKampen.IndexedConeAttachment f
  | (_, Sum.inl x) => IndexedConeAttachment.base f x
  | (_, Sum.inr ⟨j, Sum.inl _⟩) => IndexedConeAttachment.apex f j
  | (u, Sum.inr ⟨j, Sum.inr (s, t)⟩) =>
      IndexedConeAttachment.cylinder f j s (Set.Icc.convexComb t 0 u)

private theorem continuous_indexedRadialRaw :
    Continuous (indexedRadialRaw f) := by
  let gsigma : (Σ j : J, (Unit ⊕ (S j × I)) × I) →
      Hatcher.VanKampen.IndexedConeAttachment f
    | ⟨j, Sum.inl _, _⟩ => IndexedConeAttachment.apex f j
    | ⟨j, Sum.inr (s, t), u⟩ =>
        IndexedConeAttachment.cylinder f j s (Set.Icc.convexComb t 0 u)
  have hgsigma : Continuous gsigma := by
    rw [continuous_sigma_iff]
    intro j
    let gj : (Unit × I) ⊕ ((S j × I) × I) →
        Hatcher.VanKampen.IndexedConeAttachment f
      | Sum.inl _ => IndexedConeAttachment.apex f j
      | Sum.inr ((s, t), u) =>
          IndexedConeAttachment.cylinder f j s (Set.Icc.convexComb t 0 u)
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
            Σ j : J, (Unit ⊕ (S j × I)) × I) (Prod.swap p))
  have hg : Continuous g := by
    rw [continuous_sum_dom]
    constructor
    · exact (IndexedConeAttachment.continuous_base f).comp continuous_snd
    · exact hgsigma.comp
        ((Homeomorph.sigmaProdDistrib :
          (Σ j : J, Unit ⊕ (S j × I)) × I ≃ₜ
            Σ j : J, (Unit ⊕ (S j × I)) × I).continuous.comp continuous_swap)
  apply (hg.comp
    (Homeomorph.prodSumDistrib :
      I × IndexedConeAttachment.Prequotient X S ≃ₜ
        (I × X) ⊕ (I × (Σ j : J, Unit ⊕ (S j × I)))).continuous).congr
  rintro ⟨u, x | ⟨j, (_ | ⟨s, t⟩)⟩⟩ <;> rfl

private def phaseAFlatRaw :
    I × FlatPrequotient (X := X) (S := S) →
      Hatcher.VanKampen.AuxiliaryCellAttachment f s₀ x₀ γ
  | (u, Sum.inl y) => attachment f s₀ x₀ γ (indexedRadialRaw f (u, y))
  | (u, Sum.inr (Sum.inl t)) => spine f s₀ x₀ γ (raisedVertical u t)
  | (u, Sum.inr (Sum.inr ⟨j, (a, t)⟩)) =>
      phaseAStrip f s₀ x₀ γ j u a t

private theorem continuous_phaseAFlatRaw :
    Continuous (phaseAFlatRaw f s₀ x₀ γ) := by
  let gstrip : (Σ j : J, (I × I) × I) →
      Hatcher.VanKampen.AuxiliaryCellAttachment f s₀ x₀ γ
    | ⟨j, (a, t), u⟩ => phaseAStrip f s₀ x₀ γ j u a t
  have hgstrip : Continuous gstrip := by
    rw [continuous_sigma_iff]
    intro j
    exact (continuous_phaseAStrip f s₀ x₀ γ j).comp
      (continuous_snd.prodMk
        ((continuous_fst.comp continuous_fst).prodMk
          (continuous_snd.comp continuous_fst)))
  let gright : (I × I) ⊕ (I × (Σ _j : J, I × I)) →
      Hatcher.VanKampen.AuxiliaryCellAttachment f s₀ x₀ γ
    | Sum.inl (u, t) => spine f s₀ x₀ γ (raisedVertical u t)
    | Sum.inr p => gstrip
        ((Homeomorph.sigmaProdDistrib :
          (Σ _j : J, I × I) × I ≃ₜ Σ _j : J, (I × I) × I)
          (Prod.swap p))
  have hgright : Continuous gright := by
    rw [continuous_sum_dom]
    constructor
    · exact (spine f s₀ x₀ γ).continuous.comp continuous_raisedVertical
    · exact hgstrip.comp
        ((Homeomorph.sigmaProdDistrib :
          (Σ _j : J, I × I) × I ≃ₜ Σ _j : J, (I × I) × I).continuous.comp
            continuous_swap)
  let g : (I × IndexedConeAttachment.Prequotient X S) ⊕
      (I × (I ⊕ (Σ _j : J, I × I))) →
      Hatcher.VanKampen.AuxiliaryCellAttachment f s₀ x₀ γ
    | Sum.inl p => attachment f s₀ x₀ γ (indexedRadialRaw f p)
    | Sum.inr p => gright
        ((Homeomorph.prodSumDistrib :
          I × (I ⊕ (Σ _j : J, I × I)) ≃ₜ
            (I × I) ⊕ (I × (Σ _j : J, I × I))) p)
  have hg : Continuous g := by
    rw [continuous_sum_dom]
    constructor
    · exact (attachment f s₀ x₀ γ).continuous.comp
        (continuous_indexedRadialRaw f)
    · exact hgright.comp
        (Homeomorph.prodSumDistrib :
          I × (I ⊕ (Σ _j : J, I × I)) ≃ₜ
            (I × I) ⊕ (I × (Σ _j : J, I × I))).continuous
  apply (hg.comp
    (Homeomorph.prodSumDistrib :
      I × FlatPrequotient (X := X) (S := S) ≃ₜ
        (I × IndexedConeAttachment.Prequotient X S) ⊕
          (I × (I ⊕ (Σ _j : J, I × I)))).continuous).congr
  rintro ⟨u, y | (t | ⟨j, p⟩)⟩ <;> rfl

private theorem phaseAFlatRaw_mem (u : I)
    (z : flatMk f s₀ x₀ γ ⁻¹' upperCover f s₀ x₀ γ) :
    phaseAFlatRaw f s₀ x₀ γ (u, z.1) ∈ upperCover f s₀ x₀ γ := by
  rcases z with ⟨y | (t | ⟨j, a, t⟩), hmem⟩
  · rcases y with x | ⟨j, (_ | ⟨s, h⟩)⟩
    · change attachment f s₀ x₀ γ
          (IndexedConeAttachment.base f x) ∈ upperCover f s₀ x₀ γ at hmem
      rw [attachment_mem_upperCover_iff] at hmem
      exact False.elim (IndexedConeAttachment.base_not_mem_upperCover f x hmem)
    · exact apex_mem_upperCover f s₀ x₀ γ j
    · change attachment f s₀ x₀ γ
          (IndexedConeAttachment.cylinder f j s h) ∈ upperCover f s₀ x₀ γ at hmem
      have hh : h < 1 := by
        rw [attachment_mem_upperCover_iff,
          IndexedConeAttachment.cylinder_mem_upperCover_iff] at hmem
        exact hmem
      change attachment f s₀ x₀ γ
        (IndexedConeAttachment.cylinder f j s
          (Set.Icc.convexComb h 0 u)) ∈ upperCover f s₀ x₀ γ
      rw [attachment_mem_upperCover_iff,
        IndexedConeAttachment.cylinder_mem_upperCover_iff]
      change (Set.Icc.convexComb h 0 u : I) < 1
      rw [← Subtype.coe_lt_coe]
      simp only [Set.Icc.coe_convexComb]
      norm_num
      have hprod : 0 ≤ (u : ℝ) * (h : ℝ) :=
        mul_nonneg u.property.1 h.property.1
      change (h : ℝ) < 1 at hh
      nlinarith
  · change spine f s₀ x₀ γ t ∈ upperCover f s₀ x₀ γ at hmem
    rw [spine_mem_upperCover_iff] at hmem
    exact (spine_mem_upperCover_iff f s₀ x₀ γ _).2
      (raisedVertical_pos u t hmem)
  · change strip f s₀ x₀ γ j (a, t) ∈ upperCover f s₀ x₀ γ at hmem
    rw [strip_mem_upperCover_iff] at hmem
    exact phaseAStrip_mem_upperCover f s₀ x₀ γ j u a t hmem

private def phaseAFlatRawRestricted :
    I × (flatMk f s₀ x₀ γ ⁻¹' upperCover f s₀ x₀ γ) →
      upperCover f s₀ x₀ γ :=
  fun p => ⟨phaseAFlatRaw f s₀ x₀ γ (p.1, p.2.1),
    phaseAFlatRaw_mem f s₀ x₀ γ p.1 p.2⟩

private theorem continuous_phaseAFlatRawRestricted :
    Continuous (phaseAFlatRawRestricted f s₀ x₀ γ) := by
  apply Continuous.subtype_mk
  exact (continuous_phaseAFlatRaw f s₀ x₀ γ).comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))

private def indexedUpperQuotientMap :
    (IndexedConeAttachment.quotientMk f ⁻¹'
      IndexedConeAttachment.upperCover f) →
      IndexedConeAttachment.upperCover f :=
  (IndexedConeAttachment.upperCover f).restrictPreimage
    (IndexedConeAttachment.quotientMk f)

private theorem isQuotientMap_indexedUpperQuotientMap :
    IsQuotientMap (indexedUpperQuotientMap f) := by
  have hq : IsQuotientMap (IndexedConeAttachment.quotientMk f) :=
    isQuotientMap_quot_mk
  exact hq.restrictPreimage_isOpen
    ((IndexedConeAttachment.isOpenCover_lower_upper f).2.1)

private theorem indexedRadialRaw_mem (u : I)
    (z : IndexedConeAttachment.quotientMk f ⁻¹'
      IndexedConeAttachment.upperCover f) :
    attachment f s₀ x₀ γ (indexedRadialRaw f (u, z.1)) ∈
      upperCover f s₀ x₀ γ := by
  rcases z with ⟨x | ⟨j, (_ | ⟨s, t⟩)⟩, hmem⟩
  · exact False.elim (IndexedConeAttachment.base_not_mem_upperCover f x hmem)
  · exact apex_mem_upperCover f s₀ x₀ γ j
  · have ht : t < 1 :=
      (IndexedConeAttachment.cylinder_mem_upperCover_iff f j s t).1 hmem
    change attachment f s₀ x₀ γ
      (IndexedConeAttachment.cylinder f j s
        (Set.Icc.convexComb t 0 u)) ∈ upperCover f s₀ x₀ γ
    rw [attachment_mem_upperCover_iff,
      IndexedConeAttachment.cylinder_mem_upperCover_iff]
    rw [← Subtype.coe_lt_coe]
    simp only [Set.Icc.coe_convexComb]
    norm_num
    have hprod : 0 ≤ (u : ℝ) * (t : ℝ) :=
      mul_nonneg u.property.1 t.property.1
    change (t : ℝ) < 1 at ht
    nlinarith

private def indexedRadialRawRestricted :
    I × (IndexedConeAttachment.quotientMk f ⁻¹'
      IndexedConeAttachment.upperCover f) →
      upperCover f s₀ x₀ γ :=
  fun p => ⟨attachment f s₀ x₀ γ (indexedRadialRaw f (p.1, p.2.1)),
    indexedRadialRaw_mem f s₀ x₀ γ p.1 p.2⟩

private theorem continuous_indexedRadialRawRestricted :
    Continuous (indexedRadialRawRestricted f s₀ x₀ γ) := by
  apply Continuous.subtype_mk
  exact (attachment f s₀ x₀ γ).continuous.comp
    ((continuous_indexedRadialRaw f).comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))

omit [TopologicalSpace X] [∀ j, TopologicalSpace (S j)] in
private theorem indexedRadialRaw_normalForm (u : I)
    (z : IndexedConeAttachment.Prequotient X S)
    (hz : IndexedConeAttachment.quotientMk f z ∈
      IndexedConeAttachment.upperCover f) :
    indexedRadialRaw f (u, IndexedConeAttachment.normalForm f z) =
      indexedRadialRaw f (u, z) := by
  rcases z with x | ⟨j, (_ | ⟨s, t⟩)⟩
  · rfl
  · rfl
  · by_cases h0 : t = 0
    · subst t
      simp [IndexedConeAttachment.normalForm, indexedRadialRaw]
    · by_cases h1 : t = 1
      · subst t
        change IndexedConeAttachment.cylinder f j s 1 ∈
          IndexedConeAttachment.upperCover f at hz
        rw [IndexedConeAttachment.cylinder_mem_upperCover_iff] at hz
        have : ¬((1 : I) < 1) := lt_irrefl _
        contradiction
      · simp [IndexedConeAttachment.normalForm, indexedRadialRaw, h0, h1]

private theorem indexedRadialRawRestricted_eq_of_quotient_eq (u : I)
    {a b : IndexedConeAttachment.quotientMk f ⁻¹'
      IndexedConeAttachment.upperCover f}
    (h : indexedUpperQuotientMap f a = indexedUpperQuotientMap f b) :
    indexedRadialRawRestricted f s₀ x₀ γ (u, a) =
      indexedRadialRawRestricted f s₀ x₀ γ (u, b) := by
  apply Subtype.ext
  apply congrArg (attachment f s₀ x₀ γ)
  rw [← indexedRadialRaw_normalForm f u a.1 a.2,
    ← indexedRadialRaw_normalForm f u b.1 b.2]
  have hrel := Quotient.exact (congrArg Subtype.val h)
  change IndexedConeAttachment.normalForm f a.1 =
    IndexedConeAttachment.normalForm f b.1 at hrel
  rw [hrel]

private noncomputable def indexedRadialMap :
    I × IndexedConeAttachment.upperCover f →
      upperCover f s₀ x₀ γ := fun p =>
  indexedRadialRawRestricted f s₀ x₀ γ
    (p.1, Function.surjInv
      (isQuotientMap_indexedUpperQuotientMap f).surjective p.2)

private theorem indexedRadialMap_quotientMap (u : I)
    (z : IndexedConeAttachment.quotientMk f ⁻¹'
      IndexedConeAttachment.upperCover f) :
    indexedRadialMap f s₀ x₀ γ (u, indexedUpperQuotientMap f z) =
      indexedRadialRawRestricted f s₀ x₀ γ (u, z) := by
  exact indexedRadialRawRestricted_eq_of_quotient_eq f s₀ x₀ γ u
    (Function.surjInv_eq
      (isQuotientMap_indexedUpperQuotientMap f).surjective _)

private theorem continuous_indexedRadialMap :
    Continuous (indexedRadialMap f s₀ x₀ γ) := by
  apply (isQuotientMap_indexedUpperQuotientMap f).continuous_lift_prod_right
  apply (continuous_indexedRadialRawRestricted f s₀ x₀ γ).congr
  rintro ⟨u, z⟩
  exact (indexedRadialMap_quotientMap f s₀ x₀ γ u z).symm

@[simp] private theorem indexedRadialMap_zero
    (y : IndexedConeAttachment.upperCover f) :
    indexedRadialMap f s₀ x₀ γ (0, y) =
      ⟨attachment f s₀ x₀ γ y.1,
        (attachment_mem_upperCover_iff f s₀ x₀ γ y.1).2 y.2⟩ := by
  obtain ⟨z, rfl⟩ := (isQuotientMap_indexedUpperQuotientMap f).surjective y
  rw [indexedRadialMap_quotientMap]
  apply Subtype.ext
  rcases z with ⟨x | ⟨j, (_ | ⟨s, t⟩)⟩, hmem⟩
  · exact False.elim (IndexedConeAttachment.base_not_mem_upperCover f x hmem)
  · rfl
  · change attachment f s₀ x₀ γ
      (IndexedConeAttachment.cylinder f j s
        (Set.Icc.convexComb t 0 0)) =
      attachment f s₀ x₀ γ (IndexedConeAttachment.cylinder f j s t)
    simp

private theorem indexedRadialMap_one_apex
    (j : J) (s : S j) (t : I)
    (ht : IndexedConeAttachment.cylinder f j s t ∈
      IndexedConeAttachment.upperCover f) :
    indexedRadialMap f s₀ x₀ γ
        (1, ⟨IndexedConeAttachment.cylinder f j s t, ht⟩) =
      ⟨apex f s₀ x₀ γ j, apex_mem_upperCover f s₀ x₀ γ j⟩ := by
  let z : IndexedConeAttachment.quotientMk f ⁻¹'
      IndexedConeAttachment.upperCover f :=
    ⟨Sum.inr ⟨j, Sum.inr (s, t)⟩, ht⟩
  have hz : indexedUpperQuotientMap f z =
      ⟨IndexedConeAttachment.cylinder f j s t, ht⟩ := rfl
  rw [← hz, indexedRadialMap_quotientMap]
  apply Subtype.ext
  change attachment f s₀ x₀ γ
      (IndexedConeAttachment.cylinder f j s
        (Set.Icc.convexComb t 0 1)) = apex f s₀ x₀ γ j
  simp [apex]

private def flatToUpperPrequotient :
    (flatMk f s₀ x₀ γ ⁻¹' upperCover f s₀ x₀ γ) →
      (quotientMk f s₀ x₀ γ ⁻¹' upperCover f s₀ x₀ γ) :=
  fun z => ⟨flatToPrequotient f z.1, z.2⟩

private theorem isQuotientMap_flatToUpperPrequotient :
    IsQuotientMap (flatToUpperPrequotient f s₀ x₀ γ) := by
  have hopen : IsOpen (quotientMk f s₀ x₀ γ ⁻¹'
      upperCover f s₀ x₀ γ) :=
    (isOpen_upperCover f s₀ x₀ γ).preimage
      (isQuotientMap_quotientMk f s₀ x₀ γ).continuous
  exact (isQuotientMap_flatToPrequotient f).restrictPreimage_isOpen hopen

private def phaseAPrequotientMap :
    I × (quotientMk f s₀ x₀ γ ⁻¹' upperCover f s₀ x₀ γ) →
      upperCover f s₀ x₀ γ
  | (u, ⟨Sum.inl y, hmem⟩) =>
      indexedRadialMap f s₀ x₀ γ
        (u, ⟨y, (attachment_mem_upperCover_iff f s₀ x₀ γ y).1 hmem⟩)
  | (u, ⟨Sum.inr (Sum.inl t), hmem⟩) =>
      ⟨spine f s₀ x₀ γ (raisedVertical u t),
        (spine_mem_upperCover_iff f s₀ x₀ γ _).2
          (raisedVertical_pos u t
            ((spine_mem_upperCover_iff f s₀ x₀ γ t).1 hmem))⟩
  | (u, ⟨Sum.inr (Sum.inr ⟨j, (a, t)⟩), hmem⟩) =>
      ⟨phaseAStrip f s₀ x₀ γ j u a t,
        phaseAStrip_mem_upperCover f s₀ x₀ γ j u a t
          ((strip_mem_upperCover_iff f s₀ x₀ γ j (a, t)).1 hmem)⟩

private theorem phaseAPrequotientMap_flat (u : I)
    (z : flatMk f s₀ x₀ γ ⁻¹' upperCover f s₀ x₀ γ) :
    phaseAPrequotientMap f s₀ x₀ γ
        (u, flatToUpperPrequotient f s₀ x₀ γ z) =
      phaseAFlatRawRestricted f s₀ x₀ γ (u, z) := by
  rcases z with ⟨y | (t | ⟨j, a, t⟩), hmem⟩
  · have hy : IndexedConeAttachment.quotientMk f y ∈
        IndexedConeAttachment.upperCover f := by
      apply (attachment_mem_upperCover_iff f s₀ x₀ γ _).1
      exact hmem
    change indexedRadialMap f s₀ x₀ γ
        (u, indexedUpperQuotientMap f ⟨y, hy⟩) = _
    rw [indexedRadialMap_quotientMap]
    rfl
  · rfl
  · rfl

private theorem continuous_phaseAPrequotientMap :
    Continuous (phaseAPrequotientMap f s₀ x₀ γ) := by
  apply (isQuotientMap_flatToUpperPrequotient f s₀ x₀ γ).continuous_lift_prod_right
  apply (continuous_phaseAFlatRawRestricted f s₀ x₀ γ).congr
  rintro ⟨u, z⟩
  exact (phaseAPrequotientMap_flat f s₀ x₀ γ u z).symm

omit [∀ j, TopologicalSpace (S j)] in
private theorem normalForm_idempotent (z : Prequotient f) :
    normalForm f s₀ x₀ γ (normalForm f s₀ x₀ γ z) =
      normalForm f s₀ x₀ γ z := by
  rcases z with y | (t | ⟨j, a, t⟩)
  · rfl
  · by_cases ht : t = 0
    · subst t
      simp [normalForm]
    · simp [normalForm, ht]
  · by_cases ht : t = 0
    · subst t
      simp [normalForm]
    · by_cases ha0 : a = 0
      · subst a
        simp [normalForm, ht]
      · by_cases ha1 : a = 1
        · subst a
          simp [normalForm, ht]
        · simp [normalForm, ht, ha0, ha1]

private def normalizeUpperSource
    (z : quotientMk f s₀ x₀ γ ⁻¹' upperCover f s₀ x₀ γ) :
    quotientMk f s₀ x₀ γ ⁻¹' upperCover f s₀ x₀ γ :=
  ⟨normalForm f s₀ x₀ γ z.1, by
    have hq : quotientMk f s₀ x₀ γ (normalForm f s₀ x₀ γ z.1) =
        quotientMk f s₀ x₀ γ z.1 := by
      apply Quotient.sound
      exact normalForm_idempotent f s₀ x₀ γ z.1
    change quotientMk f s₀ x₀ γ (normalForm f s₀ x₀ γ z.1) ∈
      upperCover f s₀ x₀ γ
    rw [hq]
    exact z.2⟩

private theorem phaseAPrequotientMap_normalize (u : I)
    (z : quotientMk f s₀ x₀ γ ⁻¹' upperCover f s₀ x₀ γ) :
    phaseAPrequotientMap f s₀ x₀ γ
        (u, normalizeUpperSource f s₀ x₀ γ z) =
      phaseAPrequotientMap f s₀ x₀ γ (u, z) := by
  apply Subtype.ext
  rcases z with ⟨y | (t | ⟨j, a, t⟩), hmem⟩
  · rfl
  · have ht : 0 < t := (spine_mem_upperCover_iff f s₀ x₀ γ t).1 hmem
    have ht0 : t ≠ 0 := ne_of_gt ht
    simp [normalizeUpperSource, normalForm, phaseAPrequotientMap, ht0]
  · have ht : 0 < t :=
      (strip_mem_upperCover_iff f s₀ x₀ γ j (a, t)).1 hmem
    have ht0 : t ≠ 0 := ne_of_gt ht
    by_cases ha0 : a = 0
    · subst a
      simp [normalizeUpperSource, normalForm, phaseAPrequotientMap, ht0,
        phaseAStrip_left]
    · by_cases ha1 : a = 1
      · subst a
        have hcyl : IndexedConeAttachment.cylinder f j (s₀ j)
            (truncatedRadialHeight t) ∈ IndexedConeAttachment.upperCover f := by
          rw [IndexedConeAttachment.cylinder_mem_upperCover_iff]
          exact truncatedRadialHeight_lt_one_of_pos t ht
        let iz : IndexedConeAttachment.quotientMk f ⁻¹'
            IndexedConeAttachment.upperCover f :=
          ⟨Sum.inr ⟨j, Sum.inr (s₀ j, truncatedRadialHeight t)⟩, hcyl⟩
        have hi := congrArg Subtype.val
          (indexedRadialMap_quotientMap f s₀ x₀ γ u iz)
        simp only [normalizeUpperSource, normalForm, ht0, ha0,
          phaseAPrequotientMap]
        rw [phaseAStrip_right]
        change (indexedRadialMap f s₀ x₀ γ
            (u, indexedUpperQuotientMap f iz)).1 =
          attachment f s₀ x₀ γ
            (IndexedConeAttachment.cylinder f j (s₀ j)
              (Set.Icc.convexComb (truncatedRadialHeight t) 0 u))
        simpa [iz, indexedRadialRawRestricted, indexedRadialRaw] using hi
      · simp [normalizeUpperSource, normalForm, phaseAPrequotientMap,
          ht0, ha0, ha1]

private theorem phaseAPrequotientMap_eq_of_quotient_eq (u : I)
    {a b : quotientMk f s₀ x₀ γ ⁻¹' upperCover f s₀ x₀ γ}
    (h : (upperCover f s₀ x₀ γ).restrictPreimage
        (quotientMk f s₀ x₀ γ) a =
      (upperCover f s₀ x₀ γ).restrictPreimage
        (quotientMk f s₀ x₀ γ) b) :
    phaseAPrequotientMap f s₀ x₀ γ (u, a) =
      phaseAPrequotientMap f s₀ x₀ γ (u, b) := by
  rw [← phaseAPrequotientMap_normalize f s₀ x₀ γ u a,
    ← phaseAPrequotientMap_normalize f s₀ x₀ γ u b]
  apply congrArg (phaseAPrequotientMap f s₀ x₀ γ) ∘
    congrArg (fun z => (u, z))
  apply Subtype.ext
  have hrel := Quotient.exact (congrArg Subtype.val h)
  exact hrel

private noncomputable def phaseAMap :
    I × upperCover f s₀ x₀ γ → upperCover f s₀ x₀ γ := fun p =>
  phaseAPrequotientMap f s₀ x₀ γ
    (p.1, Function.surjInv
      (isQuotientMap_restrictPreimage_upperCover f s₀ x₀ γ).surjective p.2)

private theorem phaseAMap_quotientMap (u : I)
    (z : quotientMk f s₀ x₀ γ ⁻¹' upperCover f s₀ x₀ γ) :
    phaseAMap f s₀ x₀ γ
        (u, (upperCover f s₀ x₀ γ).restrictPreimage
          (quotientMk f s₀ x₀ γ) z) =
      phaseAPrequotientMap f s₀ x₀ γ (u, z) := by
  exact phaseAPrequotientMap_eq_of_quotient_eq f s₀ x₀ γ u
    (Function.surjInv_eq
      (isQuotientMap_restrictPreimage_upperCover f s₀ x₀ γ).surjective _)

private theorem continuous_phaseAMap :
    Continuous (phaseAMap f s₀ x₀ γ) := by
  apply (isQuotientMap_restrictPreimage_upperCover f s₀ x₀ γ).continuous_lift_prod_right
  apply (continuous_phaseAPrequotientMap f s₀ x₀ γ).congr
  rintro ⟨u, z⟩
  exact (phaseAMap_quotientMap f s₀ x₀ γ u z).symm

private def armPoint (j : J) (u a : I) :
    Hatcher.VanKampen.AuxiliaryCellAttachment f s₀ x₀ γ :=
  bridgePoint f s₀ x₀ γ j 1 (shrinkParameter u a)

private theorem continuous_armPoint (j : J) :
    Continuous (fun p : I × I => armPoint f s₀ x₀ γ j p.1 p.2) := by
  exact (continuous_bridgePoint f s₀ x₀ γ j).comp
    (continuous_const.prodMk
      (Set.Icc.continuous_convexComb_prod.comp
        (continuous_snd.prodMk (continuous_const.prodMk continuous_fst))))

private theorem armPoint_mem_upperCover (j : J) (u a : I) :
    armPoint f s₀ x₀ γ j u a ∈ upperCover f s₀ x₀ γ :=
  bridgePoint_mem_upperCover f s₀ x₀ γ j 1 _ zero_lt_one

@[simp] private theorem armPoint_zero (j : J) (a : I) :
    armPoint f s₀ x₀ γ j 0 a = bridgePoint f s₀ x₀ γ j 1 a := by
  simp [armPoint, shrinkParameter]

@[simp] private theorem armPoint_one (j : J) (a : I) :
    armPoint f s₀ x₀ γ j 1 a = overlapBasepoint f s₀ x₀ γ := by
  simp [armPoint, shrinkParameter, overlapBasepoint]

@[simp] private theorem armPoint_left (j : J) (u : I) :
    armPoint f s₀ x₀ γ j u 0 = overlapBasepoint f s₀ x₀ γ := by
  simp [armPoint, shrinkParameter, overlapBasepoint]

private def indexedArmRaw :
    I × IndexedConeAttachment.Prequotient X S →
      Hatcher.VanKampen.AuxiliaryCellAttachment f s₀ x₀ γ
  | (_, Sum.inl _) => overlapBasepoint f s₀ x₀ γ
  | (u, Sum.inr ⟨j, Sum.inl _⟩) => armPoint f s₀ x₀ γ j u 1
  | (u, Sum.inr ⟨j, Sum.inr _⟩) => armPoint f s₀ x₀ γ j u 1

private theorem continuous_indexedArmRaw :
    Continuous (indexedArmRaw f s₀ x₀ γ) := by
  let gsigma : (Σ j : J, (Unit ⊕ (S j × I)) × I) →
      Hatcher.VanKampen.AuxiliaryCellAttachment f s₀ x₀ γ
    | ⟨j, _, u⟩ => armPoint f s₀ x₀ γ j u 1
  have hgsigma : Continuous gsigma := by
    rw [continuous_sigma_iff]
    intro j
    exact (continuous_armPoint f s₀ x₀ γ j).comp
      (continuous_snd.prodMk continuous_const)
  let g : (I × X) ⊕ (I × (Σ j : J, Unit ⊕ (S j × I))) →
      Hatcher.VanKampen.AuxiliaryCellAttachment f s₀ x₀ γ
    | Sum.inl _ => overlapBasepoint f s₀ x₀ γ
    | Sum.inr p => gsigma
        ((Homeomorph.sigmaProdDistrib :
          (Σ j : J, Unit ⊕ (S j × I)) × I ≃ₜ
            Σ j : J, (Unit ⊕ (S j × I)) × I) (Prod.swap p))
  have hg : Continuous g := by
    rw [continuous_sum_dom]
    constructor
    · exact continuous_const
    · exact hgsigma.comp
        ((Homeomorph.sigmaProdDistrib :
          (Σ j : J, Unit ⊕ (S j × I)) × I ≃ₜ
            Σ j : J, (Unit ⊕ (S j × I)) × I).continuous.comp continuous_swap)
  apply (hg.comp
    (Homeomorph.prodSumDistrib :
      I × IndexedConeAttachment.Prequotient X S ≃ₜ
        (I × X) ⊕ (I × (Σ j : J, Unit ⊕ (S j × I)))).continuous).congr
  rintro ⟨u, x | ⟨j, (_ | ⟨s, t⟩)⟩⟩ <;> rfl

private theorem indexedArmRaw_mem (u : I)
    (z : IndexedConeAttachment.quotientMk f ⁻¹'
      IndexedConeAttachment.upperCover f) :
    indexedArmRaw f s₀ x₀ γ (u, z.1) ∈ upperCover f s₀ x₀ γ := by
  rcases z with ⟨x | ⟨j, (_ | ⟨s, t⟩)⟩, hmem⟩
  · exact overlapBasepoint_mem_upperCover f s₀ x₀ γ
  · exact armPoint_mem_upperCover f s₀ x₀ γ j u 1
  · exact armPoint_mem_upperCover f s₀ x₀ γ j u 1

private def indexedArmRawRestricted :
    I × (IndexedConeAttachment.quotientMk f ⁻¹'
      IndexedConeAttachment.upperCover f) → upperCover f s₀ x₀ γ :=
  fun p => ⟨indexedArmRaw f s₀ x₀ γ (p.1, p.2.1),
    indexedArmRaw_mem f s₀ x₀ γ p.1 p.2⟩

private theorem continuous_indexedArmRawRestricted :
    Continuous (indexedArmRawRestricted f s₀ x₀ γ) := by
  apply Continuous.subtype_mk
  exact (continuous_indexedArmRaw f s₀ x₀ γ).comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))

private theorem indexedArmRaw_normalForm (u : I)
    (z : IndexedConeAttachment.Prequotient X S)
    (hz : IndexedConeAttachment.quotientMk f z ∈
      IndexedConeAttachment.upperCover f) :
    indexedArmRaw f s₀ x₀ γ (u, IndexedConeAttachment.normalForm f z) =
      indexedArmRaw f s₀ x₀ γ (u, z) := by
  rcases z with x | ⟨j, (_ | ⟨s, t⟩)⟩
  · rfl
  · rfl
  · by_cases h0 : t = 0
    · subst t
      simp [IndexedConeAttachment.normalForm, indexedArmRaw]
    · by_cases h1 : t = 1
      · subst t
        change IndexedConeAttachment.cylinder f j s 1 ∈
          IndexedConeAttachment.upperCover f at hz
        rw [IndexedConeAttachment.cylinder_mem_upperCover_iff] at hz
        exact False.elim (lt_irrefl _ hz)
      · simp [IndexedConeAttachment.normalForm, indexedArmRaw, h0, h1]

private theorem indexedArmRawRestricted_eq_of_quotient_eq (u : I)
    {a b : IndexedConeAttachment.quotientMk f ⁻¹'
      IndexedConeAttachment.upperCover f}
    (h : indexedUpperQuotientMap f a = indexedUpperQuotientMap f b) :
    indexedArmRawRestricted f s₀ x₀ γ (u, a) =
      indexedArmRawRestricted f s₀ x₀ γ (u, b) := by
  apply Subtype.ext
  change indexedArmRaw f s₀ x₀ γ (u, a.1) =
    indexedArmRaw f s₀ x₀ γ (u, b.1)
  rw [← indexedArmRaw_normalForm f s₀ x₀ γ u a.1 a.2,
    ← indexedArmRaw_normalForm f s₀ x₀ γ u b.1 b.2]
  have hrel := Quotient.exact (congrArg Subtype.val h)
  change IndexedConeAttachment.normalForm f a.1 =
    IndexedConeAttachment.normalForm f b.1 at hrel
  rw [hrel]

private noncomputable def indexedArmMap :
    I × IndexedConeAttachment.upperCover f → upperCover f s₀ x₀ γ := fun p =>
  indexedArmRawRestricted f s₀ x₀ γ
    (p.1, Function.surjInv
      (isQuotientMap_indexedUpperQuotientMap f).surjective p.2)

private theorem indexedArmMap_quotientMap (u : I)
    (z : IndexedConeAttachment.quotientMk f ⁻¹'
      IndexedConeAttachment.upperCover f) :
    indexedArmMap f s₀ x₀ γ (u, indexedUpperQuotientMap f z) =
      indexedArmRawRestricted f s₀ x₀ γ (u, z) := by
  exact indexedArmRawRestricted_eq_of_quotient_eq f s₀ x₀ γ u
    (Function.surjInv_eq
      (isQuotientMap_indexedUpperQuotientMap f).surjective _)

private theorem continuous_indexedArmMap :
    Continuous (indexedArmMap f s₀ x₀ γ) := by
  apply (isQuotientMap_indexedUpperQuotientMap f).continuous_lift_prod_right
  apply (continuous_indexedArmRawRestricted f s₀ x₀ γ).congr
  rintro ⟨u, z⟩
  exact (indexedArmMap_quotientMap f s₀ x₀ γ u z).symm

private def phaseBFlatRaw :
    I × FlatPrequotient (X := X) (S := S) →
      Hatcher.VanKampen.AuxiliaryCellAttachment f s₀ x₀ γ
  | (u, Sum.inl y) => indexedArmRaw f s₀ x₀ γ (u, y)
  | (_, Sum.inr (Sum.inl _)) => overlapBasepoint f s₀ x₀ γ
  | (u, Sum.inr (Sum.inr ⟨j, (a, _)⟩)) => armPoint f s₀ x₀ γ j u a

private theorem continuous_phaseBFlatRaw :
    Continuous (phaseBFlatRaw f s₀ x₀ γ) := by
  let gstrip : (Σ j : J, (I × I) × I) →
      Hatcher.VanKampen.AuxiliaryCellAttachment f s₀ x₀ γ
    | ⟨j, (a, _), u⟩ => armPoint f s₀ x₀ γ j u a
  have hgstrip : Continuous gstrip := by
    rw [continuous_sigma_iff]
    intro j
    exact (continuous_armPoint f s₀ x₀ γ j).comp
      (continuous_snd.prodMk (continuous_fst.comp continuous_fst))
  let gright : (I × I) ⊕ (I × (Σ _j : J, I × I)) →
      Hatcher.VanKampen.AuxiliaryCellAttachment f s₀ x₀ γ
    | Sum.inl _ => overlapBasepoint f s₀ x₀ γ
    | Sum.inr p => gstrip
        ((Homeomorph.sigmaProdDistrib :
          (Σ _j : J, I × I) × I ≃ₜ Σ _j : J, (I × I) × I)
          (Prod.swap p))
  have hgright : Continuous gright := by
    rw [continuous_sum_dom]
    constructor
    · exact continuous_const
    · exact hgstrip.comp
        ((Homeomorph.sigmaProdDistrib :
          (Σ _j : J, I × I) × I ≃ₜ Σ _j : J, (I × I) × I).continuous.comp
            continuous_swap)
  let g : (I × IndexedConeAttachment.Prequotient X S) ⊕
      (I × (I ⊕ (Σ _j : J, I × I))) →
      Hatcher.VanKampen.AuxiliaryCellAttachment f s₀ x₀ γ
    | Sum.inl p => indexedArmRaw f s₀ x₀ γ p
    | Sum.inr p => gright
        ((Homeomorph.prodSumDistrib :
          I × (I ⊕ (Σ _j : J, I × I)) ≃ₜ
            (I × I) ⊕ (I × (Σ _j : J, I × I))) p)
  have hg : Continuous g := by
    rw [continuous_sum_dom]
    constructor
    · exact continuous_indexedArmRaw f s₀ x₀ γ
    · exact hgright.comp
        (Homeomorph.prodSumDistrib :
          I × (I ⊕ (Σ _j : J, I × I)) ≃ₜ
            (I × I) ⊕ (I × (Σ _j : J, I × I))).continuous
  apply (hg.comp
    (Homeomorph.prodSumDistrib :
      I × FlatPrequotient (X := X) (S := S) ≃ₜ
        (I × IndexedConeAttachment.Prequotient X S) ⊕
          (I × (I ⊕ (Σ _j : J, I × I)))).continuous).congr
  rintro ⟨u, y | (t | ⟨j, p⟩)⟩ <;> rfl

private theorem phaseBFlatRaw_mem (u : I)
    (z : flatMk f s₀ x₀ γ ⁻¹' upperCover f s₀ x₀ γ) :
    phaseBFlatRaw f s₀ x₀ γ (u, z.1) ∈ upperCover f s₀ x₀ γ := by
  rcases z with ⟨y | (t | ⟨j, a, t⟩), hmem⟩
  · rcases y with x | ⟨j, (_ | ⟨s, h⟩)⟩
    · exact overlapBasepoint_mem_upperCover f s₀ x₀ γ
    · exact armPoint_mem_upperCover f s₀ x₀ γ j u 1
    · exact armPoint_mem_upperCover f s₀ x₀ γ j u 1
  · exact overlapBasepoint_mem_upperCover f s₀ x₀ γ
  · exact armPoint_mem_upperCover f s₀ x₀ γ j u a

private def phaseBFlatRawRestricted :
    I × (flatMk f s₀ x₀ γ ⁻¹' upperCover f s₀ x₀ γ) →
      upperCover f s₀ x₀ γ :=
  fun p => ⟨phaseBFlatRaw f s₀ x₀ γ (p.1, p.2.1),
    phaseBFlatRaw_mem f s₀ x₀ γ p.1 p.2⟩

private theorem continuous_phaseBFlatRawRestricted :
    Continuous (phaseBFlatRawRestricted f s₀ x₀ γ) := by
  apply Continuous.subtype_mk
  exact (continuous_phaseBFlatRaw f s₀ x₀ γ).comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))

private def phaseBPrequotientMap :
    I × (quotientMk f s₀ x₀ γ ⁻¹' upperCover f s₀ x₀ γ) →
      upperCover f s₀ x₀ γ
  | (u, ⟨Sum.inl y, hmem⟩) =>
      indexedArmMap f s₀ x₀ γ
        (u, ⟨y, (attachment_mem_upperCover_iff f s₀ x₀ γ y).1 hmem⟩)
  | (_, ⟨Sum.inr (Sum.inl _), _⟩) => upperOverlapBasepoint f s₀ x₀ γ
  | (u, ⟨Sum.inr (Sum.inr ⟨j, (a, _)⟩), _⟩) =>
      ⟨armPoint f s₀ x₀ γ j u a,
        armPoint_mem_upperCover f s₀ x₀ γ j u a⟩

private theorem phaseBPrequotientMap_flat (u : I)
    (z : flatMk f s₀ x₀ γ ⁻¹' upperCover f s₀ x₀ γ) :
    phaseBPrequotientMap f s₀ x₀ γ
        (u, flatToUpperPrequotient f s₀ x₀ γ z) =
      phaseBFlatRawRestricted f s₀ x₀ γ (u, z) := by
  rcases z with ⟨y | (t | ⟨j, a, t⟩), hmem⟩
  · have hy : IndexedConeAttachment.quotientMk f y ∈
        IndexedConeAttachment.upperCover f := by
      apply (attachment_mem_upperCover_iff f s₀ x₀ γ _).1
      exact hmem
    change indexedArmMap f s₀ x₀ γ
        (u, indexedUpperQuotientMap f ⟨y, hy⟩) = _
    rw [indexedArmMap_quotientMap]
    rfl
  · rfl
  · rfl

private theorem continuous_phaseBPrequotientMap :
    Continuous (phaseBPrequotientMap f s₀ x₀ γ) := by
  apply (isQuotientMap_flatToUpperPrequotient f s₀ x₀ γ).continuous_lift_prod_right
  apply (continuous_phaseBFlatRawRestricted f s₀ x₀ γ).congr
  rintro ⟨u, z⟩
  exact (phaseBPrequotientMap_flat f s₀ x₀ γ u z).symm

private theorem phaseBPrequotientMap_normalize (u : I)
    (z : quotientMk f s₀ x₀ γ ⁻¹' upperCover f s₀ x₀ γ) :
    phaseBPrequotientMap f s₀ x₀ γ
        (u, normalizeUpperSource f s₀ x₀ γ z) =
      phaseBPrequotientMap f s₀ x₀ γ (u, z) := by
  apply Subtype.ext
  rcases z with ⟨y | (t | ⟨j, a, t⟩), hmem⟩
  · rfl
  · have ht : 0 < t := (spine_mem_upperCover_iff f s₀ x₀ γ t).1 hmem
    have ht0 : t ≠ 0 := ne_of_gt ht
    simp [normalizeUpperSource, normalForm, phaseBPrequotientMap, ht0]
  · have ht : 0 < t :=
      (strip_mem_upperCover_iff f s₀ x₀ γ j (a, t)).1 hmem
    have ht0 : t ≠ 0 := ne_of_gt ht
    by_cases ha0 : a = 0
    · subst a
      simp [normalizeUpperSource, normalForm, phaseBPrequotientMap, ht0]
      rfl
    · by_cases ha1 : a = 1
      · subst a
        have hcyl : IndexedConeAttachment.cylinder f j (s₀ j)
            (truncatedRadialHeight t) ∈ IndexedConeAttachment.upperCover f := by
          rw [IndexedConeAttachment.cylinder_mem_upperCover_iff]
          exact truncatedRadialHeight_lt_one_of_pos t ht
        let iz : IndexedConeAttachment.quotientMk f ⁻¹'
            IndexedConeAttachment.upperCover f :=
          ⟨Sum.inr ⟨j, Sum.inr (s₀ j, truncatedRadialHeight t)⟩, hcyl⟩
        have hi := congrArg Subtype.val
          (indexedArmMap_quotientMap f s₀ x₀ γ u iz)
        simp only [normalizeUpperSource, normalForm, ht0, ha0,
          phaseBPrequotientMap]
        change (indexedArmMap f s₀ x₀ γ
            (u, indexedUpperQuotientMap f iz)).1 =
          armPoint f s₀ x₀ γ j u 1
        simpa [iz, indexedArmRawRestricted, indexedArmRaw] using hi
      · simp [normalizeUpperSource, normalForm, phaseBPrequotientMap,
          ht0, ha0, ha1]

private theorem phaseBPrequotientMap_eq_of_quotient_eq (u : I)
    {a b : quotientMk f s₀ x₀ γ ⁻¹' upperCover f s₀ x₀ γ}
    (h : (upperCover f s₀ x₀ γ).restrictPreimage
        (quotientMk f s₀ x₀ γ) a =
      (upperCover f s₀ x₀ γ).restrictPreimage
        (quotientMk f s₀ x₀ γ) b) :
    phaseBPrequotientMap f s₀ x₀ γ (u, a) =
      phaseBPrequotientMap f s₀ x₀ γ (u, b) := by
  rw [← phaseBPrequotientMap_normalize f s₀ x₀ γ u a,
    ← phaseBPrequotientMap_normalize f s₀ x₀ γ u b]
  apply congrArg (phaseBPrequotientMap f s₀ x₀ γ) ∘
    congrArg (fun z => (u, z))
  apply Subtype.ext
  exact Quotient.exact (congrArg Subtype.val h)

private noncomputable def phaseBMap :
    I × upperCover f s₀ x₀ γ → upperCover f s₀ x₀ γ := fun p =>
  phaseBPrequotientMap f s₀ x₀ γ
    (p.1, Function.surjInv
      (isQuotientMap_restrictPreimage_upperCover f s₀ x₀ γ).surjective p.2)

private theorem phaseBMap_quotientMap (u : I)
    (z : quotientMk f s₀ x₀ γ ⁻¹' upperCover f s₀ x₀ γ) :
    phaseBMap f s₀ x₀ γ
        (u, (upperCover f s₀ x₀ γ).restrictPreimage
          (quotientMk f s₀ x₀ γ) z) =
      phaseBPrequotientMap f s₀ x₀ γ (u, z) := by
  exact phaseBPrequotientMap_eq_of_quotient_eq f s₀ x₀ γ u
    (Function.surjInv_eq
      (isQuotientMap_restrictPreimage_upperCover f s₀ x₀ γ).surjective _)

private theorem continuous_phaseBMap :
    Continuous (phaseBMap f s₀ x₀ γ) := by
  apply (isQuotientMap_restrictPreimage_upperCover f s₀ x₀ γ).continuous_lift_prod_right
  apply (continuous_phaseBPrequotientMap f s₀ x₀ γ).congr
  rintro ⟨u, z⟩
  exact (phaseBMap_quotientMap f s₀ x₀ γ u z).symm

private theorem indexedArmMap_zero_eq_indexedRadialMap_one
    (y : IndexedConeAttachment.upperCover f) :
    indexedArmMap f s₀ x₀ γ (0, y) =
      indexedRadialMap f s₀ x₀ γ (1, y) := by
  obtain ⟨z, rfl⟩ := (isQuotientMap_indexedUpperQuotientMap f).surjective y
  rw [indexedArmMap_quotientMap, indexedRadialMap_quotientMap]
  apply Subtype.ext
  rcases z with ⟨x | ⟨j, (_ | ⟨s, t⟩)⟩, hmem⟩
  · exact False.elim (IndexedConeAttachment.base_not_mem_upperCover f x hmem)
  · change armPoint f s₀ x₀ γ j 0 1 = apex f s₀ x₀ γ j
    rw [armPoint_zero, bridgePoint_one]
  · change armPoint f s₀ x₀ γ j 0 1 =
      attachment f s₀ x₀ γ
        (IndexedConeAttachment.cylinder f j s
          (Set.Icc.convexComb t 0 1))
    rw [armPoint_zero, bridgePoint_one]
    simp [apex]

@[simp] private theorem indexedArmMap_one
    (y : IndexedConeAttachment.upperCover f) :
    indexedArmMap f s₀ x₀ γ (1, y) = upperOverlapBasepoint f s₀ x₀ γ := by
  obtain ⟨z, rfl⟩ := (isQuotientMap_indexedUpperQuotientMap f).surjective y
  rw [indexedArmMap_quotientMap]
  apply Subtype.ext
  rcases z with ⟨x | ⟨j, (_ | ⟨s, t⟩)⟩, hmem⟩
  · rfl
  · exact armPoint_one f s₀ x₀ γ j 1
  · exact armPoint_one f s₀ x₀ γ j 1

@[simp] private theorem phaseAMap_zero (z : upperCover f s₀ x₀ γ) :
    phaseAMap f s₀ x₀ γ (0, z) = z := by
  obtain ⟨a, rfl⟩ :=
    (isQuotientMap_restrictPreimage_upperCover f s₀ x₀ γ).surjective z
  rw [phaseAMap_quotientMap]
  apply Subtype.ext
  rcases a with ⟨y | (t | ⟨j, p⟩), hmem⟩
  · have hy : y ∈ IndexedConeAttachment.upperCover f :=
      (attachment_mem_upperCover_iff f s₀ x₀ γ y).1 hmem
    exact congrArg Subtype.val (indexedRadialMap_zero f s₀ x₀ γ ⟨y, hy⟩)
  · simp [phaseAPrequotientMap, raisedVertical, spine, quotientMk]
  · simp [phaseAPrequotientMap, phaseAStrip_zero, strip, quotientMk]

@[simp] private theorem phaseAMap_center (u : I) :
    phaseAMap f s₀ x₀ γ (u, upperOverlapBasepoint f s₀ x₀ γ) =
      upperOverlapBasepoint f s₀ x₀ γ := by
  let z : quotientMk f s₀ x₀ γ ⁻¹' upperCover f s₀ x₀ γ :=
    ⟨Sum.inr (Sum.inl (1 : I)),
      overlapBasepoint_mem_upperCover f s₀ x₀ γ⟩
  have hz : (upperCover f s₀ x₀ γ).restrictPreimage
      (quotientMk f s₀ x₀ γ) z = upperOverlapBasepoint f s₀ x₀ γ := rfl
  rw [← hz, phaseAMap_quotientMap]
  apply Subtype.ext
  change spine f s₀ x₀ γ (raisedVertical u 1) = spine f s₀ x₀ γ 1
  simp [raisedVertical]

private theorem phaseBMap_zero_eq_phaseAMap_one
    (z : upperCover f s₀ x₀ γ) :
    phaseBMap f s₀ x₀ γ (0, z) = phaseAMap f s₀ x₀ γ (1, z) := by
  obtain ⟨a, rfl⟩ :=
    (isQuotientMap_restrictPreimage_upperCover f s₀ x₀ γ).surjective z
  rw [phaseBMap_quotientMap, phaseAMap_quotientMap]
  rcases a with ⟨y | (t | ⟨j, a, t⟩), hmem⟩
  · exact indexedArmMap_zero_eq_indexedRadialMap_one f s₀ x₀ γ _
  · apply Subtype.ext
    simp [phaseBPrequotientMap, phaseAPrequotientMap, raisedVertical,
      upperOverlapBasepoint, overlapBasepoint]
  · apply Subtype.ext
    simpa [phaseBPrequotientMap, phaseAPrequotientMap] using
      (phaseAStrip_one f s₀ x₀ γ j a t).symm

@[simp] private theorem phaseBMap_one (z : upperCover f s₀ x₀ γ) :
    phaseBMap f s₀ x₀ γ (1, z) = upperOverlapBasepoint f s₀ x₀ γ := by
  obtain ⟨a, rfl⟩ :=
    (isQuotientMap_restrictPreimage_upperCover f s₀ x₀ γ).surjective z
  rw [phaseBMap_quotientMap]
  rcases a with ⟨y | (t | ⟨j, a, t⟩), hmem⟩
  · exact indexedArmMap_one f s₀ x₀ γ _
  · rfl
  · apply Subtype.ext
    exact armPoint_one f s₀ x₀ γ j a

@[simp] private theorem phaseBMap_center (u : I) :
    phaseBMap f s₀ x₀ γ (u, upperOverlapBasepoint f s₀ x₀ γ) =
      upperOverlapBasepoint f s₀ x₀ γ := by
  let z : quotientMk f s₀ x₀ γ ⁻¹' upperCover f s₀ x₀ γ :=
    ⟨Sum.inr (Sum.inl (1 : I)),
      overlapBasepoint_mem_upperCover f s₀ x₀ γ⟩
  have hz : (upperCover f s₀ x₀ γ).restrictPreimage
      (quotientMk f s₀ x₀ γ) z = upperOverlapBasepoint f s₀ x₀ γ := rfl
  rw [← hz, phaseBMap_quotientMap]
  rfl

private def phaseAEnd : C(upperCover f s₀ x₀ γ,
    upperCover f s₀ x₀ γ) where
  toFun z := phaseAMap f s₀ x₀ γ (1, z)
  continuous_toFun := (continuous_phaseAMap f s₀ x₀ γ).comp
    (continuous_const.prodMk continuous_id)

private def phaseADeformation :
    (ContinuousMap.id (upperCover f s₀ x₀ γ)).HomotopyRel
      (phaseAEnd f s₀ x₀ γ) {upperOverlapBasepoint f s₀ x₀ γ} where
  toFun := phaseAMap f s₀ x₀ γ
  continuous_toFun := continuous_phaseAMap f s₀ x₀ γ
  map_zero_left := phaseAMap_zero f s₀ x₀ γ
  map_one_left _ := rfl
  prop' u z hz := by
    rw [Set.mem_singleton_iff] at hz
    subst z
    exact phaseAMap_center f s₀ x₀ γ u

private def phaseBDeformation :
    (phaseAEnd f s₀ x₀ γ).HomotopyRel
      (ContinuousMap.const (upperCover f s₀ x₀ γ)
        (upperOverlapBasepoint f s₀ x₀ γ))
      {upperOverlapBasepoint f s₀ x₀ γ} where
  toFun := phaseBMap f s₀ x₀ γ
  continuous_toFun := continuous_phaseBMap f s₀ x₀ γ
  map_zero_left := phaseBMap_zero_eq_phaseAMap_one f s₀ x₀ γ
  map_one_left := phaseBMap_one f s₀ x₀ γ
  prop' u z hz := by
    rw [Set.mem_singleton_iff] at hz
    subst z
    change phaseBMap f s₀ x₀ γ
        (u, upperOverlapBasepoint f s₀ x₀ γ) =
      phaseAMap f s₀ x₀ γ (1, upperOverlapBasepoint f s₀ x₀ γ)
    rw [phaseBMap_center, phaseAMap_center]

def upperContraction :
    (ContinuousMap.id (upperCover f s₀ x₀ γ)).HomotopyRel
      (ContinuousMap.const (upperCover f s₀ x₀ γ)
        (upperOverlapBasepoint f s₀ x₀ γ))
      {upperOverlapBasepoint f s₀ x₀ γ} :=
  (phaseADeformation f s₀ x₀ γ).trans (phaseBDeformation f s₀ x₀ γ)

def upperStrongDeformationRetract :
    Hatcher.StrongDeformationRetract
      (ContinuousMap.const Unit (upperOverlapBasepoint f s₀ x₀ γ)) :=
  Hatcher.StrongDeformationRetract.ofPointedContraction
    (upperOverlapBasepoint f s₀ x₀ γ) (upperContraction f s₀ x₀ γ)

theorem contractibleSpace_upperCover :
    ContractibleSpace (upperCover f s₀ x₀ γ) :=
  (upperStrongDeformationRetract f s₀ x₀ γ).contractibleSpace

end Hatcher.VanKampen.AuxiliaryCellAttachment
