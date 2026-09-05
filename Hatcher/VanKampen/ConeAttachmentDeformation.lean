import Hatcher.VanKampen.ConeAttachment
import Hatcher.VanKampen.WellPointedWedgeCover
import Mathlib.Topology.CompactOpen

/-!
# Deformations of the standard cone-attachment cover

The lower cover member strongly deformation-retracts onto the canonical copy
of the base space. The upper cover member contracts to the cone apex.
-/

noncomputable section

open Set Topology
open scoped unitInterval

namespace Hatcher.VanKampen.ConeAttachment

universe u v

variable {X : Type u} {S : Type v} [TopologicalSpace X]
  [TopologicalSpace S]

private def lowerRaw (f : C(S, X)) :
    I × Prequotient X S → Hatcher.VanKampen.ConeAttachment f
  | (_, Sum.inl x) => base f x
  | (_, Sum.inr (Sum.inl _)) => apex f
  | (u, Sum.inr (Sum.inr (s, t))) =>
      cylinder f s (Set.Icc.convexComb t 1 u)

private theorem continuous_lowerRaw (f : C(S, X)) :
    Continuous (lowerRaw f) := by
  have hq : Continuous (quotientMk f) :=
    (isQuotientMap_quotientMk f).continuous
  let gright : (I × Unit) ⊕ (I × (S × I)) →
      Hatcher.VanKampen.ConeAttachment f
    | Sum.inl _ => apex f
    | Sum.inr (u, s, t) =>
        cylinder f s (Set.Icc.convexComb t 1 u)
  have hgright : Continuous gright := by
    rw [continuous_sum_dom]
    constructor
    · exact continuous_const
    · change Continuous fun p : I × (S × I) =>
        cylinder f p.2.1 (Set.Icc.convexComb p.2.2 1 p.1)
      apply hq.comp
      fun_prop
  let g : (I × X) ⊕ (I × (Unit ⊕ (S × I))) →
      Hatcher.VanKampen.ConeAttachment f
    | Sum.inl (_, x) => base f x
    | Sum.inr p => gright
        ((Homeomorph.prodSumDistrib :
          I × (Unit ⊕ (S × I)) ≃ₜ (I × Unit) ⊕ (I × (S × I))) p)
  have hg : Continuous g := by
    rw [continuous_sum_dom]
    constructor
    · change Continuous fun p : I × X => base f p.2
      exact hq.comp (continuous_inl.comp continuous_snd)
    · exact hgright.comp
        (Homeomorph.prodSumDistrib :
          I × (Unit ⊕ (S × I)) ≃ₜ (I × Unit) ⊕ (I × (S × I))).continuous
  apply (hg.comp
    (Homeomorph.prodSumDistrib :
      I × (X ⊕ (Unit ⊕ (S × I))) ≃ₜ
        (I × X) ⊕ (I × (Unit ⊕ (S × I)))).continuous).congr
  rintro ⟨u, z⟩
  rcases z with x | z
  · rfl
  · rcases z with a | p
    · rfl
    · rfl

private def upperRaw (f : C(S, X)) :
    I × Prequotient X S → Hatcher.VanKampen.ConeAttachment f
  | (_, Sum.inl x) => base f x
  | (_, Sum.inr (Sum.inl _)) => apex f
  | (u, Sum.inr (Sum.inr (s, t))) =>
      cylinder f s (Set.Icc.convexComb t 0 u)

private theorem continuous_upperRaw (f : C(S, X)) :
    Continuous (upperRaw f) := by
  have hq : Continuous (quotientMk f) :=
    (isQuotientMap_quotientMk f).continuous
  let gright : (I × Unit) ⊕ (I × (S × I)) →
      Hatcher.VanKampen.ConeAttachment f
    | Sum.inl _ => apex f
    | Sum.inr (u, s, t) =>
        cylinder f s (Set.Icc.convexComb t 0 u)
  have hgright : Continuous gright := by
    rw [continuous_sum_dom]
    constructor
    · exact continuous_const
    · change Continuous fun p : I × (S × I) =>
        cylinder f p.2.1 (Set.Icc.convexComb p.2.2 0 p.1)
      apply hq.comp
      fun_prop
  let g : (I × X) ⊕ (I × (Unit ⊕ (S × I))) →
      Hatcher.VanKampen.ConeAttachment f
    | Sum.inl (_, x) => base f x
    | Sum.inr p => gright
        ((Homeomorph.prodSumDistrib :
          I × (Unit ⊕ (S × I)) ≃ₜ (I × Unit) ⊕ (I × (S × I))) p)
  have hg : Continuous g := by
    rw [continuous_sum_dom]
    constructor
    · change Continuous fun p : I × X => base f p.2
      exact hq.comp (continuous_inl.comp continuous_snd)
    · exact hgright.comp
        (Homeomorph.prodSumDistrib :
          I × (Unit ⊕ (S × I)) ≃ₜ (I × Unit) ⊕ (I × (S × I))).continuous
  apply (hg.comp
    (Homeomorph.prodSumDistrib :
      I × (X ⊕ (Unit ⊕ (S × I))) ≃ₜ
        (I × X) ⊕ (I × (Unit ⊕ (S × I)))).continuous).congr
  rintro ⟨u, z⟩
  rcases z with x | z
  · rfl
  · rcases z with a | p
    · rfl
    · rfl

private theorem lowerSource_mem_lowerPreimage (f : C(S, X))
    (z : quotientMk f ⁻¹' lowerCover f) :
    z.1 ∈ lowerPreimage := by
  exact Set.ext_iff.mp (quotientMk_preimage_lowerCover f) z.1 |>.mp z.2

private theorem upperSource_mem_upperPreimage (f : C(S, X))
    (z : quotientMk f ⁻¹' upperCover f) :
    z.1 ∈ upperPreimage := by
  exact Set.ext_iff.mp (quotientMk_preimage_upperCover f) z.1 |>.mp z.2

private theorem lowerRaw_mem (f : C(S, X)) (u : I)
    (z : quotientMk f ⁻¹' lowerCover f) :
    lowerRaw f (u, z.1) ∈ lowerCover f := by
  have hz := lowerSource_mem_lowerPreimage f z
  rcases z with ⟨z, hz'⟩
  rcases z with x | z
  · change Sum.inl x ∈ quotientMk f ⁻¹' lowerCover f
    rw [quotientMk_preimage_lowerCover]
    trivial
  · rcases z with a | ⟨s, t⟩
    · change False at hz
      contradiction
    · change Sum.inr (Sum.inr (s, Set.Icc.convexComb t 1 u)) ∈
        quotientMk f ⁻¹' lowerCover f
      rw [quotientMk_preimage_lowerCover]
      change 0 < Set.Icc.convexComb t 1 u
      change 0 < t at hz
      exact hz.trans_le (Set.Icc.le_convexComb unitInterval.le_one' u)

private theorem upperRaw_mem (f : C(S, X)) (u : I)
    (z : quotientMk f ⁻¹' upperCover f) :
    upperRaw f (u, z.1) ∈ upperCover f := by
  have hz := upperSource_mem_upperPreimage f z
  rcases z with ⟨z, hz'⟩
  rcases z with x | z
  · change False at hz
    contradiction
  · rcases z with a | ⟨s, t⟩
    · change Sum.inr (Sum.inl ()) ∈ quotientMk f ⁻¹' upperCover f
      rw [quotientMk_preimage_upperCover]
      trivial
    · change Sum.inr (Sum.inr (s, Set.Icc.convexComb t 0 u)) ∈
        quotientMk f ⁻¹' upperCover f
      rw [quotientMk_preimage_upperCover]
      change Set.Icc.convexComb t 0 u < 1
      change t < 1 at hz
      have hle : Set.Icc.convexComb t 0 u ≤ t := by
        rw [← Set.Icc.convexComb_symm]
        exact Set.Icc.convexComb_le unitInterval.nonneg' _
      exact hle.trans_lt hz

private def lowerRawRestricted (f : C(S, X)) :
    I × (quotientMk f ⁻¹' lowerCover f) → lowerCover f :=
  fun p ↦ ⟨lowerRaw f (p.1, p.2.1), lowerRaw_mem f p.1 p.2⟩

private theorem continuous_lowerRawRestricted (f : C(S, X)) :
    Continuous (lowerRawRestricted f) := by
  apply Continuous.subtype_mk
  exact (continuous_lowerRaw f).comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))

private def upperRawRestricted (f : C(S, X)) :
    I × (quotientMk f ⁻¹' upperCover f) → upperCover f :=
  fun p ↦ ⟨upperRaw f (p.1, p.2.1), upperRaw_mem f p.1 p.2⟩

private theorem continuous_upperRawRestricted (f : C(S, X)) :
    Continuous (upperRawRestricted f) := by
  apply Continuous.subtype_mk
  exact (continuous_upperRaw f).comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))

private theorem lowerRaw_eq_of_normalForm_eq (f : C(S, X)) (u : I)
    {a b : Prequotient X S} (ha : a ∈ lowerPreimage)
    (hb : b ∈ lowerPreimage) (h : normalForm f a = normalForm f b) :
    lowerRaw f (u, a) = lowerRaw f (u, b) := by
  rcases a with x | (_ | ⟨s, t⟩) <;>
    rcases b with y | (_ | ⟨r, v⟩)
  all_goals try simp only [normalForm] at h
  all_goals try split_ifs at h
  all_goals simp_all [lowerRaw]

private theorem upperRaw_eq_of_normalForm_eq (f : C(S, X)) (u : I)
    {a b : Prequotient X S} (ha : a ∈ upperPreimage)
    (hb : b ∈ upperPreimage) (h : normalForm f a = normalForm f b) :
    upperRaw f (u, a) = upperRaw f (u, b) := by
  rcases a with x | (_ | ⟨s, t⟩) <;>
    rcases b with y | (_ | ⟨r, v⟩)
  all_goals try simp only [normalForm] at h
  all_goals try split_ifs at h
  all_goals simp_all [upperRaw]

private theorem lowerRawRestricted_eq_of_quotient_eq (f : C(S, X))
    (u : I) {a b : quotientMk f ⁻¹' lowerCover f}
    (h : (lowerCover f).restrictPreimage (quotientMk f) a =
      (lowerCover f).restrictPreimage (quotientMk f) b) :
    lowerRawRestricted f (u, a) = lowerRawRestricted f (u, b) := by
  apply Subtype.ext
  apply lowerRaw_eq_of_normalForm_eq f u
  · exact lowerSource_mem_lowerPreimage f a
  · exact lowerSource_mem_lowerPreimage f b
  · have hrel := Quotient.exact (congrArg Subtype.val h)
    exact hrel

private theorem upperRawRestricted_eq_of_quotient_eq (f : C(S, X))
    (u : I) {a b : quotientMk f ⁻¹' upperCover f}
    (h : (upperCover f).restrictPreimage (quotientMk f) a =
      (upperCover f).restrictPreimage (quotientMk f) b) :
    upperRawRestricted f (u, a) = upperRawRestricted f (u, b) := by
  apply Subtype.ext
  apply upperRaw_eq_of_normalForm_eq f u
  · exact upperSource_mem_upperPreimage f a
  · exact upperSource_mem_upperPreimage f b
  · have hrel := Quotient.exact (congrArg Subtype.val h)
    exact hrel

private noncomputable def lowerDeformationMap (f : C(S, X)) :
    I × lowerCover f → lowerCover f := fun p =>
  lowerRawRestricted f
    (p.1, Function.surjInv
      (isQuotientMap_restrictPreimage_lowerCover f).surjective p.2)

private theorem lowerDeformationMap_quotientMap (f : C(S, X))
    (u : I) (z : quotientMk f ⁻¹' lowerCover f) :
    lowerDeformationMap f
        (u, (lowerCover f).restrictPreimage (quotientMk f) z) =
      lowerRawRestricted f (u, z) := by
  apply lowerRawRestricted_eq_of_quotient_eq f u
  exact Function.surjInv_eq
    (isQuotientMap_restrictPreimage_lowerCover f).surjective _

private theorem continuous_lowerDeformationMap (f : C(S, X)) :
    Continuous (lowerDeformationMap f) := by
  apply (isQuotientMap_restrictPreimage_lowerCover f).continuous_lift_prod_right
  apply (continuous_lowerRawRestricted f).congr
  rintro ⟨u, z⟩
  exact (lowerDeformationMap_quotientMap f u z).symm

private noncomputable def upperDeformationMap (f : C(S, X)) :
    I × upperCover f → upperCover f := fun p =>
  upperRawRestricted f
    (p.1, Function.surjInv
      (isQuotientMap_restrictPreimage_upperCover f).surjective p.2)

private theorem upperDeformationMap_quotientMap (f : C(S, X))
    (u : I) (z : quotientMk f ⁻¹' upperCover f) :
    upperDeformationMap f
        (u, (upperCover f).restrictPreimage (quotientMk f) z) =
      upperRawRestricted f (u, z) := by
  apply upperRawRestricted_eq_of_quotient_eq f u
  exact Function.surjInv_eq
    (isQuotientMap_restrictPreimage_upperCover f).surjective _

private theorem continuous_upperDeformationMap (f : C(S, X)) :
    Continuous (upperDeformationMap f) := by
  apply (isQuotientMap_restrictPreimage_upperCover f).continuous_lift_prod_right
  apply (continuous_upperRawRestricted f).congr
  rintro ⟨u, z⟩
  exact (upperDeformationMap_quotientMap f u z).symm

/-- The cone apex, regarded as a point of the upper cover member. -/
def upperApex (f : C(S, X)) : upperCover f :=
  ⟨apex f, by
    change Sum.inr (Sum.inl ()) ∈ quotientMk f ⁻¹' upperCover f
    rw [quotientMk_preimage_upperCover]
    trivial⟩

@[simp]
private theorem upperDeformationMap_zero (f : C(S, X))
    (z : upperCover f) : upperDeformationMap f (0, z) = z := by
  obtain ⟨a, rfl⟩ :=
    (isQuotientMap_restrictPreimage_upperCover f).surjective z
  rw [upperDeformationMap_quotientMap]
  apply Subtype.ext
  rcases a with ⟨a, ha⟩
  rcases a with x | (_ | ⟨s, t⟩) <;>
    simp [upperRawRestricted, upperRaw, base, apex, cylinder]

@[simp]
private theorem upperDeformationMap_one (f : C(S, X))
    (z : upperCover f) :
    upperDeformationMap f (1, z) = upperApex f := by
  obtain ⟨a, rfl⟩ :=
    (isQuotientMap_restrictPreimage_upperCover f).surjective z
  rw [upperDeformationMap_quotientMap]
  apply Subtype.ext
  have ha := upperSource_mem_upperPreimage f a
  rcases a with ⟨a, ha'⟩
  rcases a with x | (_ | ⟨s, t⟩)
  · change False at ha
    contradiction
  · rfl
  · simp [upperRawRestricted, upperRaw, upperApex, apex]

@[simp]
private theorem upperDeformationMap_apex (f : C(S, X)) (u : I) :
    upperDeformationMap f (u, upperApex f) = upperApex f := by
  let a : quotientMk f ⁻¹' upperCover f :=
    ⟨Sum.inr (Sum.inl ()), by
      change Sum.inr (Sum.inl ()) ∈ quotientMk f ⁻¹' upperCover f
      rw [quotientMk_preimage_upperCover]
      trivial⟩
  have ha : (upperCover f).restrictPreimage (quotientMk f) a =
      upperApex f := rfl
  rw [← ha, upperDeformationMap_quotientMap]
  rfl

/-- The upper cover member contracts to the cone apex while fixing the apex. -/
def upperContraction (f : C(S, X)) :
    (ContinuousMap.id (upperCover f)).HomotopyRel
      (ContinuousMap.const (upperCover f) (upperApex f)) {upperApex f} where
  toFun := upperDeformationMap f
  continuous_toFun := continuous_upperDeformationMap f
  map_zero_left := upperDeformationMap_zero f
  map_one_left := upperDeformationMap_one f
  prop' u z hz := by
    rw [Set.mem_singleton_iff] at hz
    subst z
    exact upperDeformationMap_apex f u

/-- The upper cover member of a cone attachment is contractible. -/
theorem contractibleSpace_upperCover (f : C(S, X)) :
    ContractibleSpace (upperCover f) :=
  Hatcher.StrongDeformationRetract.contractibleSpace_of_pointedContraction
    (upperApex f) (upperContraction f)

private def lowerRetractionPre (f : C(S, X)) :
    (quotientMk f ⁻¹' lowerCover f) → X
  | ⟨Sum.inl x, _⟩ => x
  | ⟨Sum.inr (Sum.inl _), h⟩ => False.elim <| by
      have hz : (Sum.inr (Sum.inl ()) : Prequotient X S) ∈
          lowerPreimage :=
        Set.ext_iff.mp (quotientMk_preimage_lowerCover f) _ |>.mp h
      exact hz
  | ⟨Sum.inr (Sum.inr (s, _)), _⟩ => f s

private theorem continuous_lowerRetractionPre (f : C(S, X)) :
    Continuous (lowerRetractionPre f) := by
  cases isEmpty_or_nonempty X with
  | inl hX =>
      letI : IsEmpty X := hX
      exact continuous_empty_function _
  | inr hX =>
      let x₀ : X := Classical.choice hX
      let g : Prequotient X S → X
        | Sum.inl x => x
        | Sum.inr (Sum.inl _) => x₀
        | Sum.inr (Sum.inr (s, _)) => f s
      have hg : Continuous g := by
        rw [continuous_sum_dom]
        constructor
        · exact continuous_id
        · rw [continuous_sum_dom]
          exact ⟨continuous_const, f.continuous.comp continuous_fst⟩
      apply (hg.comp continuous_subtype_val).congr
      intro z
      have hz := lowerSource_mem_lowerPreimage f z
      rcases z with ⟨z, hz'⟩
      rcases z with x | (_ | ⟨s, t⟩)
      · rfl
      · change False at hz
        contradiction
      · rfl

private theorem lowerRetractionPre_eq_of_quotient_eq (f : C(S, X))
    {a b : quotientMk f ⁻¹' lowerCover f}
    (h : (lowerCover f).restrictPreimage (quotientMk f) a =
      (lowerCover f).restrictPreimage (quotientMk f) b) :
    lowerRetractionPre f a = lowerRetractionPre f b := by
  have ha := lowerSource_mem_lowerPreimage f a
  have hb := lowerSource_mem_lowerPreimage f b
  have hrel := Quotient.exact (congrArg Subtype.val h)
  obtain ⟨a, ha'⟩ := a
  obtain ⟨b, hb'⟩ := b
  change normalForm f a = normalForm f b at hrel
  rcases a with x | (_ | ⟨s, t⟩) <;>
    rcases b with y | (_ | ⟨r, v⟩)
  all_goals try simp only [normalForm] at hrel
  all_goals try split_ifs at hrel
  all_goals simp_all [lowerRetractionPre]

private noncomputable def lowerRetractionMap (f : C(S, X)) :
    lowerCover f → X := fun z =>
  lowerRetractionPre f
    (Function.surjInv
      (isQuotientMap_restrictPreimage_lowerCover f).surjective z)

private theorem lowerRetractionMap_quotientMap (f : C(S, X))
    (z : quotientMk f ⁻¹' lowerCover f) :
    lowerRetractionMap f
        ((lowerCover f).restrictPreimage (quotientMk f) z) =
      lowerRetractionPre f z := by
  apply lowerRetractionPre_eq_of_quotient_eq f
  exact Function.surjInv_eq
    (isQuotientMap_restrictPreimage_lowerCover f).surjective _

private theorem continuous_lowerRetractionMap (f : C(S, X)) :
    Continuous (lowerRetractionMap f) := by
  apply (isQuotientMap_restrictPreimage_lowerCover f).continuous_iff.mpr
  apply (continuous_lowerRetractionPre f).congr
  intro z
  exact (lowerRetractionMap_quotientMap f z).symm

/-- The canonical copy of `X` inside the lower cone-attachment cover. -/
def lowerBaseInclusion (f : C(S, X)) : C(X, lowerCover f) where
  toFun x := ⟨base f x, by
    change Sum.inl x ∈ quotientMk f ⁻¹' lowerCover f
    rw [quotientMk_preimage_lowerCover]
    trivial⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (isQuotientMap_quotientMk f).continuous.comp continuous_inl

/-- Retraction of the lower cover member onto the canonical copy of `X`. -/
noncomputable def lowerRetraction (f : C(S, X)) : C(lowerCover f, X) where
  toFun := lowerRetractionMap f
  continuous_toFun := continuous_lowerRetractionMap f

@[simp]
theorem lowerRetraction_apply_base (f : C(S, X)) (x : X) :
    lowerRetraction f (lowerBaseInclusion f x) = x := by
  let a : quotientMk f ⁻¹' lowerCover f :=
    ⟨Sum.inl x, by
      change Sum.inl x ∈ quotientMk f ⁻¹' lowerCover f
      rw [quotientMk_preimage_lowerCover]
      trivial⟩
  have ha : (lowerCover f).restrictPreimage (quotientMk f) a =
      lowerBaseInclusion f x := rfl
  change lowerRetractionMap f (lowerBaseInclusion f x) = x
  rw [← ha, lowerRetractionMap_quotientMap]
  rfl

theorem lowerRetraction_comp_inclusion (f : C(S, X)) :
    (lowerRetraction f).comp (lowerBaseInclusion f) = ContinuousMap.id X := by
  ext x
  exact lowerRetraction_apply_base f x

@[simp]
private theorem lowerDeformationMap_zero (f : C(S, X))
    (z : lowerCover f) : lowerDeformationMap f (0, z) = z := by
  obtain ⟨a, rfl⟩ :=
    (isQuotientMap_restrictPreimage_lowerCover f).surjective z
  rw [lowerDeformationMap_quotientMap]
  apply Subtype.ext
  rcases a with ⟨a, ha⟩
  rcases a with x | (_ | ⟨s, t⟩) <;>
    simp [lowerRawRestricted, lowerRaw, base, apex, cylinder]

@[simp]
private theorem lowerDeformationMap_one (f : C(S, X))
    (z : lowerCover f) :
    lowerDeformationMap f (1, z) =
      lowerBaseInclusion f (lowerRetraction f z) := by
  obtain ⟨a, rfl⟩ :=
    (isQuotientMap_restrictPreimage_lowerCover f).surjective z
  rw [lowerDeformationMap_quotientMap]
  change lowerRawRestricted f (1, a) =
    lowerBaseInclusion f
      (lowerRetractionMap f
        ((lowerCover f).restrictPreimage (quotientMk f) a))
  rw [lowerRetractionMap_quotientMap]
  apply Subtype.ext
  have ha := lowerSource_mem_lowerPreimage f a
  rcases a with ⟨a, ha'⟩
  rcases a with x | (_ | ⟨s, t⟩)
  · rfl
  · change False at ha
    contradiction
  · simp [lowerRawRestricted, lowerRaw, lowerBaseInclusion,
      lowerRetractionPre]

@[simp]
private theorem lowerDeformationMap_base (f : C(S, X)) (u : I) (x : X) :
    lowerDeformationMap f (u, lowerBaseInclusion f x) =
      lowerBaseInclusion f x := by
  let a : quotientMk f ⁻¹' lowerCover f :=
    ⟨Sum.inl x, by
      change Sum.inl x ∈ quotientMk f ⁻¹' lowerCover f
      rw [quotientMk_preimage_lowerCover]
      trivial⟩
  have ha : (lowerCover f).restrictPreimage (quotientMk f) a =
      lowerBaseInclusion f x := rfl
  rw [← ha, lowerDeformationMap_quotientMap]
  rfl

private def lowerDeformation (f : C(S, X)) :
    (ContinuousMap.id (lowerCover f)).HomotopyRel
      ((lowerBaseInclusion f).comp (lowerRetraction f))
      (Set.range (lowerBaseInclusion f)) where
  toFun := lowerDeformationMap f
  continuous_toFun := continuous_lowerDeformationMap f
  map_zero_left := lowerDeformationMap_zero f
  map_one_left := lowerDeformationMap_one f
  prop' u z hz := by
    obtain ⟨x, rfl⟩ := hz
    exact lowerDeformationMap_base f u x

/-- The lower cover member strongly deformation-retracts onto the canonical
copy of `X`. -/
def lowerStrongDeformationRetract (f : C(S, X)) :
    Hatcher.StrongDeformationRetract (lowerBaseInclusion f) where
  retract := lowerRetraction f
  retract_inclusion := lowerRetraction_comp_inclusion f
  deformation := lowerDeformation f

end Hatcher.VanKampen.ConeAttachment
