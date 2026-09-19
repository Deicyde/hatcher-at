import Hatcher.VanKampen.AuxiliaryCellAttachment

/-!
# Hatcher's binary cover of the auxiliary cell attachment
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

/-- Raw preimage of the base-side cover: omit exactly the indexed cone apices. -/
def basePreimage : Set (Prequotient f)
  | Sum.inl y => y ∈ IndexedConeAttachment.lowerCover f
  | Sum.inr _ => True

/-- Raw preimage of the upper cover: omit the canonical base and the bottom
edges of the auxiliary strips. -/
def upperPreimage : Set (Prequotient f)
  | Sum.inl y => y ∈ IndexedConeAttachment.upperCover f
  | Sum.inr (Sum.inl t) => 0 < t
  | Sum.inr (Sum.inr ⟨_, (_, t)⟩) => 0 < t

omit [TopologicalSpace X] [∀ j, TopologicalSpace (S j)] in
@[simp] private theorem mem_basePreimage_inl
    (y : Hatcher.VanKampen.IndexedConeAttachment f) :
    Sum.inl y ∈ basePreimage (f := f) ↔
      y ∈ IndexedConeAttachment.lowerCover f :=
  Iff.rfl

omit [TopologicalSpace X] [∀ j, TopologicalSpace (S j)] in
@[simp] private theorem mem_basePreimage_inr
    (z : I ⊕ Sigma (fun _j : J ↦ I × I)) :
    Sum.inr z ∈ basePreimage (f := f) :=
  trivial

omit [TopologicalSpace X] [∀ j, TopologicalSpace (S j)] in
@[simp] private theorem mem_upperPreimage_inl
    (y : Hatcher.VanKampen.IndexedConeAttachment f) :
    Sum.inl y ∈ upperPreimage (f := f) ↔
      y ∈ IndexedConeAttachment.upperCover f :=
  Iff.rfl

omit [TopologicalSpace X] [∀ j, TopologicalSpace (S j)] in
@[simp] private theorem mem_upperPreimage_spine (t : I) :
    Sum.inr (Sum.inl t) ∈ upperPreimage (f := f) ↔ 0 < t :=
  Iff.rfl

omit [TopologicalSpace X] [∀ j, TopologicalSpace (S j)] in
@[simp] private theorem mem_upperPreimage_strip (j : J) (a t : I) :
    Sum.inr (Sum.inr ⟨j, (a, t)⟩) ∈ upperPreimage (f := f) ↔ 0 < t :=
  Iff.rfl

/-- The complement of the indexed apices is open in the auxiliary
prequotient. -/
theorem isOpen_basePreimage : IsOpen (basePreimage (f := f)) := by
  rw [isOpen_sum_iff]
  constructor
  · exact (IndexedConeAttachment.isOpenCover_lower_upper f).1
  · convert (isOpen_univ :
      IsOpen (Set.univ : Set (I ⊕ Sigma (fun _j : J ↦ I × I)))) using 1
    ext z
    simp only [Set.mem_preimage, Set.mem_univ, iff_true]
    exact mem_basePreimage_inr f z

/-- The raw upper member is open in the auxiliary prequotient. -/
theorem isOpen_upperPreimage : IsOpen (upperPreimage (f := f)) := by
  rw [isOpen_sum_iff]
  constructor
  · exact (IndexedConeAttachment.isOpenCover_lower_upper f).2.1
  · rw [isOpen_sum_iff]
    constructor
    · have hopen : IsOpen {t : I | (0 : ℝ) < (t : ℝ)} :=
        (isOpen_Ioi : IsOpen (Set.Ioi (0 : ℝ))).preimage
          (continuous_subtype_val : Continuous fun t : I => (t : ℝ))
      convert hopen using 1
      ext t
      rfl
    · rw [isOpen_sigma_iff]
      intro j
      have hopen : IsOpen {p : I × I | (0 : ℝ) < (p.2 : ℝ)} :=
        (isOpen_Ioi : IsOpen (Set.Ioi (0 : ℝ))).preimage
          ((continuous_subtype_val : Continuous fun t : I => (t : ℝ)).comp
            continuous_snd)
      convert hopen using 1
      ext p
      rfl

private theorem truncatedRadialHeight_lt_one_iff (t : I) :
    truncatedRadialHeight t < 1 ↔ 0 < t := by
  change 1 - (t : ℝ) / 2 < 1 ↔ 0 < (t : ℝ)
  constructor <;> intro h <;> linarith

omit [∀ j, TopologicalSpace (S j)] in
private theorem normalForm_mem_basePreimage_iff (z : Prequotient f) :
    normalForm f s₀ x₀ γ z ∈ basePreimage (f := f) ↔
      z ∈ basePreimage (f := f) := by
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
          simp [normalForm, ht, truncatedRadialHeight_pos]
        · simp [normalForm, ht, ha0, ha1]

omit [∀ j, TopologicalSpace (S j)] in
private theorem normalForm_mem_upperPreimage_iff (z : Prequotient f) :
    normalForm f s₀ x₀ γ z ∈ upperPreimage (f := f) ↔
      z ∈ upperPreimage (f := f) := by
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
          simp [normalForm, ht, truncatedRadialHeight_lt_one_iff]
        · simp [normalForm, ht, ha0, ha1]

/-- Hatcher's base-side cover member: the auxiliary space with every indexed
cone apex omitted. -/
def baseCover : Set (Hatcher.VanKampen.AuxiliaryCellAttachment f s₀ x₀ γ) :=
  fun z => Quotient.lift
    (fun raw => normalForm f s₀ x₀ γ raw ∈ basePreimage (f := f))
    (fun _ _ h => congrArg (fun raw => raw ∈ basePreimage (f := f)) h)
    z

/-- The auxiliary upper cover member: the canonical base is omitted, while
the positive-height spine, strips, and truncated cone neighborhoods remain. -/
def upperCover : Set (Hatcher.VanKampen.AuxiliaryCellAttachment f s₀ x₀ γ) :=
  fun z => Quotient.lift
    (fun raw => normalForm f s₀ x₀ γ raw ∈ upperPreimage (f := f))
    (fun _ _ h => congrArg (fun raw => raw ∈ upperPreimage (f := f)) h)
    z

omit [∀ j, TopologicalSpace (S j)] in
/-- The quotient map pulls the base-side member back to its raw preimage. -/
theorem quotientMk_preimage_baseCover :
    quotientMk f s₀ x₀ γ ⁻¹' baseCover f s₀ x₀ γ =
      basePreimage (f := f) := by
  ext z
  exact normalForm_mem_basePreimage_iff f s₀ x₀ γ z

omit [∀ j, TopologicalSpace (S j)] in
/-- The quotient map pulls the upper member back to its raw preimage. -/
theorem quotientMk_preimage_upperCover :
    quotientMk f s₀ x₀ γ ⁻¹' upperCover f s₀ x₀ γ =
      upperPreimage (f := f) := by
  ext z
  exact normalForm_mem_upperPreimage_iff f s₀ x₀ γ z

/-- Membership of the indexed attachment in the base-side member. -/
@[simp] theorem attachment_mem_baseCover_iff
    (y : Hatcher.VanKampen.IndexedConeAttachment f) :
    attachment f s₀ x₀ γ y ∈ baseCover f s₀ x₀ γ ↔
      y ∈ IndexedConeAttachment.lowerCover f := by
  change (Sum.inl y : Prequotient f) ∈
    quotientMk f s₀ x₀ γ ⁻¹' baseCover f s₀ x₀ γ ↔ _
  rw [quotientMk_preimage_baseCover]
  exact mem_basePreimage_inl f y

/-- Membership of the indexed attachment in the upper member. -/
@[simp] theorem attachment_mem_upperCover_iff
    (y : Hatcher.VanKampen.IndexedConeAttachment f) :
    attachment f s₀ x₀ γ y ∈ upperCover f s₀ x₀ γ ↔
      y ∈ IndexedConeAttachment.upperCover f := by
  change (Sum.inl y : Prequotient f) ∈
    quotientMk f s₀ x₀ γ ⁻¹' upperCover f s₀ x₀ γ ↔ _
  rw [quotientMk_preimage_upperCover]
  exact mem_upperPreimage_inl f y

/-- The whole common spine lies in the base-side member. -/
@[simp] theorem spine_mem_baseCover (t : I) :
    spine f s₀ x₀ γ t ∈ baseCover f s₀ x₀ γ := by
  change (Sum.inr (Sum.inl t) : Prequotient f) ∈
    quotientMk f s₀ x₀ γ ⁻¹' baseCover f s₀ x₀ γ
  rw [quotientMk_preimage_baseCover]
  exact mem_basePreimage_inr f _

/-- The upper member contains exactly the positive-height spine points. -/
@[simp] theorem spine_mem_upperCover_iff (t : I) :
    spine f s₀ x₀ γ t ∈ upperCover f s₀ x₀ γ ↔ 0 < t := by
  change (Sum.inr (Sum.inl t) : Prequotient f) ∈
    quotientMk f s₀ x₀ γ ⁻¹' upperCover f s₀ x₀ γ ↔ _
  rw [quotientMk_preimage_upperCover]
  exact mem_upperPreimage_spine f t

/-- Every strip lies in the base-side member. -/
@[simp] theorem strip_mem_baseCover (j : J) (p : I × I) :
    strip f s₀ x₀ γ j p ∈ baseCover f s₀ x₀ γ := by
  change (Sum.inr (Sum.inr ⟨j, p⟩) : Prequotient f) ∈
    quotientMk f s₀ x₀ γ ⁻¹' baseCover f s₀ x₀ γ
  rw [quotientMk_preimage_baseCover]
  exact mem_basePreimage_inr f _

/-- The upper member contains exactly the positive-height strip points. -/
@[simp] theorem strip_mem_upperCover_iff (j : J) (p : I × I) :
    strip f s₀ x₀ γ j p ∈ upperCover f s₀ x₀ γ ↔ 0 < p.2 := by
  change (Sum.inr (Sum.inr ⟨j, p⟩) : Prequotient f) ∈
    quotientMk f s₀ x₀ γ ⁻¹' upperCover f s₀ x₀ γ ↔ _
  rw [quotientMk_preimage_upperCover]
  exact mem_upperPreimage_strip f j p.1 p.2

/-- The base-side member omits every indexed cone apex. -/
@[simp] theorem apex_not_mem_baseCover (j : J) :
    apex f s₀ x₀ γ j ∉ baseCover f s₀ x₀ γ := by
  simp [apex]

/-- The upper member omits the canonical copy of the original base. -/
@[simp] theorem base_not_mem_upperCover (x : X) :
    base f s₀ x₀ γ x ∉ upperCover f s₀ x₀ γ := by
  rw [show base f s₀ x₀ γ x =
    attachment f s₀ x₀ γ (IndexedConeAttachment.base f x) from rfl]
  rw [attachment_mem_upperCover_iff]
  exact IndexedConeAttachment.base_not_mem_upperCover f x

@[simp] theorem base_mem_baseCover (x : X) :
    base f s₀ x₀ γ x ∈ baseCover f s₀ x₀ γ := by
  rw [show base f s₀ x₀ γ x =
    attachment f s₀ x₀ γ (IndexedConeAttachment.base f x) from rfl]
  rw [attachment_mem_baseCover_iff]
  exact IndexedConeAttachment.base_mem_lowerCover f x

@[simp] theorem apex_mem_upperCover (j : J) :
    apex f s₀ x₀ γ j ∈ upperCover f s₀ x₀ γ := by
  rw [show apex f s₀ x₀ γ j =
    attachment f s₀ x₀ γ (IndexedConeAttachment.apex f j) from rfl]
  rw [attachment_mem_upperCover_iff]
  exact IndexedConeAttachment.apex_mem_upperCover f j

/-- The base-side member is open. -/
theorem isOpen_baseCover : IsOpen (baseCover f s₀ x₀ γ) := by
  apply (isQuotientMap_quotientMk f s₀ x₀ γ).isCoinducing.isOpen_preimage.mp
  rw [quotientMk_preimage_baseCover]
  exact isOpen_basePreimage f

/-- The upper member is open. -/
theorem isOpen_upperCover : IsOpen (upperCover f s₀ x₀ γ) := by
  apply (isQuotientMap_quotientMk f s₀ x₀ γ).isCoinducing.isOpen_preimage.mp
  rw [quotientMk_preimage_upperCover]
  exact isOpen_upperPreimage f

theorem basePreimage_union_upperPreimage :
    basePreimage (f := f) ∪ upperPreimage (f := f) = univ := by
  ext z
  rcases z with y | (t | ⟨j, p⟩)
  · simp only [Set.mem_union, Set.mem_univ, iff_true,
      mem_basePreimage_inl, mem_upperPreimage_inl]
    have hy : y ∈ IndexedConeAttachment.lowerCover f ∪
        IndexedConeAttachment.upperCover f := by
      rw [(IndexedConeAttachment.isOpenCover_lower_upper f).2.2]
      trivial
    exact hy
  · simp only [Set.mem_union, Set.mem_univ, mem_basePreimage_inr,
      true_or]
  · simp only [Set.mem_union, Set.mem_univ, mem_basePreimage_inr,
      true_or]

/-- The base-side and upper members cover the auxiliary attachment. -/
theorem baseCover_union_upperCover :
    baseCover f s₀ x₀ γ ∪ upperCover f s₀ x₀ γ = univ := by
  apply (isQuotientMap_quotientMk f s₀ x₀ γ).surjective.preimage_injective
  rw [preimage_union, preimage_univ, quotientMk_preimage_baseCover,
    quotientMk_preimage_upperCover, basePreimage_union_upperPreimage]

/-- Hatcher's two subsets form an open cover of the auxiliary attachment. -/
theorem isOpenCover_base_upper [Nonempty J] :
    IsOpen (baseCover f s₀ x₀ γ) ∧
      IsOpen (upperCover f s₀ x₀ γ) ∧
      baseCover f s₀ x₀ γ ∪ upperCover f s₀ x₀ γ = univ :=
  ⟨isOpen_baseCover f s₀ x₀ γ, isOpen_upperCover f s₀ x₀ γ,
    baseCover_union_upperCover f s₀ x₀ γ⟩

/-- Inclusion of the base-side member into the auxiliary attachment. -/
def baseCoverInclusion : C(baseCover f s₀ x₀ γ,
    Hatcher.VanKampen.AuxiliaryCellAttachment f s₀ x₀ γ) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- Inclusion of the upper member into the auxiliary attachment. -/
def upperCoverInclusion : C(upperCover f s₀ x₀ γ,
    Hatcher.VanKampen.AuxiliaryCellAttachment f s₀ x₀ γ) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- The canonical base map, with codomain restricted to the base-side member. -/
def baseToBaseCover : C(X, baseCover f s₀ x₀ γ) where
  toFun x := ⟨base f s₀ x₀ γ x, base_mem_baseCover f s₀ x₀ γ x⟩
  continuous_toFun := (base f s₀ x₀ γ).continuous.subtype_mk _

/-- Restricting the quotient map over the open base-side member remains a
quotient map. -/
theorem isQuotientMap_restrictPreimage_baseCover :
    IsQuotientMap ((baseCover f s₀ x₀ γ).restrictPreimage
      (quotientMk f s₀ x₀ γ)) :=
  (isQuotientMap_quotientMk f s₀ x₀ γ).restrictPreimage_isOpen
    (isOpen_baseCover f s₀ x₀ γ)

/-- Restricting the quotient map over the open upper member remains a quotient
map. -/
theorem isQuotientMap_restrictPreimage_upperCover :
    IsQuotientMap ((upperCover f s₀ x₀ γ).restrictPreimage
      (quotientMk f s₀ x₀ γ)) :=
  (isQuotientMap_quotientMk f s₀ x₀ γ).restrictPreimage_isOpen
    (isOpen_upperCover f s₀ x₀ γ)

/-- The two cover members indexed in the order expected by binary van Kampen. -/
def binaryCover : Fin 2 →
    Set (Hatcher.VanKampen.AuxiliaryCellAttachment f s₀ x₀ γ) :=
  Fin.cases (baseCover f s₀ x₀ γ) (fun _ => upperCover f s₀ x₀ γ)

omit [∀ j, TopologicalSpace (S j)] in
@[simp] theorem binaryCover_zero :
    binaryCover f s₀ x₀ γ 0 = baseCover f s₀ x₀ γ :=
  rfl

omit [∀ j, TopologicalSpace (S j)] in
@[simp] theorem binaryCover_one :
    binaryCover f s₀ x₀ γ 1 = upperCover f s₀ x₀ γ :=
  rfl

/-- Every member of the binary cover is open. -/
theorem isOpen_binaryCover (i : Fin 2) :
    IsOpen (binaryCover f s₀ x₀ γ i) := by
  fin_cases i
  · exact isOpen_baseCover f s₀ x₀ γ
  · exact isOpen_upperCover f s₀ x₀ γ

/-- The binary family covers the auxiliary attachment. -/
theorem univ_subset_iUnion_binaryCover :
    univ ⊆ ⋃ i, binaryCover f s₀ x₀ γ i := by
  intro z _
  have hz : z ∈ baseCover f s₀ x₀ γ ∪ upperCover f s₀ x₀ γ := by
    rw [baseCover_union_upperCover]
    trivial
  rcases hz with hz | hz
  · exact Set.mem_iUnion.mpr ⟨0, by simpa using hz⟩
  · exact Set.mem_iUnion.mpr ⟨1, by simpa using hz⟩

/-- The top of the common spine, used as the binary-cover basepoint. -/
def overlapBasepoint :
    Hatcher.VanKampen.AuxiliaryCellAttachment f s₀ x₀ γ :=
  spine f s₀ x₀ γ 1

/-- The chosen basepoint lies in the base-side member. -/
theorem overlapBasepoint_mem_baseCover :
    overlapBasepoint f s₀ x₀ γ ∈ baseCover f s₀ x₀ γ := by
  change quotientMk f s₀ x₀ γ
      (Sum.inr (Sum.inl (1 : I))) ∈ _
  change (Sum.inr (Sum.inl (1 : I)) :
      Prequotient f) ∈ quotientMk f s₀ x₀ γ ⁻¹' baseCover f s₀ x₀ γ
  rw [quotientMk_preimage_baseCover]
  exact mem_basePreimage_inr f _

/-- The chosen basepoint lies in the upper member. -/
theorem overlapBasepoint_mem_upperCover :
    overlapBasepoint f s₀ x₀ γ ∈ upperCover f s₀ x₀ γ := by
  change quotientMk f s₀ x₀ γ
      (Sum.inr (Sum.inl (1 : I))) ∈ _
  change (Sum.inr (Sum.inl (1 : I)) :
      Prequotient f) ∈ quotientMk f s₀ x₀ γ ⁻¹' upperCover f s₀ x₀ γ
  rw [quotientMk_preimage_upperCover]
  rw [mem_upperPreimage_spine]
  exact zero_lt_one

/-- The chosen basepoint lies in the overlap. -/
theorem overlapBasepoint_mem_inter :
    overlapBasepoint f s₀ x₀ γ ∈
      baseCover f s₀ x₀ γ ∩ upperCover f s₀ x₀ γ :=
  ⟨overlapBasepoint_mem_baseCover f s₀ x₀ γ,
    overlapBasepoint_mem_upperCover f s₀ x₀ γ⟩

/-- The chosen basepoint lies in both members of the binary family. -/
theorem overlapBasepoint_mem_binaryCover (i : Fin 2) :
    overlapBasepoint f s₀ x₀ γ ∈ binaryCover f s₀ x₀ γ i := by
  fin_cases i
  · exact overlapBasepoint_mem_baseCover f s₀ x₀ γ
  · exact overlapBasepoint_mem_upperCover f s₀ x₀ γ

end Hatcher.VanKampen.AuxiliaryCellAttachment
