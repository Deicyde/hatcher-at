import Hatcher.VanKampen.AuxiliaryCellAttachmentCover

/-!
# The indexed open cover of Hatcher's auxiliary overlap

The overlap between the base-side and upper members of the auxiliary
cell-attachment cover is covered by one open set for each attached cone. The
piece indexed by `j` contains the open cylinder of cone `j`, the positive
common spine, every positive strip interior, and the right edge only of strip
`j`. Thus the other cone interiors are omitted without sacrificing openness.

When the attaching spaces are path-connected, all pairwise intersections of
these pieces are path-connected through the top of the common spine.
-/

noncomputable section

open Set Topology
open scoped unitInterval ContinuousMap

namespace Hatcher.VanKampen.IndexedConeAttachment

universe u


variable {X J : Type u} {S : J → Type u}
variable [TopologicalSpace X] [∀ j, TopologicalSpace (S j)]

/-- The raw interior of the cone with index `j`. -/
def interiorPiecePreimage (j : J) : Set (Prequotient X S)
  | Sum.inl _ => False
  | Sum.inr ⟨_, Sum.inl _⟩ => False
  | Sum.inr ⟨k, Sum.inr (_, t)⟩ => k = j ∧ 0 < t ∧ t < 1

omit [TopologicalSpace X] [∀ j, TopologicalSpace (S j)] in
private theorem normalForm_mem_interiorPiecePreimage_iff
    (f : ∀ j, S j → X) (j : J) (z : Prequotient X S) :
    normalForm f z ∈ interiorPiecePreimage (S := S) j ↔
      z ∈ interiorPiecePreimage (S := S) j := by
  rcases z with x | ⟨k, z⟩
  · simp [normalForm]
  · rcases z with star | ⟨s, t⟩
    · rcases star with ⟨⟩
      simp [normalForm]
    · by_cases h0 : t = 0
      · subst t
        simp only [normalForm, if_pos]
        change False ↔ k = j ∧ 0 < (0 : I) ∧ (0 : I) < 1
        simp
      · by_cases h1 : t = 1
        · subst t
          simp only [normalForm, h0, if_false, if_pos]
          change False ↔ k = j ∧ 0 < (1 : I) ∧ (1 : I) < 1
          simp
        · simp [normalForm, h0, h1]

/-- The open interior cylinder belonging to one indexed cone. -/
def interiorPiece (f : ∀ j, S j → X) (j : J) :
    Set (Hatcher.VanKampen.IndexedConeAttachment f) := fun z =>
  Quotient.lift
    (fun raw => normalForm f raw ∈ interiorPiecePreimage (S := S) j)
    (fun _ _ h => congrArg
      (fun raw => raw ∈ interiorPiecePreimage (S := S) j) h) z

omit [TopologicalSpace X] [∀ j, TopologicalSpace (S j)] in
@[simp] theorem quotientMk_preimage_interiorPiece
    (f : ∀ j, S j → X) (j : J) :
    quotientMk f ⁻¹' interiorPiece f j = interiorPiecePreimage (S := S) j := by
  ext z
  exact normalForm_mem_interiorPiecePreimage_iff f j z

theorem isOpen_interiorPiecePreimage (j : J) :
    IsOpen (interiorPiecePreimage (X := X) (S := S) j) := by
  rw [isOpen_sum_iff]
  constructor
  · exact isOpen_empty
  · rw [isOpen_sigma_iff]
    intro k
    rw [isOpen_sum_iff]
    constructor
    · exact isOpen_empty
    · change IsOpen {p : S k × I | k = j ∧ 0 < p.2 ∧ p.2 < 1}
      by_cases hkj : k = j
      · subst k
        have hopen :=
          (((isOpen_Ioi : IsOpen (Set.Ioi (0 : I))).preimage
              (continuous_snd : Continuous fun p : S j × I ↦ p.2)).inter
            ((isOpen_Iio : IsOpen (Set.Iio (1 : I))).preimage
              (continuous_snd : Continuous fun p : S j × I ↦ p.2)))
        convert hopen using 1
        ext p
        simp
      · have hempty : {p : S k × I | k = j ∧ 0 < p.2 ∧ p.2 < 1} = ∅ := by
          ext p
          simp [hkj]
        rw [hempty]
        exact isOpen_empty

private theorem isQuotientMap_quotientMk'
    (f : ∀ j, S j → X) : IsQuotientMap (quotientMk f) :=
  isQuotientMap_quot_mk

theorem isOpen_interiorPiece (f : ∀ j, S j → X) (j : J) :
    IsOpen (interiorPiece f j) := by
  apply (isQuotientMap_quotientMk' f).isCoinducing.isOpen_preimage.mp
  rw [quotientMk_preimage_interiorPiece]
  exact isOpen_interiorPiecePreimage j

omit [TopologicalSpace X] [∀ j, TopologicalSpace (S j)] in
@[simp] theorem base_not_mem_interiorPiece
    (f : ∀ j, S j → X) (j : J) (x : X) :
    base f x ∉ interiorPiece f j := by
  change (Sum.inl x : Prequotient X S) ∉ quotientMk f ⁻¹' interiorPiece f j
  rw [quotientMk_preimage_interiorPiece]
  exact id

omit [TopologicalSpace X] [∀ j, TopologicalSpace (S j)] in
@[simp] theorem apex_not_mem_interiorPiece
    (f : ∀ j, S j → X) (j k : J) :
    apex f k ∉ interiorPiece f j := by
  change (Sum.inr ⟨k, Sum.inl ()⟩ : Prequotient X S) ∉
    quotientMk f ⁻¹' interiorPiece f j
  rw [quotientMk_preimage_interiorPiece]
  exact id

omit [TopologicalSpace X] [∀ j, TopologicalSpace (S j)] in
@[simp] theorem cylinder_mem_interiorPiece_iff
    (f : ∀ j, S j → X) (j k : J) (s : S k) (t : I) :
    cylinder f k s t ∈ interiorPiece f j ↔
      k = j ∧ 0 < t ∧ t < 1 := by
  change (Sum.inr ⟨k, Sum.inr (s, t)⟩ : Prequotient X S) ∈
    quotientMk f ⁻¹' interiorPiece f j ↔ _
  rw [quotientMk_preimage_interiorPiece]
  rfl

omit [TopologicalSpace X] [∀ j, TopologicalSpace (S j)] in
theorem iUnion_interiorPiece (f : ∀ j, S j → X) :
    (⋃ j, interiorPiece f j) = lowerCover f ∩ upperCover f := by
  ext y
  induction y using Quotient.inductionOn' with
  | _ z =>
      rcases z with x | ⟨k, z⟩
      · rw [show Quotient.mk'' (Sum.inl x) = base f x from rfl]
        simp
      · rcases z with star | ⟨s, t⟩
        · rcases star with ⟨⟩
          rw [show Quotient.mk'' (Sum.inr ⟨k, Sum.inl ()⟩) = apex f k from rfl]
          simp
        · rw [show Quotient.mk'' (Sum.inr ⟨k, Sum.inr (s, t)⟩) =
            cylinder f k s t from rfl]
          simp

omit [TopologicalSpace X] [∀ j, TopologicalSpace (S j)] in
theorem disjoint_interiorPiece_of_ne (f : ∀ j, S j → X)
    {i j : J} (hij : i ≠ j) : Disjoint (interiorPiece f i) (interiorPiece f j) := by
  rw [Set.disjoint_left]
  intro y hyi hyj
  induction y using Quotient.inductionOn' with
  | _ z =>
      rcases z with x | ⟨k, z⟩
      · exact (base_not_mem_interiorPiece f i x) hyi
      · rcases z with star | ⟨s, t⟩
        · rcases star with ⟨⟩
          rw [show Quotient.mk'' (Sum.inr ⟨k, Sum.inl ()⟩) = apex f k from rfl] at hyi
          exact (apex_not_mem_interiorPiece f i k) hyi
        · rw [show Quotient.mk'' (Sum.inr ⟨k, Sum.inr (s, t)⟩) =
              cylinder f k s t from rfl] at hyi hyj
          have hki : k = i := (cylinder_mem_interiorPiece_iff f i k s t).mp hyi |>.1
          have hkj : k = j := (cylinder_mem_interiorPiece_iff f j k s t).mp hyj |>.1
          exact hij (hki.symm.trans hkj)

omit [TopologicalSpace X] [∀ j, TopologicalSpace (S j)] in
theorem interiorPiece_subset_coverIntersection (f : ∀ j, S j → X) (j : J) :
    interiorPiece f j ⊆ lowerCover f ∩ upperCover f := by
  rw [← iUnion_interiorPiece f]
  exact subset_iUnion (interiorPiece f) j

end Hatcher.VanKampen.IndexedConeAttachment

namespace Hatcher.VanKampen.AuxiliaryCellAttachment

universe u

variable {X J : Type u} {S : J → Type u}
variable [TopologicalSpace X] [∀ j, TopologicalSpace (S j)]
variable (f : ∀ j, S j → X) (s₀ : ∀ j, S j) (x₀ : X)
variable (γ : ∀ j, Path x₀ (f j (s₀ j)))

/-- The saturated raw set for the `j`-th member of the overlap cover.
For a nonselected strip, its right edge must be omitted with the corresponding
cone interior. -/
def intersectionPiecePreimage (j : J) : Set (Prequotient f)
  | Sum.inl y => y ∈ IndexedConeAttachment.interiorPiece f j
  | Sum.inr (Sum.inl t) => 0 < t
  | Sum.inr (Sum.inr ⟨k, (a, t)⟩) => 0 < t ∧ (k = j ∨ a < 1)

theorem isOpen_intersectionPiecePreimage (j : J) :
    IsOpen (intersectionPiecePreimage (f := f) j) := by
  rw [isOpen_sum_iff]
  constructor
  · exact IndexedConeAttachment.isOpen_interiorPiece f j
  · rw [isOpen_sum_iff]
    constructor
    · exact isOpen_Ioi
    · rw [isOpen_sigma_iff]
      intro k
      change IsOpen {p : I × I | 0 < p.2 ∧ (k = j ∨ p.1 < 1)}
      by_cases hkj : k = j
      · subst k
        have hopen : IsOpen {p : I × I | 0 < p.2} :=
          (isOpen_Ioi : IsOpen (Set.Ioi (0 : I))).preimage continuous_snd
        convert hopen using 1
        ext p
        simp
      · have hopen : IsOpen {p : I × I | 0 < p.2 ∧ p.1 < 1} :=
          ((isOpen_Ioi : IsOpen (Set.Ioi (0 : I))).preimage continuous_snd).inter
            ((isOpen_Iio : IsOpen (Set.Iio (1 : I))).preimage continuous_fst)
        convert hopen using 1
        ext p
        simp [hkj]

private theorem truncatedRadialHeight_lt_one_iff' (t : I) :
    truncatedRadialHeight t < 1 ↔ 0 < t := by
  change 1 - (t : ℝ) / 2 < 1 ↔ 0 < (t : ℝ)
  constructor <;> intro h <;> linarith

omit [∀ j, TopologicalSpace (S j)] in
private theorem normalForm_mem_intersectionPiecePreimage_iff
    (j : J) (z : Prequotient f) :
    normalForm f s₀ x₀ γ z ∈ intersectionPiecePreimage (f := f) j ↔
      z ∈ intersectionPiecePreimage (f := f) j := by
  rcases z with y | (t | ⟨k, a, t⟩)
  · rfl
  · by_cases ht : t = 0
    · subst t
      simp only [normalForm, if_pos]
      change IndexedConeAttachment.base f x₀ ∈
        IndexedConeAttachment.interiorPiece f j ↔ (0 : I) < 0
      simp
    · simp only [normalForm, ht, if_false]
  · by_cases ht : t = 0
    · subst t
      simp only [normalForm, if_pos]
      change IndexedConeAttachment.base f (γ k a) ∈
          IndexedConeAttachment.interiorPiece f j ↔
        0 < (0 : I) ∧ (k = j ∨ a < 1)
      simp
    · by_cases ha0 : a = 0
      · subst a
        simp only [normalForm, ht, if_false, if_pos]
        change 0 < t ↔ 0 < t ∧ (k = j ∨ (0 : I) < 1)
        simp
      · by_cases ha1 : a = 1
        · subst a
          simp only [normalForm, ht, one_ne_zero, if_false, if_pos]
          change IndexedConeAttachment.cylinder f k (s₀ k)
              (truncatedRadialHeight t) ∈ IndexedConeAttachment.interiorPiece f j ↔
            0 < t ∧ (k = j ∨ (1 : I) < 1)
          simp [IndexedConeAttachment.cylinder_mem_interiorPiece_iff,
            truncatedRadialHeight_pos, truncatedRadialHeight_lt_one_iff']
          exact and_comm
        · simp [normalForm, ht, ha0, ha1]

/-- The `j`-th open piece in the ambient auxiliary space. -/
def intersectionPieceAmbient (j : J) :
    Set (Hatcher.VanKampen.AuxiliaryCellAttachment f s₀ x₀ γ) := fun z =>
  Quotient.lift
    (fun raw => normalForm f s₀ x₀ γ raw ∈
      intersectionPiecePreimage (f := f) j)
    (fun _ _ h => congrArg
      (fun raw => raw ∈ intersectionPiecePreimage (f := f) j) h) z

omit [∀ j, TopologicalSpace (S j)] in
@[simp] theorem quotientMk_preimage_intersectionPieceAmbient (j : J) :
    quotientMk f s₀ x₀ γ ⁻¹' intersectionPieceAmbient f s₀ x₀ γ j =
      intersectionPiecePreimage (f := f) j := by
  ext z
  exact normalForm_mem_intersectionPiecePreimage_iff f s₀ x₀ γ j z

theorem isOpen_intersectionPieceAmbient (j : J) :
    IsOpen (intersectionPieceAmbient f s₀ x₀ γ j) := by
  apply (isQuotientMap_quotientMk f s₀ x₀ γ).isCoinducing.isOpen_preimage.mp
  rw [quotientMk_preimage_intersectionPieceAmbient]
  exact isOpen_intersectionPiecePreimage f j

/-- Restricting the auxiliary quotient map over an ambient overlap piece is
again a quotient map. -/
theorem isQuotientMap_restrictPreimage_intersectionPieceAmbient (j : J) :
    IsQuotientMap
      ((intersectionPieceAmbient f s₀ x₀ γ j).restrictPreimage
        (quotientMk f s₀ x₀ γ)) :=
  (isQuotientMap_quotientMk f s₀ x₀ γ).restrictPreimage_isOpen
    (isOpen_intersectionPieceAmbient f s₀ x₀ γ j)

omit [TopologicalSpace X] [∀ j, TopologicalSpace (S j)] in
private theorem intersectionPiecePreimage_subset_coverIntersectionPreimage (j : J) :
    intersectionPiecePreimage (f := f) j ⊆
      basePreimage (f := f) ∩ upperPreimage (f := f) := by
  intro z hz
  rcases z with y | (t | ⟨k, a, t⟩)
  · change y ∈ IndexedConeAttachment.interiorPiece f j at hz
    change y ∈ IndexedConeAttachment.lowerCover f ∩
      IndexedConeAttachment.upperCover f
    exact IndexedConeAttachment.interiorPiece_subset_coverIntersection f j hz
  · exact ⟨trivial, hz⟩
  · exact ⟨trivial, hz.1⟩

theorem intersectionPieceAmbient_subset_coverIntersection (j : J) :
    intersectionPieceAmbient f s₀ x₀ γ j ⊆
      baseCover f s₀ x₀ γ ∩ upperCover f s₀ x₀ γ := by
  intro z hz
  obtain ⟨raw, rfl⟩ := (isQuotientMap_quotientMk f s₀ x₀ γ).surjective z
  change raw ∈ quotientMk f s₀ x₀ γ ⁻¹'
      intersectionPieceAmbient f s₀ x₀ γ j at hz
  rw [quotientMk_preimage_intersectionPieceAmbient] at hz
  change raw ∈ quotientMk f s₀ x₀ γ ⁻¹'
      (baseCover f s₀ x₀ γ ∩ upperCover f s₀ x₀ γ)
  rw [preimage_inter, quotientMk_preimage_baseCover,
    quotientMk_preimage_upperCover]
  exact intersectionPiecePreimage_subset_coverIntersectionPreimage f j hz

/-- The overlap, regarded as a topological subtype. -/
abbrev CoverIntersection :=
  ↑(baseCover f s₀ x₀ γ ∩ upperCover f s₀ x₀ γ)

/-- The `j`-th member of Hatcher's indexed cover of the binary overlap. -/
def intersectionPiece (j : J) : Set (CoverIntersection f s₀ x₀ γ) :=
  ((↑) : CoverIntersection f s₀ x₀ γ →
      Hatcher.VanKampen.AuxiliaryCellAttachment f s₀ x₀ γ) ⁻¹'
    intersectionPieceAmbient f s₀ x₀ γ j

theorem isOpen_intersectionPiece (j : J) :
    IsOpen (intersectionPiece f s₀ x₀ γ j) :=
  (isOpen_intersectionPieceAmbient f s₀ x₀ γ j).preimage continuous_subtype_val

/-- Viewing an ambient overlap piece inside the binary-cover intersection only
adds the already-known proof that all of its points lie in that intersection. -/
def intersectionPieceAmbientHomeomorphIntersectionPiece (j : J) :
    ↑(intersectionPieceAmbient f s₀ x₀ γ j) ≃ₜ
      ↑(intersectionPiece f s₀ x₀ γ j) where
  toFun z :=
    ⟨⟨z.1, intersectionPieceAmbient_subset_coverIntersection
        f s₀ x₀ γ j z.2⟩, z.2⟩
  invFun z := ⟨z.1.1, z.2⟩
  left_inv z := by ext; rfl
  right_inv z := by ext; rfl
  continuous_toFun :=
    (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

@[simp] theorem attachment_mem_intersectionPieceAmbient_iff
    (j : J) (y : Hatcher.VanKampen.IndexedConeAttachment f) :
    attachment f s₀ x₀ γ y ∈ intersectionPieceAmbient f s₀ x₀ γ j ↔
      y ∈ IndexedConeAttachment.interiorPiece f j := by
  change (Sum.inl y : Prequotient f) ∈ quotientMk f s₀ x₀ γ ⁻¹'
      intersectionPieceAmbient f s₀ x₀ γ j ↔ _
  rw [quotientMk_preimage_intersectionPieceAmbient]
  rfl

@[simp] theorem spine_mem_intersectionPieceAmbient_iff (j : J) (t : I) :
    spine f s₀ x₀ γ t ∈ intersectionPieceAmbient f s₀ x₀ γ j ↔
      0 < t := by
  change (Sum.inr (Sum.inl t) : Prequotient f) ∈
    quotientMk f s₀ x₀ γ ⁻¹' intersectionPieceAmbient f s₀ x₀ γ j ↔ _
  rw [quotientMk_preimage_intersectionPieceAmbient]
  rfl

@[simp] theorem strip_mem_intersectionPieceAmbient_iff
    (j k : J) (a t : I) :
    strip f s₀ x₀ γ k (a, t) ∈ intersectionPieceAmbient f s₀ x₀ γ j ↔
      0 < t ∧ (k = j ∨ a < 1) := by
  change (Sum.inr (Sum.inr ⟨k, (a, t)⟩) : Prequotient f) ∈
    quotientMk f s₀ x₀ γ ⁻¹' intersectionPieceAmbient f s₀ x₀ γ j ↔ _
  rw [quotientMk_preimage_intersectionPieceAmbient]
  rfl

omit [TopologicalSpace X] [∀ j, TopologicalSpace (S j)] in
private theorem iUnion_intersectionPiecePreimage [Nonempty J] :
    (⋃ j, intersectionPiecePreimage (f := f) j) =
      basePreimage (f := f) ∩ upperPreimage (f := f) := by
  ext z
  rcases z with y | (t | ⟨k, a, t⟩)
  · simp only [Set.mem_iUnion, Set.mem_inter_iff]
    change (∃ j, y ∈ IndexedConeAttachment.interiorPiece f j) ↔
      y ∈ IndexedConeAttachment.lowerCover f ∧
        y ∈ IndexedConeAttachment.upperCover f
    rw [← Set.mem_iUnion]
    exact Set.ext_iff.mp (IndexedConeAttachment.iUnion_interiorPiece f) y
  · simp only [Set.mem_iUnion, Set.mem_inter_iff]
    change (∃ _j : J, 0 < t) ↔ True ∧ 0 < t
    simp
  · simp only [Set.mem_iUnion, Set.mem_inter_iff]
    change (∃ j : J, 0 < t ∧ (k = j ∨ a < 1)) ↔ True ∧ 0 < t
    constructor
    · rintro ⟨j, ht, _⟩
      exact ⟨trivial, ht⟩
    · rintro ⟨_, ht⟩
      exact ⟨k, ht, Or.inl rfl⟩

theorem iUnion_intersectionPieceAmbient [Nonempty J] :
    (⋃ j, intersectionPieceAmbient f s₀ x₀ γ j) =
      baseCover f s₀ x₀ γ ∩ upperCover f s₀ x₀ γ := by
  apply (isQuotientMap_quotientMk f s₀ x₀ γ).surjective.preimage_injective
  rw [preimage_iUnion, preimage_inter, quotientMk_preimage_baseCover,
    quotientMk_preimage_upperCover]
  simp_rw [quotientMk_preimage_intersectionPieceAmbient]
  exact iUnion_intersectionPiecePreimage f

theorem univ_subset_iUnion_intersectionPiece [Nonempty J] :
    univ ⊆ ⋃ j, intersectionPiece f s₀ x₀ γ j := by
  intro z _
  have hz : z.1 ∈ ⋃ j, intersectionPieceAmbient f s₀ x₀ γ j := by
    rw [iUnion_intersectionPieceAmbient]
    exact z.2
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hz
  exact Set.mem_iUnion.mpr ⟨j, hj⟩

/-- Hatcher's common overlap basepoint, now as a point of the overlap subtype. -/
def coverIntersectionBasepoint : CoverIntersection f s₀ x₀ γ :=
  ⟨overlapBasepoint f s₀ x₀ γ,
    overlapBasepoint_mem_inter f s₀ x₀ γ⟩

@[simp] theorem coverIntersectionBasepoint_mem_intersectionPiece (j : J) :
    coverIntersectionBasepoint f s₀ x₀ γ ∈ intersectionPiece f s₀ x₀ γ j := by
  change overlapBasepoint f s₀ x₀ γ ∈
    intersectionPieceAmbient f s₀ x₀ γ j
  simp [overlapBasepoint]

@[simp] theorem attachmentCylinder_mem_intersectionPieceAmbient_iff
    (j k : J) (s : S k) (t : I) :
    attachment f s₀ x₀ γ (IndexedConeAttachment.cylinder f k s t) ∈
        intersectionPieceAmbient f s₀ x₀ γ j ↔
      k = j ∧ 0 < t ∧ t < 1 := by
  rw [attachment_mem_intersectionPieceAmbient_iff,
    IndexedConeAttachment.cylinder_mem_interiorPiece_iff]

private theorem convexComb_pos {a b : I} (ha : 0 < a) (hb : 0 < b)
    (u : I) : 0 < Set.Icc.convexComb a b u := by
  rcases le_total a b with hab | hba
  · exact lt_of_lt_of_le ha (Set.Icc.le_convexComb hab u)
  · have h := Set.Icc.le_convexComb hba (unitInterval.symm u)
    rw [Set.Icc.convexComb_symm] at h
    exact lt_of_lt_of_le hb h

private theorem convexComb_lt_one {a b : I} (ha : a < 1) (hb : b < 1)
    (u : I) : Set.Icc.convexComb a b u < 1 := by
  rcases le_total a b with hab | hba
  · exact lt_of_le_of_lt (Set.Icc.convexComb_le hab u) hb
  · have h := Set.Icc.convexComb_le hba (unitInterval.symm u)
    rw [Set.Icc.convexComb_symm] at h
    exact lt_of_le_of_lt h ha

private def overlapSpinePoint (t : I) (ht : 0 < t) :
    CoverIntersection f s₀ x₀ γ :=
  ⟨spine f s₀ x₀ γ t,
    ⟨spine_mem_baseCover f s₀ x₀ γ t,
      (spine_mem_upperCover_iff f s₀ x₀ γ t).mpr ht⟩⟩

private def overlapStripPoint (k : J) (a t : I) (ht : 0 < t) :
    CoverIntersection f s₀ x₀ γ :=
  ⟨strip f s₀ x₀ γ k (a, t),
    ⟨strip_mem_baseCover f s₀ x₀ γ k (a, t),
      (strip_mem_upperCover_iff f s₀ x₀ γ k (a, t)).mpr ht⟩⟩

private def overlapCylinderPoint (k : J) (s : S k) (t : I)
    (ht0 : 0 < t) (ht1 : t < 1) : CoverIntersection f s₀ x₀ γ :=
  ⟨attachment f s₀ x₀ γ (IndexedConeAttachment.cylinder f k s t),
    ⟨(attachment_mem_baseCover_iff f s₀ x₀ γ _).mpr
        ((IndexedConeAttachment.cylinder_mem_lowerCover_iff f k s t).mpr ht0),
      (attachment_mem_upperCover_iff f s₀ x₀ γ _).mpr
        ((IndexedConeAttachment.cylinder_mem_upperCover_iff f k s t).mpr ht1)⟩⟩

private def overlapSpinePath (t : I) (ht : 0 < t) :
    Path (coverIntersectionBasepoint f s₀ x₀ γ)
      (overlapSpinePoint f s₀ x₀ γ t ht) where
  toFun u := overlapSpinePoint f s₀ x₀ γ
    (Set.Icc.convexComb 1 t u)
    (convexComb_pos zero_lt_one ht u)
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (spine f s₀ x₀ γ).continuous.comp (by fun_prop)
  source' := by
    apply Subtype.ext
    simp [coverIntersectionBasepoint, overlapSpinePoint, overlapBasepoint]
  target' := by
    apply Subtype.ext
    simp [overlapSpinePoint]

private theorem overlapSpinePath_mem_piece (j : J) (t : I) (ht : 0 < t)
    (u : I) : overlapSpinePath f s₀ x₀ γ t ht u ∈
      intersectionPiece f s₀ x₀ γ j := by
  change spine f s₀ x₀ γ (Set.Icc.convexComb 1 t u) ∈
    intersectionPieceAmbient f s₀ x₀ γ j
  rw [spine_mem_intersectionPieceAmbient_iff]
  exact convexComb_pos zero_lt_one ht u

private def overlapStripPath (k : J) (a t : I) (ht : 0 < t) :
    Path (overlapSpinePoint f s₀ x₀ γ t ht)
      (overlapStripPoint f s₀ x₀ γ k a t ht) where
  toFun u := overlapStripPoint f s₀ x₀ γ k
    (Set.Icc.convexComb 0 a u) t ht
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (strip f s₀ x₀ γ k).continuous.comp
      ((by fun_prop : Continuous fun u : I => Set.Icc.convexComb 0 a u).prodMk
        continuous_const)
  source' := by
    apply Subtype.ext
    simp [overlapSpinePoint, overlapStripPoint]
  target' := by
    apply Subtype.ext
    simp [overlapStripPoint]

private theorem overlapStripPath_mem_piece (i k : J) (a t : I) (ht : 0 < t)
    (hpiece : k = i ∨ a < 1) (u : I) :
    overlapStripPath f s₀ x₀ γ k a t ht u ∈
      intersectionPiece f s₀ x₀ γ i := by
  change strip f s₀ x₀ γ k
      (Set.Icc.convexComb 0 a u, t) ∈
    intersectionPieceAmbient f s₀ x₀ γ i
  rw [strip_mem_intersectionPieceAmbient_iff]
  refine ⟨ht, ?_⟩
  rcases hpiece with hki | ha
  · exact Or.inl hki
  · exact Or.inr (lt_of_le_of_lt
      (Set.Icc.convexComb_le a.property.1 u) ha)

private def midpoint : I := ⟨(1 : ℝ) / 2, by norm_num⟩

private theorem midpoint_pos : 0 < midpoint := by
  change (0 : ℝ) < 1 / 2
  norm_num

private theorem midpoint_lt_one : midpoint < 1 := by
  change (1 : ℝ) / 2 < 1
  norm_num

private def overlapTopStripPath (k : J) :
    Path (coverIntersectionBasepoint f s₀ x₀ γ)
      (overlapCylinderPoint f s₀ x₀ γ k (s₀ k) midpoint
        midpoint_pos midpoint_lt_one) :=
  (overlapStripPath f s₀ x₀ γ k 1 1 zero_lt_one).cast
    (by
      apply Subtype.ext
      simp [overlapSpinePoint, coverIntersectionBasepoint, overlapBasepoint])
    (by
      apply Subtype.ext
      simp [overlapStripPoint, overlapCylinderPoint, midpoint])

private theorem overlapTopStripPath_mem_piece (i k : J) (hki : k = i)
    (u : I) : overlapTopStripPath f s₀ x₀ γ k u ∈
      intersectionPiece f s₀ x₀ γ i := by
  exact overlapStripPath_mem_piece f s₀ x₀ γ i k 1 1 zero_lt_one
    (Or.inl hki) u

private def overlapRadialPath (k : J) (t : I) (ht0 : 0 < t) (ht1 : t < 1) :
    Path
      (overlapCylinderPoint f s₀ x₀ γ k (s₀ k) midpoint
        midpoint_pos midpoint_lt_one)
      (overlapCylinderPoint f s₀ x₀ γ k (s₀ k) t ht0 ht1) where
  toFun u := overlapCylinderPoint f s₀ x₀ γ k (s₀ k)
    (Set.Icc.convexComb midpoint t u)
    (convexComb_pos midpoint_pos ht0 u)
    (convexComb_lt_one midpoint_lt_one ht1 u)
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (attachment f s₀ x₀ γ).continuous.comp
      ((IndexedConeAttachment.continuous_cylinder f k).comp
        (continuous_const.prodMk (by fun_prop)))
  source' := by
    apply Subtype.ext
    simp [overlapCylinderPoint]
  target' := by
    apply Subtype.ext
    simp [overlapCylinderPoint]

private theorem overlapRadialPath_mem_piece
    (i k : J) (hki : k = i) (t : I) (ht0 : 0 < t) (ht1 : t < 1)
    (u : I) : overlapRadialPath f s₀ x₀ γ k t ht0 ht1 u ∈
      intersectionPiece f s₀ x₀ γ i := by
  change attachment f s₀ x₀ γ
      (IndexedConeAttachment.cylinder f k (s₀ k)
        (Set.Icc.convexComb midpoint t u)) ∈
    intersectionPieceAmbient f s₀ x₀ γ i
  rw [attachmentCylinder_mem_intersectionPieceAmbient_iff]
  exact ⟨hki, convexComb_pos midpoint_pos ht0 u,
    convexComb_lt_one midpoint_lt_one ht1 u⟩

private def overlapSpherePath [∀ k, PathConnectedSpace (S k)]
    (k : J) (s : S k) (t : I) (ht0 : 0 < t) (ht1 : t < 1) :
    Path
      (overlapCylinderPoint f s₀ x₀ γ k (s₀ k) t ht0 ht1)
      (overlapCylinderPoint f s₀ x₀ γ k s t ht0 ht1) := by
  let p : Path (s₀ k) s := PathConnectedSpace.somePath _ _
  exact
    { toFun := fun u => overlapCylinderPoint f s₀ x₀ γ k (p u) t ht0 ht1
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact (attachment f s₀ x₀ γ).continuous.comp
          ((IndexedConeAttachment.continuous_cylinder f k).comp
            (p.continuous.prodMk continuous_const))
      source' := by
        apply Subtype.ext
        simp [overlapCylinderPoint, p]
      target' := by
        apply Subtype.ext
        simp [overlapCylinderPoint, p] }

private theorem overlapSpherePath_mem_piece [∀ k, PathConnectedSpace (S k)]
    (i k : J) (hki : k = i) (s : S k) (t : I)
    (ht0 : 0 < t) (ht1 : t < 1) (u : I) :
    overlapSpherePath f s₀ x₀ γ k s t ht0 ht1 u ∈
      intersectionPiece f s₀ x₀ γ i := by
  change attachment f s₀ x₀ γ
      (IndexedConeAttachment.cylinder f k
        (PathConnectedSpace.somePath (s₀ k) s u) t) ∈
    intersectionPieceAmbient f s₀ x₀ γ i
  rw [attachmentCylinder_mem_intersectionPieceAmbient_iff]
  exact ⟨hki, ht0, ht1⟩

private theorem joinedIn_spine_piece_intersection (i j : J) (t : I)
    (ht : 0 < t) :
    JoinedIn
      (intersectionPiece f s₀ x₀ γ i ∩ intersectionPiece f s₀ x₀ γ j)
      (coverIntersectionBasepoint f s₀ x₀ γ)
      (overlapSpinePoint f s₀ x₀ γ t ht) :=
  ⟨overlapSpinePath f s₀ x₀ γ t ht, fun u =>
    ⟨overlapSpinePath_mem_piece f s₀ x₀ γ i t ht u,
      overlapSpinePath_mem_piece f s₀ x₀ γ j t ht u⟩⟩

private theorem joinedIn_strip_piece_intersection (i j k : J) (a t : I)
    (ht : 0 < t) (hi : k = i ∨ a < 1) (hj : k = j ∨ a < 1) :
    JoinedIn
      (intersectionPiece f s₀ x₀ γ i ∩ intersectionPiece f s₀ x₀ γ j)
      (coverIntersectionBasepoint f s₀ x₀ γ)
      (overlapStripPoint f s₀ x₀ γ k a t ht) := by
  apply (joinedIn_spine_piece_intersection f s₀ x₀ γ i j t ht).trans
  exact ⟨overlapStripPath f s₀ x₀ γ k a t ht, fun u =>
    ⟨overlapStripPath_mem_piece f s₀ x₀ γ i k a t ht hi u,
      overlapStripPath_mem_piece f s₀ x₀ γ j k a t ht hj u⟩⟩

private theorem joinedIn_cylinder_piece_intersection
    [∀ k, PathConnectedSpace (S k)]
    (i j k : J) (s : S k) (t : I) (hki : k = i) (hkj : k = j)
    (ht0 : 0 < t) (ht1 : t < 1) :
    JoinedIn
      (intersectionPiece f s₀ x₀ γ i ∩ intersectionPiece f s₀ x₀ γ j)
      (coverIntersectionBasepoint f s₀ x₀ γ)
      (overlapCylinderPoint f s₀ x₀ γ k s t ht0 ht1) := by
  have htop : JoinedIn
      (intersectionPiece f s₀ x₀ γ i ∩ intersectionPiece f s₀ x₀ γ j)
      (coverIntersectionBasepoint f s₀ x₀ γ)
      (overlapCylinderPoint f s₀ x₀ γ k (s₀ k) midpoint
        midpoint_pos midpoint_lt_one) :=
    ⟨overlapTopStripPath f s₀ x₀ γ k, fun u =>
      ⟨overlapTopStripPath_mem_piece f s₀ x₀ γ i k hki u,
        overlapTopStripPath_mem_piece f s₀ x₀ γ j k hkj u⟩⟩
  have hradial : JoinedIn
      (intersectionPiece f s₀ x₀ γ i ∩ intersectionPiece f s₀ x₀ γ j)
      (overlapCylinderPoint f s₀ x₀ γ k (s₀ k) midpoint
        midpoint_pos midpoint_lt_one)
      (overlapCylinderPoint f s₀ x₀ γ k (s₀ k) t ht0 ht1) :=
    ⟨overlapRadialPath f s₀ x₀ γ k t ht0 ht1, fun u =>
      ⟨overlapRadialPath_mem_piece f s₀ x₀ γ i k hki t ht0 ht1 u,
        overlapRadialPath_mem_piece f s₀ x₀ γ j k hkj t ht0 ht1 u⟩⟩
  have hsphere : JoinedIn
      (intersectionPiece f s₀ x₀ γ i ∩ intersectionPiece f s₀ x₀ γ j)
      (overlapCylinderPoint f s₀ x₀ γ k (s₀ k) t ht0 ht1)
      (overlapCylinderPoint f s₀ x₀ γ k s t ht0 ht1) :=
    ⟨overlapSpherePath f s₀ x₀ γ k s t ht0 ht1, fun u =>
      ⟨overlapSpherePath_mem_piece f s₀ x₀ γ i k hki s t ht0 ht1 u,
        overlapSpherePath_mem_piece f s₀ x₀ γ j k hkj s t ht0 ht1 u⟩⟩
  exact htop.trans (hradial.trans hsphere)

private theorem joinedIn_attachment_piece_intersection
    [∀ k, PathConnectedSpace (S k)]
    (i j : J) (y : Hatcher.VanKampen.IndexedConeAttachment f)
    (hi : y ∈ IndexedConeAttachment.interiorPiece f i) (hj : y ∈ IndexedConeAttachment.interiorPiece f j)
    (hover : attachment f s₀ x₀ γ y ∈
      baseCover f s₀ x₀ γ ∩ upperCover f s₀ x₀ γ) :
    JoinedIn
      (intersectionPiece f s₀ x₀ γ i ∩ intersectionPiece f s₀ x₀ γ j)
      (coverIntersectionBasepoint f s₀ x₀ γ)
      (⟨attachment f s₀ x₀ γ y, hover⟩ : CoverIntersection f s₀ x₀ γ) := by
  have hq : IsQuotientMap (IndexedConeAttachment.quotientMk f) :=
    isQuotientMap_quot_mk
  obtain ⟨raw, rfl⟩ := hq.surjective y
  rcases raw with x | ⟨k, z⟩
  · exact False.elim (IndexedConeAttachment.base_not_mem_interiorPiece f i x hi)
  · rcases z with star | ⟨s, t⟩
    · exact False.elim (IndexedConeAttachment.apex_not_mem_interiorPiece f i k hi)
    · obtain ⟨hki, ht0, ht1⟩ :=
        (IndexedConeAttachment.cylinder_mem_interiorPiece_iff f i k s t).mp hi
      obtain ⟨hkj, _, _⟩ :=
        (IndexedConeAttachment.cylinder_mem_interiorPiece_iff f j k s t).mp hj
      have h := joinedIn_cylinder_piece_intersection
        f s₀ x₀ γ i j k s t hki hkj ht0 ht1
      have heq : overlapCylinderPoint f s₀ x₀ γ k s t ht0 ht1 =
          (⟨attachment f s₀ x₀ γ
              (IndexedConeAttachment.quotientMk f
                (Sum.inr ⟨k, Sum.inr (s, t)⟩)), hover⟩ :
            CoverIntersection f s₀ x₀ γ) := by
        apply Subtype.ext
        rfl
      rw [← heq]
      exact h

theorem isPathConnected_intersectionPiece_inter
    [∀ k, PathConnectedSpace (S k)] (i j : J) :
    IsPathConnected
      (intersectionPiece f s₀ x₀ γ i ∩ intersectionPiece f s₀ x₀ γ j) := by
  refine ⟨coverIntersectionBasepoint f s₀ x₀ γ,
    ⟨coverIntersectionBasepoint_mem_intersectionPiece f s₀ x₀ γ i,
      coverIntersectionBasepoint_mem_intersectionPiece f s₀ x₀ γ j⟩, ?_⟩
  intro z hz
  rcases hz with ⟨hi, hj⟩
  rcases z with ⟨z, hover⟩
  obtain ⟨raw, rfl⟩ := (isQuotientMap_quotientMk f s₀ x₀ γ).surjective z
  rcases raw with y | (t | ⟨k, a, t⟩)
  · change y ∈ IndexedConeAttachment.interiorPiece f i at hi
    change y ∈ IndexedConeAttachment.interiorPiece f j at hj
    exact joinedIn_attachment_piece_intersection
      f s₀ x₀ γ i j y hi hj hover
  · change spine f s₀ x₀ γ t ∈
      intersectionPieceAmbient f s₀ x₀ γ i at hi
    have ht := (spine_mem_intersectionPieceAmbient_iff
      f s₀ x₀ γ i t).mp hi
    have h := joinedIn_spine_piece_intersection
      f s₀ x₀ γ i j t ht
    have heq : overlapSpinePoint f s₀ x₀ γ t ht =
        (⟨quotientMk f s₀ x₀ γ
            (Sum.inr (Sum.inl t)), hover⟩ :
          CoverIntersection f s₀ x₀ γ) := by
      apply Subtype.ext
      rfl
    rw [← heq]
    exact h
  · change strip f s₀ x₀ γ k (a, t) ∈
      intersectionPieceAmbient f s₀ x₀ γ i at hi
    change strip f s₀ x₀ γ k (a, t) ∈
      intersectionPieceAmbient f s₀ x₀ γ j at hj
    obtain ⟨ht, hki⟩ := (strip_mem_intersectionPieceAmbient_iff
      f s₀ x₀ γ i k a t).mp hi
    have hkj := (strip_mem_intersectionPieceAmbient_iff
      f s₀ x₀ γ j k a t).mp hj |>.2
    have h := joinedIn_strip_piece_intersection
      f s₀ x₀ γ i j k a t ht hki hkj
    have heq : overlapStripPoint f s₀ x₀ γ k a t ht =
        (⟨quotientMk f s₀ x₀ γ
            (Sum.inr (Sum.inr ⟨k, (a, t)⟩)), hover⟩ :
          CoverIntersection f s₀ x₀ γ) := by
      apply Subtype.ext
      rfl
    rw [← heq]
    exact h

/-- The four hypotheses consumed by `coverMap_surjective` for the indexed
cover of the auxiliary overlap. -/
theorem isOpenCover_intersectionPieces [Nonempty J]
    [∀ k, PathConnectedSpace (S k)] :
    (∀ j, IsOpen (intersectionPiece f s₀ x₀ γ j)) ∧
      (Set.univ ⊆ ⋃ j, intersectionPiece f s₀ x₀ γ j) ∧
      (∀ i j, IsPathConnected
        (intersectionPiece f s₀ x₀ γ i ∩ intersectionPiece f s₀ x₀ γ j)) ∧
      (∀ j, coverIntersectionBasepoint f s₀ x₀ γ ∈
        intersectionPiece f s₀ x₀ γ j) :=
  ⟨isOpen_intersectionPiece f s₀ x₀ γ,
    univ_subset_iUnion_intersectionPiece f s₀ x₀ γ,
    isPathConnected_intersectionPiece_inter f s₀ x₀ γ,
    coverIntersectionBasepoint_mem_intersectionPiece f s₀ x₀ γ⟩


end Hatcher.VanKampen.AuxiliaryCellAttachment
