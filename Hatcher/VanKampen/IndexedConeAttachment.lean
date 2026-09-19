import Mathlib.Topology.Constructions
import Mathlib.Topology.UnitInterval
import Hatcher.VanKampen.ConeAttachmentBasicCell
import Mathlib.Topology.Category.TopCat.Limits.Products

/-!
# An indexed family of cone attachments

This module constructs the quotient obtained by attaching one cone on `S j`
to `X` along `f j` for every `j : J`. Each index has its own explicit apex,
so an empty source `S j` still contributes an apex, while an empty index type
contributes nothing and recovers `X`.

The two open sets below are the direct indexed analogue of the bookkeeping
cover for one cone. The upper member is generally disconnected: it retains a
separate truncated cone neighborhood for every index. It is not yet Hatcher's
contractible auxiliary cover for a family of cell attachments.
-/

noncomputable section

open Set Topology
open CategoryTheory CategoryTheory.Limits
open scoped unitInterval

namespace Hatcher.VanKampen

universe u v w

namespace IndexedConeAttachment

/-- The disjoint-union model before quotienting. Each index has its own explicit apex. -/
abbrev Prequotient (X : Type u) {J : Type w} (S : J → Type v) :=
  X ⊕ (Σ j, Unit ⊕ (S j × I))

/-- Canonical representatives for an indexed family of cone attachments. -/
def normalForm {X : Type u} {J : Type w} {S : J → Type v}
    (f : ∀ j, S j → X) : Prequotient X S → Prequotient X S
  | Sum.inl x => Sum.inl x
  | Sum.inr ⟨j, Sum.inl _⟩ => Sum.inr ⟨j, Sum.inl ()⟩
  | Sum.inr ⟨j, Sum.inr (s, t)⟩ =>
      if t = 0 then Sum.inr ⟨j, Sum.inl ()⟩
      else if t = 1 then Sum.inl (f j s)
      else Sum.inr ⟨j, Sum.inr (s, t)⟩

/-- The kernel relation of the indexed normal-form map. -/
private def setoid {X : Type u} {J : Type w} {S : J → Type v}
    (f : ∀ j, S j → X) : Setoid (Prequotient X S) :=
  Setoid.ker (normalForm f)

end IndexedConeAttachment

/-- Attach one cone on `S j` along `f j` for every `j : J`. -/
def IndexedConeAttachment {X : Type u} {J : Type w} {S : J → Type v}
    (f : ∀ j, S j → X) : Type (max u v w) :=
  Quotient (IndexedConeAttachment.setoid f)

namespace IndexedConeAttachment

/-- The quotient topology on the indexed cone attachment. -/
instance instTopologicalSpace {X : Type u} {J : Type w} {S : J → Type v}
    [TopologicalSpace X] [∀ j, TopologicalSpace (S j)] (f : ∀ j, S j → X) :
    TopologicalSpace (Hatcher.VanKampen.IndexedConeAttachment f) :=
  TopologicalSpace.coinduced
    (Quotient.mk (setoid f) :
      Prequotient X S → Hatcher.VanKampen.IndexedConeAttachment f)
    inferInstance

/-- The defining quotient map. -/
def quotientMk {X : Type u} {J : Type w} {S : J → Type v}
    (f : ∀ j, S j → X) :
    Prequotient X S → Hatcher.VanKampen.IndexedConeAttachment f :=
  Quotient.mk (setoid f)

/-- The canonical image of the base. -/
def base {X : Type u} {J : Type w} {S : J → Type v}
    (f : ∀ j, S j → X) (x : X) :
    Hatcher.VanKampen.IndexedConeAttachment f :=
  quotientMk f (Sum.inl x)

/-- The apex belonging to index `j`. -/
def apex {X : Type u} {J : Type w} {S : J → Type v}
    (f : ∀ j, S j → X) (j : J) :
    Hatcher.VanKampen.IndexedConeAttachment f :=
  quotientMk f (Sum.inr ⟨j, Sum.inl ()⟩)

/-- A cylinder point belonging to index `j`. -/
def cylinder {X : Type u} {J : Type w} {S : J → Type v}
    (f : ∀ j, S j → X) (j : J) (s : S j) (t : I) :
    Hatcher.VanKampen.IndexedConeAttachment f :=
  quotientMk f (Sum.inr ⟨j, Sum.inr (s, t)⟩)

@[simp]
theorem cylinder_zero {X : Type u} {J : Type w} {S : J → Type v}
    (f : ∀ j, S j → X) (j : J) (s : S j) :
    cylinder f j s 0 = apex f j := by
  apply Quotient.sound
  change normalForm f (Sum.inr ⟨j, Sum.inr (s, 0)⟩) =
    normalForm f (Sum.inr ⟨j, Sum.inl ()⟩)
  simp [normalForm]

@[simp]
theorem cylinder_one {X : Type u} {J : Type w} {S : J → Type v}
    (f : ∀ j, S j → X) (j : J) (s : S j) :
    cylinder f j s 1 = base f (f j s) := by
  apply Quotient.sound
  change normalForm f (Sum.inr ⟨j, Sum.inr (s, 1)⟩) =
    normalForm f (Sum.inl (f j s))
  simp [normalForm]

/-- The raw lower member contains the base and positive-height cone points. -/
def lowerPreimage {X : Type u} {J : Type w} {S : J → Type v} :
    Set (Prequotient X S) := fun z =>
  match z with
  | Sum.inl _ => True
  | Sum.inr ⟨_, Sum.inl _⟩ => False
  | Sum.inr ⟨_, Sum.inr (_, t)⟩ => 0 < t

/-- The raw upper member contains every apex and every subunit-height cone point. -/
private def upperPreimage {X : Type u} {J : Type w} {S : J → Type v} :
    Set (Prequotient X S) := fun z =>
  match z with
  | Sum.inl _ => False
  | Sum.inr ⟨_, Sum.inl _⟩ => True
  | Sum.inr ⟨_, Sum.inr (_, t)⟩ => t < 1

/-- The raw lower member is open in the indexed coproduct. -/
theorem isOpen_lowerPreimage {X : Type u} {J : Type w} {S : J → Type v}
    [TopologicalSpace X] [∀ j, TopologicalSpace (S j)] :
    IsOpen (lowerPreimage (X := X) (S := S)) := by
  rw [isOpen_sum_iff]
  constructor
  · exact isOpen_univ
  · rw [isOpen_sigma_iff]
    intro j
    rw [isOpen_sum_iff]
    exact ⟨isOpen_empty, isOpen_Ioi.preimage continuous_snd⟩

/-- The raw upper member is open in the indexed coproduct. -/
private theorem isOpen_upperPreimage {X : Type u} {J : Type w} {S : J → Type v}
    [TopologicalSpace X] [∀ j, TopologicalSpace (S j)] :
    IsOpen (upperPreimage (X := X) (S := S)) := by
  rw [isOpen_sum_iff]
  constructor
  · exact isOpen_empty
  · rw [isOpen_sigma_iff]
    intro j
    rw [isOpen_sum_iff]
    exact ⟨isOpen_univ, isOpen_Iio.preimage continuous_snd⟩

/-- The two raw members cover the indexed prequotient. -/
private theorem lowerPreimage_union_upperPreimage
    {X : Type u} {J : Type w} {S : J → Type v} :
    lowerPreimage (X := X) (S := S) ∪ upperPreimage = univ := by
  ext z
  rcases z with x | ⟨j, z⟩
  · simp only [Set.mem_union, Set.mem_univ, iff_true]
    exact Or.inl trivial
  · rcases z with u | ⟨s, t⟩
    · rcases u with ⟨⟩
      simp only [Set.mem_union, Set.mem_univ, iff_true]
      exact Or.inr trivial
    · simp only [Set.mem_union, Set.mem_univ, iff_true]
      change 0 < t ∨ t < 1
      by_cases ht : t < 1
      · exact Or.inr ht
      · have ht' : t = 1 := le_antisymm (unitInterval.le_one t) (not_lt.mp ht)
        rw [ht']
        exact Or.inl zero_lt_one

@[simp]
private theorem mem_lowerPreimage_base
    {X : Type u} {J : Type w} {S : J → Type v} (x : X) :
    (Sum.inl x : Prequotient X S) ∈ lowerPreimage :=
  trivial

@[simp]
private theorem not_mem_lowerPreimage_apex
    {X : Type u} {J : Type w} {S : J → Type v} (j : J) :
    (Sum.inr ⟨j, Sum.inl ()⟩ : Prequotient X S) ∉ lowerPreimage :=
  id

@[simp]
private theorem mem_lowerPreimage_cylinder
    {X : Type u} {J : Type w} {S : J → Type v} (j : J) (p : S j × I) :
    (Sum.inr ⟨j, Sum.inr p⟩ : Prequotient X S) ∈ lowerPreimage ↔ 0 < p.2 :=
  Iff.rfl

private theorem normalForm_mem_lowerPreimage_iff
    {X : Type u} {J : Type w} {S : J → Type v}
    (f : ∀ j, S j → X) (z : Prequotient X S) :
    normalForm f z ∈ lowerPreimage ↔ z ∈ lowerPreimage := by
  rcases z with x | ⟨j, z⟩
  · simp [normalForm]
  · rcases z with u | ⟨s, t⟩
    · rcases u with ⟨⟩
      simp [normalForm]
    · by_cases h0 : t = 0
      · subst t
        simp [normalForm]
      · by_cases h1 : t = 1
        · subst t
          simp [normalForm]
        · simp [normalForm, h0, h1]

@[simp]
private theorem not_mem_upperPreimage_base
    {X : Type u} {J : Type w} {S : J → Type v} (x : X) :
    (Sum.inl x : Prequotient X S) ∉ upperPreimage :=
  id

@[simp]
private theorem mem_upperPreimage_apex
    {X : Type u} {J : Type w} {S : J → Type v} (j : J) :
    (Sum.inr ⟨j, Sum.inl ()⟩ : Prequotient X S) ∈ upperPreimage :=
  trivial

@[simp]
private theorem mem_upperPreimage_cylinder
    {X : Type u} {J : Type w} {S : J → Type v} (j : J) (p : S j × I) :
    (Sum.inr ⟨j, Sum.inr p⟩ : Prequotient X S) ∈ upperPreimage ↔ p.2 < 1 :=
  Iff.rfl

private theorem normalForm_mem_upperPreimage_iff
    {X : Type u} {J : Type w} {S : J → Type v}
    (f : ∀ j, S j → X) (z : Prequotient X S) :
    normalForm f z ∈ upperPreimage ↔ z ∈ upperPreimage := by
  rcases z with x | ⟨j, z⟩
  · simp [normalForm]
  · rcases z with u | ⟨s, t⟩
    · rcases u with ⟨⟩
      simp [normalForm]
    · by_cases h0 : t = 0
      · subst t
        simp [normalForm]
      · by_cases h1 : t = 1
        · subst t
          simp [normalForm]
        · simp [normalForm, h0, h1]

/-- Membership in the raw lower member is invariant under the quotient relation. -/
private theorem lowerPreimage_saturated
    {X : Type u} {J : Type w} {S : J → Type v}
    (f : ∀ j, S j → X) {a b : Prequotient X S}
    (h : setoid f a b) : a ∈ lowerPreimage ↔ b ∈ lowerPreimage := by
  change normalForm f a = normalForm f b at h
  rw [← normalForm_mem_lowerPreimage_iff f a,
    ← normalForm_mem_lowerPreimage_iff f b, h]

/-- Membership in the raw upper member is invariant under the quotient relation. -/
private theorem upperPreimage_saturated
    {X : Type u} {J : Type w} {S : J → Type v}
    (f : ∀ j, S j → X) {a b : Prequotient X S}
    (h : setoid f a b) : a ∈ upperPreimage ↔ b ∈ upperPreimage := by
  change normalForm f a = normalForm f b at h
  rw [← normalForm_mem_upperPreimage_iff f a,
    ← normalForm_mem_upperPreimage_iff f b, h]

/-- The defining map is a quotient map for the indexed coproduct topology. -/
private theorem isQuotientMap_quotientMk
    {X : Type u} {J : Type w} {S : J → Type v}
    [TopologicalSpace X] [∀ j, TopologicalSpace (S j)]
    (f : ∀ j, S j → X) : IsQuotientMap (quotientMk f) := by
  exact isQuotientMap_quot_mk

/-- The saturated lower member descended to the quotient. -/
def lowerCover {X : Type u} {J : Type w} {S : J → Type v}
    (f : ∀ j, S j → X) :
    Set (Hatcher.VanKampen.IndexedConeAttachment f) := fun z =>
  Quotient.lift
    (fun raw => normalForm f raw ∈ lowerPreimage)
    (fun _ _ h => congrArg (fun raw => raw ∈ lowerPreimage) h)
    z

/-- The lower quotient member has exactly the declared raw preimage. -/
theorem quotientMk_preimage_lowerCover
    {X : Type u} {J : Type w} {S : J → Type v}
    (f : ∀ j, S j → X) :
    quotientMk f ⁻¹' lowerCover f = lowerPreimage := by
  ext z
  exact normalForm_mem_lowerPreimage_iff f z

/-- The canonical base lies in the lower member of the indexed cover. -/
@[simp] theorem base_mem_lowerCover
    {X : Type u} {J : Type w} {S : J → Type v}
    (f : ∀ j, S j → X) (x : X) :
    base f x ∈ lowerCover f := by
  change (Sum.inl x : Prequotient X S) ∈ quotientMk f ⁻¹' lowerCover f
  rw [quotientMk_preimage_lowerCover]
  trivial

/-- Every indexed apex is omitted from the lower cover member. -/
@[simp] theorem apex_not_mem_lowerCover
    {X : Type u} {J : Type w} {S : J → Type v}
    (f : ∀ j, S j → X) (j : J) :
    apex f j ∉ lowerCover f := by
  change (Sum.inr ⟨j, Sum.inl ()⟩ : Prequotient X S) ∉
    quotientMk f ⁻¹' lowerCover f
  rw [quotientMk_preimage_lowerCover]
  exact id

/-- A cylinder point belongs to the lower member exactly at positive height. -/
@[simp] theorem cylinder_mem_lowerCover_iff
    {X : Type u} {J : Type w} {S : J → Type v}
    (f : ∀ j, S j → X) (j : J) (s : S j) (t : I) :
    cylinder f j s t ∈ lowerCover f ↔ 0 < t := by
  change (Sum.inr ⟨j, Sum.inr (s, t)⟩ : Prequotient X S) ∈
    quotientMk f ⁻¹' lowerCover f ↔ 0 < t
  rw [quotientMk_preimage_lowerCover]
  rfl

/-- The lower quotient member is open. -/
theorem isOpen_lowerCover
    {X : Type u} {J : Type w} {S : J → Type v}
    [TopologicalSpace X] [∀ j, TopologicalSpace (S j)]
    (f : ∀ j, S j → X) : IsOpen (lowerCover f) := by
  apply (isQuotientMap_quotientMk f).isCoinducing.isOpen_preimage.mp
  rw [quotientMk_preimage_lowerCover]
  exact isOpen_lowerPreimage

/-- Restricting the indexed quotient map over the lower open member remains a
quotient map. -/
theorem isQuotientMap_restrictPreimage_lowerCover
    {X : Type u} {J : Type w} {S : J → Type v}
    [TopologicalSpace X] [∀ j, TopologicalSpace (S j)]
    (f : ∀ j, S j → X) :
    IsQuotientMap ((lowerCover f).restrictPreimage (quotientMk f)) :=
  (isQuotientMap_quotientMk f).restrictPreimage_isOpen
    (isOpen_lowerCover f)

/-- The saturated upper member descended to the quotient. It is generally
disconnected, with one separate truncated cone piece for each index, and is not
Hatcher's contractible auxiliary cover. -/
def upperCover {X : Type u} {J : Type w} {S : J → Type v}
    (f : ∀ j, S j → X) :
    Set (Hatcher.VanKampen.IndexedConeAttachment f) := fun z =>
  Quotient.lift
    (fun raw => normalForm f raw ∈ upperPreimage)
    (fun _ _ h => congrArg (fun raw => raw ∈ upperPreimage) h)
    z

/-- The upper quotient member has exactly the declared raw preimage. -/
private theorem quotientMk_preimage_upperCover
    {X : Type u} {J : Type w} {S : J → Type v}
    (f : ∀ j, S j → X) :
    quotientMk f ⁻¹' upperCover f = upperPreimage := by
  ext z
  exact normalForm_mem_upperPreimage_iff f z

/-- The canonical base is omitted from the upper member of the indexed cover. -/
@[simp] theorem base_not_mem_upperCover
    {X : Type u} {J : Type w} {S : J → Type v}
    (f : ∀ j, S j → X) (x : X) :
    base f x ∉ upperCover f := by
  change (Sum.inl x : Prequotient X S) ∉ quotientMk f ⁻¹' upperCover f
  rw [quotientMk_preimage_upperCover]
  exact id

/-- Every indexed apex belongs to the upper cover member. -/
@[simp] theorem apex_mem_upperCover
    {X : Type u} {J : Type w} {S : J → Type v}
    (f : ∀ j, S j → X) (j : J) :
    apex f j ∈ upperCover f := by
  change (Sum.inr ⟨j, Sum.inl ()⟩ : Prequotient X S) ∈
    quotientMk f ⁻¹' upperCover f
  rw [quotientMk_preimage_upperCover]
  trivial

/-- A cylinder point belongs to the upper member exactly below height one. -/
@[simp] theorem cylinder_mem_upperCover_iff
    {X : Type u} {J : Type w} {S : J → Type v}
    (f : ∀ j, S j → X) (j : J) (s : S j) (t : I) :
    cylinder f j s t ∈ upperCover f ↔ t < 1 := by
  change (Sum.inr ⟨j, Sum.inr (s, t)⟩ : Prequotient X S) ∈
    quotientMk f ⁻¹' upperCover f ↔ t < 1
  rw [quotientMk_preimage_upperCover]
  rfl

/-- The upper quotient member is open. -/
private theorem isOpen_upperCover
    {X : Type u} {J : Type w} {S : J → Type v}
    [TopologicalSpace X] [∀ j, TopologicalSpace (S j)]
    (f : ∀ j, S j → X) : IsOpen (upperCover f) := by
  apply (isQuotientMap_quotientMk f).isCoinducing.isOpen_preimage.mp
  rw [quotientMk_preimage_upperCover]
  exact isOpen_upperPreimage

/-- The two open members cover the indexed cone attachment. -/
private theorem lowerCover_union_upperCover
    {X : Type u} {J : Type w} {S : J → Type v}
    [TopologicalSpace X] [∀ j, TopologicalSpace (S j)]
    (f : ∀ j, S j → X) : lowerCover f ∪ upperCover f = univ := by
  apply (isQuotientMap_quotientMk f).surjective.preimage_injective
  rw [preimage_union, preimage_univ, quotientMk_preimage_lowerCover,
    quotientMk_preimage_upperCover, lowerPreimage_union_upperPreimage]

/-- The standard pair is an open cover of every indexed cone attachment.
The upper member is generally disconnected and is not yet Hatcher's
contractible auxiliary cover. -/
theorem isOpenCover_lower_upper
    {X : Type u} {J : Type w} {S : J → Type v}
    [TopologicalSpace X] [∀ j, TopologicalSpace (S j)]
    (f : ∀ j, S j → X) :
    IsOpen (lowerCover f) ∧ IsOpen (upperCover f) ∧
      lowerCover f ∪ upperCover f = univ :=
  ⟨isOpen_lowerCover f, isOpen_upperCover f, lowerCover_union_upperCover f⟩

/-- With no indices, the construction is exactly the base, with no apex summand left over. -/
private def emptyIndexEquiv {X : Type u} {S : Empty → Type v}
    (f : ∀ j, S j → X) :
    Hatcher.VanKampen.IndexedConeAttachment f ≃ X where
  toFun := Quotient.lift
    (fun z => match z with
      | Sum.inl x => x
      | Sum.inr ⟨j, _⟩ => nomatch j)
    (by
      intro a b h
      change normalForm f a = normalForm f b at h
      rcases a with x | ⟨j, a⟩
      · rcases b with y | ⟨k, b⟩
        · exact Sum.inl.inj h
        · exact Empty.elim k
      · exact Empty.elim j)
  invFun := base f
  left_inv q := Quotient.inductionOn' q fun z => by
    rcases z with x | ⟨j, z⟩
    · rfl
    · exact Empty.elim j
  right_inv _ := rfl

private theorem continuous_emptyIndexEquiv
    {X : Type u} {S : Empty → Type v}
    [TopologicalSpace X] [∀ j, TopologicalSpace (S j)]
    (f : ∀ j, S j → X) : Continuous (emptyIndexEquiv f) := by
  apply Continuous.quotient_lift
  rw [continuous_sum_dom]
  constructor
  · exact continuous_id
  · rw [continuous_sigma_iff]
    exact fun j => Empty.elim j

private theorem continuous_emptyIndexEquiv_symm
    {X : Type u} {S : Empty → Type v}
    [TopologicalSpace X] [∀ j, TopologicalSpace (S j)]
    (f : ∀ j, S j → X) : Continuous (emptyIndexEquiv f).symm := by
  change Continuous (fun x => quotientMk f (Sum.inl x))
  exact (isQuotientMap_quotientMk f).continuous.comp continuous_inl

/-- With no indices, the quotient topology is homeomorphic to the topology on the base. -/
def emptyIndexHomeomorph
    {X : Type u} {S : Empty → Type v}
    [TopologicalSpace X] [∀ j, TopologicalSpace (S j)]
    (f : ∀ j, S j → X) :
    Hatcher.VanKampen.IndexedConeAttachment f ≃ₜ X where
  toEquiv := emptyIndexEquiv f
  continuous_toFun := continuous_emptyIndexEquiv f
  continuous_invFun := continuous_emptyIndexEquiv_symm f

section Pushout

variable {X J : Type u} {S : J → Type u}
variable [TopologicalSpace X] [∀ j, TopologicalSpace (S j)]

/-- The canonical map from the base into an indexed cone attachment is continuous. -/
theorem continuous_base (f : ∀ j, S j → X) : Continuous (base f) := by
  change Continuous (fun x : X ↦ quotientMk f (Sum.inl x))
  exact (isQuotientMap_quotientMk f).continuous.comp continuous_inl

/-- The cylinder map for one member of an indexed cone attachment is continuous. -/
theorem continuous_cylinder (f : ∀ j, S j → X) (j : J) :
    Continuous (fun p : S j × I ↦ cylinder f j p.1 p.2) := by
  change Continuous
    (fun p : S j × I ↦ quotientMk f (Sum.inr ⟨j, Sum.inr p⟩))
  have hinner : Continuous
      (fun p : S j × I ↦ (Sum.inr p : Unit ⊕ (S j × I))) :=
    continuous_inr
  have hsigma : Continuous
      (fun z : Unit ⊕ (S j × I) ↦
        (⟨j, z⟩ : Σ j, Unit ⊕ (S j × I))) :=
    (TopCat.sigmaι
      (fun j ↦ TopCat.of (Unit ⊕ (S j × I))) j).hom.continuous
  have houter : Continuous
      (fun z : Σ j, Unit ⊕ (S j × I) ↦
        (Sum.inr z : Prequotient X S)) :=
    continuous_inr
  exact (isQuotientMap_quotientMk f).continuous.comp
    (houter.comp (hsigma.comp hinner))

private def coneRaw (f : ∀ j, S j → X) (j : J) :
    ConeAttachment.Prequotient (S j) (S j) →
      Hatcher.VanKampen.IndexedConeAttachment f
  | Sum.inl s => base f (f j s)
  | Sum.inr (Sum.inl _) => apex f j
  | Sum.inr (Sum.inr (s, t)) => cylinder f j s t

omit [TopologicalSpace X] [∀ j, TopologicalSpace (S j)] in
private theorem coneRaw_normalForm (f : ∀ j, S j → X) (j : J)
    (z : ConeAttachment.Prequotient (S j) (S j)) :
    coneRaw f j (ConeAttachment.normalForm (id : S j → S j) z) =
      coneRaw f j z := by
  rcases z with s | z
  · rfl
  · rcases z with u₀ | ⟨s, t⟩
    · rcases u₀ with ⟨⟩
      rfl
    · by_cases h0 : t = 0
      · subst t
        simp [ConeAttachment.normalForm, coneRaw]
      · by_cases h1 : t = 1
        · subst t
          simp [ConeAttachment.normalForm, coneRaw]
        · simp [ConeAttachment.normalForm, coneRaw, h0, h1]

/-- The canonical map from the retained cone at index `j` into the indexed
cone attachment. -/
def coneMap (f : ∀ j, S j → X) (j : J) :
    Hatcher.VanKampen.ConeAttachment (id : S j → S j) →
      Hatcher.VanKampen.IndexedConeAttachment f :=
  Quotient.lift (coneRaw f j) (by
    intro a b hab
    change ConeAttachment.normalForm (id : S j → S j) a =
      ConeAttachment.normalForm id b at hab
    rw [← coneRaw_normalForm f j a, ← coneRaw_normalForm f j b, hab])

omit [TopologicalSpace X] [∀ j, TopologicalSpace (S j)] in
@[simp]
theorem coneMap_base (f : ∀ j, S j → X) (j : J) (s : S j) :
    coneMap f j (ConeAttachment.base id s) = base f (f j s) := rfl

omit [TopologicalSpace X] [∀ j, TopologicalSpace (S j)] in
@[simp]
theorem coneMap_apex (f : ∀ j, S j → X) (j : J) :
    coneMap f j (ConeAttachment.apex id) = apex f j := rfl

omit [TopologicalSpace X] [∀ j, TopologicalSpace (S j)] in
@[simp]
theorem coneMap_cylinder (f : ∀ j, S j → X) (j : J) (s : S j) (t : I) :
    coneMap f j (ConeAttachment.cylinder id s t) = cylinder f j s t := rfl

theorem continuous_coneMap (f : ∀ j, S j → X)
    (hf : ∀ j, Continuous (f j)) (j : J) : Continuous (coneMap f j) := by
  apply (ConeAttachment.isQuotientMap_quotientMk
    (id : S j → S j)).continuous_iff.mpr
  rw [continuous_sum_dom]
  constructor
  · simpa [coneMap, coneRaw, ConeAttachment.quotientMk, Function.comp_def] using
      (continuous_base f).comp (hf j)
  · rw [continuous_sum_dom]
    constructor
    · simpa [coneMap, coneRaw, ConeAttachment.quotientMk, Function.comp_def] using
        (continuous_const : Continuous (fun _ : Unit ↦ apex f j))
    · simpa [coneMap, coneRaw, ConeAttachment.quotientMk, Function.comp_def] using
        continuous_cylinder f j

/-- The coproduct of all attaching maps. -/
def sigmaAttachingHom (f : ∀ j, S j → X) (hf : ∀ j, Continuous (f j)) :
    TopCat.of (Σ j, S j) ⟶ TopCat.of X :=
  TopCat.ofHom ⟨fun p ↦ f p.1 p.2, by
    rw [continuous_sigma_iff]
    intro j
    simpa using hf j⟩

/-- The coproduct of the retained-boundary inclusions into the explicit cones. -/
def sigmaConeBoundaryHom (S : J → Type u) [∀ j, TopologicalSpace (S j)] :
    TopCat.of (Σ j, S j) ⟶
      TopCat.of (Σ j, Hatcher.VanKampen.ConeAttachment (id : S j → S j)) :=
  TopCat.ofHom ⟨fun p ↦ ⟨p.1, ConeAttachment.base id p.2⟩, by
    rw [continuous_sigma_iff]
    intro j
    exact (TopCat.sigmaι
      (fun j ↦ TopCat.of
        (Hatcher.VanKampen.ConeAttachment (id : S j → S j))) j).hom.continuous.comp
      (ConeAttachment.continuous_base id)⟩

/-- The canonical base inclusion as a morphism of topological spaces. -/
def baseHom (f : ∀ j, S j → X) :
    TopCat.of X ⟶ TopCat.of (Hatcher.VanKampen.IndexedConeAttachment f) :=
  TopCat.ofHom ⟨base f, continuous_base f⟩

/-- The coproduct of the canonical maps from the retained cones into the
indexed cone attachment. -/
def sigmaConeHom (f : ∀ j, S j → X) (hf : ∀ j, Continuous (f j)) :
    TopCat.of (Σ j, Hatcher.VanKampen.ConeAttachment (id : S j → S j)) ⟶
      TopCat.of (Hatcher.VanKampen.IndexedConeAttachment f) :=
  TopCat.ofHom ⟨fun p ↦ coneMap f p.1 p.2, by
    rw [continuous_sigma_iff]
    intro j
    exact continuous_coneMap f hf j⟩

private def descRaw {Z : Type u} (_f : ∀ j, S j → X) (h : X → Z)
    (k : (Σ j, Hatcher.VanKampen.ConeAttachment (id : S j → S j)) → Z) :
    Prequotient X S → Z
  | Sum.inl x => h x
  | Sum.inr ⟨j, Sum.inl _⟩ => k ⟨j, ConeAttachment.apex id⟩
  | Sum.inr ⟨j, Sum.inr (s, t)⟩ => k ⟨j, ConeAttachment.cylinder id s t⟩

omit [TopologicalSpace X] [∀ j, TopologicalSpace (S j)] in
private theorem descRaw_normalForm {Z : Type u} (f : ∀ j, S j → X)
    (h : X → Z)
    (k : (Σ j, Hatcher.VanKampen.ConeAttachment (id : S j → S j)) → Z)
    (w : ∀ j s, h (f j s) = k ⟨j, ConeAttachment.base id s⟩)
    (z : Prequotient X S) :
    descRaw f h k (normalForm f z) = descRaw f h k z := by
  rcases z with x | ⟨j, z⟩
  · rfl
  · rcases z with u₀ | ⟨s, t⟩
    · rcases u₀ with ⟨⟩
      rfl
    · by_cases h0 : t = 0
      · subst t
        simp [normalForm, descRaw]
      · by_cases h1 : t = 1
        · subst t
          simpa [normalForm, descRaw] using w j s
        · simp [normalForm, descRaw, h0, h1]

private def desc {Z : Type u} (f : ∀ j, S j → X) (h : X → Z)
    (k : (Σ j, Hatcher.VanKampen.ConeAttachment (id : S j → S j)) → Z)
    (w : ∀ j s, h (f j s) = k ⟨j, ConeAttachment.base id s⟩) :
    Hatcher.VanKampen.IndexedConeAttachment f → Z :=
  Quotient.lift (descRaw f h k) (by
    intro a b hab
    change normalForm f a = normalForm f b at hab
    rw [← descRaw_normalForm f h k w a, ← descRaw_normalForm f h k w b, hab])

private theorem continuous_desc {Z : Type u} [TopologicalSpace Z]
    (f : ∀ j, S j → X) (h : X → Z)
    (k : (Σ j, Hatcher.VanKampen.ConeAttachment (id : S j → S j)) → Z)
    (w : ∀ j s, h (f j s) = k ⟨j, ConeAttachment.base id s⟩)
    (hh : Continuous h) (hk : Continuous k) : Continuous (desc f h k w) := by
  apply (isQuotientMap_quotientMk f).continuous_iff.mpr
  rw [continuous_sum_dom]
  constructor
  · simpa [desc, descRaw, quotientMk, Function.comp_def] using hh
  · rw [continuous_sigma_iff]
    intro j
    rw [continuous_sum_dom]
    constructor
    · simpa [desc, descRaw, quotientMk, Function.comp_def] using
        (continuous_const : Continuous
          (fun _ : Unit ↦ k ⟨j, ConeAttachment.apex id⟩))
    · have hj : Continuous
          (fun p : S j × I ↦
            (⟨j, ConeAttachment.cylinder id p.1 p.2⟩ :
              Σ j, Hatcher.VanKampen.ConeAttachment (id : S j → S j))) :=
        (TopCat.sigmaι
          (fun j ↦ TopCat.of
            (Hatcher.VanKampen.ConeAttachment (id : S j → S j))) j).hom.continuous.comp
          (ConeAttachment.continuous_cylinder id)
      simpa [desc, descRaw, quotientMk, Function.comp_def] using hk.comp hj

/-- The explicit indexed cone attachment is the pushout of the coproduct of
its attaching maps and the coproduct of its retained-boundary inclusions. -/
theorem isPushout_indexedConeAttachment (f : ∀ j, S j → X)
    (hf : ∀ j, Continuous (f j)) :
    IsPushout (sigmaAttachingHom f hf) (sigmaConeBoundaryHom S)
      (baseHom f) (sigmaConeHom f hf) := by
  have comm : sigmaAttachingHom f hf ≫ baseHom f =
      sigmaConeBoundaryHom S ≫ sigmaConeHom f hf := by
    ext p
    rcases p with ⟨j, s⟩
    rfl
  let d (c : PushoutCocone (sigmaAttachingHom f hf) (sigmaConeBoundaryHom S)) :
      TopCat.of (Hatcher.VanKampen.IndexedConeAttachment f) ⟶ c.pt :=
    let w : ∀ j s, c.inl (f j s) =
        c.inr ⟨j, ConeAttachment.base id s⟩ := fun j s ↦
      ConcreteCategory.congr_hom c.condition ⟨j, s⟩
    TopCat.ofHom ⟨desc f c.inl c.inr w,
      continuous_desc f c.inl c.inr w
        c.inl.hom.continuous c.inr.hom.continuous⟩
  refine { w := comm, isColimit' := ⟨?_⟩ }
  refine PushoutCocone.IsColimit.mk comm d ?_ ?_ ?_
  · intro c
    ext x
    rfl
  · intro c
    let w : ∀ j s, c.inl (f j s) =
        c.inr ⟨j, ConeAttachment.base id s⟩ := fun j s ↦
      ConcreteCategory.congr_hom c.condition ⟨j, s⟩
    ext q
    rcases q with ⟨j, q⟩
    refine Quotient.inductionOn q ?_
    intro z
    rcases z with s | z
    · exact w j s
    · rcases z with u₀ | ⟨s, t⟩
      · rfl
      · rfl
  · intro c m hmBase hmCone
    ext q
    refine Quotient.inductionOn q ?_
    intro z
    rcases z with x | ⟨j, z⟩
    · exact ConcreteCategory.congr_hom hmBase x
    · rcases z with u₀ | ⟨s, t⟩
      · exact ConcreteCategory.congr_hom hmCone
          ⟨j, ConeAttachment.apex id⟩
      · exact ConcreteCategory.congr_hom hmCone
          ⟨j, ConeAttachment.cylinder id s t⟩

/-- The indexed cone pushout as an `AttachCells` structure for the retained
cone boundary maps. -/
def attachCells_indexedConeAttachment (f : ∀ j, S j → X)
    (hf : ∀ j, Continuous (f j)) :
    HomotopicalAlgebra.AttachCells.{u}
      (fun j : J ↦ ConeAttachment.coneBoundaryHom (S j)) (baseHom f) where
  ι := J
  π := id
  cofan₁ := TopCat.sigmaCofan (fun j ↦ TopCat.of (S j))
  cofan₂ := TopCat.sigmaCofan (fun j ↦ TopCat.of
    (Hatcher.VanKampen.ConeAttachment (id : S j → S j)))
  isColimit₁ := TopCat.sigmaCofanIsColimit _
  isColimit₂ := TopCat.sigmaCofanIsColimit _
  m := sigmaConeBoundaryHom S
  hm j := by
    ext s
    rfl
  g₁ := sigmaAttachingHom f hf
  g₂ := sigmaConeHom f hf
  isPushout := isPushout_indexedConeAttachment f hf

/-- An indexed family of cones on standard disk boundaries gives an
`AttachCells` structure for Mathlib's standard `n`-cell family. -/
def attachCells_basicCell (n : ℕ) {X J : Type u} [TopologicalSpace X]
    (f : ∀ _j : J,
      ((TopCat.diskBoundary.{u} n : TopCat.{u}) : Type u) → X)
    (hf : ∀ j, Continuous (f j)) :
    HomotopicalAlgebra.AttachCells.{u}
      (TopCat.RelativeCWComplex.basicCell.{u} n) (baseHom f) :=
  (attachCells_indexedConeAttachment f hf).reindexCellTypes
    (TopCat.RelativeCWComplex.basicCell.{u} n) (fun _ ↦ ())
    (fun _ ↦ ConeAttachment.coneBoundaryIsoBasicCell n)

end Pushout

end IndexedConeAttachment

end Hatcher.VanKampen
