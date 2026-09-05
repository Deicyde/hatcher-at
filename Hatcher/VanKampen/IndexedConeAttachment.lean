import Mathlib.Topology.Constructions
import Mathlib.Topology.UnitInterval

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
open scoped unitInterval

namespace Hatcher.VanKampen

universe u v w

namespace IndexedConeAttachment

/-- The disjoint-union model before quotienting. Each index has its own explicit apex. -/
abbrev Prequotient (X : Type u) {J : Type w} (S : J → Type v) :=
  X ⊕ (Σ j, Unit ⊕ (S j × I))

/-- Canonical representatives for an indexed family of cone attachments. -/
private def normalForm {X : Type u} {J : Type w} {S : J → Type v}
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
private def lowerPreimage {X : Type u} {J : Type w} {S : J → Type v} :
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
private theorem isOpen_lowerPreimage {X : Type u} {J : Type w} {S : J → Type v}
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
private theorem quotientMk_preimage_lowerCover
    {X : Type u} {J : Type w} {S : J → Type v}
    (f : ∀ j, S j → X) :
    quotientMk f ⁻¹' lowerCover f = lowerPreimage := by
  ext z
  exact normalForm_mem_lowerPreimage_iff f z

/-- The lower quotient member is open. -/
private theorem isOpen_lowerCover
    {X : Type u} {J : Type w} {S : J → Type v}
    [TopologicalSpace X] [∀ j, TopologicalSpace (S j)]
    (f : ∀ j, S j → X) : IsOpen (lowerCover f) := by
  apply (isQuotientMap_quotientMk f).isCoinducing.isOpen_preimage.mp
  rw [quotientMk_preimage_lowerCover]
  exact isOpen_lowerPreimage

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

end IndexedConeAttachment

end Hatcher.VanKampen
