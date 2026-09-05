import Mathlib.Topology.Constructions
import Mathlib.Topology.UnitInterval

/-!
# A single cone attachment

This module constructs the point-set quotient obtained by attaching one
augmented cone on `S` to `X`. It supplies one explicit apex even when `S` is
empty, so the empty case is `X ⊔ point`. This is a building block for Hatcher's
cell-attachment argument, not the arbitrary-family `AttachCells` model: a
family requires one apex per attached cell and additional deformation data.
-/

noncomputable section

open Set Topology
open scoped unitInterval

namespace Hatcher.VanKampen

universe u v

namespace ConeAttachment

/-- The disjoint-union model before the cone apex and attaching boundary are
identified. The middle summand supplies an explicit apex even when `S` is
empty. -/
abbrev Prequotient (X : Type u) (S : Type v) :=
  X ⊕ (Unit ⊕ (S × I))

/-- Canonical representatives for the cone attachment: height zero is sent to
the apex, height one is sent through the attaching map, and interior cylinder
points remain unchanged. -/
def normalForm {X : Type u} {S : Type v} (f : S → X) :
    Prequotient X S → Prequotient X S
  | Sum.inl x => Sum.inl x
  | Sum.inr (Sum.inl _) => Sum.inr (Sum.inl ())
  | Sum.inr (Sum.inr (s, t)) =>
      if t = 0 then Sum.inr (Sum.inl ())
      else if t = 1 then Sum.inl (f s)
      else Sum.inr (Sum.inr (s, t))

/-- The equivalence relation that collapses `S × {0}` to the cone apex and
glues `S × {1}` to `X` through `f`. -/
def setoid {X : Type u} {S : Type v} (f : S → X) :
    Setoid (Prequotient X S) :=
  Setoid.ker (normalForm f)

end ConeAttachment

/-- The point-set adjunction obtained by attaching one cone on `S` to `X`
along `f`. This is the single-cell building block, not an indexed family of
attachments. -/
def ConeAttachment {X : Type u} {S : Type v} (f : S → X) :
    Type (max u v) :=
  Quotient (ConeAttachment.setoid f)

namespace ConeAttachment

/-- The quotient topology on a cone attachment. -/
instance instTopologicalSpace {X : Type u} {S : Type v}
    [TopologicalSpace X] [TopologicalSpace S] (f : S → X) :
    TopologicalSpace (Hatcher.VanKampen.ConeAttachment f) :=
  TopologicalSpace.coinduced
    (Quotient.mk (setoid f) :
      Prequotient X S → Hatcher.VanKampen.ConeAttachment f)
    inferInstance

/-- The defining quotient map for a cone attachment. -/
def quotientMk {X : Type u} {S : Type v} (f : S → X) :
    Prequotient X S → Hatcher.VanKampen.ConeAttachment f :=
  Quotient.mk (setoid f)

/-- The canonical image of the original space in a cone attachment. Without
continuity of `f`, no embedding claim is made. -/
def base {X : Type u} {S : Type v} (f : S → X) (x : X) :
    Hatcher.VanKampen.ConeAttachment f :=
  quotientMk f (Sum.inl x)

/-- The apex of the attached cone. -/
def apex {X : Type u} {S : Type v} (f : S → X) :
    Hatcher.VanKampen.ConeAttachment f :=
  quotientMk f (Sum.inr (Sum.inl ()))

/-- A point of the cone cylinder before its endpoints are identified. -/
def cylinder {X : Type u} {S : Type v} (f : S → X) (s : S) (t : I) :
    Hatcher.VanKampen.ConeAttachment f :=
  quotientMk f (Sum.inr (Sum.inr (s, t)))

/-- Every height-zero cylinder point is the cone apex. -/
@[simp]
theorem cylinder_zero {X : Type u} {S : Type v} (f : S → X) (s : S) :
    cylinder f s 0 = apex f := by
  apply Quotient.sound
  change normalForm f (Sum.inr (Sum.inr (s, 0))) =
    normalForm f (Sum.inr (Sum.inl ()))
  simp [normalForm]

/-- Every height-one cylinder point is glued to its image under the attaching
map. -/
@[simp]
theorem cylinder_one {X : Type u} {S : Type v} (f : S → X) (s : S) :
    cylinder f s 1 = base f (f s) := by
  apply Quotient.sound
  change normalForm f (Sum.inr (Sum.inr (s, 1))) =
    normalForm f (Sum.inl (f s))
  simp [normalForm]

/-- The defining map of a cone attachment is a quotient map for the coproduct
topology on its prequotient. -/
theorem isQuotientMap_quotientMk {X : Type u} {S : Type v}
    [TopologicalSpace X] [TopologicalSpace S] (f : S → X) :
    IsQuotientMap (quotientMk f) := by
  exact isQuotientMap_quot_mk

/-- The preimage of the cover member obtained by deleting the cone apex. -/
def lowerPreimage {X : Type u} {S : Type v} :
    Set (Prequotient X S) := fun z =>
  match z with
  | Sum.inl _ => True
  | Sum.inr (Sum.inl _) => False
  | Sum.inr (Sum.inr (_, t)) => 0 < t

/-- The preimage of the cover member obtained by deleting the canonical image
of `X`. -/
def upperPreimage {X : Type u} {S : Type v} :
    Set (Prequotient X S) := fun z =>
  match z with
  | Sum.inl _ => False
  | Sum.inr (Sum.inl _) => True
  | Sum.inr (Sum.inr (_, t)) => t < 1

/-- The complement of the apex is open in the prequotient. -/
theorem isOpen_lowerPreimage {X : Type u} {S : Type v}
    [TopologicalSpace X] [TopologicalSpace S] :
    IsOpen (lowerPreimage (X := X) (S := S)) := by
  rw [isOpen_sum_iff]
  constructor
  · exact isOpen_univ
  · rw [isOpen_sum_iff]
    exact ⟨isOpen_empty, isOpen_Ioi.preimage continuous_snd⟩

/-- The complement of the base space is open in the prequotient. -/
theorem isOpen_upperPreimage {X : Type u} {S : Type v}
    [TopologicalSpace X] [TopologicalSpace S] :
    IsOpen (upperPreimage (X := X) (S := S)) := by
  rw [isOpen_sum_iff]
  constructor
  · exact isOpen_empty
  · rw [isOpen_sum_iff]
    exact ⟨isOpen_univ, isOpen_Iio.preimage continuous_snd⟩

/-- The two named preimages cover the cone-attachment prequotient. -/
theorem lowerPreimage_union_upperPreimage {X : Type u} {S : Type v} :
    lowerPreimage (X := X) (S := S) ∪ upperPreimage = univ := by
  ext z
  rcases z with x | z
  · simp only [Set.mem_union, Set.mem_univ, iff_true]
    left
    change True
    trivial
  · rcases z with u | ⟨s, t⟩
    · rcases u with ⟨⟩
      simp only [Set.mem_union, Set.mem_univ, iff_true]
      right
      change True
      trivial
    · simp only [Set.mem_union, Set.mem_univ, iff_true]
      change 0 < t ∨ t < 1
      by_cases ht : t < 1
      · exact Or.inr ht
      · have ht' : t = 1 := le_antisymm (unitInterval.le_one t) (not_lt.mp ht)
        rw [ht']
        exact Or.inl zero_lt_one

@[simp]
private theorem mem_lowerPreimage_base {X : Type u} {S : Type v} (x : X) :
    (Sum.inl x : Prequotient X S) ∈ lowerPreimage :=
  trivial

@[simp]
private theorem not_mem_lowerPreimage_apex {X : Type u} {S : Type v} :
    (Sum.inr (Sum.inl ()) : Prequotient X S) ∉ lowerPreimage :=
  id

@[simp]
private theorem mem_lowerPreimage_cylinder {X : Type u} {S : Type v}
    (p : S × I) :
    (Sum.inr (Sum.inr p) : Prequotient X S) ∈ lowerPreimage ↔ 0 < p.2 :=
  Iff.rfl

@[simp]
private theorem not_mem_upperPreimage_base {X : Type u} {S : Type v} (x : X) :
    (Sum.inl x : Prequotient X S) ∉ upperPreimage :=
  id

@[simp]
private theorem mem_upperPreimage_apex {X : Type u} {S : Type v} :
    (Sum.inr (Sum.inl ()) : Prequotient X S) ∈ upperPreimage :=
  trivial

@[simp]
private theorem mem_upperPreimage_cylinder {X : Type u} {S : Type v}
    (p : S × I) :
    (Sum.inr (Sum.inr p) : Prequotient X S) ∈ upperPreimage ↔ p.2 < 1 :=
  Iff.rfl

private theorem normalForm_mem_lowerPreimage_iff
    {X : Type u} {S : Type v} (f : S → X) (z : Prequotient X S) :
    normalForm f z ∈ lowerPreimage ↔ z ∈ lowerPreimage := by
  rcases z with x | z
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

private theorem normalForm_mem_upperPreimage_iff
    {X : Type u} {S : Type v} (f : S → X) (z : Prequotient X S) :
    normalForm f z ∈ upperPreimage ↔ z ∈ upperPreimage := by
  rcases z with x | z
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

/-- The open cover member containing the canonical image of `X` and all
positive-height cone points. -/
def lowerCover {X : Type u} {S : Type v} (f : S → X) :
    Set (Hatcher.VanKampen.ConeAttachment f) := fun z =>
  Quotient.lift
    (fun raw => normalForm f raw ∈ lowerPreimage)
    (fun _ _ h => congrArg (fun raw => raw ∈ lowerPreimage) h)
    z

/-- The defining quotient map pulls the lower cover member back to its named
preimage. -/
theorem quotientMk_preimage_lowerCover {X : Type u} {S : Type v}
    (f : S → X) :
    quotientMk f ⁻¹' lowerCover f = lowerPreimage := by
  ext z
  exact normalForm_mem_lowerPreimage_iff f z

/-- The lower member of the standard two-set cone-attachment cover is open. -/
theorem isOpen_lowerCover {X : Type u} {S : Type v}
    [TopologicalSpace X] [TopologicalSpace S] (f : S → X) :
    IsOpen (lowerCover f) := by
  apply (isQuotientMap_quotientMk f).isCoinducing.isOpen_preimage.mp
  rw [quotientMk_preimage_lowerCover]
  exact isOpen_lowerPreimage

/-- The open cover member containing the cone apex and all subunit-height
cone points. -/
def upperCover {X : Type u} {S : Type v} (f : S → X) :
    Set (Hatcher.VanKampen.ConeAttachment f) := fun z =>
  Quotient.lift
    (fun raw => normalForm f raw ∈ upperPreimage)
    (fun _ _ h => congrArg (fun raw => raw ∈ upperPreimage) h)
    z

/-- The defining quotient map pulls the upper cover member back to its named
preimage. -/
theorem quotientMk_preimage_upperCover {X : Type u} {S : Type v}
    (f : S → X) :
    quotientMk f ⁻¹' upperCover f = upperPreimage := by
  ext z
  exact normalForm_mem_upperPreimage_iff f z

/-- The upper member of the standard two-set cone-attachment cover is open. -/
theorem isOpen_upperCover {X : Type u} {S : Type v}
    [TopologicalSpace X] [TopologicalSpace S] (f : S → X) :
    IsOpen (upperCover f) := by
  apply (isQuotientMap_quotientMk f).isCoinducing.isOpen_preimage.mp
  rw [quotientMk_preimage_upperCover]
  exact isOpen_upperPreimage

/-- The lower and upper members cover the cone attachment. -/
theorem lowerCover_union_upperCover {X : Type u} {S : Type v}
    [TopologicalSpace X] [TopologicalSpace S] (f : S → X) :
    lowerCover f ∪ upperCover f = univ := by
  apply (isQuotientMap_quotientMk f).surjective.preimage_injective
  rw [preimage_union, preimage_univ, quotientMk_preimage_lowerCover,
    quotientMk_preimage_upperCover, lowerPreimage_union_upperPreimage]

/-- The two standard subsets form an open cover of a single cone attachment. -/
theorem isOpenCover_lower_upper {X : Type u} {S : Type v}
    [TopologicalSpace X] [TopologicalSpace S] (f : S → X) :
    IsOpen (lowerCover f) ∧ IsOpen (upperCover f) ∧
      lowerCover f ∪ upperCover f = univ :=
  ⟨isOpen_lowerCover f, isOpen_upperCover f,
    lowerCover_union_upperCover f⟩

/-- Restricting the quotient map over the lower open member remains a quotient
map. This is the input needed to descend its deformation toward the base. -/
theorem isQuotientMap_restrictPreimage_lowerCover
    {X : Type u} {S : Type v} [TopologicalSpace X] [TopologicalSpace S]
    (f : S → X) :
    IsQuotientMap ((lowerCover f).restrictPreimage (quotientMk f)) :=
  (isQuotientMap_quotientMk f).restrictPreimage_isOpen
    (isOpen_lowerCover f)

/-- Restricting the quotient map over the upper open member remains a quotient
map. This is the input needed to descend its contraction toward the apex. -/
theorem isQuotientMap_restrictPreimage_upperCover
    {X : Type u} {S : Type v} [TopologicalSpace X] [TopologicalSpace S]
    (f : S → X) :
    IsQuotientMap ((upperCover f).restrictPreimage (quotientMk f)) :=
  (isQuotientMap_quotientMk f).restrictPreimage_isOpen
    (isOpen_upperCover f)

end ConeAttachment

end Hatcher.VanKampen
