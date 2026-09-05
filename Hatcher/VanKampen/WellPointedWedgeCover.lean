import Hatcher.VanKampen.PointedWedge
import Mathlib.Topology.Homotopy.Basic

noncomputable section

open Set
open scoped unitInterval

namespace Hatcher

universe u v

/-- A point is well-pointed if it has an open neighborhood that strongly
contracts to it. -/
def WellPointedAt {X : Type u} [TopologicalSpace X] (x₀ : X) : Prop :=
  ∃ (N : Set X) (hx₀ : x₀ ∈ N), IsOpen N ∧
    Nonempty ((ContinuousMap.id N).HomotopyRel
      (ContinuousMap.const N ⟨x₀, hx₀⟩) {⟨x₀, hx₀⟩})

namespace WellPointedAt

variable {X : Type u} [TopologicalSpace X] {x₀ : X}

/-- A chosen open neighborhood witnessing that `x₀` is well-pointed. -/
noncomputable def neighborhood (h : WellPointedAt x₀) : Set X :=
  h.choose

/-- The basepoint belongs to its chosen well-pointed neighborhood. -/
theorem mem_neighborhood (h : WellPointedAt x₀) :
    x₀ ∈ h.neighborhood :=
  h.choose_spec.choose

/-- The chosen well-pointed neighborhood is open. -/
theorem isOpen_neighborhood (h : WellPointedAt x₀) :
    IsOpen h.neighborhood :=
  h.choose_spec.choose_spec.1

/-- The basepoint as a point of its chosen neighborhood. -/
noncomputable def neighborhoodBasepoint (h : WellPointedAt x₀) :
    h.neighborhood :=
  ⟨x₀, h.mem_neighborhood⟩

/-- A chosen contraction of the neighborhood to its basepoint, fixed at that
basepoint throughout. -/
noncomputable def contraction (h : WellPointedAt x₀) :
    (ContinuousMap.id h.neighborhood).HomotopyRel
      (ContinuousMap.const h.neighborhood h.neighborhoodBasepoint)
      {h.neighborhoodBasepoint} := by
  exact h.choose_spec.choose_spec.2.some

@[simp]
theorem neighborhoodBasepoint_val (h : WellPointedAt x₀) :
    (h.neighborhoodBasepoint : X) = x₀ :=
  rfl

@[simp]
theorem contraction_zero (h : WellPointedAt x₀) (x : h.neighborhood) :
    h.contraction (0, x) = x := by
  exact h.contraction.apply_zero x

@[simp]
theorem contraction_one (h : WellPointedAt x₀) (x : h.neighborhood) :
    h.contraction (1, x) = h.neighborhoodBasepoint := by
  exact h.contraction.apply_one x

@[simp]
theorem contraction_basepoint (h : WellPointedAt x₀) (t : I) :
    h.contraction (t, h.neighborhoodBasepoint) =
      h.neighborhoodBasepoint := by
  apply h.contraction.eq_fst
  simp

end WellPointedAt

namespace PointedWedge

variable {ι : Type u} {X : ι → Type v} [∀ i, TopologicalSpace (X i)]
  (x₀ : ∀ i, X i)

/-- The saturated prequotient set underlying the standard wedge cover member. -/
def coverPreimage (N : ∀ i, Set (X i)) (i : ι) :
    Set (Option (Σ j, X j)) :=
  fun z => match z with
    | none => True
    | some p => p.1 = i ∨ p.2 ∈ N p.1

omit [∀ i, TopologicalSpace (X i)] in
private theorem coverPreimage_eq_of_eqvGen
    (N : ∀ i, Set (X i)) (hN : ∀ i, x₀ i ∈ N i) (i : ι)
    {a b : Option (Σ j, X j)}
    (h : Relation.EqvGen (Rel X x₀) a b) :
    coverPreimage N i a = coverPreimage N i b := by
  induction h with
  | rel a b h =>
      cases h with
      | base j => simp [coverPreimage, hN j]
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- One member of the standard open cover of a well-pointed wedge. -/
def coverSet (N : ∀ i, Set (X i)) (hN : ∀ i, x₀ i ∈ N i) (i : ι) :
    Set (Hatcher.PointedWedge X x₀) :=
  fun z => Quotient.liftOn z (fun a => a ∈ coverPreimage N i)
    (fun _ _ h => coverPreimage_eq_of_eqvGen x₀ N hN i h)

omit [∀ i, TopologicalSpace (X i)] in
@[simp]
theorem quotientMk_preimage_coverSet
    (N : ∀ i, Set (X i)) (hN : ∀ i, x₀ i ∈ N i) (i : ι) :
    (Quotient.mk (setoid X x₀)) ⁻¹' coverSet x₀ N hN i =
      coverPreimage N i := by
  ext z
  rfl

omit [∀ i, TopologicalSpace (X i)] in
/-- A summand maps into its corresponding member of the wedge cover. -/
@[simp]
theorem inclusion_mem_coverSet
    (N : ∀ i, Set (X i)) (hN : ∀ i, x₀ i ∈ N i)
    (i : ι) (x : X i) :
    inclusion x₀ i x ∈ coverSet x₀ N hN i := by
  change some ⟨i, x⟩ ∈
    (Quotient.mk (setoid X x₀)) ⁻¹' coverSet x₀ N hN i
  rw [quotientMk_preimage_coverSet]
  exact Or.inl rfl

omit [∀ i, TopologicalSpace (X i)] in
/-- The wedge point belongs to every member of the wedge cover. -/
@[simp]
theorem basepoint_mem_coverSet
    (N : ∀ i, Set (X i)) (hN : ∀ i, x₀ i ∈ N i) (i : ι) :
    basepoint x₀ ∈ coverSet x₀ N hN i := by
  change none ∈
    (Quotient.mk (setoid X x₀)) ⁻¹' coverSet x₀ N hN i
  rw [quotientMk_preimage_coverSet]
  trivial

theorem isOpen_coverSet
    (N : ∀ i, Set (X i)) (hN : ∀ i, x₀ i ∈ N i)
    (hNopen : ∀ i, IsOpen (N i)) (i : ι) :
    IsOpen (coverSet x₀ N hN i) := by
  rw [isOpen_coinduced]
  change @IsOpen (Option (Σ j, X j))
    (TopologicalSpace.coinduced (fun z : Σ j, X j => some z) inferInstance ⊔
      TopologicalSpace.coinduced
        (fun _ : Unit => (none : Option (Σ j, X j))) inferInstance)
    (coverPreimage N i)
  rw [isOpen_sup]
  constructor
  · rw [isOpen_coinduced, isOpen_sigma_iff]
    intro j
    change IsOpen {x : X j | j = i ∨ x ∈ N j}
    by_cases hji : j = i
    · simp [hji]
    · simpa [hji] using hNopen j
  · rw [isOpen_coinduced]
    change IsOpen (Set.univ : Set Unit)
    exact isOpen_univ

omit [∀ i, TopologicalSpace (X i)] in
/-- For a nonempty family, the standard wedge-cover members cover the whole
wedge. -/
theorem univ_subset_iUnion_coverSet [Nonempty ι]
    (N : ∀ i, Set (X i)) (hN : ∀ i, x₀ i ∈ N i) :
    Set.univ ⊆ ⋃ i, coverSet x₀ N hN i := by
  intro z _
  induction z using Quotient.inductionOn with
  | _ a =>
      cases a with
      | none =>
          obtain ⟨i⟩ := ‹Nonempty ι›
          apply mem_iUnion.mpr
          refine ⟨i, ?_⟩
          change coverPreimage N i none
          trivial
      | some p =>
          apply mem_iUnion.mpr
          refine ⟨p.1, ?_⟩
          change coverPreimage N p.1 (some p)
          exact Or.inl rfl

/-- The standard cover associated to chosen well-pointed neighborhoods. -/
def vanKampenCover (hwell : ∀ i, WellPointedAt (x₀ i)) (i : ι) :
    Set (Hatcher.PointedWedge X x₀) :=
  coverSet x₀ (fun j ↦ (hwell j).neighborhood)
    (fun j ↦ (hwell j).mem_neighborhood) i

/-- Each summand maps into its own member of the well-pointed wedge cover. -/
@[simp]
theorem inclusion_mem_vanKampenCover
    (hwell : ∀ i, WellPointedAt (x₀ i)) (i : ι) (x : X i) :
    inclusion x₀ i x ∈ vanKampenCover x₀ hwell i :=
  inclusion_mem_coverSet x₀ _ _ i x

/-- Every member of the well-pointed wedge cover contains the wedge point. -/
@[simp]
theorem basepoint_mem_vanKampenCover
    (hwell : ∀ i, WellPointedAt (x₀ i)) (i : ι) :
    basepoint x₀ ∈ vanKampenCover x₀ hwell i :=
  basepoint_mem_coverSet x₀ _ _ i

/-- Every member of the well-pointed wedge cover is open. -/
theorem isOpen_vanKampenCover
    (hwell : ∀ i, WellPointedAt (x₀ i)) (i : ι) :
    IsOpen (vanKampenCover x₀ hwell i) :=
  isOpen_coverSet x₀ _ _ (fun j ↦ (hwell j).isOpen_neighborhood) i

/-- For a nonempty family, the well-pointed wedge cover covers the whole
wedge. -/
theorem univ_subset_iUnion_vanKampenCover [Nonempty ι]
    (hwell : ∀ i, WellPointedAt (x₀ i)) :
    Set.univ ⊆ ⋃ i, vanKampenCover x₀ hwell i :=
  univ_subset_iUnion_coverSet x₀ _ _

end PointedWedge

end Hatcher
