import Hatcher.VanKampen.PointedWedge
import Mathlib.Topology.Homotopy.Contractible

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

/-- A strong deformation retract presented by its inclusion into the ambient
space. -/
structure StrongDeformationRetract
    {A : Type u} {Y : Type v} [TopologicalSpace A] [TopologicalSpace Y]
    (inclusion : C(A, Y)) where
  retract : C(Y, A)
  retract_inclusion : retract.comp inclusion = ContinuousMap.id A
  deformation :
    (ContinuousMap.id Y).HomotopyRel (inclusion.comp retract) (Set.range inclusion)

namespace StrongDeformationRetract

variable {A : Type u} {Y : Type v} [TopologicalSpace A] [TopologicalSpace Y]
  {inclusion : C(A, Y)}

/-- A strong deformation retract supplies the corresponding homotopy
equivalence. -/
def toHomotopyEquiv (h : StrongDeformationRetract inclusion) :
    ContinuousMap.HomotopyEquiv Y A where
  toFun := h.retract
  invFun := inclusion
  left_inv := ⟨h.deformation.toHomotopy.symm⟩
  right_inv := by
    rw [h.retract_inclusion]

/-- A strong deformation retract onto a contractible space is contractible. -/
theorem contractibleSpace [ContractibleSpace A]
    (h : StrongDeformationRetract inclusion) : ContractibleSpace Y :=
  h.toHomotopyEquiv.contractibleSpace

/-- A strong deformation retract onto a path-connected space is
path-connected. -/
theorem pathConnectedSpace [PathConnectedSpace A]
    (h : StrongDeformationRetract inclusion) : PathConnectedSpace Y where
  nonempty := by
    obtain ⟨a⟩ := (PathConnectedSpace.nonempty : Nonempty A)
    exact ⟨inclusion a⟩
  joined y z := by
    have hy : Joined y (inclusion (h.retract y)) :=
      ⟨h.deformation.toHomotopy.evalAt y⟩
    have hz : Joined z (inclusion (h.retract z)) :=
      ⟨h.deformation.toHomotopy.evalAt z⟩
    have ha : Joined (h.retract y) (h.retract z) :=
      PathConnectedSpace.joined _ _
    have hi : Joined (inclusion (h.retract y)) (inclusion (h.retract z)) :=
      ⟨ha.somePath.map inclusion.continuous⟩
    exact hy.trans (hi.trans hz.symm)

/-- A contraction fixing its center is a strong deformation retract onto that
point, represented by `Unit`. -/
def ofPointedContraction (y₀ : Y)
    (H : (ContinuousMap.id Y).HomotopyRel
      (ContinuousMap.const Y y₀) {y₀}) :
    StrongDeformationRetract (ContinuousMap.const Unit y₀) where
  retract := ContinuousMap.const Y ()
  retract_inclusion := by
    ext
  deformation := by
    change (ContinuousMap.id Y).HomotopyRel (ContinuousMap.const Y y₀)
      (Set.range fun _ : Unit ↦ y₀)
    rw [Set.range_const]
    exact H

/-- A pointed contraction supplies contractibility. -/
theorem contractibleSpace_of_pointedContraction (y₀ : Y)
    (H : (ContinuousMap.id Y).HomotopyRel
      (ContinuousMap.const Y y₀) {y₀}) :
    ContractibleSpace Y :=
  (ofPointedContraction y₀ H).contractibleSpace

end StrongDeformationRetract

namespace PointedWedge

variable {ι : Type u} {X : ι → Type v} [∀ i, TopologicalSpace (X i)]
  (x₀ : ∀ i, X i)

omit [∀ i, TopologicalSpace (X i)] in
/-- Every point of an empty pointed wedge is its basepoint. -/
theorem eq_basepoint_of_isEmpty [IsEmpty ι]
    (z : Hatcher.PointedWedge X x₀) : z = basepoint x₀ := by
  induction z using Quotient.inductionOn with
  | _ z =>
    cases z with
    | none => rfl
    | some p => exact isEmptyElim p.1

omit [∀ i, TopologicalSpace (X i)] in
/-- An empty pointed wedge has exactly one point. -/
instance instUniqueOfIsEmpty [IsEmpty ι] :
    Unique (Hatcher.PointedWedge X x₀) where
  default := basepoint x₀
  uniq := eq_basepoint_of_isEmpty x₀

/-- An empty pointed wedge is contractible. -/
instance instContractibleSpaceOfIsEmpty [IsEmpty ι] :
    ContractibleSpace (Hatcher.PointedWedge X x₀) :=
  inferInstance

/-- The canonical summand inclusion, with codomain restricted to a subset
that contains the whole summand. -/
def inclusionToSubset (W : Set (Hatcher.PointedWedge X x₀)) (i : ι)
    (hW : ∀ x, inclusion x₀ i x ∈ W) : C(X i, W) where
  toFun x := ⟨inclusion x₀ i x, hW x⟩
  continuous_toFun := (continuous_inclusion x₀ i).subtype_mk _

@[simp]
theorem coe_inclusionToSubset
    (W : Set (Hatcher.PointedWedge X x₀)) (i : ι)
    (hW : ∀ x, inclusion x₀ i x ∈ W) (x : X i) :
    ((inclusionToSubset x₀ W i hW x : W) :
      Hatcher.PointedWedge X x₀) = inclusion x₀ i x :=
  rfl

@[simp]
theorem inclusionToSubset_basepoint
    (W : Set (Hatcher.PointedWedge X x₀)) (i : ι)
    (hW : ∀ x, inclusion x₀ i x ∈ W) :
    inclusionToSubset x₀ W i hW (x₀ i) =
      ⟨basepoint x₀, by simpa using hW (x₀ i)⟩ := by
  apply Subtype.ext
  exact inclusion_basepoint x₀ i

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

/-- The canonical summand inclusion into its member of the well-pointed wedge
cover. -/
def vanKampenCoverInclusion
    (hwell : ∀ i, WellPointedAt (x₀ i)) (i : ι) :
    C(X i, vanKampenCover x₀ hwell i) :=
  inclusionToSubset x₀ _ i (inclusion_mem_vanKampenCover x₀ hwell i)

@[simp]
theorem coe_vanKampenCoverInclusion
    (hwell : ∀ i, WellPointedAt (x₀ i)) (i : ι) (x : X i) :
    ((vanKampenCoverInclusion x₀ hwell i x : vanKampenCover x₀ hwell i) :
      Hatcher.PointedWedge X x₀) = inclusion x₀ i x :=
  rfl

@[simp]
theorem vanKampenCoverInclusion_basepoint
    (hwell : ∀ i, WellPointedAt (x₀ i)) (i : ι) :
    vanKampenCoverInclusion x₀ hwell i (x₀ i) =
      ⟨basepoint x₀, basepoint_mem_coverSet x₀ _ _ i⟩ := by
  apply Subtype.ext
  exact inclusion_basepoint x₀ i

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
