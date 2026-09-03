import Mathlib.Topology.CWComplex.Classical.Subcomplex
import Mathlib.Topology.DiscreteSubset

noncomputable section

open Set

namespace Hatcher

open Topology

universe u

variable {X : Type u} [TopologicalSpace X] {C K : Set X} [CWComplex C]

private abbrev Cell (C : Set X) [CWComplex C] := Σ n, RelCWComplex.cell C n

private def cellOpen (e : Cell C) : Set X :=
  RelCWComplex.openCell (C := C) e.1 e.2

private def cellBoundary (e : Cell C) : Set X :=
  RelCWComplex.cellFrontier (C := C) e.1 e.2

private def cellClosed (e : Cell C) : Set X :=
  RelCWComplex.closedCell (C := C) e.1 e.2

private def ClosedUnderFrontier (S : Set (Cell C)) : Prop :=
  ∀ e ∈ S, cellBoundary (C := C) e ⊆ ⋃ f : S, cellOpen (C := C) f.1

private theorem exists_finite_closed_cell_family (n : ℕ) (i : RelCWComplex.cell C n) :
    ∃ S : Set (Cell C), S.Finite ∧ (⟨n, i⟩ : Cell C) ∈ S ∧ ClosedUnderFrontier S := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      obtain ⟨I, hI⟩ := CWComplex.cellFrontier_subset_finite_openCell n i
      let B := Σ m : Fin n, {j // j ∈ I m}
      haveI : Finite B := inferInstance
      have hrec : ∀ b : B,
          ∃ S : Set (Cell C), S.Finite ∧
            (⟨b.1.1, b.2.1⟩ : Cell C) ∈ S ∧ ClosedUnderFrontier S := by
        intro b
        exact ih b.1.1 b.1.2 b.2.1
      choose S hSfinite hSself hSclosed using hrec
      let T : Set (Cell C) := {(⟨n, i⟩ : Cell C)} ∪ ⋃ b : B, S b
      refine ⟨T, (Set.finite_singleton _).union (Set.finite_iUnion hSfinite), ?_, ?_⟩
      · exact Set.mem_union_left _ (Set.mem_singleton _)
      · intro e he x hx
        change e ∈ ({(⟨n, i⟩ : Cell C)} ∪ ⋃ b : B, S b) at he
        rcases he with he | he
        · have heq : e = (⟨n, i⟩ : Cell C) := Set.mem_singleton_iff.mp he
          subst e
          have hx' := hI hx
          simp only [Set.mem_iUnion] at hx'
          obtain ⟨m, hm, j, hj, hxj⟩ := hx'
          let b : B := ⟨⟨m, hm⟩, ⟨j, hj⟩⟩
          apply Set.mem_iUnion.mpr
          refine ⟨⟨(⟨m, j⟩ : Cell C), ?_⟩, hxj⟩
          exact Set.mem_union_right _
            (Set.mem_iUnion_of_mem b (hSself b))
        · obtain ⟨b, heb⟩ := Set.mem_iUnion.mp he
          have hxb := hSclosed b e heb hx
          obtain ⟨d, hxd⟩ := Set.mem_iUnion.mp hxb
          apply Set.mem_iUnion.mpr
          refine ⟨⟨d.1, ?_⟩, hxd⟩
          exact Set.mem_union_right _
            (Set.mem_iUnion_of_mem b d.2)

private theorem exists_finite_closed_cell_family_of_finite
    (S : Set (Cell C)) (hS : S.Finite) :
    ∃ T : Set (Cell C), T.Finite ∧ S ⊆ T ∧ ClosedUnderFrontier T := by
  letI := hS.fintype
  have hrec : ∀ e : S,
      ∃ T : Set (Cell C), T.Finite ∧ e.1 ∈ T ∧ ClosedUnderFrontier T := by
    intro e
    exact exists_finite_closed_cell_family e.1.1 e.1.2
  choose T hTfinite hTself hTclosed using hrec
  let R : Set (Cell C) := ⋃ e : S, T e
  refine ⟨R, Set.finite_iUnion hTfinite, ?_, ?_⟩
  · intro e he
    exact Set.mem_iUnion_of_mem (⟨e, he⟩ : S) (hTself ⟨e, he⟩)
  · intro e he x hx
    obtain ⟨s, hes⟩ := Set.mem_iUnion.mp he
    have hxs := hTclosed s e hes hx
    obtain ⟨d, hxd⟩ := Set.mem_iUnion.mp hxs
    apply Set.mem_iUnion.mpr
    refine ⟨⟨d.1, ?_⟩, hxd⟩
    exact Set.mem_iUnion_of_mem s d.2

private theorem iUnion_cells_eq (S : Set (Cell C)) :
    (⋃ n, ⋃ j : {i : RelCWComplex.cell C n // (⟨n, i⟩ : Cell C) ∈ S},
        RelCWComplex.openCell (C := C) n j.1) =
      ⋃ e : S, cellOpen (C := C) e.1 := by
  ext x
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨n, j, hx⟩
    exact ⟨⟨⟨n, j.1⟩, j.2⟩, hx⟩
  · rintro ⟨e, hx⟩
    exact ⟨e.1.1, ⟨⟨e.1.2, e.2⟩, hx⟩⟩

private def subcomplexOfClosedCellFamily (S : Set (Cell C))
    [T2Space X] (hS : ClosedUnderFrontier S) : CWComplex.Subcomplex C :=
  CWComplex.Subcomplex.mk' C
    (⋃ e : S, cellOpen (C := C) e.1)
    (fun n => {i | (⟨n, i⟩ : Cell C) ∈ S})
    (by
      intro n i x hx
      rw [← RelCWComplex.cellFrontier_union_openCell_eq_closedCell] at hx
      rcases hx with hx | hx
      · exact hS ⟨n, i.1⟩ i.2 hx
      · exact Set.mem_iUnion_of_mem
          (⟨⟨n, i.1⟩, i.2⟩ : S) hx)
    (iUnion_cells_eq S)

private theorem finite_subcomplexOfClosedCellFamily
    [T2Space X] (S : Set (Cell C)) (hSfinite : S.Finite)
    (hS : ClosedUnderFrontier S) :
    CWComplex.Finite (subcomplexOfClosedCellFamily S hS : Set X) := by
  let E := subcomplexOfClosedCellFamily S hS
  letI := hSfinite.fintype
  apply CWComplex.finite_of_finite_cells (C := (E : Set X))
  let e : (Σ n, RelCWComplex.cell (E : Set X) n) ≃ S :=
    { toFun := fun c => ⟨⟨c.1, c.2.1⟩, c.2.2⟩
      invFun := fun c => ⟨c.1.1, ⟨c.1.2, c.2⟩⟩
      left_inv := by rintro ⟨n, i⟩; rfl
      right_inv := by rintro ⟨⟨n, i⟩, hi⟩; rfl }
  exact (Equiv.finite_iff e).mpr inferInstance

private theorem exists_finite_subcomplex_of_finite_cells
    [T2Space X] (S : Set (Cell C)) (hSfinite : S.Finite) :
    ∃ E : CWComplex.Subcomplex C,
      (⋃ e : S, cellOpen (C := C) e.1) ⊆ E ∧ CWComplex.Finite (E : Set X) := by
  obtain ⟨T, hTfinite, hST, hTclosed⟩ :=
    exists_finite_closed_cell_family_of_finite S hSfinite
  let E := subcomplexOfClosedCellFamily T hTclosed
  refine ⟨E, ?_, finite_subcomplexOfClosedCellFamily T hTfinite hTclosed⟩
  intro x hx
  obtain ⟨e, hxe⟩ := Set.mem_iUnion.mp hx
  exact Set.mem_iUnion_of_mem (⟨e.1, hST e.2⟩ : T) hxe

private theorem finite_cells_meeting_closedCell (n : ℕ) (i : RelCWComplex.cell C n) :
    {e : Cell C | ¬ Disjoint (cellOpen (C := C) e) (cellClosed (C := C) ⟨n, i⟩)}.Finite := by
  obtain ⟨I, hI⟩ := CWComplex.cellFrontier_subset_finite_openCell n i
  let B := Σ m : Fin n, {j // j ∈ I m}
  haveI : Finite B := inferInstance
  let f : B → Cell C := fun b => ⟨b.1.1, b.2.1⟩
  apply ((Set.finite_singleton (⟨n, i⟩ : Cell C)).union (Set.finite_range f)).subset
  intro e he
  obtain ⟨x, hxe, hxclosed⟩ := Set.not_disjoint_iff.mp he
  change x ∈ RelCWComplex.closedCell (C := C) n i at hxclosed
  rw [← RelCWComplex.cellFrontier_union_openCell_eq_closedCell] at hxclosed
  rcases hxclosed with hxfrontier | hxopen
  · have hx' := hI hxfrontier
    simp only [Set.mem_iUnion] at hx'
    obtain ⟨m, hm, j, hj, hxj⟩ := hx'
    right
    refine ⟨⟨⟨m, hm⟩, ⟨j, hj⟩⟩, ?_⟩
    apply RelCWComplex.eq_of_not_disjoint_openCell (C := C)
    apply Set.not_disjoint_iff.mpr
    exact ⟨x, hxj, hxe⟩
  · left
    apply RelCWComplex.eq_of_not_disjoint_openCell (C := C)
    apply Set.not_disjoint_iff.mpr
    exact ⟨x, hxe, hxopen⟩

private def cellsMeeting (K : Set X) : Set (Cell C) :=
  {e | (K ∩ cellOpen (C := C) e).Nonempty}

private theorem finite_cellsMeeting_of_isCompact
    [T2Space X] (hK : IsCompact K) (hKC : K ⊆ C) :
    (cellsMeeting (C := C) K).Finite := by
  classical
  by_contra hfinite
  let M := cellsMeeting (C := C) K
  have hpoint : ∀ e : M, ∃ x, x ∈ K ∩ cellOpen (C := C) e.1 := fun e => e.2
  choose p hp using hpoint
  have hpK : Set.range p ⊆ K := by
    rintro _ ⟨e, rfl⟩
    exact (hp e).1
  have hpC : Set.range p ⊆ C := hpK.trans hKC
  have hp_injective : Function.Injective p := by
    intro a b hab
    apply Subtype.ext
    apply RelCWComplex.eq_of_not_disjoint_openCell (C := C)
    apply Set.not_disjoint_iff.mpr
    refine ⟨p a, (hp a).2, ?_⟩
    rw [hab]
    exact (hp b).2
  have hclosed : ∀ A : Set X, A ⊆ Set.range p → IsClosed A := by
    intro A hA
    rw [CWComplex.closed C A (hA.trans hpC)]
    intro n i
    let Q : Set (Cell C) :=
      {e | ¬ Disjoint (cellOpen (C := C) e) (cellClosed (C := C) ⟨n, i⟩)}
    have hQfinite : Q.Finite := finite_cells_meeting_closedCell n i
    let R : Set M := {e | p e ∈ cellClosed (C := C) ⟨n, i⟩}
    letI := hQfinite.fintype
    let q : R → Q := fun e =>
      ⟨e.1.1, Set.not_disjoint_iff.mpr ⟨p e.1, (hp e.1).2, e.2⟩⟩
    have hq : Function.Injective q := by
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : Q => z.1) hab
    letI : Finite R := Finite.of_injective q hq
    have hRfinite : R.Finite := Set.toFinite R
    apply ((hRfinite.image p).subset ?_).isClosed
    rintro x ⟨hxA, hxclosed⟩
    obtain ⟨e, rfl⟩ := hA hxA
    exact ⟨e, hxclosed, rfl⟩
  have hpDiscrete : IsDiscrete (Set.range p) := by
    rw [isDiscrete_iff_forall_exists_isOpen]
    intro x hx
    refine ⟨(Set.range p \ {x})ᶜ, (hclosed _ Set.sdiff_subset).isOpen_compl, ?_⟩
    ext y
    simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_sdiff,
      Set.mem_range, Set.mem_singleton_iff]
    aesop
  have hpCompact : IsCompact (Set.range p) :=
    hK.of_isClosed_subset (hclosed _ Subset.rfl) hpK
  have hpFinite : (Set.range p).Finite := hpCompact.finite hpDiscrete
  letI := hpFinite.fintype
  let q : M → Set.range p := fun e => ⟨p e, ⟨e, rfl⟩⟩
  have hq : Function.Injective q := fun a b h =>
    hp_injective (congrArg Subtype.val h)
  letI : Finite M := Finite.of_injective q hq
  exact hfinite (Set.toFinite M)

/-- **Hatcher, Proposition A.1 (page 520).** Every compact subset of a CW
complex is contained in a finite subcomplex. -/
theorem compact_subset_finite_subcomplex
    [T2Space X] (hK : IsCompact K) (hKC : K ⊆ C) :
    ∃ E : CWComplex.Subcomplex C, K ⊆ E ∧ CWComplex.Finite (E : Set X) := by
  let S := cellsMeeting (C := C) K
  have hSfinite : S.Finite := finite_cellsMeeting_of_isCompact hK hKC
  obtain ⟨E, hSE, hEfinite⟩ :=
    exists_finite_subcomplex_of_finite_cells S hSfinite
  refine ⟨E, ?_, hEfinite⟩
  intro x hxK
  apply hSE
  have hxC := hKC hxK
  rw [← CWComplex.iUnion_openCell_eq_complex (C := C)] at hxC
  simp only [Set.mem_iUnion] at hxC
  obtain ⟨n, i, hxi⟩ := hxC
  apply Set.mem_iUnion.mpr
  exact ⟨⟨(⟨n, i⟩ : Cell C), ⟨x, hxK, hxi⟩⟩, hxi⟩

end Hatcher
