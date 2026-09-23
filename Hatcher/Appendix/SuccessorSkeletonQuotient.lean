import Hatcher.Appendix.ClassicalCellArrowIso
import Mathlib.Topology.CWComplex.Classical.Subcomplex
import Mathlib.Topology.Category.TopCat.Limits.Products

/-!
# Successor skeleta as quotient spaces

This file assembles the old strict skeleton and the closed characteristic maps
of the next-dimensional cells into the quotient presentation of a successor
strict skeleton. It also exposes the associated coproduct square and descent
maps used to build the abstract cell attachment.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Metric Set Function
open scoped TopCat

namespace Hatcher.ClassicalCW

universe u

open Topology

variable {X : Type u} [TopologicalSpace X] [T2Space X]
variable (C : Set X) {D : Set X} [RelCWComplex C D]

/-- Inclusion of one classical skeleton into its successor. -/
def skeletonLTStepOldMap (n : ℕ) :
    ↑(RelCWComplex.skeletonLT C n : Set X) →
      ↑(RelCWComplex.skeletonLT C (n + 1) : Set X) :=
  fun x ↦ ⟨x, RelCWComplex.skeletonLT_mono (C := C) (by norm_num) x.2⟩

/-- A closed characteristic map with codomain restricted to the successor skeleton. -/
def skeletonLTStepClosedCellMap (n : ℕ) (i : RelCWComplex.cell C n) :
    ↑(closedBall (0 : Fin n → ℝ) 1) →
      ↑(RelCWComplex.skeletonLT C (n + 1) : Set X) :=
  fun x ↦ ⟨RelCWComplex.map n i x,
    RelCWComplex.closedCell_subset_skeletonLT (C := C) n i ⟨x, x.2, rfl⟩⟩

/-- The coproduct of all closed characteristic maps at dimension `n`. -/
def skeletonLTStepClosedCellsMap (n : ℕ) :
    (Σ _i : RelCWComplex.cell C n, ↑(closedBall (0 : Fin n → ℝ) 1)) →
      ↑(RelCWComplex.skeletonLT C (n + 1) : Set X) :=
  fun x ↦ skeletonLTStepClosedCellMap C n x.1 x.2

/-- The old-skeleton inclusion and all new closed characteristic maps assembled jointly. -/
def skeletonLTStepJointMap (n : ℕ) :
    ↑(RelCWComplex.skeletonLT C n : Set X) ⊕
        (Σ _i : RelCWComplex.cell C n, ↑(closedBall (0 : Fin n → ℝ) 1)) →
      ↑(RelCWComplex.skeletonLT C (n + 1) : Set X) :=
  Sum.elim (skeletonLTStepOldMap C n) (skeletonLTStepClosedCellsMap C n)

lemma continuous_skeletonLTStepOldMap (n : ℕ) :
    Continuous (skeletonLTStepOldMap C n) :=
  continuous_subtype_val.subtype_mk _

lemma continuous_skeletonLTStepClosedCellMap (n : ℕ) (i : RelCWComplex.cell C n) :
    Continuous (skeletonLTStepClosedCellMap C n i) :=
  (RelCWComplex.continuousOn n i).restrict.subtype_mk _

lemma continuous_skeletonLTStepClosedCellsMap (n : ℕ) :
    Continuous (skeletonLTStepClosedCellsMap C n) := by
  apply continuous_sigma
  intro i
  exact continuous_skeletonLTStepClosedCellMap C n i

lemma continuous_skeletonLTStepJointMap (n : ℕ) :
    Continuous (skeletonLTStepJointMap C n) :=
  (continuous_skeletonLTStepOldMap C n).sumElim
    (continuous_skeletonLTStepClosedCellsMap C n)

/-- The joint successor-stage map as a bundled continuous map. -/
def skeletonLTStepJointContinuousMap (n : ℕ) :
    C(↑(RelCWComplex.skeletonLT C n : Set X) ⊕
        (Σ _i : RelCWComplex.cell C n, ↑(closedBall (0 : Fin n → ℝ) 1)),
      ↑(RelCWComplex.skeletonLT C (n + 1) : Set X)) where
  toFun := skeletonLTStepJointMap C n
  continuous_toFun := continuous_skeletonLTStepJointMap C n

/-- A classical cell boundary characteristic map into the preceding skeleton. -/
def skeletonLTStepBoundaryMap (n : ℕ) (i : RelCWComplex.cell C n) :
    ↑(sphere (0 : Fin n → ℝ) 1) →
      ↑(RelCWComplex.skeletonLT C n : Set X) :=
  fun x ↦ ⟨RelCWComplex.map n i x,
    RelCWComplex.cellFrontier_subset_skeletonLT (C := C) n i ⟨x, x.2, rfl⟩⟩

lemma continuous_skeletonLTStepBoundaryMap (n : ℕ) (i : RelCWComplex.cell C n) :
    Continuous (skeletonLTStepBoundaryMap C n i) :=
  ((RelCWComplex.continuousOn n i).mono sphere_subset_closedBall).restrict.subtype_mk _

/-- Coproduct cofan of the universe-lifted classical cell boundaries. -/
noncomputable def skeletonLTStepBoundaryCofan (n : ℕ) :
    Cofan (fun _ : RelCWComplex.cell C n ↦ classicalDiskBoundary.{u} n) :=
  TopCat.sigmaCofan _

/-- Coproduct cofan of the universe-lifted classical closed cells. -/
noncomputable def skeletonLTStepClosedCellCofan (n : ℕ) :
    Cofan (fun _ : RelCWComplex.cell C n ↦ classicalDisk.{u} n) :=
  TopCat.sigmaCofan _

/-- Coproduct of the classical boundary inclusions. -/
noncomputable def skeletonLTStepBoundaryInclusion (n : ℕ) :
    (skeletonLTStepBoundaryCofan C n).pt ⟶
      (skeletonLTStepClosedCellCofan C n).pt :=
  TopCat.ofHom
    { toFun := fun x ↦ ⟨x.1, classicalDiskBoundaryInclusion n x.2⟩
      continuous_toFun := by
        apply continuous_sigma
        intro _i
        exact continuous_sigmaMk.comp
          (ConcreteCategory.hom (classicalDiskBoundaryInclusion n)).continuous }

/-- Coproduct of the classical attaching maps. -/
noncomputable def skeletonLTStepAttachingMap (n : ℕ) :
    (skeletonLTStepBoundaryCofan C n).pt ⟶
      TopCat.of ↑(RelCWComplex.skeletonLT C n : Set X) :=
  TopCat.ofHom
    { toFun := fun x ↦ skeletonLTStepBoundaryMap C n x.1 x.2.down
      continuous_toFun := by
        apply continuous_sigma
        intro i
        exact (continuous_skeletonLTStepBoundaryMap C n i).comp continuous_uliftDown }

/-- Coproduct of the closed characteristic maps. -/
noncomputable def skeletonLTStepCharacteristicMap (n : ℕ) :
    (skeletonLTStepClosedCellCofan C n).pt ⟶
      TopCat.of ↑(RelCWComplex.skeletonLT C (n + 1) : Set X) :=
  TopCat.ofHom
    { toFun := fun x ↦ skeletonLTStepClosedCellMap C n x.1 x.2.down
      continuous_toFun := by
        apply continuous_sigma
        intro i
        exact (continuous_skeletonLTStepClosedCellMap C n i).comp continuous_uliftDown }

/-- The old-skeleton inclusion as a morphism in `TopCat`. -/
noncomputable def skeletonLTInclusion (n : ℕ) :
    TopCat.of ↑(RelCWComplex.skeletonLT C n : Set X) ⟶
      TopCat.of ↑(RelCWComplex.skeletonLT C (n + 1) : Set X) :=
  TopCat.ofHom
    { toFun := skeletonLTStepOldMap C n
      continuous_toFun := continuous_skeletonLTStepOldMap C n }

/-- The classical attaching square commutes. -/
theorem skeletonLTStep_square (n : ℕ) :
    skeletonLTStepBoundaryInclusion C n ≫ skeletonLTStepCharacteristicMap C n =
      skeletonLTStepAttachingMap C n ≫ skeletonLTInclusion C n := by
  ext x
  rfl

lemma surjective_skeletonLTStepJointMap (n : ℕ) :
    Surjective (skeletonLTStepJointMap C n) := by
  intro y
  have hy : y.1 ∈ (RelCWComplex.skeletonLT C n : Set X) ∪
      ⋃ (i : RelCWComplex.cell C n), RelCWComplex.closedCell n i := by
    rw [RelCWComplex.skeletonLT_union_iUnion_closedCell_eq_skeletonLT_succ]
    exact y.2
  rcases hy with hy | hy
  · exact ⟨Sum.inl ⟨y.1, hy⟩, Subtype.ext rfl⟩
  · simp only [mem_iUnion] at hy
    obtain ⟨i, z, hz, hzy⟩ := hy
    refine ⟨Sum.inr ⟨i, ⟨z, hz⟩⟩, Subtype.ext ?_⟩
    exact hzy

private theorem mem_sphere_of_map_mem_skeletonLT (n : ℕ)
    (i : RelCWComplex.cell C n) {x : Fin n → ℝ}
    (hx : x ∈ closedBall 0 1)
    (hmap : RelCWComplex.map n i x ∈
      (RelCWComplex.skeletonLT C n : Set X)) :
    x ∈ sphere 0 1 := by
  rw [← ball_union_sphere] at hx
  rcases hx with hx | hx
  · have hopen : RelCWComplex.map n i x ∈
        RelCWComplex.openCell (C := C) n i := ⟨x, hx, rfl⟩
    exact ((RelCWComplex.disjoint_skeletonLT_openCell (C := C)
      (n := (n : ℕ∞)) (m := n) (j := i) le_rfl).notMem_of_mem_left hmap hopen).elim
  · exact hx

private theorem cell_eq_or_map_mem_skeletonLT (n : ℕ)
    (i k : RelCWComplex.cell C n) {x y : Fin n → ℝ}
    (hx : x ∈ closedBall 0 1) (hy : y ∈ closedBall 0 1)
    (hmap : RelCWComplex.map n i x = RelCWComplex.map n k y) :
    (i = k ∧ x = y) ∨
      RelCWComplex.map n i x ∈ (RelCWComplex.skeletonLT C n : Set X) := by
  by_cases hik : i = k
  · subst k
    by_cases hxy : x = y
    · exact Or.inl ⟨rfl, hxy⟩
    · right
      by_cases hxs : x ∈ sphere (0 : Fin n → ℝ) 1
      · exact RelCWComplex.cellFrontier_subset_skeletonLT (C := C) n i
          ⟨x, hxs, rfl⟩
      by_cases hys : y ∈ sphere (0 : Fin n → ℝ) 1
      · exact RelCWComplex.cellFrontier_subset_skeletonLT (C := C) n i
          ⟨y, hys, hmap.symm⟩
      have hxb : x ∈ ball (0 : Fin n → ℝ) 1 := by
        rw [← ball_union_sphere] at hx
        exact hx.resolve_right hxs
      have hyb : y ∈ ball (0 : Fin n → ℝ) 1 := by
        rw [← ball_union_sphere] at hy
        exact hy.resolve_right hys
      have hxy' : x = y := (RelCWComplex.map n i).injOn
        (by rwa [RelCWComplex.source_eq])
        (by rwa [RelCWComplex.source_eq]) hmap
      exact (hxy hxy').elim
  · right
    by_cases hxs : x ∈ sphere (0 : Fin n → ℝ) 1
    · exact RelCWComplex.cellFrontier_subset_skeletonLT (C := C) n i
        ⟨x, hxs, rfl⟩
    by_cases hys : y ∈ sphere (0 : Fin n → ℝ) 1
    · have hyold := RelCWComplex.cellFrontier_subset_skeletonLT (C := C) n k
          ⟨y, hys, rfl⟩
      exact hmap.symm ▸ hyold
    have hxb : x ∈ ball (0 : Fin n → ℝ) 1 := by
      rw [← ball_union_sphere] at hx
      exact hx.resolve_right hxs
    have hyb : y ∈ ball (0 : Fin n → ℝ) 1 := by
      rw [← ball_union_sphere] at hy
      exact hy.resolve_right hys
    have hopenx : RelCWComplex.map n i x ∈
        RelCWComplex.openCell (C := C) n i := ⟨x, hxb, rfl⟩
    have hopeny : RelCWComplex.map n i x ∈
        RelCWComplex.openCell (C := C) n k := ⟨y, hyb, hmap.symm⟩
    have hne : (⟨n, i⟩ : Σ m, RelCWComplex.cell C m) ≠ ⟨n, k⟩ := by
      simpa using hik
    exact ((RelCWComplex.disjoint_openCell_of_ne (C := C) hne).notMem_of_mem_left
      hopenx hopeny).elim

/-- The joint successor-skeleton characteristic map is a quotient map. -/
theorem skeletonLTStepJointMap_isQuotient (n : ℕ) :
    IsQuotientMap (skeletonLTStepJointMap C n) := by
  rw [isQuotientMap_iff_isClosed]
  refine ⟨surjective_skeletonLTStepJointMap C n, ?_⟩
  intro A
  constructor
  · intro hA
    exact hA.preimage (continuous_skeletonLTStepJointMap C n)
  · intro hpre
    rw [isClosed_sum_iff] at hpre
    have hleft := hpre.1
    have hright := hpre.2
    rw [isClosed_sigma_iff] at hright
    change IsClosed ((skeletonLTStepOldMap C n) ⁻¹' A) at hleft
    change ∀ i, IsClosed ((skeletonLTStepClosedCellMap C n i) ⁻¹' A) at hright
    let E0 := RelCWComplex.skeletonLT C n
    let E1 := RelCWComplex.skeletonLT C (n + 1)
    let B : Set X := ((↑) : ↑(E1 : Set X) → X) '' A
    have hOldClosed : IsClosed
        (((↑) : ↑(E0 : Set X) → X) ''
          ((skeletonLTStepOldMap C n) ⁻¹' A)) := by
      exact E0.closed.isClosedEmbedding_subtypeVal.isClosed_iff_image_isClosed.1 hleft
    have hOldEq :
        (((↑) : ↑(E0 : Set X) → X) ''
          ((skeletonLTStepOldMap C n) ⁻¹' A)) =
            B ∩ (E0 : Set X) := by
      ext x
      constructor
      · rintro ⟨x0, hx0A, rfl⟩
        refine ⟨⟨skeletonLTStepOldMap C n x0, hx0A, rfl⟩, x0.2⟩
      · rintro ⟨⟨y, hyA, hyx⟩, hx0⟩
        let x0 : ↑(E0 : Set X) := ⟨x, hx0⟩
        refine ⟨x0, ?_, rfl⟩
        have heq : skeletonLTStepOldMap C n x0 = y := by
          apply Subtype.ext
          exact hyx.symm
        change skeletonLTStepOldMap C n x0 ∈ A
        rwa [heq]
    have hBOldClosed : IsClosed (B ∩ (E0 : Set X)) := hOldEq ▸ hOldClosed
    have hBsub : B ⊆ (E1 : Set X) := by
      intro x hx
      obtain ⟨y, _hyA, rfl⟩ := hx
      exact y.2
    apply E1.closed.isClosedEmbedding_subtypeVal.isClosed_iff_image_isClosed.2
    change IsClosed B
    rw [RelCWComplex.closed (C := (E1 : Set X)) (D := D) B hBsub]
    constructor
    · intro m j
      change IsClosed (B ∩ RelCWComplex.closedCell (C := C) m j.1)
      have hmENat : (m : ℕ∞) < (n + 1 : ℕ∞) := by
        simpa [E1, RelCWComplex.skeletonLT_I] using j.2
      have hm : m ≤ n := by
        norm_cast at hmENat
        omega
      rcases hm.eq_or_lt with rfl | hmn
      · let S : Set ↑(closedBall (0 : Fin m → ℝ) 1) :=
            (skeletonLTStepClosedCellMap C m j.1) ⁻¹' A
        let φ : ↑(closedBall (0 : Fin m → ℝ) 1) → X :=
          fun z ↦ RelCWComplex.map m j.1 z
        have hSclosed : IsClosed S := hright j.1
        have hScompact : IsCompact S := hSclosed.isCompact
        have hφcontinuous : Continuous φ :=
          (RelCWComplex.continuousOn m j.1).restrict
        have hφSclosed : IsClosed (φ '' S) :=
          (hScompact.image hφcontinuous).isClosed
        have hφSeq : φ '' S =
            B ∩ RelCWComplex.closedCell (C := C) m j.1 := by
          ext x
          constructor
          · rintro ⟨z, hzS, rfl⟩
            refine ⟨⟨skeletonLTStepClosedCellMap C m j.1 z, hzS, rfl⟩, ?_⟩
            exact ⟨z, z.2, rfl⟩
          · rintro ⟨⟨y, hyA, hyx⟩, hxcell⟩
            obtain ⟨z, hz, hzx⟩ := hxcell
            let z' : ↑(closedBall (0 : Fin m → ℝ) 1) := ⟨z, hz⟩
            refine ⟨z', ?_, ?_⟩
            · change skeletonLTStepClosedCellMap C m j.1 z' ∈ A
              have heq : skeletonLTStepClosedCellMap C m j.1 z' = y := by
                apply Subtype.ext
                exact hzx.trans hyx.symm
              rwa [heq]
            · exact hzx
        exact hφSeq ▸ hφSclosed
      · have hcellsubset :
            RelCWComplex.closedCell (C := C) m j.1 ⊆ (E0 : Set X) := by
          refine (RelCWComplex.closedCell_subset_skeletonLT (C := C) m j.1).trans ?_
          apply RelCWComplex.skeletonLT_mono (C := C)
          norm_cast
        have hclosed := hBOldClosed.inter
          (RelCWComplex.isClosed_closedCell (C := C) (n := m) (i := j.1))
        simpa only [inter_assoc, inter_eq_right.mpr hcellsubset] using hclosed
    · have hDsubset : D ⊆ (E0 : Set X) := E0.base_subset
      have hclosed := hBOldClosed.inter (RelCWComplex.isClosedBase C)
      simpa only [inter_assoc, inter_eq_right.mpr hDsubset] using hclosed

/-- Piecewise map from an old skeleton and the new closed cells. -/
def skeletonLTStepCoconeMap {Z : Type*} [TopologicalSpace Z] (n : ℕ)
    (old : C(↑(RelCWComplex.skeletonLT C n : Set X), Z))
    (cells : ∀ _i : RelCWComplex.cell C n,
      C(↑(closedBall (0 : Fin n → ℝ) 1), Z)) :
    C(↑(RelCWComplex.skeletonLT C n : Set X) ⊕
        (Σ _i : RelCWComplex.cell C n, ↑(closedBall (0 : Fin n → ℝ) 1)), Z) where
  toFun := Sum.elim old (fun x ↦ cells x.1 x.2)
  continuous_toFun := old.continuous.sumElim (continuous_sigma fun i ↦ (cells i).continuous)

private theorem skeletonLTStepCoconeMap_factorsThrough
    {Z : Type*} [TopologicalSpace Z] (n : ℕ)
    (old : C(↑(RelCWComplex.skeletonLT C n : Set X), Z))
    (cells : ∀ _i : RelCWComplex.cell C n,
      C(↑(closedBall (0 : Fin n → ℝ) 1), Z))
    (hboundary : ∀ (i : RelCWComplex.cell C n)
      (x : ↑(sphere (0 : Fin n → ℝ) 1)),
      old (skeletonLTStepBoundaryMap C n i x) =
        cells i ⟨x, sphere_subset_closedBall x.2⟩) :
    Function.FactorsThrough (skeletonLTStepCoconeMap C n old cells)
      (skeletonLTStepJointContinuousMap C n) := by
  intro a b hab
  rcases a with x | p
  · rcases b with y | p
    · change skeletonLTStepOldMap C n x = skeletonLTStepOldMap C n y at hab
      have hxy : x = y := Subtype.ext (congrArg
        (Subtype.val : ↑(RelCWComplex.skeletonLT C (n + 1) : Set X) → X) hab)
      subst y
      rfl
    · obtain ⟨i, y⟩ := p
      change skeletonLTStepOldMap C n x =
        skeletonLTStepClosedCellMap C n i y at hab
      have habv : x.1 = RelCWComplex.map n i y :=
        congrArg (Subtype.val :
          ↑(RelCWComplex.skeletonLT C (n + 1) : Set X) → X) hab
      have hymem : RelCWComplex.map n i y ∈
          (RelCWComplex.skeletonLT C n : Set X) := by
        rw [← habv]
        exact x.2
      have hysphere := mem_sphere_of_map_mem_skeletonLT C n i y.2 hymem
      let ys : ↑(sphere (0 : Fin n → ℝ) 1) := ⟨y, hysphere⟩
      change old x = cells i y
      calc
        old x = old (skeletonLTStepBoundaryMap C n i ys) := by
          congr 1
          apply Subtype.ext
          exact habv
        _ = cells i ⟨ys, sphere_subset_closedBall ys.2⟩ := hboundary i ys
        _ = cells i y := by
          congr 1
  · obtain ⟨i, x⟩ := p
    rcases b with y | p
    · change skeletonLTStepClosedCellMap C n i x =
        skeletonLTStepOldMap C n y at hab
      have habv : RelCWComplex.map n i x = y.1 :=
        congrArg (Subtype.val :
          ↑(RelCWComplex.skeletonLT C (n + 1) : Set X) → X) hab
      have hxmem : RelCWComplex.map n i x ∈
          (RelCWComplex.skeletonLT C n : Set X) := by
        rw [habv]
        exact y.2
      have hxsphere := mem_sphere_of_map_mem_skeletonLT C n i x.2 hxmem
      let xs : ↑(sphere (0 : Fin n → ℝ) 1) := ⟨x, hxsphere⟩
      change cells i x = old y
      calc
        cells i x = cells i ⟨xs, sphere_subset_closedBall xs.2⟩ := by
          congr 1
        _ = old (skeletonLTStepBoundaryMap C n i xs) := (hboundary i xs).symm
        _ = old y := by
          congr 1
          apply Subtype.ext
          exact habv
    · obtain ⟨k, y⟩ := p
      change skeletonLTStepClosedCellMap C n i x =
        skeletonLTStepClosedCellMap C n k y at hab
      have habv : RelCWComplex.map n i x = RelCWComplex.map n k y :=
        congrArg (Subtype.val :
          ↑(RelCWComplex.skeletonLT C (n + 1) : Set X) → X) hab
      rcases cell_eq_or_map_mem_skeletonLT C n i k x.2 y.2 habv with hxy | hmem
      · obtain ⟨rfl, hxy⟩ := hxy
        have hxy' : x = y := Subtype.ext hxy
        subst y
        rfl
      · have hxsphere := mem_sphere_of_map_mem_skeletonLT C n i x.2 hmem
        have hymem : RelCWComplex.map n k y ∈
            (RelCWComplex.skeletonLT C n : Set X) := habv ▸ hmem
        have hysphere := mem_sphere_of_map_mem_skeletonLT C n k y.2 hymem
        let xs : ↑(sphere (0 : Fin n → ℝ) 1) := ⟨x, hxsphere⟩
        let ys : ↑(sphere (0 : Fin n → ℝ) 1) := ⟨y, hysphere⟩
        change cells i x = cells k y
        calc
          cells i x = cells i ⟨xs, sphere_subset_closedBall xs.2⟩ := by
            congr 1
          _ = old (skeletonLTStepBoundaryMap C n i xs) := (hboundary i xs).symm
          _ = old (skeletonLTStepBoundaryMap C n k ys) := by
            congr 1
            apply Subtype.ext
            exact habv
          _ = cells k ⟨ys, sphere_subset_closedBall ys.2⟩ := hboundary k ys
          _ = cells k y := by
            congr 1

/-- Descend maps whose cell restrictions agree with the old-skeleton map on every boundary. -/
noncomputable def skeletonLTStepDesc
    {Z : Type*} [TopologicalSpace Z] (n : ℕ)
    (old : C(↑(RelCWComplex.skeletonLT C n : Set X), Z))
    (cells : ∀ _i : RelCWComplex.cell C n,
      C(↑(closedBall (0 : Fin n → ℝ) 1), Z))
    (hboundary : ∀ (i : RelCWComplex.cell C n)
      (x : ↑(sphere (0 : Fin n → ℝ) 1)),
      old (skeletonLTStepBoundaryMap C n i x) =
        cells i ⟨x, sphere_subset_closedBall x.2⟩) :
    C(↑(RelCWComplex.skeletonLT C (n + 1) : Set X), Z) :=
  (skeletonLTStepJointMap_isQuotient C n).lift
    (f := skeletonLTStepJointContinuousMap C n)
    (skeletonLTStepCoconeMap C n old cells)
    (skeletonLTStepCoconeMap_factorsThrough C n old cells hboundary)

@[simp]
theorem skeletonLTStepDesc_old_apply
    {Z : Type*} [TopologicalSpace Z] (n : ℕ)
    (old : C(↑(RelCWComplex.skeletonLT C n : Set X), Z))
    (cells : ∀ _i : RelCWComplex.cell C n,
      C(↑(closedBall (0 : Fin n → ℝ) 1), Z))
    (hboundary : ∀ (i : RelCWComplex.cell C n)
      (x : ↑(sphere (0 : Fin n → ℝ) 1)),
      old (skeletonLTStepBoundaryMap C n i x) =
        cells i ⟨x, sphere_subset_closedBall x.2⟩)
    (x : ↑(RelCWComplex.skeletonLT C n : Set X)) :
    skeletonLTStepDesc C n old cells hboundary (skeletonLTStepOldMap C n x) = old x := by
  have hcomp := (skeletonLTStepJointMap_isQuotient C n).lift_comp
    (f := skeletonLTStepJointContinuousMap C n)
    (skeletonLTStepCoconeMap C n old cells)
    (skeletonLTStepCoconeMap_factorsThrough C n old cells hboundary)
  exact ContinuousMap.congr_fun hcomp (Sum.inl x)

@[simp]
theorem skeletonLTStepDesc_cell_apply
    {Z : Type*} [TopologicalSpace Z] (n : ℕ)
    (old : C(↑(RelCWComplex.skeletonLT C n : Set X), Z))
    (cells : ∀ _i : RelCWComplex.cell C n,
      C(↑(closedBall (0 : Fin n → ℝ) 1), Z))
    (hboundary : ∀ (i : RelCWComplex.cell C n)
      (x : ↑(sphere (0 : Fin n → ℝ) 1)),
      old (skeletonLTStepBoundaryMap C n i x) =
        cells i ⟨x, sphere_subset_closedBall x.2⟩)
    (i : RelCWComplex.cell C n)
    (x : ↑(closedBall (0 : Fin n → ℝ) 1)) :
    skeletonLTStepDesc C n old cells hboundary (skeletonLTStepClosedCellMap C n i x) =
      cells i x := by
  have hcomp := (skeletonLTStepJointMap_isQuotient C n).lift_comp
    (f := skeletonLTStepJointContinuousMap C n)
    (skeletonLTStepCoconeMap C n old cells)
    (skeletonLTStepCoconeMap_factorsThrough C n old cells hboundary)
  exact ContinuousMap.congr_fun hcomp (Sum.inr ⟨i, x⟩)

end Hatcher.ClassicalCW
