import Hatcher.VanKampen.HomotopyCoverDecomposition

noncomputable section

open Set
open scoped unitInterval

namespace Hatcher.VanKampen

namespace IntervalSubdivision

private theorem range_eq_ofFn_val (n : ℕ) :
    List.range n = List.ofFn (fun k : Fin n ↦ k.val) := by
  apply List.ext_getElem
  · simp
  · intro i hi₁ hi₂
    rw [List.getElem_range, List.getElem_ofFn]

private theorem flatten_rangeBlocks {n : ℕ} (a : Fin (n + 1) → ℕ)
    (ha : StrictMono a) :
    (List.ofFn fun i : Fin n ↦
      List.range' (a i.castSucc) (a i.succ - a i.castSucc)).flatten =
      List.range' (a 0) (a (Fin.last n) - a 0) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ_last, List.flatten_append]
      have hsucc : ∀ i : Fin n, i.succ.castSucc = i.castSucc.succ :=
        fun _ ↦ rfl
      have hzero : Fin.castSucc (0 : Fin (n + 1)) =
          (0 : Fin (n + 2)) := rfl
      have hprefix :
          (List.ofFn fun i : Fin n ↦
            List.range' (a i.castSucc.castSucc)
              (a i.castSucc.succ - a i.castSucc.castSucc)).flatten =
            List.range' (a 0)
              (a (Fin.last n).castSucc - a 0) := by
        simpa only [Function.comp_apply, hsucc, hzero] using
          ih (a := a ∘ Fin.castSucc) (ha.comp Fin.strictMono_castSucc)
      rw [hprefix]
      simp only [List.flatten_singleton]
      have hlast : (Fin.last n).succ = Fin.last (n + 1) := rfl
      rw [hlast]
      have h₀m : a 0 ≤ a (Fin.last n).castSucc :=
        ha.monotone (Fin.zero_le _)
      have hme : a (Fin.last n).castSucc ≤ a (Fin.last (n + 1)) :=
        ha.monotone (Fin.le_last _)
      calc
        List.range' (a 0) (a (Fin.last n).castSucc - a 0) ++
            List.range' (a (Fin.last n).castSucc)
              (a (Fin.last (n + 1)) - a (Fin.last n).castSucc) =
            List.range' (a 0)
              ((a (Fin.last n).castSucc - a 0) +
                (a (Fin.last (n + 1)) - a (Fin.last n).castSucc)) := by
          simpa only [one_mul, Nat.add_sub_of_le h₀m] using
            (List.range'_append
            (s := a 0)
            (m := a (Fin.last n).castSucc - a 0)
            (n := a (Fin.last (n + 1)) - a (Fin.last n).castSucc)
            (step := 1))
        _ = List.range' (a 0) (a (Fin.last (n + 1)) - a 0) := by
          congr 2
          omega

/-- The index in the common refinement of a vertex of the left subdivision. -/
noncomputable def commonRefinementLeftVertex (s t : IntervalSubdivision)
    (j : Fin (s.cells + 1)) : Fin ((commonRefinement s t).cells + 1) := by
  have hj : s.point j ∈ (commonRefinement s t).vertices :=
    vertices_subset_commonRefinement_left s t <|
      Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  rw [vertices] at hj
  exact Classical.choose (Finset.mem_image.mp hj)

theorem commonRefinementLeftVertex_spec (s t : IntervalSubdivision)
    (j : Fin (s.cells + 1)) :
    (commonRefinement s t).point (commonRefinementLeftVertex s t j) =
      s.point j := by
  unfold commonRefinementLeftVertex
  exact (Classical.choose_spec
    (Finset.mem_image.mp
      (vertices_subset_commonRefinement_left s t <|
        Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩))).2

theorem commonRefinementLeftVertex_strictMono (s t : IntervalSubdivision) :
    StrictMono (commonRefinementLeftVertex s t) := by
  intro i j hij
  apply (commonRefinement s t).strictMono.lt_iff_lt.mp
  rw [commonRefinementLeftVertex_spec, commonRefinementLeftVertex_spec]
  exact s.strictMono hij

@[simp]
theorem commonRefinementLeftVertex_zero (s t : IntervalSubdivision) :
    commonRefinementLeftVertex s t 0 = 0 := by
  apply (commonRefinement s t).strictMono.injective
  rw [commonRefinementLeftVertex_spec, s.left, (commonRefinement s t).left]

@[simp]
theorem commonRefinementLeftVertex_last (s t : IntervalSubdivision) :
    commonRefinementLeftVertex s t (Fin.last s.cells) =
      Fin.last (commonRefinement s t).cells := by
  apply (commonRefinement s t).strictMono.injective
  rw [commonRefinementLeftVertex_spec, s.right, (commonRefinement s t).right]

/-- The number of common-refinement cells contained in one left cell. -/
def commonRefinementLeftBlockSize (s t : IntervalSubdivision)
    (i : Fin s.cells) : ℕ :=
  (commonRefinementLeftVertex s t i.succ).val -
    (commonRefinementLeftVertex s t i.castSucc).val

theorem commonRefinementLeftBlockSize_pos (s t : IntervalSubdivision)
    (i : Fin s.cells) : 0 < commonRefinementLeftBlockSize s t i := by
  unfold commonRefinementLeftBlockSize
  have h : commonRefinementLeftVertex s t i.castSucc <
      commonRefinementLeftVertex s t i.succ :=
    commonRefinementLeftVertex_strictMono s t Fin.castSucc_lt_succ
  omega

/-- The `j`th refined cell inside the `i`th cell of the left subdivision. -/
def commonRefinementLeftBlockCell (s t : IntervalSubdivision)
    (i : Fin s.cells) (j : Fin (commonRefinementLeftBlockSize s t i)) :
    Fin (commonRefinement s t).cells := by
  let a := commonRefinementLeftVertex s t i.castSucc
  let b := commonRefinementLeftVertex s t i.succ
  refine ⟨a.val + j.val, ?_⟩
  have hab : a.val < b.val := by
    exact commonRefinementLeftVertex_strictMono s t Fin.castSucc_lt_succ
  have hj : j.val < b.val - a.val := j.isLt
  have hb : b.val ≤ (commonRefinement s t).cells := Nat.le_of_lt_succ b.isLt
  omega

/-- The `j`th refined vertex spanning the `i`th cell of the left subdivision. -/
def commonRefinementLeftBlockVertex (s t : IntervalSubdivision)
    (i : Fin s.cells)
    (j : Fin (commonRefinementLeftBlockSize s t i + 1)) :
    Fin ((commonRefinement s t).cells + 1) := by
  let a := commonRefinementLeftVertex s t i.castSucc
  let b := commonRefinementLeftVertex s t i.succ
  refine ⟨a.val + j.val, ?_⟩
  have hab : a.val < b.val := by
    exact commonRefinementLeftVertex_strictMono s t Fin.castSucc_lt_succ
  have hj : j.val < (b.val - a.val) + 1 := j.isLt
  have hb : b.val < (commonRefinement s t).cells + 1 := b.isLt
  omega

@[simp]
theorem commonRefinementLeftBlockVertex_zero (s t : IntervalSubdivision)
    (i : Fin s.cells) :
    commonRefinementLeftBlockVertex s t i 0 =
      commonRefinementLeftVertex s t i.castSucc := by
  apply Fin.ext
  rfl

@[simp]
theorem commonRefinementLeftBlockVertex_last (s t : IntervalSubdivision)
    (i : Fin s.cells) :
    commonRefinementLeftBlockVertex s t i
        (Fin.last (commonRefinementLeftBlockSize s t i)) =
      commonRefinementLeftVertex s t i.succ := by
  apply Fin.ext
  unfold commonRefinementLeftBlockVertex commonRefinementLeftBlockSize
  dsimp only
  have h : commonRefinementLeftVertex s t i.castSucc <
      commonRefinementLeftVertex s t i.succ :=
    commonRefinementLeftVertex_strictMono s t Fin.castSucc_lt_succ
  change (commonRefinementLeftVertex s t i.castSucc).val +
      ((commonRefinementLeftVertex s t i.succ).val -
        (commonRefinementLeftVertex s t i.castSucc).val) =
    (commonRefinementLeftVertex s t i.succ).val
  exact Nat.add_sub_of_le (Nat.le_of_lt h)

@[simp]
theorem commonRefinementLeftBlockVertex_castSucc (s t : IntervalSubdivision)
    (i : Fin s.cells) (j : Fin (commonRefinementLeftBlockSize s t i)) :
    commonRefinementLeftBlockVertex s t i j.castSucc =
      (commonRefinementLeftBlockCell s t i j).castSucc := by
  apply Fin.ext
  rfl

@[simp]
theorem commonRefinementLeftBlockVertex_succ (s t : IntervalSubdivision)
    (i : Fin s.cells) (j : Fin (commonRefinementLeftBlockSize s t i)) :
    commonRefinementLeftBlockVertex s t i j.succ =
      (commonRefinementLeftBlockCell s t i j).succ := by
  apply Fin.ext
  rfl

theorem commonRefinementLeftBlockPoint_zero (s t : IntervalSubdivision)
    (i : Fin s.cells) :
    (commonRefinement s t).point
        (commonRefinementLeftBlockVertex s t i 0) = s.point i.castSucc := by
  rw [commonRefinementLeftBlockVertex_zero,
    commonRefinementLeftVertex_spec]

theorem commonRefinementLeftBlockPoint_last (s t : IntervalSubdivision)
    (i : Fin s.cells) :
    (commonRefinement s t).point
        (commonRefinementLeftBlockVertex s t i
          (Fin.last (commonRefinementLeftBlockSize s t i))) =
      s.point i.succ := by
  rw [commonRefinementLeftBlockVertex_last,
    commonRefinementLeftVertex_spec]

private theorem cell_container_unique (coarse refined : IntervalSubdivision)
    (k : Fin refined.cells) (i j : Fin coarse.cells)
    (hi : refined.cell k ⊆ coarse.cell i)
    (hj : refined.cell k ⊆ coarse.cell j) : i = j := by
  by_contra hne
  have hrefined : refined.point k.castSucc < refined.point k.succ :=
    refined.strictMono Fin.castSucc_lt_succ
  have hik := hi ⟨le_rfl,
    (refined.strictMono Fin.castSucc_lt_succ).le⟩
  have hjk := hj ⟨le_rfl,
    (refined.strictMono Fin.castSucc_lt_succ).le⟩
  have hik' := hi ⟨(refined.strictMono Fin.castSucc_lt_succ).le, le_rfl⟩
  have hjk' := hj ⟨(refined.strictMono Fin.castSucc_lt_succ).le, le_rfl⟩
  rcases lt_or_gt_of_ne hne with hij | hji
  · have hindex : i.succ ≤ j.castSucc := by
      change i.val + 1 ≤ j.val
      exact hij
    have hcoarse := coarse.strictMono.monotone hindex
    exact (not_lt_of_ge (hik'.2.trans (hcoarse.trans hjk.1))) hrefined
  · have hindex : j.succ ≤ i.castSucc := by
      change j.val + 1 ≤ i.val
      exact hji
    have hcoarse := coarse.strictMono.monotone hindex
    exact (not_lt_of_ge (hjk'.2.trans (hcoarse.trans hik.1))) hrefined

theorem commonRefinementLeftBlockCell_spec (s t : IntervalSubdivision)
    (i : Fin s.cells) (j : Fin (commonRefinementLeftBlockSize s t i)) :
    (commonRefinement s t).cell (commonRefinementLeftBlockCell s t i j) ⊆
      s.cell i := by
  intro x hx
  constructor
  · calc
      s.point i.castSucc = (commonRefinement s t).point
          (commonRefinementLeftVertex s t i.castSucc) :=
        (commonRefinementLeftVertex_spec s t i.castSucc).symm
      _ ≤ (commonRefinement s t).point
          (commonRefinementLeftBlockCell s t i j).castSucc := by
        apply (commonRefinement s t).strictMono.monotone
        change (commonRefinementLeftVertex s t i.castSucc).val ≤
          (commonRefinementLeftVertex s t i.castSucc).val + j.val
        omega
      _ ≤ x := hx.1
  · calc
      x ≤ (commonRefinement s t).point
          (commonRefinementLeftBlockCell s t i j).succ := hx.2
      _ ≤ (commonRefinement s t).point
          (commonRefinementLeftVertex s t i.succ) := by
        apply (commonRefinement s t).strictMono.monotone
        unfold commonRefinementLeftBlockCell commonRefinementLeftBlockSize
        dsimp only
        have h : (commonRefinementLeftVertex s t i.castSucc).val <
            (commonRefinementLeftVertex s t i.succ).val :=
          commonRefinementLeftVertex_strictMono s t Fin.castSucc_lt_succ
        have hj : j.val <
            (commonRefinementLeftVertex s t i.succ).val -
              (commonRefinementLeftVertex s t i.castSucc).val := by
          have hj' := j.isLt
          change j.val < commonRefinementLeftBlockSize s t i at hj'
          exact hj'
        change (commonRefinementLeftVertex s t i.castSucc).val + j.val + 1 ≤
          (commonRefinementLeftVertex s t i.succ).val
        omega
      _ = s.point i.succ := commonRefinementLeftVertex_spec s t i.succ

@[simp]
theorem commonRefinementLeftCell_blockCell (s t : IntervalSubdivision)
    (i : Fin s.cells) (j : Fin (commonRefinementLeftBlockSize s t i)) :
    commonRefinementLeftCell s t (commonRefinementLeftBlockCell s t i j) = i := by
  apply cell_container_unique s (commonRefinement s t)
    (commonRefinementLeftBlockCell s t i j)
  · exact commonRefinementLeftCell_spec s t _
  · exact commonRefinementLeftBlockCell_spec s t i j

/-- The ordered list of common-refinement cells inside one left cell. -/
def commonRefinementLeftBlockCells (s t : IntervalSubdivision)
    (i : Fin s.cells) : List (Fin (commonRefinement s t).cells) :=
  List.ofFn (commonRefinementLeftBlockCell s t i)

theorem commonRefinementLeftBlockCells_map_val (s t : IntervalSubdivision)
    (i : Fin s.cells) :
    (commonRefinementLeftBlockCells s t i).map Fin.val =
      List.range' (commonRefinementLeftVertex s t i.castSucc).val
        (commonRefinementLeftBlockSize s t i) := by
  apply List.ext_getElem
  · simp [commonRefinementLeftBlockCells]
  · intro n hn₁ hn₂
    simp only [commonRefinementLeftBlockCells] at hn₁ ⊢
    rw [List.getElem_map, List.getElem_ofFn, List.getElem_range']
    simp [commonRefinementLeftBlockCell]

/-- The ordered left-cell blocks partition all common-refinement cells. -/
theorem commonRefinementLeftBlockCells_flatten (s t : IntervalSubdivision) :
    (List.ofFn fun i : Fin s.cells ↦
      commonRefinementLeftBlockCells s t i).flatten =
      List.ofFn (id : Fin (commonRefinement s t).cells →
        Fin (commonRefinement s t).cells) := by
  apply (List.map_injective_iff.mpr Fin.val_injective)
  rw [List.map_flatten]
  simp only [List.map_ofFn]
  change (List.ofFn fun i : Fin s.cells ↦
      (commonRefinementLeftBlockCells s t i).map Fin.val).flatten =
    List.ofFn (fun k : Fin (commonRefinement s t).cells ↦ k.val)
  simp_rw [commonRefinementLeftBlockCells_map_val]
  simp only [commonRefinementLeftBlockSize]
  rw [flatten_rangeBlocks
    (fun j ↦ (commonRefinementLeftVertex s t j).val)]
  · simp only [commonRefinementLeftVertex_zero,
      commonRefinementLeftVertex_last, Fin.val_last]
    change List.range' 0 (commonRefinement s t).cells =
      List.ofFn (fun k : Fin (commonRefinement s t).cells ↦ k.val)
    rw [← List.range_eq_range', range_eq_ofFn_val]
  · exact fun _ _ h ↦ commonRefinementLeftVertex_strictMono s t h

/-- The index in the common refinement of a vertex of the right subdivision. -/
noncomputable def commonRefinementRightVertex (s t : IntervalSubdivision)
    (j : Fin (t.cells + 1)) : Fin ((commonRefinement s t).cells + 1) := by
  have hj : t.point j ∈ (commonRefinement s t).vertices :=
    vertices_subset_commonRefinement_right s t <|
      Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  rw [vertices] at hj
  exact Classical.choose (Finset.mem_image.mp hj)

theorem commonRefinementRightVertex_spec (s t : IntervalSubdivision)
    (j : Fin (t.cells + 1)) :
    (commonRefinement s t).point (commonRefinementRightVertex s t j) =
      t.point j := by
  unfold commonRefinementRightVertex
  exact (Classical.choose_spec
    (Finset.mem_image.mp
      (vertices_subset_commonRefinement_right s t <|
        Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩))).2

theorem commonRefinementRightVertex_strictMono (s t : IntervalSubdivision) :
    StrictMono (commonRefinementRightVertex s t) := by
  intro i j hij
  apply (commonRefinement s t).strictMono.lt_iff_lt.mp
  rw [commonRefinementRightVertex_spec, commonRefinementRightVertex_spec]
  exact t.strictMono hij

@[simp]
theorem commonRefinementRightVertex_zero (s t : IntervalSubdivision) :
    commonRefinementRightVertex s t 0 = 0 := by
  apply (commonRefinement s t).strictMono.injective
  rw [commonRefinementRightVertex_spec, t.left, (commonRefinement s t).left]

@[simp]
theorem commonRefinementRightVertex_last (s t : IntervalSubdivision) :
    commonRefinementRightVertex s t (Fin.last t.cells) =
      Fin.last (commonRefinement s t).cells := by
  apply (commonRefinement s t).strictMono.injective
  rw [commonRefinementRightVertex_spec, t.right, (commonRefinement s t).right]

/-- The number of common-refinement cells contained in one right cell. -/
def commonRefinementRightBlockSize (s t : IntervalSubdivision)
    (i : Fin t.cells) : ℕ :=
  (commonRefinementRightVertex s t i.succ).val -
    (commonRefinementRightVertex s t i.castSucc).val

theorem commonRefinementRightBlockSize_pos (s t : IntervalSubdivision)
    (i : Fin t.cells) : 0 < commonRefinementRightBlockSize s t i := by
  unfold commonRefinementRightBlockSize
  have h : commonRefinementRightVertex s t i.castSucc <
      commonRefinementRightVertex s t i.succ :=
    commonRefinementRightVertex_strictMono s t Fin.castSucc_lt_succ
  omega

/-- The `j`th refined cell inside the `i`th cell of the right subdivision. -/
def commonRefinementRightBlockCell (s t : IntervalSubdivision)
    (i : Fin t.cells) (j : Fin (commonRefinementRightBlockSize s t i)) :
    Fin (commonRefinement s t).cells := by
  let a := commonRefinementRightVertex s t i.castSucc
  let b := commonRefinementRightVertex s t i.succ
  refine ⟨a.val + j.val, ?_⟩
  have hab : a.val < b.val := by
    exact commonRefinementRightVertex_strictMono s t Fin.castSucc_lt_succ
  have hj : j.val < b.val - a.val := j.isLt
  have hb : b.val ≤ (commonRefinement s t).cells := Nat.le_of_lt_succ b.isLt
  omega

/-- The `j`th refined vertex spanning the `i`th cell of the right subdivision. -/
def commonRefinementRightBlockVertex (s t : IntervalSubdivision)
    (i : Fin t.cells)
    (j : Fin (commonRefinementRightBlockSize s t i + 1)) :
    Fin ((commonRefinement s t).cells + 1) := by
  let a := commonRefinementRightVertex s t i.castSucc
  let b := commonRefinementRightVertex s t i.succ
  refine ⟨a.val + j.val, ?_⟩
  have hab : a.val < b.val := by
    exact commonRefinementRightVertex_strictMono s t Fin.castSucc_lt_succ
  have hj : j.val < (b.val - a.val) + 1 := j.isLt
  have hb : b.val < (commonRefinement s t).cells + 1 := b.isLt
  omega

@[simp]
theorem commonRefinementRightBlockVertex_zero (s t : IntervalSubdivision)
    (i : Fin t.cells) :
    commonRefinementRightBlockVertex s t i 0 =
      commonRefinementRightVertex s t i.castSucc := by
  apply Fin.ext
  rfl

@[simp]
theorem commonRefinementRightBlockVertex_last (s t : IntervalSubdivision)
    (i : Fin t.cells) :
    commonRefinementRightBlockVertex s t i
        (Fin.last (commonRefinementRightBlockSize s t i)) =
      commonRefinementRightVertex s t i.succ := by
  apply Fin.ext
  unfold commonRefinementRightBlockVertex commonRefinementRightBlockSize
  dsimp only
  have h : commonRefinementRightVertex s t i.castSucc <
      commonRefinementRightVertex s t i.succ :=
    commonRefinementRightVertex_strictMono s t Fin.castSucc_lt_succ
  change (commonRefinementRightVertex s t i.castSucc).val +
      ((commonRefinementRightVertex s t i.succ).val -
        (commonRefinementRightVertex s t i.castSucc).val) =
    (commonRefinementRightVertex s t i.succ).val
  exact Nat.add_sub_of_le (Nat.le_of_lt h)

@[simp]
theorem commonRefinementRightBlockVertex_castSucc (s t : IntervalSubdivision)
    (i : Fin t.cells) (j : Fin (commonRefinementRightBlockSize s t i)) :
    commonRefinementRightBlockVertex s t i j.castSucc =
      (commonRefinementRightBlockCell s t i j).castSucc := by
  apply Fin.ext
  rfl

@[simp]
theorem commonRefinementRightBlockVertex_succ (s t : IntervalSubdivision)
    (i : Fin t.cells) (j : Fin (commonRefinementRightBlockSize s t i)) :
    commonRefinementRightBlockVertex s t i j.succ =
      (commonRefinementRightBlockCell s t i j).succ := by
  apply Fin.ext
  rfl

theorem commonRefinementRightBlockPoint_zero (s t : IntervalSubdivision)
    (i : Fin t.cells) :
    (commonRefinement s t).point
        (commonRefinementRightBlockVertex s t i 0) = t.point i.castSucc := by
  rw [commonRefinementRightBlockVertex_zero,
    commonRefinementRightVertex_spec]

theorem commonRefinementRightBlockPoint_last (s t : IntervalSubdivision)
    (i : Fin t.cells) :
    (commonRefinement s t).point
        (commonRefinementRightBlockVertex s t i
          (Fin.last (commonRefinementRightBlockSize s t i))) =
      t.point i.succ := by
  rw [commonRefinementRightBlockVertex_last,
    commonRefinementRightVertex_spec]

theorem commonRefinementRightBlockCell_spec (s t : IntervalSubdivision)
    (i : Fin t.cells) (j : Fin (commonRefinementRightBlockSize s t i)) :
    (commonRefinement s t).cell (commonRefinementRightBlockCell s t i j) ⊆
      t.cell i := by
  intro x hx
  constructor
  · calc
      t.point i.castSucc = (commonRefinement s t).point
          (commonRefinementRightVertex s t i.castSucc) :=
        (commonRefinementRightVertex_spec s t i.castSucc).symm
      _ ≤ (commonRefinement s t).point
          (commonRefinementRightBlockCell s t i j).castSucc := by
        apply (commonRefinement s t).strictMono.monotone
        change (commonRefinementRightVertex s t i.castSucc).val ≤
          (commonRefinementRightVertex s t i.castSucc).val + j.val
        omega
      _ ≤ x := hx.1
  · calc
      x ≤ (commonRefinement s t).point
          (commonRefinementRightBlockCell s t i j).succ := hx.2
      _ ≤ (commonRefinement s t).point
          (commonRefinementRightVertex s t i.succ) := by
        apply (commonRefinement s t).strictMono.monotone
        unfold commonRefinementRightBlockCell commonRefinementRightBlockSize
        dsimp only
        have h : (commonRefinementRightVertex s t i.castSucc).val <
            (commonRefinementRightVertex s t i.succ).val :=
          commonRefinementRightVertex_strictMono s t Fin.castSucc_lt_succ
        have hj : j.val <
            (commonRefinementRightVertex s t i.succ).val -
              (commonRefinementRightVertex s t i.castSucc).val := by
          have hj' := j.isLt
          change j.val < commonRefinementRightBlockSize s t i at hj'
          exact hj'
        change (commonRefinementRightVertex s t i.castSucc).val + j.val + 1 ≤
          (commonRefinementRightVertex s t i.succ).val
        omega
      _ = t.point i.succ := commonRefinementRightVertex_spec s t i.succ

@[simp]
theorem commonRefinementRightCell_blockCell (s t : IntervalSubdivision)
    (i : Fin t.cells) (j : Fin (commonRefinementRightBlockSize s t i)) :
    commonRefinementRightCell s t (commonRefinementRightBlockCell s t i j) = i := by
  apply cell_container_unique t (commonRefinement s t)
    (commonRefinementRightBlockCell s t i j)
  · exact commonRefinementRightCell_spec s t _
  · exact commonRefinementRightBlockCell_spec s t i j

/-- The ordered list of common-refinement cells inside one right cell. -/
def commonRefinementRightBlockCells (s t : IntervalSubdivision)
    (i : Fin t.cells) : List (Fin (commonRefinement s t).cells) :=
  List.ofFn (commonRefinementRightBlockCell s t i)

theorem commonRefinementRightBlockCells_map_val (s t : IntervalSubdivision)
    (i : Fin t.cells) :
    (commonRefinementRightBlockCells s t i).map Fin.val =
      List.range' (commonRefinementRightVertex s t i.castSucc).val
        (commonRefinementRightBlockSize s t i) := by
  apply List.ext_getElem
  · simp [commonRefinementRightBlockCells]
  · intro n hn₁ hn₂
    simp only [commonRefinementRightBlockCells] at hn₁ ⊢
    rw [List.getElem_map, List.getElem_ofFn, List.getElem_range']
    simp [commonRefinementRightBlockCell]

/-- The ordered right-cell blocks partition all common-refinement cells. -/
theorem commonRefinementRightBlockCells_flatten (s t : IntervalSubdivision) :
    (List.ofFn fun i : Fin t.cells ↦
      commonRefinementRightBlockCells s t i).flatten =
      List.ofFn (id : Fin (commonRefinement s t).cells →
        Fin (commonRefinement s t).cells) := by
  apply (List.map_injective_iff.mpr Fin.val_injective)
  rw [List.map_flatten]
  simp only [List.map_ofFn]
  change (List.ofFn fun i : Fin t.cells ↦
      (commonRefinementRightBlockCells s t i).map Fin.val).flatten =
    List.ofFn (fun k : Fin (commonRefinement s t).cells ↦ k.val)
  simp_rw [commonRefinementRightBlockCells_map_val]
  simp only [commonRefinementRightBlockSize]
  rw [flatten_rangeBlocks
    (fun j ↦ (commonRefinementRightVertex s t j).val)]
  · simp only [commonRefinementRightVertex_zero,
      commonRefinementRightVertex_last, Fin.val_last]
    change List.range' 0 (commonRefinement s t).cells =
      List.ofFn (fun k : Fin (commonRefinement s t).cells ↦ k.val)
    rw [← List.range_eq_range', range_eq_ofFn_val]
  · exact fun _ _ h ↦ commonRefinementRightVertex_strictMono s t h

end IntervalSubdivision

end Hatcher.VanKampen
