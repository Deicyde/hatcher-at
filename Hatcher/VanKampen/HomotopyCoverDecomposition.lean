import Hatcher.VanKampen.CoverFactorization
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Subpath
import Mathlib.Topology.UnitInterval

noncomputable section

open Set
open scoped unitInterval

namespace Hatcher.VanKampen

universe u v

/-- A finite nondegenerate subdivision of the unit interval. -/
structure IntervalSubdivision where
  cells : ℕ
  point : Fin (cells + 1) → I
  left : point 0 = 0
  right : point (Fin.last cells) = 1
  strictMono : StrictMono point

namespace IntervalSubdivision

def cell (s : IntervalSubdivision) (k : Fin s.cells) : Set I :=
  Icc (s.point k.castSucc) (s.point k.succ)

def vertices (s : IntervalSubdivision) : Finset I :=
  Finset.univ.image s.point

def interiorVertices (s : IntervalSubdivision) : Finset I :=
  (s.vertices.erase 0).erase 1

def commonVertices (s t : IntervalSubdivision) : Finset I :=
  s.vertices ∪ t.vertices

theorem zero_mem_vertices (s : IntervalSubdivision) : 0 ∈ s.vertices := by
  rw [vertices]
  exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, s.left⟩

theorem one_mem_vertices (s : IntervalSubdivision) : 1 ∈ s.vertices := by
  rw [vertices]
  exact Finset.mem_image.mpr
    ⟨Fin.last s.cells, Finset.mem_univ _, s.right⟩

theorem cells_pos (s : IntervalSubdivision) : 0 < s.cells := by
  by_contra h
  have hc : s.cells = 0 := Nat.eq_zero_of_not_pos h
  have hi : (0 : Fin (s.cells + 1)) = Fin.last s.cells := by
    apply Fin.ext
    simp [hc]
  have hzero_one : (0 : I) = 1 :=
    s.left.symm.trans ((congrArg s.point hi).trans s.right)
  exact zero_ne_one hzero_one

/-- Every point of the unit interval belongs to a cell of a strict
subdivision. -/
theorem exists_mem_cell (s : IntervalSubdivision) (x : I) :
    ∃ k : Fin s.cells, x ∈ s.cell k := by
  let p : Fin (s.cells + 1) → Prop := fun j ↦ x ≤ s.point j
  have hp : ∃ j, p j := by
    refine ⟨Fin.last s.cells, ?_⟩
    change x ≤ s.point (Fin.last s.cells)
    rw [s.right]
    exact le_top
  let j := Fin.find p hp
  by_cases hj0 : j = 0
  · have hx0 : x = 0 := by
      apply le_antisymm
      · have := Fin.find_spec hp
        change x ≤ s.point j at this
        rw [hj0, s.left] at this
        exact this
      · exact bot_le
    refine ⟨⟨0, s.cells_pos⟩, ?_⟩
    rw [cell, hx0]
    constructor
    · rw [show (⟨0, s.cells_pos⟩ : Fin s.cells).castSucc = 0 by rfl, s.left]
    · exact bot_le
  · obtain ⟨k, hk⟩ := Fin.exists_succ_eq.mpr hj0
    refine ⟨k, ?_⟩
    rw [cell]
    constructor
    · have hklt : k.castSucc < j := by
        rw [← hk]
        exact Fin.castSucc_lt_succ
      have hnot := Fin.find_min hp hklt
      change ¬x ≤ s.point k.castSucc at hnot
      exact le_of_lt (lt_of_not_ge hnot)
    · have := Fin.find_spec hp
      change x ≤ s.point j at this
      rwa [← hk] at this

theorem one_le_card_commonVertices (s t : IntervalSubdivision) :
    1 ≤ (commonVertices s t).card := by
  rw [Finset.one_le_card]
  exact ⟨0, Finset.mem_union_left _ s.zero_mem_vertices⟩

/-- The subdivision whose vertices are exactly the union of two subdivisions'
vertices. -/
def commonRefinement (s t : IntervalSubdivision) : IntervalSubdivision := by
  let V := commonVertices s t
  have hcardPos : 0 < V.card := one_le_card_commonVertices s t
  have hcard : V.card = (V.card - 1) + 1 :=
    (Nat.sub_add_cancel hcardPos).symm
  refine
    { cells := V.card - 1
      point := V.orderEmbOfFin hcard
      left := ?_
      right := ?_
      strictMono := (V.orderEmbOfFin hcard).strictMono }
  · change V.orderEmbOfFin hcard ⟨0, by omega⟩ = 0
    rw [Finset.orderEmbOfFin_zero hcard]
    apply le_antisymm
    · exact Finset.min'_le V 0
        (Finset.mem_union_left _ s.zero_mem_vertices)
    · exact bot_le
  · have hkpos : 0 < (V.card - 1) + 1 := by omega
    change V.orderEmbOfFin hcard (Fin.last (V.card - 1)) = 1
    rw [show Fin.last (V.card - 1) =
        ⟨((V.card - 1) + 1) - 1, Nat.sub_lt hkpos (by omega)⟩ by
          apply Fin.ext
          simp]
    rw [Finset.orderEmbOfFin_last hcard hkpos]
    apply le_antisymm
    · exact le_top
    · exact Finset.le_max' V 1
        (Finset.mem_union_left _ s.one_mem_vertices)

theorem vertices_commonRefinement (s t : IntervalSubdivision) :
    (commonRefinement s t).vertices = commonVertices s t := by
  unfold vertices commonRefinement
  dsimp only
  exact Finset.image_orderEmbOfFin_univ _ _

theorem vertices_subset_commonRefinement_left (s t : IntervalSubdivision) :
    s.vertices ⊆ (commonRefinement s t).vertices := by
  rw [vertices_commonRefinement]
  exact Finset.subset_union_left

theorem vertices_subset_commonRefinement_right (s t : IntervalSubdivision) :
    t.vertices ⊆ (commonRefinement s t).vertices := by
  rw [vertices_commonRefinement]
  exact Finset.subset_union_right

/-- No vertex of either original subdivision lies strictly inside a cell of
their common refinement. -/
theorem not_mem_Ioo_of_mem_commonVertices (s t : IntervalSubdivision)
    (k : Fin (commonRefinement s t).cells) (x : I)
    (hx : x ∈ commonVertices s t) :
    x ∉ Ioo ((commonRefinement s t).point k.castSucc)
      ((commonRefinement s t).point k.succ) := by
  intro hxIoo
  have hxv : x ∈ (commonRefinement s t).vertices := by
    rw [vertices_commonRefinement]
    exact hx
  rw [vertices] at hxv
  obtain ⟨j, _hj, rfl⟩ := Finset.mem_image.mp hxv
  have hleft : k.castSucc < j := by
    by_contra h
    exact (not_lt_of_ge ((commonRefinement s t).strictMono.monotone
      (le_of_not_gt h))) hxIoo.1
  have hright : j < k.succ := by
    by_contra h
    exact (not_lt_of_ge ((commonRefinement s t).strictMono.monotone
      (le_of_not_gt h))) hxIoo.2
  have hleft' : k.val + 1 ≤ j.val := by
    exact hleft
  have hright' : j.val < k.val + 1 := by
    exact hright
  exact (not_lt_of_ge hleft') hright'

/-- If all vertices of `q` occur in the common refinement of `s` and `t`,
then every common-refinement cell lies in a cell of `q`. -/
theorem commonRefinement_cell_subset_of_vertices_subset
    (s t q : IntervalSubdivision) (hq : q.vertices ⊆ commonVertices s t)
    (k : Fin (commonRefinement s t).cells) :
    ∃ i : Fin q.cells, (commonRefinement s t).cell k ⊆ q.cell i := by
  let r := commonRefinement s t
  have hab : r.point k.castSucc < r.point k.succ :=
    r.strictMono Fin.castSucc_lt_succ
  obtain ⟨y, hay, hyb⟩ := exists_between hab
  obtain ⟨i, hycell⟩ := q.exists_mem_cell y
  refine ⟨i, Icc_subset_Icc ?_ ?_⟩
  · by_contra hle
    have hinside : q.point i.castSucc ∈
        Ioo (r.point k.castSucc) (r.point k.succ) :=
      ⟨lt_of_not_ge hle, hycell.1.trans_lt hyb⟩
    exact not_mem_Ioo_of_mem_commonVertices s t k (q.point i.castSucc)
      (hq <| Finset.mem_image.mpr
        ⟨i.castSucc, Finset.mem_univ _, rfl⟩) hinside
  · by_contra hle
    have hinside : q.point i.succ ∈
        Ioo (r.point k.castSucc) (r.point k.succ) :=
      ⟨hay.trans_le hycell.2, lt_of_not_ge hle⟩
    exact not_mem_Ioo_of_mem_commonVertices s t k (q.point i.succ)
      (hq <| Finset.mem_image.mpr
        ⟨i.succ, Finset.mem_univ _, rfl⟩) hinside

theorem commonRefinement_cell_subset_left (s t : IntervalSubdivision)
    (k : Fin (commonRefinement s t).cells) :
    ∃ i : Fin s.cells, (commonRefinement s t).cell k ⊆ s.cell i := by
  exact commonRefinement_cell_subset_of_vertices_subset s t s
    Finset.subset_union_left k

theorem commonRefinement_cell_subset_right (s t : IntervalSubdivision)
    (k : Fin (commonRefinement s t).cells) :
    ∃ i : Fin t.cells, (commonRefinement s t).cell k ⊆ t.cell i := by
  exact commonRefinement_cell_subset_of_vertices_subset s t t
    Finset.subset_union_right k

noncomputable def commonRefinementLeftCell (s t : IntervalSubdivision)
    (k : Fin (commonRefinement s t).cells) : Fin s.cells :=
  Classical.choose (commonRefinement_cell_subset_left s t k)

theorem commonRefinementLeftCell_spec (s t : IntervalSubdivision)
    (k : Fin (commonRefinement s t).cells) :
    (commonRefinement s t).cell k ⊆ s.cell (commonRefinementLeftCell s t k) :=
  Classical.choose_spec (commonRefinement_cell_subset_left s t k)

noncomputable def commonRefinementRightCell (s t : IntervalSubdivision)
    (k : Fin (commonRefinement s t).cells) : Fin t.cells :=
  Classical.choose (commonRefinement_cell_subset_right s t k)

theorem commonRefinementRightCell_spec (s t : IntervalSubdivision)
    (k : Fin (commonRefinement s t).cells) :
    (commonRefinement s t).cell k ⊆ t.cell (commonRefinementRightCell s t k) :=
  Classical.choose_spec (commonRefinement_cell_subset_right s t k)

theorem interiorVertices_disjoint_of_point_not_mem
    (s : IntervalSubdivision) (forbidden : Finset I)
    (havoid : ∀ k, k ≠ 0 → k ≠ Fin.last s.cells → s.point k ∉ forbidden) :
    Disjoint s.interiorVertices forbidden := by
  rw [Finset.disjoint_left]
  intro x hx hxf
  have hx' : x ∈ (s.vertices.erase 0).erase 1 := hx
  have hx1 : x ≠ 1 := (Finset.mem_erase.mp hx').1
  have hx0 : x ≠ 0 := (Finset.mem_erase.mp (Finset.mem_erase.mp hx').2).1
  have hxv : x ∈ s.vertices :=
    (Finset.mem_erase.mp (Finset.mem_erase.mp hx').2).2
  rcases Finset.mem_image.mp hxv with ⟨k, -, rfl⟩
  have hk0 : k ≠ 0 := by
    intro hk
    subst k
    exact hx0 s.left
  have hklast : k ≠ Fin.last s.cells := by
    intro hk
    subst k
    exact hx1 s.right
  exact havoid k hk0 hklast hxf

/-- The cells of a subdivision whose closed interval contains `x`. -/
noncomputable def incidentCells (s : IntervalSubdivision) (x : I) :
    Finset (Fin s.cells) := by
  classical
  exact Finset.univ.filter fun k ↦ x ∈ s.cell k

@[simp]
theorem mem_incidentCells (s : IntervalSubdivision) (x : I) (k : Fin s.cells) :
    k ∈ s.incidentCells x ↔ x ∈ s.cell k := by
  simp [incidentCells]

/-- At most two closed cells in a strict interval subdivision contain one point. -/
theorem card_incidentCells_le_two (s : IntervalSubdivision) (x : I) :
    (s.incidentCells x).card ≤ 2 := by
  classical
  by_cases hne : (s.incidentCells x).Nonempty
  · let a := (s.incidentCells x).min' hne
    let b := (s.incidentCells x).max' hne
    have ha : a ∈ s.incidentCells x := Finset.min'_mem _ _
    have hb : b ∈ s.incidentCells x := Finset.max'_mem _ _
    have hax : x ∈ s.cell a := (s.mem_incidentCells x a).mp ha
    have hbx : x ∈ s.cell b := (s.mem_incidentCells x b).mp hb
    have hab : b.val ≤ a.val + 1 := by
      by_contra h
      have hlt : a.succ < b.castSucc := by
        change a.val + 1 < b.val
        omega
      have hp : s.point a.succ < s.point b.castSucc := s.strictMono hlt
      exact (not_lt_of_ge hbx.1) (hax.2.trans_lt hp)
    have hsub : s.incidentCells x ⊆ {a, b} := by
      intro k hk
      have hak : a ≤ k := Finset.min'_le _ _ hk
      have hkb : k ≤ b := Finset.le_max' _ _ hk
      have hka' : a.val ≤ k.val := hak
      have hkb' : k.val ≤ b.val := hkb
      have hkval : k.val = a.val ∨ k.val = b.val := by omega
      rcases hkval with hkval | hkval
      · simp [Fin.ext hkval]
      · simp [Fin.ext hkval]
    exact (Finset.card_le_card hsub).trans Finset.card_le_two
  · simp only [Finset.not_nonempty_iff_eq_empty] at hne
    simp [hne]

/-- Away from an interior subdivision vertex, at most one closed cell contains
the point. -/
theorem card_incidentCells_le_one_of_not_mem_interior
    (s : IntervalSubdivision) (x : I) (hx : x ∉ s.interiorVertices) :
    (s.incidentCells x).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  have hax : x ∈ s.cell a := (s.mem_incidentCells x a).mp ha
  have hbx : x ∈ s.cell b := (s.mem_incidentCells x b).mp hb
  by_contra hne
  have contra {a b : Fin s.cells}
      (hax : x ∈ s.cell a) (hbx : x ∈ s.cell b) (hab : a < b) : False := by
    have hstep : b.val = a.val + 1 := by
      by_contra hstep
      have hlt : a.succ < b.castSucc := by
        change a.val + 1 < b.val
        omega
      have hp : s.point a.succ < s.point b.castSucc := s.strictMono hlt
      exact (not_lt_of_ge hbx.1) (hax.2.trans_lt hp)
    have heq : a.succ = b.castSucc := Fin.ext hstep.symm
    have hvertex : x = s.point b.castSucc := by
      apply le_antisymm
      · simpa [← heq] using hax.2
      · exact hbx.1
    apply hx
    rw [interiorVertices, Finset.mem_erase, Finset.mem_erase]
    refine ⟨?_, ?_, Finset.mem_image.mpr
      ⟨b.castSucc, Finset.mem_univ _, hvertex.symm⟩⟩
    · have hlt : b.castSucc < Fin.last s.cells := by
        change b.val < s.cells
        exact b.isLt
      have hp : s.point b.castSucc < s.point (Fin.last s.cells) :=
        s.strictMono hlt
      rw [s.right] at hp
      exact hvertex.symm ▸ ne_of_lt hp
    · have hbpos : 0 < b.val := by omega
      have hlt : (0 : Fin (s.cells + 1)) < b.castSucc := by
        exact_mod_cast hbpos
      have hp : s.point 0 < s.point b.castSucc := s.strictMono hlt
      rw [s.left] at hp
      exact hvertex.symm ▸ ne_of_gt hp
  rcases lt_or_gt_of_ne hne with hab | hba
  · exact (contra hax hbx hab).elim
  · exact (contra hbx hax hba).elim

/-- A finite forbidden set cannot exhaust a nonempty open interval. -/
theorem exists_mem_Ioo_not_mem_finset (a b : I) (h : a < b)
    (forbidden : Finset I) :
    ∃ x ∈ Ioo a b, x ∉ forbidden := by
  obtain ⟨x, hx, hxf⟩ :=
    ((Set.Ioo_infinite h).sdiff forbidden.finite_toSet).nonempty
  exact ⟨x, hx, by simpa using hxf⟩

namespace FineMesh

/-- Left endpoint of the `j`th perturbation window in a uniform mesh with
`m + 1` interior vertices. -/
def windowLeft (m : ℕ) (j : Fin (m + 1)) : I :=
  ⟨(j : ℝ) / (m + 2), by positivity, by
    rw [div_le_one (by positivity : (0 : ℝ) < m + 2)]
    norm_cast
    omega⟩

/-- Right endpoint of the `j`th perturbation window. -/
def windowRight (m : ℕ) (j : Fin (m + 1)) : I :=
  ⟨((j : ℝ) + 1) / (m + 2), by positivity, by
    rw [div_le_one (by positivity : (0 : ℝ) < m + 2)]
    norm_cast
    omega⟩

theorem windowLeft_lt_windowRight (m : ℕ) (j : Fin (m + 1)) :
    windowLeft m j < windowRight m j := by
  change (j : ℝ) / (m + 2) < ((j : ℝ) + 1) / (m + 2)
  exact (div_lt_div_iff_of_pos_right (by positivity : (0 : ℝ) < m + 2)).2
    (by linarith)

/-- An interior mesh point chosen away from `forbidden`. -/
def choice (m : ℕ) (forbidden : Finset I) (j : Fin (m + 1)) : I :=
  Classical.choose
    (exists_mem_Ioo_not_mem_finset (windowLeft m j) (windowRight m j)
      (windowLeft_lt_windowRight m j) forbidden)

theorem choice_spec (m : ℕ) (forbidden : Finset I) (j : Fin (m + 1)) :
    choice m forbidden j ∈ Ioo (windowLeft m j) (windowRight m j) ∧
      choice m forbidden j ∉ forbidden :=
  Classical.choose_spec
    (exists_mem_Ioo_not_mem_finset (windowLeft m j) (windowRight m j)
      (windowLeft_lt_windowRight m j) forbidden)

/-- Uniformly spaced windows, independently perturbed away from a finite set,
with the two endpoints inserted. -/
def point (m : ℕ) (forbidden : Finset I) : Fin (m + 3) → I :=
  Fin.cases 0 (Fin.lastCases 1 (choice m forbidden))

@[simp] theorem point_zero (m : ℕ) (forbidden : Finset I) :
    point m forbidden 0 = 0 := rfl

@[simp] theorem point_interior (m : ℕ) (forbidden : Finset I)
    (j : Fin (m + 1)) :
    point m forbidden j.castSucc.succ = choice m forbidden j := by
  simp [point]

@[simp] theorem point_last (m : ℕ) (forbidden : Finset I) :
    point m forbidden (Fin.last (m + 2)) = 1 := by
  rw [show Fin.last (m + 2) = (Fin.last (m + 1)).succ by rfl]
  unfold point
  rw [Fin.cases_succ, Fin.lastCases_last]

theorem point_strictMono (m : ℕ) (forbidden : Finset I) :
    StrictMono (point m forbidden) := by
  rw [Fin.strictMono_iff_lt_succ]
  intro k
  refine Fin.cases ?_ (fun i ↦ ?_) k
  · rw [show (0 : Fin (m + 2)).castSucc = 0 by rfl]
    rw [show (0 : Fin (m + 2)).succ = (0 : Fin (m + 1)).castSucc.succ by rfl]
    simp only [point_zero, point_interior]
    simpa [windowLeft] using (choice_spec m forbidden 0).1.1
  · refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · rw [show (Fin.last m).succ.succ = Fin.last (m + 2) by rfl]
      rw [show (Fin.last m).succ.castSucc =
        (Fin.last m).castSucc.succ by rfl]
      simp only [point_last, point_interior]
      exact (choice_spec m forbidden (Fin.last m)).1.2.trans_le
        (show windowRight m (Fin.last m) ≤ (1 : I) by exact le_top)
    · rw [show j.castSucc.succ.castSucc = j.castSucc.castSucc.succ by rfl]
      rw [show j.castSucc.succ.succ = j.succ.castSucc.succ by rfl]
      simp only [point_interior]
      exact (choice_spec m forbidden j.castSucc).1.2.trans
        (by simpa [windowRight, windowLeft] using
          (choice_spec m forbidden j.succ).1.1)

theorem point_interior_avoids (m : ℕ) (forbidden : Finset I)
    (j : Fin (m + 1)) :
    point m forbidden j.castSucc.succ ∉ forbidden := by
  simpa using (choice_spec m forbidden j).2

/-- Every consecutive gap is smaller than twice the uniform window width. -/
theorem point_gap_lt (m : ℕ) (forbidden : Finset I) (k : Fin (m + 2)) :
    ((point m forbidden k.succ : I) : ℝ) - point m forbidden k.castSucc <
      (2 : ℝ) / (m + 2) := by
  have hden : (0 : ℝ) < m + 2 := by positivity
  refine Fin.cases ?_ (fun i ↦ ?_) k
  · rw [show (0 : Fin (m + 2)).castSucc = 0 by rfl]
    rw [show (0 : Fin (m + 2)).succ = (0 : Fin (m + 1)).castSucc.succ by rfl]
    simp only [point_zero, point_interior]
    rw [show (((0 : I) : ℝ)) = 0 by rfl, sub_zero]
    have hu := (choice_spec m forbidden 0).1.2
    change ((choice m forbidden 0 : I) : ℝ) <
      ((windowRight m 0 : I) : ℝ) at hu
    simp [windowRight] at hu
    have h12 : (1 : ℝ) / (m + 2) < 2 / (m + 2) :=
      (div_lt_div_iff_of_pos_right hden).2 (by norm_num)
    exact hu.trans (by simpa [one_div] using h12)
  · refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · rw [show (Fin.last m).succ.succ = Fin.last (m + 2) by rfl]
      rw [show (Fin.last m).succ.castSucc =
        (Fin.last m).castSucc.succ by rfl]
      simp only [point_last, point_interior]
      change (1 : ℝ) - ((choice m forbidden (Fin.last m) : I) : ℝ) <
        2 / (m + 2)
      have hl := (choice_spec m forbidden (Fin.last m)).1.1
      change (m : ℝ) / (m + 2) <
        ((choice m forbidden (Fin.last m) : I) : ℝ) at hl
      have hid : (1 : ℝ) - (m : ℝ) / (m + 2) = 2 / (m + 2) := by
        field_simp
        ring
      linarith
    · rw [show j.castSucc.succ.castSucc = j.castSucc.castSucc.succ by rfl]
      rw [show j.castSucc.succ.succ = j.succ.castSucc.succ by rfl]
      simp only [point_interior]
      have hl := (choice_spec m forbidden j.castSucc).1.1
      have hu := (choice_spec m forbidden j.succ).1.2
      change (j : ℝ) / (m + 2) <
        ((choice m forbidden j.castSucc : I) : ℝ) at hl
      change ((choice m forbidden j.succ : I) : ℝ) <
        ((windowRight m j.succ : I) : ℝ) at hu
      simp [windowRight] at hu
      have hu' : ((choice m forbidden j.succ : I) : ℝ) <
          ((j : ℝ) + 2) / (m + 2) := by
        convert hu using 1
        all_goals ring
      have hid : ((j : ℝ) + 2) / (m + 2) - (j : ℝ) / (m + 2) =
          2 / (m + 2) := by
        field_simp
        ring
      linarith [hu']

/-- There is an arbitrarily fine strict subdivision whose interior vertices
avoid any prescribed finite set. -/
theorem exists_fine_point (forbidden : Finset I) {ε : ℝ} (hε : 0 < ε) :
    ∃ m : ℕ,
      point m forbidden 0 = 0 ∧
      point m forbidden (Fin.last (m + 2)) = 1 ∧
      StrictMono (point m forbidden) ∧
      (∀ j : Fin (m + 1), point m forbidden j.castSucc.succ ∉ forbidden) ∧
      ∀ k : Fin (m + 2),
        ((point m forbidden k.succ : I) : ℝ) - point m forbidden k.castSucc < ε := by
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt (half_pos hε)
  have hmono : (1 : ℝ) / (m + 2) ≤ 1 / (m + 1) :=
    one_div_le_one_div_of_le (by positivity) (by norm_num)
  have hsmall : (1 : ℝ) / (m + 2) < ε / 2 := hmono.trans_lt hm
  have hgap : (2 : ℝ) / (m + 2) < ε := by
    have hid : (2 : ℝ) / (m + 2) = 2 * (1 / (m + 2)) := by ring
    rw [hid]
    linarith
  refine ⟨m, point_zero _ _, point_last _ _, point_strictMono _ _,
    point_interior_avoids _ _, ?_⟩
  intro k
  exact (point_gap_lt m forbidden k).trans hgap

end FineMesh

end IntervalSubdivision

namespace IntervalSubdivision.FineMesh

/-- Package the explicit avoiding mesh as a strict subdivision. -/
def subdivision (m : ℕ) (forbidden : Finset I) : IntervalSubdivision where
  cells := m + 2
  point := point m forbidden
  left := point_zero m forbidden
  right := point_last m forbidden
  strictMono := point_strictMono m forbidden

theorem point_nonendpoint_avoids (m : ℕ) (forbidden : Finset I)
    (k : Fin (m + 3)) (hk0 : k ≠ 0) (hklast : k ≠ Fin.last (m + 2)) :
    point m forbidden k ∉ forbidden := by
  let j : Fin (m + 1) := ⟨k.val - 1, by
    have hklt : k.val < m + 2 := by
      have hkne : k.val ≠ m + 2 := by
        intro heq
        apply hklast
        apply Fin.ext
        simpa using heq
      have := k.isLt
      omega
    omega⟩
  have hk : k = j.castSucc.succ := by
    apply Fin.ext
    have hkpos : 0 < k.val := by
      have hkne : k.val ≠ 0 := by
        intro heq
        apply hk0
        apply Fin.ext
        simpa using heq
      omega
    simp [j]
    omega
  rw [hk]
  exact point_interior_avoids m forbidden j

theorem subdivision_interior_disjoint (m : ℕ) (forbidden : Finset I) :
    Disjoint (subdivision m forbidden).interiorVertices forbidden := by
  apply IntervalSubdivision.interiorVertices_disjoint_of_point_not_mem
  exact point_nonendpoint_avoids m forbidden

/-- Package the fine avoiding mesh theorem as a strict subdivision. -/
theorem exists_subdivision_avoiding (forbidden : Finset I) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ s : IntervalSubdivision,
      Disjoint s.interiorVertices forbidden ∧
      ∀ k : Fin s.cells,
        ((s.point k.succ : I) : ℝ) - s.point k.castSucc < ε := by
  obtain ⟨m, _hzero, _hone, _hmono, _havoid, hgap⟩ :=
    exists_fine_point forbidden hε
  exact ⟨subdivision m forbidden, subdivision_interior_disjoint m forbidden, hgap⟩

end IntervalSubdivision.FineMesh

namespace IntervalSubdivision

/-- A rectangle whose two coordinate widths are less than `ε` lies in the
`ε`-ball about its lower-left corner. -/
theorem unit_rectangle_subset_ball {a b c d : I} {ε : ℝ}
    (hx : (b : ℝ) - a < ε) (hy : (d : ℝ) - c < ε) :
    Icc a b ×ˢ Icc c d ⊆ Metric.ball (a, c) ε := by
  rintro ⟨x, y⟩ ⟨hxmem, hymem⟩
  rw [Metric.mem_ball]
  change max |(x : ℝ) - (a : ℝ)| |(y : ℝ) - (c : ℝ)| < ε
  rw [abs_of_nonneg (sub_nonneg.mpr (show (a : ℝ) ≤ x from hxmem.1)),
    abs_of_nonneg (sub_nonneg.mpr (show (c : ℝ) ≤ y from hymem.1))]
  exact max_lt
    (lt_of_le_of_lt
      (sub_le_sub_right (show (x : ℝ) ≤ b from hxmem.2) (a : ℝ)) hx)
    (lt_of_le_of_lt
      (sub_le_sub_right (show (y : ℝ) ≤ d from hymem.2) (c : ℝ)) hy)

end IntervalSubdivision

theorem exists_bottom_collar {K : Set I} {W : Set (I × I)}
    (hK : IsCompact K) (hW : IsOpen W)
    (hbase : {0} ×ˢ K ⊆ W) :
    ∃ b : I, 0 < b ∧ Icc 0 b ×ˢ K ⊆ W := by
  obtain ⟨u, v, hu, _hv, hzero, hKv, huv⟩ :=
    generalized_tube_lemma isCompact_singleton hK hW hbase
  have hzero_mem : (0 : I) ∈ u := hzero (by simp)
  obtain ⟨b, hzero_lt_b, hub⟩ :=
    exists_Ico_subset_of_mem_nhds (hu.mem_nhds hzero_mem)
      ⟨(1 : I), zero_lt_one⟩
  obtain ⟨c, hzero_lt_c, hcb⟩ := exists_between hzero_lt_b
  refine ⟨c, hzero_lt_c, ?_⟩
  exact (prod_mono ((Icc_subset_Ico_right hcb).trans hub) hKv).trans huv

theorem exists_top_collar {K : Set I} {W : Set (I × I)}
    (hK : IsCompact K) (hW : IsOpen W)
    (hbase : {1} ×ˢ K ⊆ W) :
    ∃ a : I, a < 1 ∧ Icc a 1 ×ˢ K ⊆ W := by
  obtain ⟨u, v, hu, _hv, hone, hKv, huv⟩ :=
    generalized_tube_lemma isCompact_singleton hK hW hbase
  have hone_mem : (1 : I) ∈ u := hone (by simp)
  obtain ⟨a, ha_lt_one, hua⟩ :=
    exists_Ioc_subset_of_mem_nhds (hu.mem_nhds hone_mem)
      ⟨(0 : I), zero_lt_one⟩
  obtain ⟨c, hac, hc_lt_one⟩ := exists_between ha_lt_one
  refine ⟨c, hc_lt_one, ?_⟩
  exact (prod_mono ((Icc_subset_Ioc_left hac).trans hua) hKv).trans huv

theorem exists_common_bottom_collar {κ : Type*} [Fintype κ] [Nonempty κ]
    (K : κ → Set I) (W : κ → Set (I × I))
    (hK : ∀ k, IsCompact (K k)) (hW : ∀ k, IsOpen (W k))
    (hbase : ∀ k, {0} ×ˢ K k ⊆ W k) :
    ∃ b : I, 0 < b ∧ ∀ k, Icc 0 b ×ˢ K k ⊆ W k := by
  choose b hbpos hbsub using fun k ↦ exists_bottom_collar (hK k) (hW k) (hbase k)
  let bmin : I := Finset.univ.inf' Finset.univ_nonempty b
  have hbmin : 0 < bmin := (Finset.lt_inf'_iff Finset.univ_nonempty).2
    (fun k _ ↦ hbpos k)
  refine ⟨bmin, hbmin, fun k ↦ ?_⟩
  have hle : bmin ≤ b k := Finset.inf'_le b (Finset.mem_univ k)
  exact (prod_mono (Icc_subset_Icc_right hle) Subset.rfl).trans (hbsub k)

theorem exists_common_top_collar {κ : Type*} [Fintype κ] [Nonempty κ]
    (K : κ → Set I) (W : κ → Set (I × I))
    (hK : ∀ k, IsCompact (K k)) (hW : ∀ k, IsOpen (W k))
    (hbase : ∀ k, {1} ×ˢ K k ⊆ W k) :
    ∃ a : I, a < 1 ∧ ∀ k, Icc a 1 ×ˢ K k ⊆ W k := by
  choose a hapos hasub using fun k ↦ exists_top_collar (hK k) (hW k) (hbase k)
  let amax : I := Finset.univ.sup' Finset.univ_nonempty a
  have hamax : amax < 1 := (Finset.sup'_lt_iff Finset.univ_nonempty).2
    (fun k _ ↦ hapos k)
  refine ⟨amax, hamax, fun k ↦ ?_⟩
  have hle : a k ≤ amax := Finset.le_sup' a (Finset.mem_univ k)
  exact (prod_mono (Icc_subset_Icc_left hle) Subset.rfl).trans (hasub k)

/-- Halving a unit-interval parameter. -/
def unitHalf (t : I) : I :=
  ⟨(t : ℝ) / 2, div_nonneg t.property.1 (by norm_num), by
    have := t.property.2
    linarith⟩

theorem unitHalf_strictMono : StrictMono unitHalf := by
  intro a b hab
  change (a : ℝ) / 2 < (b : ℝ) / 2
  exact (div_lt_div_iff_of_pos_right (by norm_num)).2 hab

@[simp] theorem unitHalf_zero : unitHalf 0 = 0 := by
  apply Subtype.ext
  norm_num [unitHalf]

@[simp] theorem unitHalf_one : unitHalf 1 = ⟨(1 : ℝ) / 2, by norm_num⟩ := by
  rfl

/-- Canonical cut points for Mathlib's right-associated-by-fold
`Path.concat`. For `n + 1` factors the cuts are
`0, 2⁻ⁿ, 2⁻⁽ⁿ⁻¹⁾, ..., 1/2, 1`. -/
def concatSubdivisionPoint : (n : ℕ) → Fin (n + 2) → I
  := fun n ↦ Nat.rec (motive := fun m ↦ Fin (m + 2) → I)
    (Fin.cases 0 (fun _ ↦ 1))
    (fun _ point ↦ Fin.lastCases 1 (fun k ↦ unitHalf (point k))) n

@[simp] theorem concatSubdivisionPoint_zero (n : ℕ) :
    concatSubdivisionPoint n 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [concatSubdivisionPoint]
      change Fin.lastCases (motive := fun _ : Fin (n + 3) ↦ I) (1 : I)
        (fun k ↦ unitHalf (concatSubdivisionPoint n k)) 0 = (0 : I)
      calc
        _ = unitHalf (concatSubdivisionPoint n (0 : Fin (n + 2))) := by
          convert Fin.lastCases_castSucc
            (motive := fun _ : Fin (n + 3) ↦ I) (last := (1 : I))
            (cast := fun k ↦ unitHalf (concatSubdivisionPoint n k))
            (0 : Fin (n + 2))
          congr 1
        _ = 0 := by rw [ih, unitHalf_zero]

@[simp] theorem concatSubdivisionPoint_last (n : ℕ) :
    concatSubdivisionPoint n (Fin.last (n + 1)) = 1 := by
  cases n with
  | zero => rfl
  | succ n => simp [concatSubdivisionPoint]

@[simp] theorem concatSubdivisionPoint_succ_cast
    (n : ℕ) (k : Fin (n + 2)) :
    concatSubdivisionPoint (n + 1) k.castSucc =
      unitHalf (concatSubdivisionPoint n k) := by
  simp [concatSubdivisionPoint]

theorem concatSubdivisionPoint_strictMono (n : ℕ) :
    StrictMono (concatSubdivisionPoint n) := by
  induction n with
  | zero =>
      rw [Fin.strictMono_iff_lt_succ]
      intro k
      fin_cases k
      change (0 : I) < 1
      exact zero_lt_one
  | succ n ih =>
      rw [Fin.strictMono_iff_lt_succ]
      intro k
      refine Fin.lastCases ?_ (fun j ↦ ?_) k
      · rw [show (Fin.last (n + 1)).succ = Fin.last (n + 2) by rfl]
        rw [show (Fin.last (n + 1)).castSucc =
          (Fin.last (n + 1)).castSucc by rfl]
        simp only [concatSubdivisionPoint_last, concatSubdivisionPoint_succ_cast]
        change (1 : ℝ) / 2 < 1
        norm_num
      · rw [show j.castSucc.castSucc = j.castSucc.castSucc by rfl]
        rw [show j.castSucc.succ = j.succ.castSucc by rfl]
        simp only [concatSubdivisionPoint_succ_cast]
        exact unitHalf_strictMono (ih Fin.castSucc_lt_succ)

/-- One factor, including the initial constant half introduced by
`Path.concat`, remains in the factor's assigned set. -/
theorem concat_one_mem {X : Type*} [TopologicalSpace X] {x₀ : X}
    (f : Fin 1 → Path x₀ x₀) (S : Fin 1 → Set X)
    (hx₀ : ∀ k, x₀ ∈ S k) (hf : ∀ k t, f k t ∈ S k) (t : I) :
    Path.concat (fun _ : Fin 2 ↦ x₀) f t ∈ S 0 := by
  rw [Path.concat_succ, Path.concat_zero]
  change ((Path.refl x₀).trans (f 0)) t ∈ S 0
  rw [Path.trans_apply]
  split_ifs
  · simpa using hx₀ 0
  · exact hf 0 _

/-- Each canonical dyadic cell of `Path.concat` is carried by the
corresponding factor. -/
theorem concat_mem_on_canonical_cell {X : Type*} [TopologicalSpace X]
    {x₀ : X} (n : ℕ) (f : Fin (n + 1) → Path x₀ x₀)
    (S : Fin (n + 1) → Set X)
    (hx₀ : ∀ k, x₀ ∈ S k) (hf : ∀ k t, f k t ∈ S k) :
    ∀ k : Fin (n + 1),
      Icc (concatSubdivisionPoint n k.castSucc)
          (concatSubdivisionPoint n k.succ) ⊆
        (Path.concat (fun _ : Fin (n + 2) ↦ x₀) f) ⁻¹' S k := by
  induction n with
  | zero =>
      intro k t ht
      fin_cases k
      exact concat_one_mem f S hx₀ hf t
  | succ n ih =>
      intro k
      refine Fin.lastCases ?_ (fun j ↦ ?_) k
      · intro t ht
        have htLower := ht.1
        rw [concatSubdivisionPoint_succ_cast,
          concatSubdivisionPoint_last, unitHalf_one] at htLower
        change (1 : ℝ) / 2 ≤ (t : ℝ) at htLower
        rw [Path.concat_succ]
        change ((Path.concat (fun _ : Fin (n + 2) ↦ x₀)
          (fun q ↦ f q.castSucc)).trans (f (Fin.last (n + 1)))) t ∈
            S (Fin.last (n + 1))
        rw [Path.trans_apply]
        split_ifs with htHalf
        · have htEq : (t : ℝ) = 1 / 2 := le_antisymm htHalf htLower
          have hq : (⟨2 * (t : ℝ),
              ⟨mul_nonneg (by norm_num) t.property.1, by linarith⟩⟩ : I) = 1 := by
            apply Subtype.ext
            simp [htEq]
          rw [hq, Path.target]
          exact hx₀ (Fin.last (n + 1))
        · exact hf (Fin.last (n + 1)) _
      · intro t ht
        have htLower := ht.1
        have htUpper := ht.2
        rw [concatSubdivisionPoint_succ_cast] at htLower
        rw [show j.castSucc.succ = j.succ.castSucc by rfl,
          concatSubdivisionPoint_succ_cast] at htUpper
        change ((concatSubdivisionPoint n j.castSucc : I) : ℝ) / 2 ≤
          (t : ℝ) at htLower
        change (t : ℝ) ≤
          ((concatSubdivisionPoint n j.succ : I) : ℝ) / 2 at htUpper
        have htHalf : (t : ℝ) ≤ 1 / 2 := by
          have hp : ((concatSubdivisionPoint n j.succ : I) : ℝ) ≤ 1 :=
            (concatSubdivisionPoint n j.succ).property.2
          linarith
        let q : I := ⟨2 * (t : ℝ),
          ⟨mul_nonneg (by norm_num) t.property.1, by linarith⟩⟩
        have hqcell : q ∈ Icc (concatSubdivisionPoint n j.castSucc)
            (concatSubdivisionPoint n j.succ) := by
          constructor <;> change (_ : ℝ) ≤ _ <;> dsimp [q] <;> linarith
        rw [Path.concat_succ]
        change ((Path.concat (fun _ : Fin (n + 2) ↦ x₀)
          (fun q ↦ f q.castSucc)).trans (f (Fin.last (n + 1)))) t ∈
            S j.castSucc
        rw [Path.trans_apply, dif_pos htHalf]
        change Path.concat (fun _ : Fin (n + 2) ↦ x₀)
          (fun q ↦ f q.castSucc) q ∈ S j.castSucc
        exact ih (fun q ↦ f q.castSucc) (fun q ↦ S q.castSucc)
          (fun q ↦ hx₀ q.castSucc) (fun q ↦ hf q.castSucc) j hqcell

namespace Factorization

variable {iota : Type u} {X : Type v} [TopologicalSpace X]
  {U : iota → Set X} {x₀ : X} {hx₀ : ∀ i, x₀ ∈ U i}
  {γ : Path x₀ x₀}

/-- The canonical dyadic subdivision of a factorization's concatenated path. -/
def concatSubdivision (F : Factorization U x₀ hx₀ γ) :
    IntervalSubdivision where
  cells := F.n + 1
  point := concatSubdivisionPoint F.n
  left := concatSubdivisionPoint_zero F.n
  right := concatSubdivisionPoint_last F.n
  strictMono := concatSubdivisionPoint_strictMono F.n

/-- On its canonical closed cell, the concatenated path of a factorization
stays in the cover member carrying that factor. -/
theorem concatenatedPath_cell_subset
    (F : Factorization U x₀ hx₀ γ) (k : Fin (F.n + 1)) :
    Icc ((F.concatSubdivision).point k.castSucc)
        ((F.concatSubdivision).point k.succ) ⊆
      F.concatenatedPath ⁻¹' U (F.index k) := by
  apply concat_mem_on_canonical_cell F.n
    (fun q ↦ F.ambientFactor q) (fun q ↦ U (F.index q))
    (fun q ↦ hx₀ (F.index q))
  intro q t
  exact (F.factor q t).property

end Factorization

/-- Two reusable fine middle-row subdivisions. `B` avoids both boundary rows,
and `C` avoids `B` and the top row, so the pattern
`bottom, B, C, B, C, ..., top` has disjoint adjacent interior vertices. -/
theorem exists_middleRowPair (bottom top : IntervalSubdivision)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ B C : IntervalSubdivision,
      Disjoint bottom.interiorVertices B.interiorVertices ∧
      Disjoint B.interiorVertices top.interiorVertices ∧
      Disjoint B.interiorVertices C.interiorVertices ∧
      Disjoint C.interiorVertices top.interiorVertices ∧
      (∀ k : Fin B.cells,
        ((B.point k.succ : I) : ℝ) - B.point k.castSucc < ε) ∧
      ∀ k : Fin C.cells,
        ((C.point k.succ : I) : ℝ) - C.point k.castSucc < ε := by
  obtain ⟨B, hB, hBgap⟩ := IntervalSubdivision.FineMesh.exists_subdivision_avoiding
    (bottom.interiorVertices ∪ top.interiorVertices) hε
  obtain ⟨C, hC, hCgap⟩ := IntervalSubdivision.FineMesh.exists_subdivision_avoiding
    (B.interiorVertices ∪ top.interiorVertices) hε
  refine ⟨B, C, ?_, ?_, ?_, ?_, hBgap, hCgap⟩
  · exact (hB.mono_right Finset.subset_union_left).symm
  · exact hB.mono_right Finset.subset_union_right
  · exact (hC.mono_right Finset.subset_union_left).symm
  · exact hC.mono_right Finset.subset_union_right

/-- A fine vertical subdivision with at least three bands can be chosen so
its first and last bands lie in prescribed bottom and top collars. -/
theorem exists_verticalSubdivision_for_collars (b a : I)
    (hb : 0 < b) (ha : a < 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ m : ℕ,
      (∀ k : Fin (m + 3),
        ((IntervalSubdivision.FineMesh.point (m + 1) ∅ k.succ : I) : ℝ) -
          IntervalSubdivision.FineMesh.point (m + 1) ∅ k.castSucc < ε) ∧
      IntervalSubdivision.FineMesh.point (m + 1) ∅
          (0 : Fin (m + 3)).succ < b ∧
      a < IntervalSubdivision.FineMesh.point (m + 1) ∅
        (Fin.last (m + 2)).castSucc := by
  let η : ℝ := min ε (min (b : ℝ) (1 - (a : ℝ)))
  have hη : 0 < η := by
    apply lt_min hε
    apply lt_min
    · exact_mod_cast hb
    · have ha' : (a : ℝ) < 1 := by exact_mod_cast ha
      linarith
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt (half_pos hη)
  have hsmall : (2 : ℝ) / (m + 3) < η := by
    have hmono : (1 : ℝ) / (m + 3) ≤ 1 / (m + 1) :=
      one_div_le_one_div_of_le (by positivity) (by norm_num)
    have hhalf : (1 : ℝ) / (m + 3) < η / 2 := hmono.trans_lt hm
    have hid : (2 : ℝ) / (m + 3) = 2 * (1 / (m + 3)) := by ring
    rw [hid]
    linarith
  have hgap : ∀ k : Fin (m + 3),
      ((IntervalSubdivision.FineMesh.point (m + 1) ∅ k.succ : I) : ℝ) -
        IntervalSubdivision.FineMesh.point (m + 1) ∅ k.castSucc < η := by
    intro k
    apply (IntervalSubdivision.FineMesh.point_gap_lt (m + 1) ∅ k).trans
    have heq : (((m + 1 : ℕ) : ℝ) + 2) = (m : ℝ) + 3 := by
      push_cast
      ring
    rw [heq]
    exact hsmall
  refine ⟨m, fun k ↦ (hgap k).trans_le (min_le_left _ _), ?_, ?_⟩
  · rw [← Subtype.coe_lt_coe]
    have h := hgap (0 : Fin (m + 3))
    rw [show (0 : Fin (m + 3)).castSucc = 0 by rfl] at h
    rw [show (0 : Fin (m + 3)).succ =
      (0 : Fin (m + 2)).castSucc.succ by rfl] at h
    simp only [IntervalSubdivision.FineMesh.point_zero,
      IntervalSubdivision.FineMesh.point_interior] at h
    norm_num at h
    rw [show (0 : Fin (m + 3)).succ =
      (0 : Fin (m + 2)).castSucc.succ by rfl]
    rw [IntervalSubdivision.FineMesh.point_interior]
    exact h.trans_le (min_le_of_right_le (min_le_left _ _))
  · rw [← Subtype.coe_lt_coe]
    have h := hgap (Fin.last (m + 2))
    rw [show (Fin.last (m + 2)).succ = Fin.last (m + 3) by rfl] at h
    simp only [IntervalSubdivision.FineMesh.point_last] at h
    have hηtop : η ≤ 1 - (a : ℝ) := min_le_of_right_le (min_le_right _ _)
    change (a : ℝ) <
      ((IntervalSubdivision.FineMesh.point (m + 1) ∅
        (Fin.last (m + 2)).castSucc : I) : ℝ)
    change (1 : ℝ) -
      ((IntervalSubdivision.FineMesh.point (m + 1) ∅
        (Fin.last (m + 2)).castSucc : I) : ℝ) < η at h
    linarith

/-- A strict boundary subdivision together with its cover labels. -/
structure BoundaryCover {X : Type v} [TopologicalSpace X]
    (U : ι → Set X) {x₀ x₁ : X} (p : Path x₀ x₁) where
  subdivision : IntervalSubdivision
  label : Fin subdivision.cells → ι
  mapsTo : ∀ k, MapsTo p (subdivision.cell k) (U (label k))

/-- A strict interval subdivision carrying one label per cell. -/
structure LabeledSubdivision (ι : Type u) where
  subdivision : IntervalSubdivision
  label : Fin subdivision.cells → ι

/-- Select exact bottom and top rows, with arbitrary rows in between. -/
def boundaryHorizontal {m : ℕ} (bottom top : LabeledSubdivision ι)
    (middle : Fin (m + 3) → LabeledSubdivision ι) :
    Fin (m + 3) → LabeledSubdivision ι :=
  Fin.cases bottom fun i ↦
    Fin.lastCases top (fun j ↦ middle j.castSucc.succ) i

@[simp]
theorem boundaryHorizontal_zero {m : ℕ} (bottom top : LabeledSubdivision ι)
    (middle : Fin (m + 3) → LabeledSubdivision ι) :
    boundaryHorizontal bottom top middle 0 = bottom := rfl

@[simp]
theorem boundaryHorizontal_middle {m : ℕ} (bottom top : LabeledSubdivision ι)
    (middle : Fin (m + 3) → LabeledSubdivision ι) (j : Fin (m + 1)) :
    boundaryHorizontal bottom top middle j.castSucc.succ =
      middle j.castSucc.succ := by
  rw [boundaryHorizontal, Fin.cases_succ, Fin.lastCases_castSucc]

@[simp]
theorem boundaryHorizontal_last {m : ℕ} (bottom top : LabeledSubdivision ι)
    (middle : Fin (m + 3) → LabeledSubdivision ι) :
    boundaryHorizontal bottom top middle (Fin.last (m + 2)) = top := by
  rw [show Fin.last (m + 2) = (Fin.last (m + 1)).succ by rfl]
  rw [boundaryHorizontal, Fin.cases_succ, Fin.lastCases_last]

/-- Dependent elimination over exact boundary rows and arbitrary middle rows. -/
theorem boundaryHorizontal_cell_elim {m : ℕ}
    (bottom top : LabeledSubdivision ι)
    (middle : Fin (m + 3) → LabeledSubdivision ι)
    (P : (r : Fin (m + 3)) → (row : LabeledSubdivision ι) →
      Fin row.subdivision.cells → Prop)
    (hzero : ∀ k : Fin bottom.subdivision.cells, P 0 bottom k)
    (hmiddle : ∀ (j : Fin (m + 1))
      (k : Fin (middle j.castSucc.succ).subdivision.cells),
      P j.castSucc.succ (middle j.castSucc.succ) k)
    (hlast : ∀ k : Fin top.subdivision.cells,
      P (Fin.last (m + 2)) top k) :
    ∀ (r : Fin (m + 3))
      (k : Fin ((boundaryHorizontal bottom top middle r).subdivision.cells)),
      P r (boundaryHorizontal bottom top middle r) k := by
  intro r
  refine Fin.cases ?_ (fun i ↦ ?_) r
  · simpa only [boundaryHorizontal_zero] using hzero
  · refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · rw [Fin.succ_last, boundaryHorizontal_last]
      exact hlast
    · rw [boundaryHorizontal_middle]
      exact hmiddle j

namespace BoundaryCover

variable {X : Type v} [TopologicalSpace X] {U : ι → Set X}
  {x₀ x₁ : X} {p q : Path x₀ x₁}

def toLabeled (B : BoundaryCover U p) : LabeledSubdivision ι where
  subdivision := B.subdivision
  label := B.label

/-- A finite labeled boundary decomposition extends to one common bottom
collar of an endpoint-fixed homotopy. -/
theorem exists_common_bottom_collar (B : BoundaryCover U p)
    (H : p.Homotopy q) (hU : ∀ i, IsOpen (U i)) :
    ∃ b : I, 0 < b ∧ ∀ k,
      Icc 0 b ×ˢ B.subdivision.cell k ⊆ H ⁻¹' U (B.label k) := by
  have hcells : 0 < B.subdivision.cells := by
    by_contra h
    have hc : B.subdivision.cells = 0 := Nat.eq_zero_of_not_pos h
    have hi : (0 : Fin (B.subdivision.cells + 1)) =
        Fin.last B.subdivision.cells := by
      apply Fin.ext
      simp [hc]
    have hzero_one : (0 : I) = 1 :=
      B.subdivision.left.symm.trans <|
        (congrArg B.subdivision.point hi).trans B.subdivision.right
    exact zero_ne_one hzero_one
  letI : Nonempty (Fin B.subdivision.cells) := Fin.pos_iff_nonempty.mp hcells
  apply Hatcher.VanKampen.exists_common_bottom_collar
  · intro k
    exact isCompact_Icc
  · intro k
    exact (hU (B.label k)).preimage H.continuous
  · intro k
    rintro ⟨t, s⟩ ⟨ht, hs⟩
    simp only [mem_singleton_iff] at ht
    subst t
    simpa using B.mapsTo k hs

/-- A finite labeled boundary decomposition extends to one common top collar
of an endpoint-fixed homotopy. -/
theorem exists_common_top_collar (B : BoundaryCover U q)
    (H : p.Homotopy q) (hU : ∀ i, IsOpen (U i)) :
    ∃ a : I, a < 1 ∧ ∀ k,
      Icc a 1 ×ˢ B.subdivision.cell k ⊆ H ⁻¹' U (B.label k) := by
  have hcells : 0 < B.subdivision.cells := by
    by_contra h
    have hc : B.subdivision.cells = 0 := Nat.eq_zero_of_not_pos h
    have hi : (0 : Fin (B.subdivision.cells + 1)) =
        Fin.last B.subdivision.cells := by
      apply Fin.ext
      simp [hc]
    have hzero_one : (0 : I) = 1 :=
      B.subdivision.left.symm.trans <|
        (congrArg B.subdivision.point hi).trans B.subdivision.right
    exact zero_ne_one hzero_one
  letI : Nonempty (Fin B.subdivision.cells) := Fin.pos_iff_nonempty.mp hcells
  apply Hatcher.VanKampen.exists_common_top_collar
  · intro k
    exact isCompact_Icc
  · intro k
    exact (hU (B.label k)).preimage H.continuous
  · intro k
    rintro ⟨t, s⟩ ⟨ht, hs⟩
    simp only [mem_singleton_iff] at ht
    subst t
    simpa using B.mapsTo k hs

end BoundaryCover

/-- The intersection of the cover members in a finite set of labels. -/
def coverIntersection (U : ι → Set X) (labels : Finset ι) : Set X :=
  {x | ∀ i ∈ labels, x ∈ U i}

/-- Member, pairwise, and triple path-connectivity imply path-connectivity of
any nonempty intersection involving at most three distinct cover labels. -/
theorem isPathConnected_coverIntersection_of_card_le_three
    [TopologicalSpace X] (U : ι → Set X) (labels : Finset ι)
    (hnonempty : labels.Nonempty) (hcard : labels.card ≤ 3)
    (hone : ∀ i, IsPathConnected (U i))
    (htwo : ∀ i j, IsPathConnected (U i ∩ U j))
    (hthree : ∀ i j k, IsPathConnected (U i ∩ U j ∩ U k)) :
    IsPathConnected (coverIntersection U labels) := by
  classical
  have hcases : labels.card = 1 ∨ labels.card = 2 ∨ labels.card = 3 := by
    have hpos := Finset.card_pos.mpr hnonempty
    omega
  rcases hcases with hcard1 | hcard2 | hcard3
  · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hcard1
    simpa [coverIntersection] using hone i
  · obtain ⟨i, j, _hij, rfl⟩ := Finset.card_eq_two.mp hcard2
    simpa [coverIntersection, and_assoc] using htwo i j
  · obtain ⟨i, j, k, _hij, _hik, _hjk, rfl⟩ :=
      Finset.card_eq_three.mp hcard3
    have heq : coverIntersection U {i, j, k} = U i ∩ U j ∩ U k := by
      ext x
      constructor
      · intro hx
        exact ⟨⟨hx i (by simp), hx j (by simp)⟩, hx k (by simp)⟩
      · rintro ⟨⟨hxi, hxj⟩, hxk⟩ a ha
        simp only [Finset.mem_insert, Finset.mem_singleton] at ha
        rcases ha with rfl | rfl | rfl
        · exact hxi
        · exact hxj
        · exact hxk
    rw [heq]
    exact hthree i j k

/-- A boundary-compatible staggered grid, using time as the first coordinate
of the homotopy square. -/
structure StaggeredCoverGrid {X : Type v} [TopologicalSpace X]
    (U : ι → Set X) {x₀ x₁ : X} {p q : Path x₀ x₁}
    (H : p.Homotopy q) (bottom : BoundaryCover U p)
    (top : BoundaryCover U q) where
  extraRows : ℕ
  level : Fin (extraRows + 4) → I
  level_zero : level 0 = 0
  level_one : level (Fin.last (extraRows + 3)) = 1
  level_strictMono : StrictMono level
  horizontal : Fin (extraRows + 3) → LabeledSubdivision ι
  subordinate : ∀ r k,
    Icc (level r.castSucc) (level r.succ) ×ˢ
        (horizontal r).subdivision.cell k ⊆
      H ⁻¹' U ((horizontal r).label k)
  adjacent_disjoint : ∀ r : Fin (extraRows + 2),
    Disjoint (horizontal r.castSucc).subdivision.interiorVertices
      (horizontal r.succ).subdivision.interiorVertices
  bottom_eq : horizontal 0 = bottom.toLabeled
  top_eq : horizontal (Fin.last (extraRows + 2)) = top.toLabeled

namespace StaggeredCoverGrid

/-- The number of closed grid cells incident at an interface point, counted
separately in the bands immediately below and above the interface. -/
def interfaceIncidentCellCount {X : Type v} [TopologicalSpace X]
    {U : ι → Set X} {x₀ x₁ : X} {p q : Path x₀ x₁}
    {H : p.Homotopy q} {bottom : BoundaryCover U p}
    {top : BoundaryCover U q} (G : StaggeredCoverGrid U H bottom top)
    (r : Fin (G.extraRows + 2)) (x : I) : ℕ :=
  ((G.horizontal r.castSucc).subdivision.incidentCells x).card +
    ((G.horizontal r.succ).subdivision.incidentCells x).card

/-- Staggering adjacent rows forces every interface point to have at most
three incident closed grid cells. -/
theorem interfaceIncidentCellCount_le_three {X : Type v} [TopologicalSpace X]
    {U : ι → Set X} {x₀ x₁ : X} {p q : Path x₀ x₁}
    {H : p.Homotopy q} {bottom : BoundaryCover U p}
    {top : BoundaryCover U q} (G : StaggeredCoverGrid U H bottom top)
    (r : Fin (G.extraRows + 2)) (x : I) :
    G.interfaceIncidentCellCount r x ≤ 3 := by
  have hd := G.adjacent_disjoint r
  rw [Finset.disjoint_left] at hd
  by_cases hlo : x ∈ (G.horizontal r.castSucc).subdivision.interiorVertices
  · have hhi : x ∉ (G.horizontal r.succ).subdivision.interiorVertices :=
      fun hx ↦ hd hlo hx
    have hlo2 := (G.horizontal r.castSucc).subdivision.card_incidentCells_le_two x
    have hhi1 := (G.horizontal r.succ).subdivision
      |>.card_incidentCells_le_one_of_not_mem_interior x hhi
    unfold interfaceIncidentCellCount
    omega
  · have hlo1 := (G.horizontal r.castSucc).subdivision
      |>.card_incidentCells_le_one_of_not_mem_interior x hlo
    have hhi2 := (G.horizontal r.succ).subdivision.card_incidentCells_le_two x
    unfold interfaceIncidentCellCount
    omega

/-- The cover labels of all closed grid cells incident to one interface
point. -/
def interfaceLabels {X : Type v} [TopologicalSpace X]
    {U : ι → Set X} {x₀ x₁ : X} {p q : Path x₀ x₁}
    {H : p.Homotopy q} {bottom : BoundaryCover U p}
    {top : BoundaryCover U q} (G : StaggeredCoverGrid U H bottom top)
    (r : Fin (G.extraRows + 2)) (x : I) : Finset ι := by
  classical
  exact
    ((G.horizontal r.castSucc).subdivision.incidentCells x).image
        (G.horizontal r.castSucc).label ∪
      ((G.horizontal r.succ).subdivision.incidentCells x).image
        (G.horizontal r.succ).label

theorem interfaceLabels_nonempty {X : Type v} [TopologicalSpace X]
    {U : ι → Set X} {x₀ x₁ : X} {p q : Path x₀ x₁}
    {H : p.Homotopy q} {bottom : BoundaryCover U p}
    {top : BoundaryCover U q} (G : StaggeredCoverGrid U H bottom top)
    (r : Fin (G.extraRows + 2)) (x : I) :
    (G.interfaceLabels r x).Nonempty := by
  classical
  obtain ⟨k, hk⟩ :=
    (G.horizontal r.castSucc).subdivision.exists_mem_cell x
  refine ⟨(G.horizontal r.castSucc).label k, ?_⟩
  unfold interfaceLabels
  apply Finset.mem_union_left
  exact Finset.mem_image.mpr
    ⟨k, ((G.horizontal r.castSucc).subdivision.mem_incidentCells x k).mpr hk, rfl⟩

theorem card_interfaceLabels_le_three {X : Type v} [TopologicalSpace X]
    {U : ι → Set X} {x₀ x₁ : X} {p q : Path x₀ x₁}
    {H : p.Homotopy q} {bottom : BoundaryCover U p}
    {top : BoundaryCover U q} (G : StaggeredCoverGrid U H bottom top)
    (r : Fin (G.extraRows + 2)) (x : I) :
    (G.interfaceLabels r x).card ≤ 3 := by
  classical
  calc
    (G.interfaceLabels r x).card ≤
        (((G.horizontal r.castSucc).subdivision.incidentCells x).image
          (G.horizontal r.castSucc).label).card +
        (((G.horizontal r.succ).subdivision.incidentCells x).image
          (G.horizontal r.succ).label).card := by
      simpa [interfaceLabels] using
        (Finset.card_union_le
          (((G.horizontal r.castSucc).subdivision.incidentCells x).image
            (G.horizontal r.castSucc).label)
          (((G.horizontal r.succ).subdivision.incidentCells x).image
            (G.horizontal r.succ).label))
    _ ≤ ((G.horizontal r.castSucc).subdivision.incidentCells x).card +
        ((G.horizontal r.succ).subdivision.incidentCells x).card :=
      Nat.add_le_add Finset.card_image_le Finset.card_image_le
    _ = G.interfaceIncidentCellCount r x := rfl
    _ ≤ 3 := G.interfaceIncidentCellCount_le_three r x

/-- The homotopy point on an interface lies in every incident cell label. -/
theorem homotopy_mem_of_mem_interfaceLabels {X : Type v} [TopologicalSpace X]
    {U : ι → Set X} {x₀ x₁ : X} {p q : Path x₀ x₁}
    {H : p.Homotopy q} {bottom : BoundaryCover U p}
    {top : BoundaryCover U q} (G : StaggeredCoverGrid U H bottom top)
    (r : Fin (G.extraRows + 2)) (x : I) (i : ι)
    (hi : i ∈ G.interfaceLabels r x) :
    H (G.level r.castSucc.succ, x) ∈ U i := by
  classical
  rw [interfaceLabels, Finset.mem_union, Finset.mem_image,
    Finset.mem_image] at hi
  rcases hi with ⟨k, hk, hki⟩ | ⟨k, hk, hki⟩
  · subst i
    apply G.subordinate r.castSucc k
    constructor
    · exact ⟨(G.level_strictMono Fin.castSucc_lt_succ).le, le_rfl⟩
    · exact ((G.horizontal r.castSucc).subdivision.mem_incidentCells x k).mp hk
  · subst i
    apply G.subordinate r.succ k
    constructor
    · have hlevel : G.level r.succ.castSucc ≤ G.level r.succ.succ :=
        (G.level_strictMono
          (show r.succ.castSucc < r.succ.succ from Fin.castSucc_lt_succ)).le
      exact ⟨le_rfl, hlevel⟩
    · exact ((G.horizontal r.succ).subdivision.mem_incidentCells x k).mp hk

/-- A connector from the shared basepoint to one interface point, chosen in
the intersection of all incident cover labels. -/
noncomputable def interfaceConnector {X : Type v} [TopologicalSpace X]
    {U : ι → Set X} {x₀ x₁ : X} {p q : Path x₀ x₁}
    {H : p.Homotopy q} {bottom : BoundaryCover U p}
    {top : BoundaryCover U q} (G : StaggeredCoverGrid U H bottom top)
    (hx₀ : ∀ i, x₀ ∈ U i)
    (hone : ∀ i, IsPathConnected (U i))
    (htwo : ∀ i j, IsPathConnected (U i ∩ U j))
    (hthree : ∀ i j k, IsPathConnected (U i ∩ U j ∩ U k))
    (r : Fin (G.extraRows + 2)) (x : I) :
    Path x₀ (H (G.level r.castSucc.succ, x)) :=
  let labels := G.interfaceLabels r x
  let hconnected := isPathConnected_coverIntersection_of_card_le_three
    U labels (G.interfaceLabels_nonempty r x)
      (G.card_interfaceLabels_le_three r x) hone htwo hthree
  let hbase : x₀ ∈ coverIntersection U labels :=
    fun i _ ↦ hx₀ i
  let hpoint : H (G.level r.castSucc.succ, x) ∈
      coverIntersection U labels :=
    fun i hi ↦ G.homotopy_mem_of_mem_interfaceLabels r x i hi
  (hconnected.joinedIn x₀ hbase _ hpoint).somePath

theorem interfaceConnector_range {X : Type v} [TopologicalSpace X]
    {U : ι → Set X} {x₀ x₁ : X} {p q : Path x₀ x₁}
    {H : p.Homotopy q} {bottom : BoundaryCover U p}
    {top : BoundaryCover U q} (G : StaggeredCoverGrid U H bottom top)
    (hx₀ : ∀ i, x₀ ∈ U i)
    (hone : ∀ i, IsPathConnected (U i))
    (htwo : ∀ i j, IsPathConnected (U i ∩ U j))
    (hthree : ∀ i j k, IsPathConnected (U i ∩ U j ∩ U k))
    (r : Fin (G.extraRows + 2)) (x : I) {i : ι}
    (hi : i ∈ G.interfaceLabels r x) :
    Set.range (G.interfaceConnector hx₀ hone htwo hthree r x) ⊆ U i := by
  intro y hy
  obtain ⟨t, rfl⟩ := hy
  exact (JoinedIn.somePath_mem
    ((isPathConnected_coverIntersection_of_card_le_three
      U (G.interfaceLabels r x) (G.interfaceLabels_nonempty r x)
      (G.card_interfaceLabels_le_three r x) hone htwo hthree).joinedIn
        x₀ (fun i _ ↦ hx₀ i)
        (H (G.level r.castSucc.succ, x))
        (fun i hi ↦ G.homotopy_mem_of_mem_interfaceLabels r x i hi)) t) i hi

end StaggeredCoverGrid

/-- The geometric row pattern used by the constructor. -/
def staggeredRow (bottom top B C : IntervalSubdivision) (m : ℕ)
    (r : Fin (m + 3)) : IntervalSubdivision :=
  if r.val = 0 then bottom
  else if r.val = m + 2 then top
  else if Even r.val then C else B

@[simp]
theorem staggeredRow_zero (bottom top B C : IntervalSubdivision) (m : ℕ) :
    staggeredRow bottom top B C m 0 = bottom := by
  simp [staggeredRow]

@[simp]
theorem staggeredRow_last (bottom top B C : IntervalSubdivision) (m : ℕ) :
    staggeredRow bottom top B C m (Fin.last (m + 2)) = top := by
  simp [staggeredRow]

/-- The alternating pattern inherits disjointness from its four constituent
adjacency checks. -/
theorem staggeredRow_adjacent_disjoint
    (bottom top B C : IntervalSubdivision) (m : ℕ)
    (hbottomB : Disjoint bottom.interiorVertices B.interiorVertices)
    (hBtop : Disjoint B.interiorVertices top.interiorVertices)
    (hBC : Disjoint B.interiorVertices C.interiorVertices)
    (hCtop : Disjoint C.interiorVertices top.interiorVertices)
    (r : Fin (m + 2)) :
    Disjoint (staggeredRow bottom top B C m r.castSucc).interiorVertices
      (staggeredRow bottom top B C m r.succ).interiorVertices := by
  by_cases hr0 : r.val = 0
  · have hnotTop : r.val ≠ m + 2 := by omega
    have hsucc0 : r.val + 1 ≠ 0 := by omega
    have hsuccTop : r.val + 1 ≠ m + 2 := by omega
    have hsuccOdd : ¬Even (r.val + 1) := by
      norm_num [hr0]
    simpa [staggeredRow, hr0, hnotTop, hsucc0, hsuccTop, hsuccOdd] using hbottomB
  · by_cases hrlast : r.val + 1 = m + 2
    · have hrTop : r.val ≠ m + 2 := by omega
      have hsucc0 : r.val + 1 ≠ 0 := by omega
      by_cases hrEven : Even r.val
      · simpa [staggeredRow, hr0, hrTop, hsucc0, hrlast, hrEven] using hCtop
      · simpa [staggeredRow, hr0, hrTop, hsucc0, hrlast, hrEven] using hBtop
    · have hrTop : r.val ≠ m + 2 := by omega
      have hsucc0 : r.val + 1 ≠ 0 := by omega
      have hrNotPenult : r.val ≠ m + 1 := by omega
      by_cases hrEven : Even r.val
      · have hsuccEven : ¬Even (r.val + 1) := by
          intro h
          exact (Nat.even_add_one.mp h) hrEven
        simpa [staggeredRow, hr0, hrTop, hsucc0, hrlast, hrNotPenult,
          hrEven, hsuccEven]
          using hBC.symm
      · have hsuccEven : Even (r.val + 1) := Nat.even_add_one.mpr hrEven
        simpa [staggeredRow, hr0, hrTop, hsucc0, hrlast, hrNotPenult,
          hrEven, hsuccEven]
          using hBC

/-- Construct a boundary-compatible staggered grid subordinate to an arbitrary
open cover. -/
theorem exists_staggeredCoverGrid {X : Type v} [TopologicalSpace X]
    {U : ι → Set X} {x₀ x₁ : X} {p q : Path x₀ x₁}
    (H : p.Homotopy q) (bottom : BoundaryCover U p)
    (top : BoundaryCover U q) (hU : ∀ i, IsOpen (U i))
    (hcover : univ ⊆ ⋃ i, U i) :
    Nonempty (StaggeredCoverGrid U H bottom top) := by
  have hcopen : ∀ i, IsOpen (H ⁻¹' U i) := fun i ↦ (hU i).preimage H.continuous
  have hccover : univ ⊆ ⋃ i, H ⁻¹' U i := by
    intro z _hz
    have hz := hcover (show H z ∈ univ by simp)
    simpa only [mem_iUnion, mem_preimage] using hz
  obtain ⟨ε, hε, hball⟩ :=
    lebesgue_number_lemma_of_metric isCompact_univ hcopen hccover
  obtain ⟨b, hb, hbottom⟩ := bottom.exists_common_bottom_collar H hU
  obtain ⟨a, ha, htop⟩ := top.exists_common_top_collar H hU
  obtain ⟨B, C, hbottomB, hBtop, hBC, hCtop, hBgap, hCgap⟩ :=
    exists_middleRowPair bottom.subdivision top.subdivision hε
  obtain ⟨m, hYgap, hYfirst, hYlast⟩ :=
    exists_verticalSubdivision_for_collars b a hb ha hε
  let level : Fin (m + 4) → I :=
    IntervalSubdivision.FineMesh.point (m + 1) ∅
  have hmiddleB : ∀ (r : Fin (m + 3)) (k : Fin B.cells), ∃ i,
      Icc (level r.castSucc) (level r.succ) ×ˢ B.cell k ⊆ H ⁻¹' U i := by
    intro r k
    obtain ⟨i, hi⟩ := hball (level r.castSucc, B.point k.castSucc) (by simp)
    refine ⟨i, ?_⟩
    simpa only [level, IntervalSubdivision.cell, Set.Icc_prod_Icc] using
      (IntervalSubdivision.unit_rectangle_subset_ball
        (hYgap r) (hBgap k)).trans hi
  have hmiddleC : ∀ (r : Fin (m + 3)) (k : Fin C.cells), ∃ i,
      Icc (level r.castSucc) (level r.succ) ×ˢ C.cell k ⊆ H ⁻¹' U i := by
    intro r k
    obtain ⟨i, hi⟩ := hball (level r.castSucc, C.point k.castSucc) (by simp)
    refine ⟨i, ?_⟩
    simpa only [level, IntervalSubdivision.cell, Set.Icc_prod_Icc] using
      (IntervalSubdivision.unit_rectangle_subset_ball
        (hYgap r) (hCgap k)).trans hi
  let middleB (r : Fin (m + 3)) : LabeledSubdivision ι :=
    { subdivision := B
      label := fun k ↦ Classical.choose (hmiddleB r k) }
  let middleC (r : Fin (m + 3)) : LabeledSubdivision ι :=
    { subdivision := C
      label := fun k ↦ Classical.choose (hmiddleC r k) }
  let middleRow (r : Fin (m + 3)) : LabeledSubdivision ι :=
    if Even r.val then middleC r else middleB r
  let horizontal : Fin (m + 3) → LabeledSubdivision ι :=
    boundaryHorizontal bottom.toLabeled top.toLabeled middleRow
  have horizontal_subdivision (r : Fin (m + 3)) :
      (horizontal r).subdivision =
        staggeredRow bottom.subdivision top.subdivision B C m r := by
    refine Fin.cases ?_ (fun i ↦ ?_) r
    · simp [horizontal, BoundaryCover.toLabeled]
    · refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · rw [Fin.succ_last]
        simp [horizontal, BoundaryCover.toLabeled]
      · change
          (boundaryHorizontal bottom.toLabeled top.toLabeled middleRow
            j.castSucc.succ).subdivision =
            staggeredRow bottom.subdivision top.subdivision B C m j.castSucc.succ
        rw [boundaryHorizontal_middle]
        have hjTop : j.val ≠ m + 1 := by omega
        by_cases hj : Even (j.val + 1)
        · simp [middleRow, middleC, staggeredRow, hj, hjTop]
        · simp [middleRow, middleB, staggeredRow, hj, hjTop]
  have hsubordinate : ∀ r k,
      Icc (level r.castSucc) (level r.succ) ×ˢ
          (horizontal r).subdivision.cell k ⊆
        H ⁻¹' U ((horizontal r).label k) := by
    change ∀ r k,
      Icc (level r.castSucc) (level r.succ) ×ˢ
          ((boundaryHorizontal bottom.toLabeled top.toLabeled middleRow r).subdivision.cell k) ⊆
        H ⁻¹' U ((boundaryHorizontal bottom.toLabeled top.toLabeled middleRow r).label k)
    apply boundaryHorizontal_cell_elim bottom.toLabeled top.toLabeled middleRow
      (fun r row k ↦
        Icc (level r.castSucc) (level r.succ) ×ˢ row.subdivision.cell k ⊆
          H ⁻¹' U (row.label k))
    · intro k
      have hy : Icc (level (0 : Fin (m + 3)).castSucc)
          (level (0 : Fin (m + 3)).succ) ⊆ Icc 0 b := by
        apply Icc_subset_Icc
        · simp [level]
        · exact hYfirst.le
      exact (prod_mono hy Subset.rfl).trans (hbottom k)
    · intro j
      by_cases hj : Even (j.castSucc.succ : Fin (m + 3)).val
      · have hrow : middleRow j.castSucc.succ = middleC j.castSucc.succ := by
          change (if Even (j.castSucc.succ : Fin (m + 3)).val then
              middleC j.castSucc.succ else middleB j.castSucc.succ) = _
          exact if_pos hj
        rw [hrow]
        intro k
        exact Classical.choose_spec (hmiddleC j.castSucc.succ k)
      · have hrow : middleRow j.castSucc.succ = middleB j.castSucc.succ := by
          change (if Even (j.castSucc.succ : Fin (m + 3)).val then
              middleC j.castSucc.succ else middleB j.castSucc.succ) = _
          exact if_neg hj
        rw [hrow]
        intro k
        exact Classical.choose_spec (hmiddleB j.castSucc.succ k)
    · intro k
      have hy : Icc (level (Fin.last (m + 2)).castSucc)
          (level (Fin.last (m + 2)).succ) ⊆ Icc a 1 := by
        apply Icc_subset_Icc
        · exact hYlast.le
        · simp [level]
      exact (prod_mono hy Subset.rfl).trans (htop k)
  refine ⟨
    { extraRows := m
      level := level
      level_zero := by simp [level]
      level_one := by simp [level]
      level_strictMono := IntervalSubdivision.FineMesh.point_strictMono _ _
      horizontal := horizontal
      subordinate := hsubordinate
      adjacent_disjoint := ?_
      bottom_eq := by simp [horizontal]
      top_eq := by simp [horizontal] }⟩
  · intro r
    rw [horizontal_subdivision, horizontal_subdivision]
    exact staggeredRow_adjacent_disjoint bottom.subdivision top.subdivision B C m
      hbottomB hBtop hBC hCtop r

/-- A homotopy square has a finite subordinate decomposition with at most
three regions incident at every interface point. -/
theorem exists_coverDecomposition_atMostThree
    {X : Type v} [TopologicalSpace X]
    {U : ι → Set X} {x₀ x₁ : X} {p q : Path x₀ x₁}
    (H : p.Homotopy q) (bottom : BoundaryCover U p)
    (top : BoundaryCover U q) (hU : ∀ i, IsOpen (U i))
    (hcover : univ ⊆ ⋃ i, U i) :
    ∃ G : StaggeredCoverGrid U H bottom top,
      ∀ r x, G.interfaceIncidentCellCount r x ≤ 3 := by
  obtain ⟨G⟩ := exists_staggeredCoverGrid H bottom top hU hcover
  exact ⟨G, G.interfaceIncidentCellCount_le_three⟩

namespace Factorization

variable {X : Type v} [TopologicalSpace X] {U : ι → Set X}
  {x₀ : X} {hx₀ : ∀ i, x₀ ∈ U i} {γ : Path x₀ x₀}

/-- The canonical concatenated path, equipped with its exact factor labels,
is valid boundary input for the generic staggered-grid constructor. -/
def boundaryCover (F : Factorization U x₀ hx₀ γ) :
    BoundaryCover U F.concatenatedPath where
  subdivision := F.concatSubdivision
  label := F.index
  mapsTo := F.concatenatedPath_cell_subset

/-- A homotopy between two factored loops admits a staggered cover grid whose
bottom and top rows are exactly the two factor lists. -/
theorem exists_staggeredCoverGrid {δ : Path x₀ x₀}
    (F : Factorization U x₀ hx₀ γ)
    (G : Factorization U x₀ hx₀ δ) (h : γ.Homotopic δ)
    (hU : ∀ i, IsOpen (U i)) (hcover : univ ⊆ ⋃ i, U i) :
    Nonempty (StaggeredCoverGrid U (F.boundaryHomotopy G h)
      F.boundaryCover G.boundaryCover) :=
  Hatcher.VanKampen.exists_staggeredCoverGrid
    (F.boundaryHomotopy G h) F.boundaryCover G.boundaryCover hU hcover

end Factorization

end Hatcher.VanKampen
