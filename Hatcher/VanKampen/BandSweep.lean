import Hatcher.VanKampen.InterfaceFactorization

noncomputable section

namespace Hatcher.VanKampen.Factorization

universe u v

variable {ι : Type u} {X : Type v} [TopologicalSpace X]
  {U : ι → Set X} {x₀ : X} {hx₀ : ∀ i, x₀ ∈ U i}

/-- Expand one cell boundary relation into its left, upper, and inverse-right
edge entries. -/
theorem moves_expand_cell
    (before after : List (Entry U x₀ hx₀)) (i : ι)
    (left upper right bottom : CoverGroup U x₀ hx₀ i)
    (hcell : bottom = right⁻¹ * upper * left) :
    Moves
      (before ++ [⟨i, bottom⟩] ++ after)
      (before ++ [⟨i, left⟩, ⟨i, upper⟩, ⟨i, right⁻¹⟩] ++ after) := by
  rw [hcell]
  simpa [sameCoverEntries, mul_assoc] using
    (moves_split_sameCover (U := U) (x₀ := x₀) (hx₀ := hx₀)
      before after i left [upper, right⁻¹])

/-- The cellular boundary homotopy supplies the class equality needed to
expand one grid cell. -/
theorem moves_expand_cell_of_homotopy
    (before after : List (Entry U x₀ hx₀)) (i : ι)
    {a b c d : U i}
    (ca : Path (⟨x₀, hx₀ i⟩ : U i) a)
    (cb : Path (⟨x₀, hx₀ i⟩ : U i) b)
    (cc : Path (⟨x₀, hx₀ i⟩ : U i) c)
    (cd : Path (⟨x₀, hx₀ i⟩ : U i) d)
    (bottom : Path a b) (right : Path b d)
    (left : Path a c) (upper : Path c d)
    (hsquare : (bottom.trans right).Homotopic (left.trans upper)) :
    Moves
      (before ++ [⟨i, FundamentalGroup.fromPath
        (.mk (closeEdge ca bottom cb))⟩] ++ after)
      (before ++
        [⟨i, FundamentalGroup.fromPath (.mk (closeEdge ca left cc))⟩,
         ⟨i, FundamentalGroup.fromPath (.mk (closeEdge cc upper cd))⟩,
         ⟨i, (FundamentalGroup.fromPath
           (.mk (closeEdge cb right cd)))⁻¹⟩] ++ after) := by
  apply moves_expand_cell
  exact fundamentalGroup_cell_relation ca cb cc cd bottom right left upper hsquare

/-- Two adjacent cells expand by their square relations, then their common
vertical connector cancels through the overlap relation. -/
theorem moves_across_two_adjacent_cells
    (before after : List (Entry U x₀ hx₀)) (i j : ι)
    (leftI upperI rightI bottomI : CoverGroup U x₀ hx₀ i)
    (leftJ upperJ rightJ bottomJ : CoverGroup U x₀ hx₀ j)
    (ω : OverlapGroup U x₀ hx₀ i j)
    (hcellI : bottomI = rightI⁻¹ * upperI * leftI)
    (hcellJ : bottomJ = rightJ⁻¹ * upperJ * leftJ)
    (hsharedI : rightI = overlapToLeft U x₀ hx₀ i j ω)
    (hsharedJ : leftJ = overlapToRight U x₀ hx₀ i j ω) :
    Moves
      (before ++ [⟨i, bottomI⟩, ⟨j, bottomJ⟩] ++ after)
      (before ++
        [⟨i, leftI⟩, ⟨i, upperI⟩,
         ⟨j, upperJ⟩, ⟨j, rightJ⁻¹⟩] ++ after) := by
  have hfirst := moves_expand_cell
    (U := U) (x₀ := x₀) (hx₀ := hx₀)
    before (⟨j, bottomJ⟩ :: after) i leftI upperI rightI bottomI hcellI
  have hsecond := moves_expand_cell
    (U := U) (x₀ := x₀) (hx₀ := hx₀)
    (before ++ [⟨i, leftI⟩, ⟨i, upperI⟩, ⟨i, rightI⁻¹⟩]) after
    j leftJ upperJ rightJ bottomJ hcellJ
  have hcancel := moves_cancel_connector
    (U := U) (x₀ := x₀) (hx₀ := hx₀)
    (before ++ [⟨i, leftI⟩, ⟨i, upperI⟩])
    (⟨j, rightJ⁻¹⟩ :: after) i j upperJ ω
  rw [hsharedI, hsharedJ] at hsecond
  have hfirst' : Moves
      (before ++ [⟨i, bottomI⟩, ⟨j, bottomJ⟩] ++ after)
      (before ++ [⟨i, leftI⟩, ⟨i, upperI⟩, ⟨i, rightI⁻¹⟩,
        ⟨j, bottomJ⟩] ++ after) := by
    simpa [List.append_assoc] using hfirst
  have hsecond' : Moves
      (before ++ [⟨i, leftI⟩, ⟨i, upperI⟩, ⟨i,
          (overlapToLeft U x₀ hx₀ i j ω)⁻¹⟩, ⟨j, bottomJ⟩] ++ after)
      (before ++ [⟨i, leftI⟩, ⟨i, upperI⟩, ⟨i,
          (overlapToLeft U x₀ hx₀ i j ω)⁻¹⟩,
        ⟨j, overlapToRight U x₀ hx₀ i j ω⟩,
        ⟨j, upperJ⟩, ⟨j, rightJ⁻¹⟩] ++ after) := by
    simpa [List.append_assoc] using hsecond
  rw [hsharedI] at hfirst'
  have hcancel' : Moves
      (before ++ [⟨i, leftI⟩, ⟨i, upperI⟩, ⟨i,
          (overlapToLeft U x₀ hx₀ i j ω)⁻¹⟩,
        ⟨j, overlapToRight U x₀ hx₀ i j ω⟩,
        ⟨j, upperJ⟩, ⟨j, rightJ⁻¹⟩] ++ after)
      (before ++ [⟨i, leftI⟩, ⟨i, upperI⟩,
        ⟨j, upperJ⟩, ⟨j, rightJ⁻¹⟩] ++ after) := by
    simpa [List.append_assoc] using hcancel
  exact hfirst'.trans (hsecond'.trans hcancel')

/-- Geometric two-cell form: each square gives a boundary relation, while
the common vertical edge is represented by one overlap loop. -/
theorem moves_across_two_adjacent_cells_of_homotopies
    (before after : List (Entry U x₀ hx₀)) (i j : ι)
    {aI bI cI dI : U i} {aJ bJ cJ dJ : U j}
    (caI : Path (⟨x₀, hx₀ i⟩ : U i) aI)
    (cbI : Path (⟨x₀, hx₀ i⟩ : U i) bI)
    (ccI : Path (⟨x₀, hx₀ i⟩ : U i) cI)
    (cdI : Path (⟨x₀, hx₀ i⟩ : U i) dI)
    (bottomI : Path aI bI) (rightI : Path bI dI)
    (leftI : Path aI cI) (upperI : Path cI dI)
    (hsquareI : (bottomI.trans rightI).Homotopic
      (leftI.trans upperI))
    (caJ : Path (⟨x₀, hx₀ j⟩ : U j) aJ)
    (cbJ : Path (⟨x₀, hx₀ j⟩ : U j) bJ)
    (ccJ : Path (⟨x₀, hx₀ j⟩ : U j) cJ)
    (cdJ : Path (⟨x₀, hx₀ j⟩ : U j) dJ)
    (bottomJ : Path aJ bJ) (rightJ : Path bJ dJ)
    (leftJ : Path aJ cJ) (upperJ : Path cJ dJ)
    (hsquareJ : (bottomJ.trans rightJ).Homotopic
      (leftJ.trans upperJ))
    (ω : OverlapGroup U x₀ hx₀ i j)
    (hsharedI : FundamentalGroup.fromPath
        (.mk (closeEdge cbI rightI cdI)) =
      overlapToLeft U x₀ hx₀ i j ω)
    (hsharedJ : FundamentalGroup.fromPath
        (.mk (closeEdge caJ leftJ ccJ)) =
      overlapToRight U x₀ hx₀ i j ω) :
    Moves
      (before ++
        [⟨i, FundamentalGroup.fromPath (.mk (closeEdge caI bottomI cbI))⟩,
         ⟨j, FundamentalGroup.fromPath (.mk (closeEdge caJ bottomJ cbJ))⟩] ++
        after)
      (before ++
        [⟨i, FundamentalGroup.fromPath (.mk (closeEdge caI leftI ccI))⟩,
         ⟨i, FundamentalGroup.fromPath (.mk (closeEdge ccI upperI cdI))⟩,
         ⟨j, FundamentalGroup.fromPath (.mk (closeEdge ccJ upperJ cdJ))⟩,
         ⟨j, (FundamentalGroup.fromPath
           (.mk (closeEdge cbJ rightJ cdJ)))⁻¹⟩] ++ after) := by
  apply moves_across_two_adjacent_cells
    (ω := ω)
  · exact fundamentalGroup_cell_relation caI cbI ccI cdI
      bottomI rightI leftI upperI hsquareI
  · exact fundamentalGroup_cell_relation caJ cbJ ccJ cdJ
      bottomJ rightJ leftJ upperJ hsquareJ
  · exact hsharedI
  · exact hsharedJ

def bandCellEntries {n : ℕ} (index : Fin (n + 1) → ι)
    (top left right : ∀ k, CoverGroup U x₀ hx₀ (index k))
    (k : Fin (n + 1)) : List (Entry U x₀ hx₀) :=
  [⟨index k, left k⟩, ⟨index k, top k⟩, ⟨index k, (right k)⁻¹⟩]

def bandExpandedEntries {n : ℕ} (index : Fin (n + 1) → ι)
    (top left right : ∀ k, CoverGroup U x₀ hx₀ (index k)) :
    List (Entry U x₀ hx₀) :=
  (List.ofFn fun k ↦ bandCellEntries index top left right k).flatten

def bandTopEntries {n : ℕ} (index : Fin (n + 1) → ι)
    (top : ∀ k, CoverGroup U x₀ hx₀ (index k)) :
    List (Entry U x₀ hx₀) :=
  List.ofFn fun k ↦ ⟨index k, top k⟩

def bandOpenEntries {n : ℕ} (index : Fin (n + 1) → ι)
    (top left right : ∀ k, CoverGroup U x₀ hx₀ (index k)) :
    List (Entry U x₀ hx₀) :=
  ⟨index 0, left 0⟩ :: bandTopEntries index top ++
    [⟨index (Fin.last n), (right (Fin.last n))⁻¹⟩]

/-- Adjacent vertical connector loops cancel after changing cover through
their common overlap. The two exterior connector loops are retained. -/
theorem moves_cancel_band_internal_connectors {n : ℕ}
    (index : Fin (n + 1) → ι)
    (top left right : ∀ k, CoverGroup U x₀ hx₀ (index k))
    (overlap : ∀ k : Fin n,
      OverlapGroup U x₀ hx₀ (index k.castSucc) (index k.succ))
    (hright : ∀ k : Fin n, right k.castSucc =
      overlapToLeft U x₀ hx₀ (index k.castSucc) (index k.succ) (overlap k))
    (hleft : ∀ k : Fin n, left k.succ =
      overlapToRight U x₀ hx₀ (index k.castSucc) (index k.succ) (overlap k)) :
    Moves (bandExpandedEntries index top left right)
      (bandOpenEntries index top left right) := by
  induction n with
  | zero =>
      exact Relation.ReflTransGen.refl
  | succ n ih =>
      let index' : Fin (n + 1) → ι := index ∘ Fin.succ
      let top' : ∀ k, CoverGroup U x₀ hx₀ (index' k) :=
        fun k ↦ top k.succ
      let left' : ∀ k, CoverGroup U x₀ hx₀ (index' k) :=
        fun k ↦ left k.succ
      let right' : ∀ k, CoverGroup U x₀ hx₀ (index' k) :=
        fun k ↦ right k.succ
      let overlap' : ∀ k : Fin n,
          OverlapGroup U x₀ hx₀ (index' k.castSucc) (index' k.succ) :=
        fun k ↦ overlap k.succ
      have htail : Moves
          (bandExpandedEntries index' top' left' right')
          (bandOpenEntries index' top' left' right') := by
        apply ih index' top' left' right' overlap'
        · intro k
          exact hright k.succ
        · intro k
          exact hleft k.succ
      let firstCell : List (Entry U x₀ hx₀) :=
        bandCellEntries index top left right 0
      have htail' := htail.prefix firstCell
      have hcancel := moves_cancel_connector
        (U := U) (x₀ := x₀) (hx₀ := hx₀)
        [⟨index 0, left 0⟩, ⟨index 0, top 0⟩]
        (List.ofFn (fun k : Fin n ↦
          (⟨index k.succ.succ, top k.succ.succ⟩ : Entry U x₀ hx₀)) ++
          [⟨index (Fin.last (n + 1)), (right (Fin.last (n + 1)))⁻¹⟩])
        (index (0 : Fin (n + 1)).castSucc)
        (index (0 : Fin (n + 1)).succ)
        (top (0 : Fin (n + 1)).succ) (overlap 0)
      rw [← hright 0, ← hleft 0] at hcancel
      have hexpanded : bandExpandedEntries index top left right =
          firstCell ++ bandExpandedEntries index' top' left' right' := by
        unfold bandExpandedEntries firstCell
        rw [List.ofFn_succ, List.flatten_cons]
        rfl
      have htail'' : Moves
          (bandExpandedEntries index top left right)
          (firstCell ++ bandOpenEntries index' top' left' right') := by
        rw [hexpanded]
        exact htail'
      have hcancel' : Moves
          (firstCell ++ bandOpenEntries index' top' left' right')
          (bandOpenEntries index top left right) := by
        unfold bandOpenEntries bandTopEntries
        convert hcancel using 1 <;>
          simp [bandCellEntries, firstCell, index', top', left', right',
            List.ofFn_succ, Fin.succ_last]
        all_goals exact ⟨rfl, rfl⟩
      exact htail''.trans hcancel'

/-- A row of cellular identities gives a move chain from the bottom entries
to the top entries once the two exterior vertical loops are trivial. -/
theorem moves_of_band_cell_relations {n : ℕ}
    (index : Fin (n + 1) → ι)
    (bottom top left right : ∀ k, CoverGroup U x₀ hx₀ (index k))
    (overlap : ∀ k : Fin n,
      OverlapGroup U x₀ hx₀ (index k.castSucc) (index k.succ))
    (hcell : ∀ k, bottom k = (right k)⁻¹ * top k * left k)
    (hright : ∀ k : Fin n, right k.castSucc =
      overlapToLeft U x₀ hx₀ (index k.castSucc) (index k.succ) (overlap k))
    (hleft : ∀ k : Fin n, left k.succ =
      overlapToRight U x₀ hx₀ (index k.castSucc) (index k.succ) (overlap k))
    (hleft_zero : left 0 = 1)
    (hright_last : right (Fin.last n) = 1) :
    Moves (List.ofFn fun k ↦ (⟨index k, bottom k⟩ : Entry U x₀ hx₀))
      (bandTopEntries index top) := by
  let blocks : List (CoverBlock (U := U) (x₀ := x₀) (hx₀ := hx₀)) :=
    List.ofFn fun k ↦
      { index := index k
        head := left k
        tail := [top k, (right k)⁻¹] }
  have hsplit := moves_split_blocks blocks
  have hcoarse : coarseEntries blocks =
      List.ofFn fun k ↦ (⟨index k, bottom k⟩ : Entry U x₀ hx₀) := by
    unfold coarseEntries
    simp only [blocks, List.map_ofFn]
    rw [List.ofFn_inj]
    funext k
    simpa [Function.comp_def, CoverBlock.coarseEntry, mul_assoc] using
      congrArg (fun z : CoverGroup U x₀ hx₀ (index k) ↦
        (⟨index k, z⟩ : Entry U x₀ hx₀)) (hcell k).symm
  have hfine : fineEntries blocks =
      bandExpandedEntries index top left right := by
    change (blocks.map CoverBlock.fineEntries).flatten = _
    unfold bandExpandedEntries
    congr 1
    simp only [blocks, List.map_ofFn]
    rw [List.ofFn_inj]
    funext k
    unfold Function.comp CoverBlock.fineEntries sameCoverEntries
    rfl
  rw [hcoarse, hfine] at hsplit
  have hcancel := moves_cancel_band_internal_connectors index top left right
    overlap hright hleft
  have hleftMove : Moves
      (bandOpenEntries index top left right)
      (bandTopEntries index top ++
        [⟨index (Fin.last n), (right (Fin.last n))⁻¹⟩]) := by
    have h := Relation.ReflTransGen.single <| Move.combine
      (U := U) (x₀ := x₀) (hx₀ := hx₀)
      ([] : List (Entry U x₀ hx₀))
      (List.ofFn (fun k : Fin n ↦
        (⟨index k.succ, top k.succ⟩ : Entry U x₀ hx₀)) ++
        [⟨index (Fin.last n), (right (Fin.last n))⁻¹⟩])
      (index 0) (left 0) (top 0)
    rw [hleft_zero] at h
    unfold bandOpenEntries bandTopEntries
    rw [List.ofFn_succ, hleft_zero]
    simpa [List.append_assoc] using h
  have hrightMove : Moves
      (bandTopEntries index top ++
        [⟨index (Fin.last n), (right (Fin.last n))⁻¹⟩])
      (bandTopEntries index top) := by
    have h := Relation.ReflTransGen.single <| Move.combine
      (U := U) (x₀ := x₀) (hx₀ := hx₀)
      (List.ofFn fun k : Fin n ↦
        (⟨index k.castSucc, top k.castSucc⟩ : Entry U x₀ hx₀))
      ([] : List (Entry U x₀ hx₀))
      (index (Fin.last n)) (top (Fin.last n))
      (right (Fin.last n))⁻¹
    rw [hright_last] at h
    unfold bandTopEntries
    rw [List.ofFn_succ_last, hright_last]
    simpa using h
  exact hsplit.trans (hcancel.trans (hleftMove.trans hrightMove))

end Hatcher.VanKampen.Factorization
