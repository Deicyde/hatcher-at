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

end Hatcher.VanKampen.Factorization
