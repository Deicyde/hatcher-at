import Hatcher.VanKampen.BandSweep
import Hatcher.VanKampen.RefinementProduct

noncomputable section

open Set
open scoped unitInterval

namespace Hatcher.VanKampen

universe u v

namespace StaggeredCoverGrid

variable {ι : Type u} {X : Type v} [TopologicalSpace X]
  {U : ι → Set X} {x₀ : X} {p q : Path x₀ x₀}
  {H : p.Homotopy q} {bottom : BoundaryCover U p}
  {top : BoundaryCover U q}

def bandLowerPath (G : StaggeredCoverGrid U H bottom top)
    (r : Fin (G.extraRows + 2)) : Path x₀ x₀ :=
  H.eval (G.level r.castSucc.castSucc)

/-- Reparameterize one grid cell in the band below an interface. -/
def lowerBandCellMap (G : StaggeredCoverGrid U H bottom top)
    (r : Fin (G.extraRows + 2))
    (k : Fin (G.horizontal r.castSucc).subdivision.cells) :
    C(I × I, U ((G.horizontal r.castSucc).label k)) :=
  G.bandCellMap r.castSucc k

@[simp]
theorem lowerBandCellMap_zero_zero (G : StaggeredCoverGrid U H bottom top)
    (r : Fin (G.extraRows + 2))
    (k : Fin (G.horizontal r.castSucc).subdivision.cells) :
    ((G.lowerBandCellMap r k ((0 : I), (0 : I))) : X) =
      G.bandLowerPath r ((G.horizontal r.castSucc).subdivision.point k.castSucc) := by
  simp [lowerBandCellMap, bandCellMap, bandLowerPath]

@[simp]
theorem lowerBandCellMap_zero_one (G : StaggeredCoverGrid U H bottom top)
    (r : Fin (G.extraRows + 2))
    (k : Fin (G.horizontal r.castSucc).subdivision.cells) :
    ((G.lowerBandCellMap r k ((0 : I), (1 : I))) : X) =
      G.bandLowerPath r ((G.horizontal r.castSucc).subdivision.point k.succ) := by
  simp [lowerBandCellMap, bandCellMap, bandLowerPath]

@[simp]
theorem lowerBandCellMap_one_zero (G : StaggeredCoverGrid U H bottom top)
    (r : Fin (G.extraRows + 2))
    (k : Fin (G.horizontal r.castSucc).subdivision.cells) :
    ((G.lowerBandCellMap r k ((1 : I), (0 : I))) : X) =
      G.interfacePath r ((G.horizontal r.castSucc).subdivision.point k.castSucc) := by
  simp [lowerBandCellMap, bandCellMap, interfacePath]

@[simp]
theorem lowerBandCellMap_one_one (G : StaggeredCoverGrid U H bottom top)
    (r : Fin (G.extraRows + 2))
    (k : Fin (G.horizontal r.castSucc).subdivision.cells) :
    ((G.lowerBandCellMap r k ((1 : I), (1 : I))) : X) =
      G.interfacePath r ((G.horizontal r.castSucc).subdivision.point k.succ) := by
  simp [lowerBandCellMap, bandCellMap, interfacePath]

def bandLowerBoundary (G : StaggeredCoverGrid U H bottom top)
    (r : Fin (G.extraRows + 2)) : BoundaryCover U (G.bandLowerPath r) where
  subdivision := (G.horizontal r.castSucc).subdivision
  label := (G.horizontal r.castSucc).label
  mapsTo k x hx := by
    apply G.subordinate r.castSucc k
    exact ⟨⟨le_rfl, (G.level_strictMono Fin.castSucc_lt_succ).le⟩, hx⟩

def bandUpperBoundary (G : StaggeredCoverGrid U H bottom top)
    (r : Fin (G.extraRows + 2)) : BoundaryCover U (G.interfacePath r) where
  subdivision := (G.horizontal r.castSucc).subdivision
  label := (G.horizontal r.castSucc).label
  mapsTo k x hx := by
    apply G.subordinate r.castSucc k
    exact ⟨⟨(G.level_strictMono Fin.castSucc_lt_succ).le, le_rfl⟩, hx⟩

def upperCoarseVertex (G : StaggeredCoverGrid U H bottom top)
    (r : Fin (G.extraRows + 2))
    (j : Fin ((G.horizontal r.castSucc).subdivision.cells + 1)) :
    Fin ((G.interfaceSubdivision r).cells + 1) :=
  Fin.cast (by unfold interfaceSubdivision; rfl)
    (IntervalSubdivision.commonRefinementLeftVertex
      (G.horizontal r.castSucc).subdivision
      (G.horizontal r.succ).subdivision j)

theorem upperCoarseVertex_spec (G : StaggeredCoverGrid U H bottom top)
    (r : Fin (G.extraRows + 2))
    (j : Fin ((G.horizontal r.castSucc).subdivision.cells + 1)) :
    (G.interfaceSubdivision r).point (G.upperCoarseVertex r j) =
      (G.horizontal r.castSucc).subdivision.point j := by
  unfold upperCoarseVertex interfaceSubdivision
  exact IntervalSubdivision.commonRefinementLeftVertex_spec _ _ j

@[simp]
theorem upperCoarseVertex_zero (G : StaggeredCoverGrid U H bottom top)
    (r : Fin (G.extraRows + 2)) : G.upperCoarseVertex r 0 = 0 := by
  apply (G.interfaceSubdivision r).strictMono.injective
  rw [G.upperCoarseVertex_spec r, (G.horizontal r.castSucc).subdivision.left,
    (G.interfaceSubdivision r).left]

@[simp]
theorem upperCoarseVertex_last (G : StaggeredCoverGrid U H bottom top)
    (r : Fin (G.extraRows + 2)) :
    G.upperCoarseVertex r
        (Fin.last (G.horizontal r.castSucc).subdivision.cells) =
      Fin.last (G.interfaceSubdivision r).cells := by
  apply (G.interfaceSubdivision r).strictMono.injective
  rw [G.upperCoarseVertex_spec r, (G.horizontal r.castSucc).subdivision.right,
    (G.interfaceSubdivision r).right]

/-- Restrict the chosen interface connector at a coarse-row vertex to a
cell incident to that vertex. -/
def upperCoarseConnectorPath
    (G : StaggeredCoverGrid U H bottom top)
    (hx₀ : ∀ i, x₀ ∈ U i)
    (hone : ∀ i, IsPathConnected (U i))
    (htwo : ∀ i j, IsPathConnected (U i ∩ U j))
    (hthree : ∀ i j k, IsPathConnected (U i ∩ U j ∩ U k))
    (r : Fin (G.extraRows + 2))
    (j : Fin ((G.horizontal r.castSucc).subdivision.cells + 1)) :
    Path x₀
      (G.interfacePath r ((G.horizontal r.castSucc).subdivision.point j)) :=
  (G.interfaceVertexConnector hx₀ hone htwo hthree r
    (G.upperCoarseVertex r j)).cast rfl <| by
        exact congrArg (G.interfacePath r)
          (G.upperCoarseVertex_spec r j).symm

def upperCoarseConnectors
    (G : StaggeredCoverGrid U H bottom top)
    (hx₀ : ∀ i, x₀ ∈ U i)
    (hone : ∀ i, IsPathConnected (U i))
    (htwo : ∀ i j, IsPathConnected (U i ∩ U j))
    (hthree : ∀ i j k, IsPathConnected (U i ∩ U j ∩ U k))
    (r : Fin (G.extraRows + 2)) :
    BoundaryConnectors (G.bandUpperBoundary r) where
  path := G.upperCoarseConnectorPath hx₀ hone htwo hthree r
  left_eq := by
    change G.upperCoarseConnectorPath hx₀ hone htwo hthree r
        (0 : Fin ((G.horizontal r.castSucc).subdivision.cells + 1)) =
      (Path.refl x₀).cast rfl
        ((congrArg (G.interfacePath r)
          (G.horizontal r.castSucc).subdivision.left).trans
          (G.interfacePath r).source)
    ext t
    unfold upperCoarseConnectorPath
    rw [Path.cast_coe]
    have hv := G.upperCoarseVertex_zero r
    rw [hv]
    unfold interfaceVertexConnector
    rw [dif_pos rfl, Path.cast_coe, Path.cast_coe]
  right_eq := by
    change G.upperCoarseConnectorPath hx₀ hone htwo hthree r
        (Fin.last (G.horizontal r.castSucc).subdivision.cells) =
      (Path.refl x₀).cast rfl
        ((congrArg (G.interfacePath r)
          (G.horizontal r.castSucc).subdivision.right).trans
          (G.interfacePath r).target)
    ext t
    unfold upperCoarseConnectorPath
    rw [Path.cast_coe]
    have hv := G.upperCoarseVertex_last r
    rw [hv]
    unfold interfaceVertexConnector
    have hne : (Fin.last (G.interfaceSubdivision r).cells :
        Fin (G.interfaceSubdivision r).cells.succ) ≠ 0 := by
      intro h
      have hval : (G.interfaceSubdivision r).cells = 0 := by
        simpa using congrArg Fin.val h
      exact (Nat.ne_of_gt (G.interfaceSubdivision r).cells_pos) hval
    rw [dif_neg hne, dif_pos rfl, Path.cast_coe, Path.cast_coe]
  range_left k := by
    classical
    change Set.range (G.upperCoarseConnectorPath hx₀ hone htwo hthree r
      k.castSucc) ⊆ U ((G.horizontal r.castSucc).label k)
    unfold upperCoarseConnectorPath
    intro y hy
    rcases hy with ⟨t, rfl⟩
    apply G.interfaceVertexConnector_range hx₀ hone htwo hthree r _ ?_ ⟨t, rfl⟩
    unfold interfaceLabels
    apply Finset.mem_union_left
    apply Finset.mem_image.mpr
    refine ⟨k, ?_, rfl⟩
    rw [IntervalSubdivision.mem_incidentCells, G.upperCoarseVertex_spec r]
    exact ⟨le_rfl,
      ((G.horizontal r.castSucc).subdivision.strictMono
        Fin.castSucc_lt_succ).le⟩
  range_right k := by
    classical
    change Set.range (G.upperCoarseConnectorPath hx₀ hone htwo hthree r
      k.succ) ⊆ U ((G.horizontal r.castSucc).label k)
    unfold upperCoarseConnectorPath
    intro y hy
    rcases hy with ⟨t, rfl⟩
    apply G.interfaceVertexConnector_range hx₀ hone htwo hthree r _ ?_ ⟨t, rfl⟩
    unfold interfaceLabels
    apply Finset.mem_union_left
    apply Finset.mem_image.mpr
    refine ⟨k, ?_, rfl⟩
    rw [IntervalSubdivision.mem_incidentCells, G.upperCoarseVertex_spec r]
    exact ⟨((G.horizontal r.castSucc).subdivision.strictMono
      Fin.castSucc_lt_succ).le, le_rfl⟩

def bandBottomEdge (G : StaggeredCoverGrid U H bottom top)
    (r : Fin (G.extraRows + 2))
    (k : Fin (G.horizontal r.castSucc).subdivision.cells) :=
  UnitSquare.lower.map (G.lowerBandCellMap r k).continuous

def bandTopEdge (G : StaggeredCoverGrid U H bottom top)
    (r : Fin (G.extraRows + 2))
    (k : Fin (G.horizontal r.castSucc).subdivision.cells) :=
  UnitSquare.upper.map (G.lowerBandCellMap r k).continuous

def bandLeftEdge (G : StaggeredCoverGrid U H bottom top)
    (r : Fin (G.extraRows + 2))
    (k : Fin (G.horizontal r.castSucc).subdivision.cells) :=
  UnitSquare.left.map (G.lowerBandCellMap r k).continuous

def bandRightEdge (G : StaggeredCoverGrid U H bottom top)
    (r : Fin (G.extraRows + 2))
    (k : Fin (G.horizontal r.castSucc).subdivision.cells) :=
  UnitSquare.right.map (G.lowerBandCellMap r k).continuous

def bandLowerLeftConnector
    (G : StaggeredCoverGrid U H bottom top)
    (hx₀ : ∀ i, x₀ ∈ U i) (r : Fin (G.extraRows + 2))
    (C : BoundaryConnectors (G.bandLowerBoundary r))
    (k : Fin (G.horizontal r.castSucc).subdivision.cells) :
    Path (⟨x₀, hx₀ ((G.horizontal r.castSucc).label k)⟩ :
      U ((G.horizontal r.castSucc).label k))
      (G.lowerBandCellMap r k ((0 : I), (0 : I))) :=
  (C.leftPathIn (hx₀ := hx₀) k).cast rfl
    (Subtype.ext (G.lowerBandCellMap_zero_zero r k))

def bandLowerRightConnector
    (G : StaggeredCoverGrid U H bottom top)
    (hx₀ : ∀ i, x₀ ∈ U i) (r : Fin (G.extraRows + 2))
    (C : BoundaryConnectors (G.bandLowerBoundary r))
    (k : Fin (G.horizontal r.castSucc).subdivision.cells) :
    Path (⟨x₀, hx₀ ((G.horizontal r.castSucc).label k)⟩ :
      U ((G.horizontal r.castSucc).label k))
      (G.lowerBandCellMap r k ((0 : I), (1 : I))) :=
  (C.rightPathIn (hx₀ := hx₀) k).cast rfl
    (Subtype.ext (G.lowerBandCellMap_zero_one r k))

def bandUpperLeftConnector
    (G : StaggeredCoverGrid U H bottom top)
    (hx₀ : ∀ i, x₀ ∈ U i) (r : Fin (G.extraRows + 2))
    (C : BoundaryConnectors (G.bandUpperBoundary r))
    (k : Fin (G.horizontal r.castSucc).subdivision.cells) :
    Path (⟨x₀, hx₀ ((G.horizontal r.castSucc).label k)⟩ :
      U ((G.horizontal r.castSucc).label k))
      (G.lowerBandCellMap r k ((1 : I), (0 : I))) :=
  (C.leftPathIn (hx₀ := hx₀) k).cast rfl
    (Subtype.ext (G.lowerBandCellMap_one_zero r k))

def bandUpperRightConnector
    (G : StaggeredCoverGrid U H bottom top)
    (hx₀ : ∀ i, x₀ ∈ U i) (r : Fin (G.extraRows + 2))
    (C : BoundaryConnectors (G.bandUpperBoundary r))
    (k : Fin (G.horizontal r.castSucc).subdivision.cells) :
    Path (⟨x₀, hx₀ ((G.horizontal r.castSucc).label k)⟩ :
      U ((G.horizontal r.castSucc).label k))
      (G.lowerBandCellMap r k ((1 : I), (1 : I))) :=
  (C.rightPathIn (hx₀ := hx₀) k).cast rfl
    (Subtype.ext (G.lowerBandCellMap_one_one r k))

def bandLeftLoop
    (G : StaggeredCoverGrid U H bottom top)
    (hx₀ : ∀ i, x₀ ∈ U i) (r : Fin (G.extraRows + 2))
    (C₀ : BoundaryConnectors (G.bandLowerBoundary r))
    (C₁ : BoundaryConnectors (G.bandUpperBoundary r))
    (k : Fin (G.horizontal r.castSucc).subdivision.cells) :=
  closeEdge (G.bandLowerLeftConnector hx₀ r C₀ k) (G.bandLeftEdge r k)
    (G.bandUpperLeftConnector hx₀ r C₁ k)

def bandRightLoop
    (G : StaggeredCoverGrid U H bottom top)
    (hx₀ : ∀ i, x₀ ∈ U i) (r : Fin (G.extraRows + 2))
    (C₀ : BoundaryConnectors (G.bandLowerBoundary r))
    (C₁ : BoundaryConnectors (G.bandUpperBoundary r))
    (k : Fin (G.horizontal r.castSucc).subdivision.cells) :=
  closeEdge (G.bandLowerRightConnector hx₀ r C₀ k) (G.bandRightEdge r k)
    (G.bandUpperRightConnector hx₀ r C₁ k)

def bandBottomClass
    (G : StaggeredCoverGrid U H bottom top)
    (hx₀ : ∀ i, x₀ ∈ U i) (r : Fin (G.extraRows + 2))
    (C : BoundaryConnectors (G.bandLowerBoundary r))
    (k : Fin (G.horizontal r.castSucc).subdivision.cells) :
    CoverGroup U x₀ hx₀ ((G.horizontal r.castSucc).label k) :=
  FundamentalGroup.fromPath (.mk (closeEdge
    (G.bandLowerLeftConnector hx₀ r C k) (G.bandBottomEdge r k)
    (G.bandLowerRightConnector hx₀ r C k)))

def bandTopClass
    (G : StaggeredCoverGrid U H bottom top)
    (hx₀ : ∀ i, x₀ ∈ U i) (r : Fin (G.extraRows + 2))
    (C : BoundaryConnectors (G.bandUpperBoundary r))
    (k : Fin (G.horizontal r.castSucc).subdivision.cells) :
    CoverGroup U x₀ hx₀ ((G.horizontal r.castSucc).label k) :=
  FundamentalGroup.fromPath (.mk (closeEdge
    (G.bandUpperLeftConnector hx₀ r C k) (G.bandTopEdge r k)
    (G.bandUpperRightConnector hx₀ r C k)))

def bandLeftClass
    (G : StaggeredCoverGrid U H bottom top)
    (hx₀ : ∀ i, x₀ ∈ U i) (r : Fin (G.extraRows + 2))
    (C₀ : BoundaryConnectors (G.bandLowerBoundary r))
    (C₁ : BoundaryConnectors (G.bandUpperBoundary r))
    (k : Fin (G.horizontal r.castSucc).subdivision.cells) :
    CoverGroup U x₀ hx₀ ((G.horizontal r.castSucc).label k) :=
  FundamentalGroup.fromPath (.mk (G.bandLeftLoop hx₀ r C₀ C₁ k))

def bandRightClass
    (G : StaggeredCoverGrid U H bottom top)
    (hx₀ : ∀ i, x₀ ∈ U i) (r : Fin (G.extraRows + 2))
    (C₀ : BoundaryConnectors (G.bandLowerBoundary r))
    (C₁ : BoundaryConnectors (G.bandUpperBoundary r))
    (k : Fin (G.horizontal r.castSucc).subdivision.cells) :
    CoverGroup U x₀ hx₀ ((G.horizontal r.castSucc).label k) :=
  FundamentalGroup.fromPath (.mk (G.bandRightLoop hx₀ r C₀ C₁ k))

theorem bandCell_relation
    (G : StaggeredCoverGrid U H bottom top)
    (hx₀ : ∀ i, x₀ ∈ U i) (r : Fin (G.extraRows + 2))
    (C₀ : BoundaryConnectors (G.bandLowerBoundary r))
    (C₁ : BoundaryConnectors (G.bandUpperBoundary r))
    (k : Fin (G.horizontal r.castSucc).subdivision.cells) :
    G.bandBottomClass hx₀ r C₀ k =
      (G.bandRightClass hx₀ r C₀ C₁ k)⁻¹ *
        G.bandTopClass hx₀ r C₁ k * G.bandLeftClass hx₀ r C₀ C₁ k := by
  exact fundamentalGroup_cell_relation
    (G.bandLowerLeftConnector hx₀ r C₀ k)
    (G.bandLowerRightConnector hx₀ r C₀ k)
    (G.bandUpperLeftConnector hx₀ r C₁ k)
    (G.bandUpperRightConnector hx₀ r C₁ k)
    (G.bandBottomEdge r k) (G.bandRightEdge r k)
    (G.bandLeftEdge r k) (G.bandTopEdge r k)
    ⟨UnitSquare.mappedBoundaryHomotopy (G.lowerBandCellMap r k)⟩

theorem bandRightLoop_map_eq_bandLeftLoop_map
    (G : StaggeredCoverGrid U H bottom top)
    (hx₀ : ∀ i, x₀ ∈ U i) (r : Fin (G.extraRows + 2))
    (C₀ : BoundaryConnectors (G.bandLowerBoundary r))
    (C₁ : BoundaryConnectors (G.bandUpperBoundary r))
    {n : ℕ} (hn : n + 1 = (G.horizontal r.castSucc).subdivision.cells)
    (k : Fin n) :
    (G.bandRightLoop hx₀ r C₀ C₁ (Fin.cast hn k.castSucc)).map
        (continuous_subtype_val : Continuous
          (fun z : U ((G.horizontal r.castSucc).label (Fin.cast hn k.castSucc)) =>
            (z : X))) =
      (G.bandLeftLoop hx₀ r C₀ C₁ (Fin.cast hn k.succ)).map
        (continuous_subtype_val : Continuous
          (fun z : U ((G.horizontal r.castSucc).label (Fin.cast hn k.succ)) =>
            (z : X))) := by
  have hlower (t : I) :
      ((G.bandLowerRightConnector hx₀ r C₀
        (Fin.cast hn k.castSucc) t :
          U ((G.horizontal r.castSucc).label (Fin.cast hn k.castSucc))) : X) =
      ((G.bandLowerLeftConnector hx₀ r C₀
        (Fin.cast hn k.succ) t :
          U ((G.horizontal r.castSucc).label (Fin.cast hn k.succ))) : X) := by
    change C₀.path (Fin.cast hn k.castSucc).succ t =
      C₀.path (Fin.cast hn k.succ).castSucc t
    congr 1
  have hedge (t : I) :
      ((G.bandRightEdge r (Fin.cast hn k.castSucc) t :
          U ((G.horizontal r.castSucc).label (Fin.cast hn k.castSucc))) : X) =
      ((G.bandLeftEdge r (Fin.cast hn k.succ) t :
          U ((G.horizontal r.castSucc).label (Fin.cast hn k.succ))) : X) := by
    unfold bandRightEdge bandLeftEdge
    change ((G.lowerBandCellMap r (Fin.cast hn k.castSucc)
        (UnitSquare.right t)) : X) =
      ((G.lowerBandCellMap r (Fin.cast hn k.succ)
        (UnitSquare.left t)) : X)
    unfold UnitSquare.right UnitSquare.left
    simp only [Path.prod_coe, UnitSquare.idPath, Path.refl_apply]
    unfold lowerBandCellMap bandCellMap
    change H
      (Icc.convexComb (G.level r.castSucc.castSucc)
        (G.level r.castSucc.succ) (UnitSquare.idPath t),
       Icc.convexComb
        ((G.horizontal r.castSucc).subdivision.point
          (Fin.cast hn k.castSucc).castSucc)
        ((G.horizontal r.castSucc).subdivision.point
          (Fin.cast hn k.castSucc).succ) 1) =
      H
      (Icc.convexComb (G.level r.castSucc.castSucc)
        (G.level r.castSucc.succ) (UnitSquare.idPath t),
       Icc.convexComb
        ((G.horizontal r.castSucc).subdivision.point
          (Fin.cast hn k.succ).castSucc)
        ((G.horizontal r.castSucc).subdivision.point
          (Fin.cast hn k.succ).succ) 0)
    have hone : Icc.convexComb
        ((G.horizontal r.castSucc).subdivision.point
          (Fin.cast hn k.castSucc).castSucc)
        ((G.horizontal r.castSucc).subdivision.point
          (Fin.cast hn k.castSucc).succ) 1 =
        (G.horizontal r.castSucc).subdivision.point
          (Fin.cast hn k.castSucc).succ := by
      apply Subtype.ext
      simp only [Icc.coe_convexComb]
      norm_num
    have hzero : Icc.convexComb
        ((G.horizontal r.castSucc).subdivision.point
          (Fin.cast hn k.succ).castSucc)
        ((G.horizontal r.castSucc).subdivision.point
          (Fin.cast hn k.succ).succ) 0 =
        (G.horizontal r.castSucc).subdivision.point
          (Fin.cast hn k.succ).castSucc := by
      apply Subtype.ext
      simp only [Icc.coe_convexComb]
      norm_num
    rw [hone, hzero]
    congr 2
  have hupper (t : I) :
      ((G.bandUpperRightConnector hx₀ r C₁
        (Fin.cast hn k.castSucc) t :
          U ((G.horizontal r.castSucc).label (Fin.cast hn k.castSucc))) : X) =
      ((G.bandUpperLeftConnector hx₀ r C₁
        (Fin.cast hn k.succ) t :
          U ((G.horizontal r.castSucc).label (Fin.cast hn k.succ))) : X) := by
    change C₁.path (Fin.cast hn k.castSucc).succ t =
      C₁.path (Fin.cast hn k.succ).castSucc t
    congr 1
  ext t
  change ((G.bandRightLoop hx₀ r C₀ C₁ (Fin.cast hn k.castSucc) t :
      U ((G.horizontal r.castSucc).label (Fin.cast hn k.castSucc))) : X) =
    ((G.bandLeftLoop hx₀ r C₀ C₁ (Fin.cast hn k.succ) t :
      U ((G.horizontal r.castSucc).label (Fin.cast hn k.succ))) : X)
  unfold bandRightLoop bandLeftLoop closeEdge
  simp only [Path.trans_apply]
  split
  · exact hlower _
  · split
    · exact hedge _
    · change
        ((G.bandUpperRightConnector hx₀ r C₁
          (Fin.cast hn k.castSucc) (σ _) :
            U ((G.horizontal r.castSucc).label (Fin.cast hn k.castSucc))) : X) =
        ((G.bandUpperLeftConnector hx₀ r C₁
          (Fin.cast hn k.succ) (σ _) :
            U ((G.horizontal r.castSucc).label (Fin.cast hn k.succ))) : X)
      exact hupper _

end StaggeredCoverGrid

end Hatcher.VanKampen
