import Hatcher.VanKampen.HomotopySweep

noncomputable section

open Set
open scoped unitInterval

namespace Hatcher.VanKampen.StaggeredCoverGrid

universe u v

variable {ι : Type u} {X : Type v} [TopologicalSpace X]
  {U : ι → Set X} {x₀ : X} {hx₀ : ∀ i, x₀ ∈ U i}
  {p q γ δ : Path x₀ x₀}
  {H : p.Homotopy q} {bottom : BoundaryCover U p}
  {top : BoundaryCover U q}

/-- The final interface, immediately below the final grid band. -/
def finalInterface (G : StaggeredCoverGrid U H bottom top) :
    Fin (G.extraRows + 2) :=
  Fin.last (G.extraRows + 1)

/-- The final grid band. -/
def finalBand (G : StaggeredCoverGrid U H bottom top) :
    Fin (G.extraRows + 3) :=
  Fin.last (G.extraRows + 2)

@[simp]
theorem finalInterface_succ (G : StaggeredCoverGrid U H bottom top) :
    G.finalInterface.succ = G.finalBand := by
  apply Fin.ext
  rfl

@[simp]
theorem finalBand_succ (G : StaggeredCoverGrid U H bottom top) :
    G.finalBand.succ = Fin.last (G.extraRows + 3) := by
  apply Fin.ext
  rfl

/-- The lower boundary of the final grid band, with the final row's coarse
subdivision and labels. -/
def finalBandLowerBoundary (G : StaggeredCoverGrid U H bottom top) :
    BoundaryCover U (G.interfacePath G.finalInterface) where
  subdivision := (G.horizontal G.finalBand).subdivision
  label := (G.horizontal G.finalBand).label
  mapsTo k x hx := by
    apply G.subordinate G.finalBand k
    refine ⟨⟨le_rfl, ?_⟩, hx⟩
    have hindex : G.finalInterface.castSucc.succ = G.finalBand.castSucc := by
      apply Fin.ext
      rfl
    rw [hindex]
    exact (G.level_strictMono Fin.castSucc_lt_succ).le

/-- A final-row vertex, located in the common refinement at the final
interface. -/
def finalBandLowerVertex (G : StaggeredCoverGrid U H bottom top)
    (j : Fin ((G.horizontal G.finalBand).subdivision.cells + 1)) :
    Fin ((G.interfaceSubdivision G.finalInterface).cells + 1) :=
  IntervalSubdivision.commonRefinementRightVertex
    (G.horizontal G.finalInterface.castSucc).subdivision
    (G.horizontal G.finalInterface.succ).subdivision
    (Fin.cast (by rw [G.finalInterface_succ]) j)

theorem finalBandLowerVertex_spec
    (G : StaggeredCoverGrid U H bottom top)
    (j : Fin ((G.horizontal G.finalBand).subdivision.cells + 1)) :
    (G.interfaceSubdivision G.finalInterface).point
        (G.finalBandLowerVertex j) =
      (G.horizontal G.finalBand).subdivision.point j := by
  unfold finalBandLowerVertex interfaceSubdivision
  rw [IntervalSubdivision.commonRefinementRightVertex_spec]
  rfl

@[simp]
theorem finalBandLowerVertex_zero
    (G : StaggeredCoverGrid U H bottom top) :
    G.finalBandLowerVertex 0 = 0 := by
  apply (G.interfaceSubdivision G.finalInterface).strictMono.injective
  rw [G.finalBandLowerVertex_spec,
    (G.horizontal G.finalBand).subdivision.left,
    (G.interfaceSubdivision G.finalInterface).left]

@[simp]
theorem finalBandLowerVertex_last
    (G : StaggeredCoverGrid U H bottom top) :
    G.finalBandLowerVertex
        (Fin.last (G.horizontal G.finalBand).subdivision.cells) =
      Fin.last (G.interfaceSubdivision G.finalInterface).cells := by
  apply (G.interfaceSubdivision G.finalInterface).strictMono.injective
  rw [G.finalBandLowerVertex_spec,
    (G.horizontal G.finalBand).subdivision.right,
    (G.interfaceSubdivision G.finalInterface).right]

/-- Restrict the final interface connector to a vertex of the final row's
coarse subdivision. -/
def finalBandLowerConnectorPath
    (G : StaggeredCoverGrid U H bottom top)
    (hx₀ : ∀ i, x₀ ∈ U i)
    (hone : ∀ i, IsPathConnected (U i))
    (htwo : ∀ i j, IsPathConnected (U i ∩ U j))
    (hthree : ∀ i j k, IsPathConnected (U i ∩ U j ∩ U k))
    (j : Fin ((G.horizontal G.finalBand).subdivision.cells + 1)) :
    Path x₀
      (G.interfacePath G.finalInterface
        ((G.horizontal G.finalBand).subdivision.point j)) :=
  (G.interfaceVertexConnector hx₀ hone htwo hthree G.finalInterface
    (G.finalBandLowerVertex j)).cast rfl <| by
      exact congrArg (G.interfacePath G.finalInterface)
        (G.finalBandLowerVertex_spec j).symm

/-- Coarse lower connectors for the final grid band, sampled from the final
interface connector family. -/
def finalBandLowerConnectors
    (G : StaggeredCoverGrid U H bottom top)
    (hx₀ : ∀ i, x₀ ∈ U i)
    (hone : ∀ i, IsPathConnected (U i))
    (htwo : ∀ i j, IsPathConnected (U i ∩ U j))
    (hthree : ∀ i j k, IsPathConnected (U i ∩ U j ∩ U k)) :
    BoundaryConnectors G.finalBandLowerBoundary where
  path := G.finalBandLowerConnectorPath hx₀ hone htwo hthree
  left_eq := by
    change G.finalBandLowerConnectorPath hx₀ hone htwo hthree
        (0 : Fin ((G.horizontal G.finalBand).subdivision.cells + 1)) =
      (Path.refl x₀).cast rfl
        ((congrArg (G.interfacePath G.finalInterface)
          (G.horizontal G.finalBand).subdivision.left).trans
          (G.interfacePath G.finalInterface).source)
    ext t
    unfold finalBandLowerConnectorPath
    rw [Path.cast_coe, G.finalBandLowerVertex_zero]
    unfold interfaceVertexConnector
    rw [dif_pos rfl, Path.cast_coe, Path.cast_coe]
  right_eq := by
    change G.finalBandLowerConnectorPath hx₀ hone htwo hthree
        (Fin.last (G.horizontal G.finalBand).subdivision.cells) =
      (Path.refl x₀).cast rfl
        ((congrArg (G.interfacePath G.finalInterface)
          (G.horizontal G.finalBand).subdivision.right).trans
          (G.interfacePath G.finalInterface).target)
    ext t
    unfold finalBandLowerConnectorPath
    rw [Path.cast_coe, G.finalBandLowerVertex_last]
    unfold interfaceVertexConnector
    have hne : (Fin.last (G.interfaceSubdivision G.finalInterface).cells :
        Fin (G.interfaceSubdivision G.finalInterface).cells.succ) ≠ 0 := by
      intro h
      have hval : (G.interfaceSubdivision G.finalInterface).cells = 0 := by
        simpa using congrArg Fin.val h
      exact (Nat.ne_of_gt
        (G.interfaceSubdivision G.finalInterface).cells_pos) hval
    rw [dif_neg hne, dif_pos rfl, Path.cast_coe, Path.cast_coe]
  range_left k := by
    classical
    change Fin ((G.horizontal G.finalBand).subdivision.cells) at k
    change Set.range (G.finalBandLowerConnectorPath hx₀ hone htwo hthree
      k.castSucc) ⊆ U ((G.horizontal G.finalBand).label k)
    unfold finalBandLowerConnectorPath
    intro y hy
    rcases hy with ⟨t, rfl⟩
    apply G.interfaceVertexConnector_range hx₀ hone htwo hthree
      G.finalInterface _ ?_ ⟨t, rfl⟩
    unfold interfaceLabels
    apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    refine ⟨Fin.cast (by rw [G.finalInterface_succ]) k, ?_, ?_⟩
    · rw [IntervalSubdivision.mem_incidentCells,
        G.finalBandLowerVertex_spec]
      exact ⟨le_rfl,
        ((G.horizontal G.finalBand).subdivision.strictMono
          Fin.castSucc_lt_succ).le⟩
    · rfl

  range_right k := by
    classical
    change Fin ((G.horizontal G.finalBand).subdivision.cells) at k
    change Set.range (G.finalBandLowerConnectorPath hx₀ hone htwo hthree
      k.succ) ⊆ U ((G.horizontal G.finalBand).label k)
    unfold finalBandLowerConnectorPath
    intro y hy
    rcases hy with ⟨t, rfl⟩
    apply G.interfaceVertexConnector_range hx₀ hone htwo hthree
      G.finalInterface _ ?_ ⟨t, rfl⟩
    unfold interfaceLabels
    apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    refine ⟨Fin.cast (by rw [G.finalInterface_succ]) k, ?_, ?_⟩
    · rw [IntervalSubdivision.mem_incidentCells,
        G.finalBandLowerVertex_spec]
      exact ⟨((G.horizontal G.finalBand).subdivision.strictMono
        Fin.castSucc_lt_succ).le, le_rfl⟩
    · rfl

@[simp]
theorem finalBandCellMap_zero_zero
    (G : StaggeredCoverGrid U H bottom top)
    (k : Fin (G.horizontal G.finalBand).subdivision.cells) :
    ((G.bandCellMap G.finalBand k ((0 : I), (0 : I))) : X) =
      G.interfacePath G.finalInterface
        ((G.horizontal G.finalBand).subdivision.point k.castSucc) := by
  unfold bandCellMap interfacePath
  have hindex : G.finalInterface.castSucc.succ = G.finalBand.castSucc := by
    apply Fin.ext
    rfl
  rw [hindex]
  simp

@[simp]
theorem finalBandCellMap_zero_one
    (G : StaggeredCoverGrid U H bottom top)
    (k : Fin (G.horizontal G.finalBand).subdivision.cells) :
    ((G.bandCellMap G.finalBand k ((0 : I), (1 : I))) : X) =
      G.interfacePath G.finalInterface
        ((G.horizontal G.finalBand).subdivision.point k.succ) := by
  unfold bandCellMap interfacePath
  have hindex : G.finalInterface.castSucc.succ = G.finalBand.castSucc := by
    apply Fin.ext
    rfl
  rw [hindex]
  simp

@[simp]
theorem finalBandCellMap_one_zero
    (G : StaggeredCoverGrid U H bottom top)
    (k : Fin (G.horizontal G.finalBand).subdivision.cells) :
    ((G.bandCellMap G.finalBand k ((1 : I), (0 : I))) : X) =
      G.lastBandUpperPath
        ((G.horizontal G.finalBand).subdivision.point k.castSucc) := by
  unfold bandCellMap lastBandUpperPath
  change H
      (Icc.convexComb (G.level G.finalBand.castSucc)
        (G.level G.finalBand.succ) 1,
       Icc.convexComb
        ((G.horizontal G.finalBand).subdivision.point k.castSucc)
        ((G.horizontal G.finalBand).subdivision.point k.succ) 0) =
    H (G.level (Fin.last (G.extraRows + 3)),
      (G.horizontal G.finalBand).subdivision.point k.castSucc)
  congr 1
  apply Prod.ext
  · simp
  · simp

@[simp]
theorem finalBandCellMap_one_one
    (G : StaggeredCoverGrid U H bottom top)
    (k : Fin (G.horizontal G.finalBand).subdivision.cells) :
    ((G.bandCellMap G.finalBand k ((1 : I), (1 : I))) : X) =
      G.lastBandUpperPath
        ((G.horizontal G.finalBand).subdivision.point k.succ) := by
  unfold bandCellMap lastBandUpperPath
  change H
      (Icc.convexComb (G.level G.finalBand.castSucc)
        (G.level G.finalBand.succ) 1,
       Icc.convexComb
        ((G.horizontal G.finalBand).subdivision.point k.castSucc)
        ((G.horizontal G.finalBand).subdivision.point k.succ) 1) =
    H (G.level (Fin.last (G.extraRows + 3)),
      (G.horizontal G.finalBand).subdivision.point k.succ)
  congr 1
  apply Prod.ext
  · simp
  · simp

def finalBandBottomEdge (G : StaggeredCoverGrid U H bottom top)
    (k : Fin (G.horizontal G.finalBand).subdivision.cells) :=
  UnitSquare.lower.map (G.bandCellMap G.finalBand k).continuous

def finalBandTopEdge (G : StaggeredCoverGrid U H bottom top)
    (k : Fin (G.horizontal G.finalBand).subdivision.cells) :=
  UnitSquare.upper.map (G.bandCellMap G.finalBand k).continuous

def finalBandLeftEdge (G : StaggeredCoverGrid U H bottom top)
    (k : Fin (G.horizontal G.finalBand).subdivision.cells) :=
  UnitSquare.left.map (G.bandCellMap G.finalBand k).continuous

def finalBandRightEdge (G : StaggeredCoverGrid U H bottom top)
    (k : Fin (G.horizontal G.finalBand).subdivision.cells) :=
  UnitSquare.right.map (G.bandCellMap G.finalBand k).continuous

def finalBandLowerLeftConnector
    (G : StaggeredCoverGrid U H bottom top)
    (hx₀ : ∀ i, x₀ ∈ U i)
    (C : BoundaryConnectors G.finalBandLowerBoundary)
    (k : Fin (G.horizontal G.finalBand).subdivision.cells) :
    Path (⟨x₀, hx₀ ((G.horizontal G.finalBand).label k)⟩ :
      U ((G.horizontal G.finalBand).label k))
      (G.bandCellMap G.finalBand k ((0 : I), (0 : I))) :=
  (C.leftPathIn (hx₀ := hx₀) k).cast rfl
    (Subtype.ext (G.finalBandCellMap_zero_zero k))

def finalBandLowerRightConnector
    (G : StaggeredCoverGrid U H bottom top)
    (hx₀ : ∀ i, x₀ ∈ U i)
    (C : BoundaryConnectors G.finalBandLowerBoundary)
    (k : Fin (G.horizontal G.finalBand).subdivision.cells) :
    Path (⟨x₀, hx₀ ((G.horizontal G.finalBand).label k)⟩ :
      U ((G.horizontal G.finalBand).label k))
      (G.bandCellMap G.finalBand k ((0 : I), (1 : I))) :=
  (C.rightPathIn (hx₀ := hx₀) k).cast rfl
    (Subtype.ext (G.finalBandCellMap_zero_one k))

def finalBandUpperLeftConnector
    (G : StaggeredCoverGrid U H bottom top)
    (hx₀ : ∀ i, x₀ ∈ U i)
    (C : BoundaryConnectors G.lastBandUpperBoundary)
    (k : Fin (G.horizontal G.finalBand).subdivision.cells) :
    Path (⟨x₀, hx₀ ((G.horizontal G.finalBand).label k)⟩ :
      U ((G.horizontal G.finalBand).label k))
      (G.bandCellMap G.finalBand k ((1 : I), (0 : I))) :=
  (C.leftPathIn (hx₀ := hx₀) k).cast rfl
    (Subtype.ext (G.finalBandCellMap_one_zero k))

def finalBandUpperRightConnector
    (G : StaggeredCoverGrid U H bottom top)
    (hx₀ : ∀ i, x₀ ∈ U i)
    (C : BoundaryConnectors G.lastBandUpperBoundary)
    (k : Fin (G.horizontal G.finalBand).subdivision.cells) :
    Path (⟨x₀, hx₀ ((G.horizontal G.finalBand).label k)⟩ :
      U ((G.horizontal G.finalBand).label k))
      (G.bandCellMap G.finalBand k ((1 : I), (1 : I))) :=
  (C.rightPathIn (hx₀ := hx₀) k).cast rfl
    (Subtype.ext (G.finalBandCellMap_one_one k))

def finalBandLeftLoop
    (G : StaggeredCoverGrid U H bottom top)
    (hx₀ : ∀ i, x₀ ∈ U i)
    (C₀ : BoundaryConnectors G.finalBandLowerBoundary)
    (C₁ : BoundaryConnectors G.lastBandUpperBoundary)
    (k : Fin (G.horizontal G.finalBand).subdivision.cells) :=
  closeEdge (G.finalBandLowerLeftConnector hx₀ C₀ k)
    (G.finalBandLeftEdge k) (G.finalBandUpperLeftConnector hx₀ C₁ k)

def finalBandRightLoop
    (G : StaggeredCoverGrid U H bottom top)
    (hx₀ : ∀ i, x₀ ∈ U i)
    (C₀ : BoundaryConnectors G.finalBandLowerBoundary)
    (C₁ : BoundaryConnectors G.lastBandUpperBoundary)
    (k : Fin (G.horizontal G.finalBand).subdivision.cells) :=
  closeEdge (G.finalBandLowerRightConnector hx₀ C₀ k)
    (G.finalBandRightEdge k) (G.finalBandUpperRightConnector hx₀ C₁ k)

def finalBandBottomClass
    (G : StaggeredCoverGrid U H bottom top)
    (hx₀ : ∀ i, x₀ ∈ U i)
    (C : BoundaryConnectors G.finalBandLowerBoundary)
    (k : Fin (G.horizontal G.finalBand).subdivision.cells) :
    CoverGroup U x₀ hx₀ ((G.horizontal G.finalBand).label k) :=
  FundamentalGroup.fromPath (.mk (closeEdge
    (G.finalBandLowerLeftConnector hx₀ C k) (G.finalBandBottomEdge k)
    (G.finalBandLowerRightConnector hx₀ C k)))

def finalBandTopClass
    (G : StaggeredCoverGrid U H bottom top)
    (hx₀ : ∀ i, x₀ ∈ U i)
    (C : BoundaryConnectors G.lastBandUpperBoundary)
    (k : Fin (G.horizontal G.finalBand).subdivision.cells) :
    CoverGroup U x₀ hx₀ ((G.horizontal G.finalBand).label k) :=
  FundamentalGroup.fromPath (.mk (closeEdge
    (G.finalBandUpperLeftConnector hx₀ C k) (G.finalBandTopEdge k)
    (G.finalBandUpperRightConnector hx₀ C k)))

def finalBandLeftClass
    (G : StaggeredCoverGrid U H bottom top)
    (hx₀ : ∀ i, x₀ ∈ U i)
    (C₀ : BoundaryConnectors G.finalBandLowerBoundary)
    (C₁ : BoundaryConnectors G.lastBandUpperBoundary)
    (k : Fin (G.horizontal G.finalBand).subdivision.cells) :
    CoverGroup U x₀ hx₀ ((G.horizontal G.finalBand).label k) :=
  FundamentalGroup.fromPath (.mk (G.finalBandLeftLoop hx₀ C₀ C₁ k))

def finalBandRightClass
    (G : StaggeredCoverGrid U H bottom top)
    (hx₀ : ∀ i, x₀ ∈ U i)
    (C₀ : BoundaryConnectors G.finalBandLowerBoundary)
    (C₁ : BoundaryConnectors G.lastBandUpperBoundary)
    (k : Fin (G.horizontal G.finalBand).subdivision.cells) :
    CoverGroup U x₀ hx₀ ((G.horizontal G.finalBand).label k) :=
  FundamentalGroup.fromPath (.mk (G.finalBandRightLoop hx₀ C₀ C₁ k))

theorem finalBandCell_relation
    (G : StaggeredCoverGrid U H bottom top)
    (hx₀ : ∀ i, x₀ ∈ U i)
    (C₀ : BoundaryConnectors G.finalBandLowerBoundary)
    (C₁ : BoundaryConnectors G.lastBandUpperBoundary)
    (k : Fin (G.horizontal G.finalBand).subdivision.cells) :
    G.finalBandBottomClass hx₀ C₀ k =
      (G.finalBandRightClass hx₀ C₀ C₁ k)⁻¹ *
        G.finalBandTopClass hx₀ C₁ k *
          G.finalBandLeftClass hx₀ C₀ C₁ k := by
  exact fundamentalGroup_cell_relation
    (G.finalBandLowerLeftConnector hx₀ C₀ k)
    (G.finalBandLowerRightConnector hx₀ C₀ k)
    (G.finalBandUpperLeftConnector hx₀ C₁ k)
    (G.finalBandUpperRightConnector hx₀ C₁ k)
    (G.finalBandBottomEdge k) (G.finalBandRightEdge k)
    (G.finalBandLeftEdge k) (G.finalBandTopEdge k)
    ⟨UnitSquare.mappedBoundaryHomotopy (G.bandCellMap G.finalBand k)⟩

theorem finalBandRightLoop_map_eq_leftLoop_map
    (G : StaggeredCoverGrid U H bottom top)
    (hx₀ : ∀ i, x₀ ∈ U i)
    (C₀ : BoundaryConnectors G.finalBandLowerBoundary)
    (C₁ : BoundaryConnectors G.lastBandUpperBoundary)
    {n : ℕ} (hn : n + 1 = (G.horizontal G.finalBand).subdivision.cells)
    (k : Fin n) :
    (G.finalBandRightLoop hx₀ C₀ C₁ (Fin.cast hn k.castSucc)).map
        (continuous_subtype_val : Continuous
          (fun z : U ((G.horizontal G.finalBand).label
            (Fin.cast hn k.castSucc)) => (z : X))) =
      (G.finalBandLeftLoop hx₀ C₀ C₁ (Fin.cast hn k.succ)).map
        (continuous_subtype_val : Continuous
          (fun z : U ((G.horizontal G.finalBand).label
            (Fin.cast hn k.succ)) => (z : X))) := by
  have hlower (t : I) :
      ((G.finalBandLowerRightConnector hx₀ C₀
        (Fin.cast hn k.castSucc) t :
          U ((G.horizontal G.finalBand).label
            (Fin.cast hn k.castSucc))) : X) =
      ((G.finalBandLowerLeftConnector hx₀ C₀
        (Fin.cast hn k.succ) t :
          U ((G.horizontal G.finalBand).label
            (Fin.cast hn k.succ))) : X) := by
    change C₀.path (Fin.cast hn k.castSucc).succ t =
      C₀.path (Fin.cast hn k.succ).castSucc t
    congr 1
  have hedge (t : I) :
      ((G.finalBandRightEdge (Fin.cast hn k.castSucc) t :
          U ((G.horizontal G.finalBand).label
            (Fin.cast hn k.castSucc))) : X) =
      ((G.finalBandLeftEdge (Fin.cast hn k.succ) t :
          U ((G.horizontal G.finalBand).label
            (Fin.cast hn k.succ))) : X) := by
    unfold finalBandRightEdge finalBandLeftEdge
    change ((G.bandCellMap G.finalBand (Fin.cast hn k.castSucc)
        (UnitSquare.right t)) : X) =
      ((G.bandCellMap G.finalBand (Fin.cast hn k.succ)
        (UnitSquare.left t)) : X)
    unfold UnitSquare.right UnitSquare.left
    simp only [Path.prod_coe, UnitSquare.idPath, Path.refl_apply]
    unfold bandCellMap
    change H
      (Icc.convexComb (G.level G.finalBand.castSucc)
        (G.level G.finalBand.succ) (UnitSquare.idPath t),
       Icc.convexComb
        ((G.horizontal G.finalBand).subdivision.point
          (Fin.cast hn k.castSucc).castSucc)
        ((G.horizontal G.finalBand).subdivision.point
          (Fin.cast hn k.castSucc).succ) 1) =
      H
      (Icc.convexComb (G.level G.finalBand.castSucc)
        (G.level G.finalBand.succ) (UnitSquare.idPath t),
       Icc.convexComb
        ((G.horizontal G.finalBand).subdivision.point
          (Fin.cast hn k.succ).castSucc)
        ((G.horizontal G.finalBand).subdivision.point
          (Fin.cast hn k.succ).succ) 0)
    have hone : Icc.convexComb
        ((G.horizontal G.finalBand).subdivision.point
          (Fin.cast hn k.castSucc).castSucc)
        ((G.horizontal G.finalBand).subdivision.point
          (Fin.cast hn k.castSucc).succ) 1 =
        (G.horizontal G.finalBand).subdivision.point
          (Fin.cast hn k.castSucc).succ := by
      apply Subtype.ext
      simp only [Icc.coe_convexComb]
      norm_num
    have hzero : Icc.convexComb
        ((G.horizontal G.finalBand).subdivision.point
          (Fin.cast hn k.succ).castSucc)
        ((G.horizontal G.finalBand).subdivision.point
          (Fin.cast hn k.succ).succ) 0 =
        (G.horizontal G.finalBand).subdivision.point
          (Fin.cast hn k.succ).castSucc := by
      apply Subtype.ext
      simp only [Icc.coe_convexComb]
      norm_num
    rw [hone, hzero]
    congr 2
  have hupper (t : I) :
      ((G.finalBandUpperRightConnector hx₀ C₁
        (Fin.cast hn k.castSucc) t :
          U ((G.horizontal G.finalBand).label
            (Fin.cast hn k.castSucc))) : X) =
      ((G.finalBandUpperLeftConnector hx₀ C₁
        (Fin.cast hn k.succ) t :
          U ((G.horizontal G.finalBand).label
            (Fin.cast hn k.succ))) : X) := by
    change C₁.path (Fin.cast hn k.castSucc).succ t =
      C₁.path (Fin.cast hn k.succ).castSucc t
    congr 1
  ext t
  change ((G.finalBandRightLoop hx₀ C₀ C₁
      (Fin.cast hn k.castSucc) t :
        U ((G.horizontal G.finalBand).label
          (Fin.cast hn k.castSucc))) : X) =
    ((G.finalBandLeftLoop hx₀ C₀ C₁
      (Fin.cast hn k.succ) t :
        U ((G.horizontal G.finalBand).label
          (Fin.cast hn k.succ))) : X)
  unfold finalBandRightLoop finalBandLeftLoop closeEdge
  simp only [Path.trans_apply]
  split
  · exact hlower _
  · split
    · exact hedge _
    · change
        ((G.finalBandUpperRightConnector hx₀ C₁
          (Fin.cast hn k.castSucc) (σ _) :
            U ((G.horizontal G.finalBand).label
              (Fin.cast hn k.castSucc))) : X) =
        ((G.finalBandUpperLeftConnector hx₀ C₁
          (Fin.cast hn k.succ) (σ _) :
            U ((G.horizontal G.finalBand).label
              (Fin.cast hn k.succ))) : X)
      exact hupper _

def finalBandVerticalOverlapFactor
    (G : StaggeredCoverGrid U H bottom top)
    (hx₀ : ∀ i, x₀ ∈ U i)
    (C₀ : BoundaryConnectors G.finalBandLowerBoundary)
    (C₁ : BoundaryConnectors G.lastBandUpperBoundary)
    {n : ℕ} (hn : n + 1 = (G.horizontal G.finalBand).subdivision.cells)
    (k : Fin n) :
    Path
      (⟨x₀, ⟨hx₀ ((G.horizontal G.finalBand).label
          (Fin.cast hn k.castSucc)),
        hx₀ ((G.horizontal G.finalBand).label
          (Fin.cast hn k.succ))⟩⟩ :
        (U ((G.horizontal G.finalBand).label
            (Fin.cast hn k.castSucc)) ∩
          U ((G.horizontal G.finalBand).label
            (Fin.cast hn k.succ)) : Set X))
      ⟨x₀, ⟨hx₀ ((G.horizontal G.finalBand).label
          (Fin.cast hn k.castSucc)),
        hx₀ ((G.horizontal G.finalBand).label
          (Fin.cast hn k.succ))⟩⟩ := by
  let rf := G.finalBandRightLoop hx₀ C₀ C₁ (Fin.cast hn k.castSucc)
  let lf := G.finalBandLeftLoop hx₀ C₀ C₁ (Fin.cast hn k.succ)
  have hmap : rf.map
        (continuous_subtype_val : Continuous
          (fun z : U ((G.horizontal G.finalBand).label
            (Fin.cast hn k.castSucc)) => (z : X))) =
      lf.map
        (continuous_subtype_val : Continuous
          (fun z : U ((G.horizontal G.finalBand).label
            (Fin.cast hn k.succ)) => (z : X))) :=
    G.finalBandRightLoop_map_eq_leftLoop_map hx₀ C₀ C₁ hn k
  refine
    { toFun := fun t ↦ ⟨(rf t : X), ⟨(rf t).property, ?_⟩⟩
      continuous_toFun := (continuous_subtype_val.comp rf.continuous).subtype_mk _
      source' := by
        apply Subtype.ext
        change (rf 0 : X) = x₀
        exact congrArg Subtype.val rf.source
      target' := by
        apply Subtype.ext
        change (rf 1 : X) = x₀
        exact congrArg Subtype.val rf.target }
  have ht := congrArg (fun z : Path x₀ x₀ ↦ z t) hmap
  change (rf t : X) = (lf t : X) at ht
  rw [ht]
  exact (lf t).property

def finalBandVerticalOverlapClass
    (G : StaggeredCoverGrid U H bottom top)
    (hx₀ : ∀ i, x₀ ∈ U i)
    (C₀ : BoundaryConnectors G.finalBandLowerBoundary)
    (C₁ : BoundaryConnectors G.lastBandUpperBoundary)
    {n : ℕ} (hn : n + 1 = (G.horizontal G.finalBand).subdivision.cells)
    (k : Fin n) :
    OverlapGroup U x₀ hx₀
      ((G.horizontal G.finalBand).label (Fin.cast hn k.castSucc))
      ((G.horizontal G.finalBand).label (Fin.cast hn k.succ)) :=
  Path.Homotopic.Quotient.mk
    (G.finalBandVerticalOverlapFactor hx₀ C₀ C₁ hn k)

theorem overlapToLeft_finalBandVerticalOverlapClass
    (G : StaggeredCoverGrid U H bottom top)
    (hx₀ : ∀ i, x₀ ∈ U i)
    (C₀ : BoundaryConnectors G.finalBandLowerBoundary)
    (C₁ : BoundaryConnectors G.lastBandUpperBoundary)
    {n : ℕ} (hn : n + 1 = (G.horizontal G.finalBand).subdivision.cells)
    (k : Fin n) :
    overlapToLeft U x₀ hx₀
      ((G.horizontal G.finalBand).label (Fin.cast hn k.castSucc))
      ((G.horizontal G.finalBand).label (Fin.cast hn k.succ))
      (G.finalBandVerticalOverlapClass hx₀ C₀ C₁ hn k) =
    G.finalBandRightClass hx₀ C₀ C₁ (Fin.cast hn k.castSucc) := by
  change Path.Homotopic.Quotient.mk _ = Path.Homotopic.Quotient.mk _
  apply Path.Homotopic.Quotient.eq.mpr
  apply Path.Homotopic.refl

theorem overlapToRight_finalBandVerticalOverlapClass
    (G : StaggeredCoverGrid U H bottom top)
    (hx₀ : ∀ i, x₀ ∈ U i)
    (C₀ : BoundaryConnectors G.finalBandLowerBoundary)
    (C₁ : BoundaryConnectors G.lastBandUpperBoundary)
    {n : ℕ} (hn : n + 1 = (G.horizontal G.finalBand).subdivision.cells)
    (k : Fin n) :
    overlapToRight U x₀ hx₀
      ((G.horizontal G.finalBand).label (Fin.cast hn k.castSucc))
      ((G.horizontal G.finalBand).label (Fin.cast hn k.succ))
      (G.finalBandVerticalOverlapClass hx₀ C₀ C₁ hn k) =
    G.finalBandLeftClass hx₀ C₀ C₁ (Fin.cast hn k.succ) := by
  change Path.Homotopic.Quotient.mk _ = Path.Homotopic.Quotient.mk _
  apply Path.Homotopic.Quotient.eq.mpr
  convert Path.Homotopic.refl
    (G.finalBandLeftLoop hx₀ C₀ C₁ (Fin.cast hn k.succ)) using 1
  · rfl
  · rfl
  · ext t
    exact congrArg (fun z : Path x₀ x₀ ↦ z t)
      (G.finalBandRightLoop_map_eq_leftLoop_map hx₀ C₀ C₁ hn k)

theorem finalBandBottomClass_eq_factor
    (G : StaggeredCoverGrid U H bottom top)
    (hx₀ : ∀ i, x₀ ∈ U i)
    (C : BoundaryConnectors G.finalBandLowerBoundary)
    (k : Fin G.finalBandLowerBoundary.subdivision.cells) :
    G.finalBandBottomClass hx₀ C k =
      (Path.Homotopic.Quotient.mk (C.factor (hx₀ := hx₀) k) :
        CoverGroup U x₀ hx₀ (G.finalBandLowerBoundary.label k)) := by
  apply congrArg FundamentalGroup.fromPath
  apply Path.Homotopic.Quotient.eq.mpr
  have hleft (t : I) : G.finalBandLowerLeftConnector hx₀ C k t =
      C.leftPathIn (hx₀ := hx₀) k t := by
    apply Subtype.ext
    rfl
  have hedge (t : I) : G.finalBandBottomEdge k t =
      G.finalBandLowerBoundary.cellPathIn k t := by
    apply Subtype.ext
    change ((G.finalBandBottomEdge k t :
        U (G.finalBandLowerBoundary.label k)) : X) =
      G.interfacePath G.finalInterface (Icc.convexComb
        (G.finalBandLowerBoundary.subdivision.point k.castSucc)
        (G.finalBandLowerBoundary.subdivision.point k.succ) t)
    unfold finalBandBottomEdge
    rw [Path.map_coe]
    change ((G.bandCellMap G.finalBand k (UnitSquare.lower t)) : X) = _
    unfold UnitSquare.lower
    simp only [Path.prod_coe, Path.refl_apply, UnitSquare.idPath]
    unfold bandCellMap interfacePath
    have hindex : G.finalInterface.castSucc.succ =
        G.finalBand.castSucc := by
      apply Fin.ext
      rfl
    change H
        (Icc.convexComb (G.level G.finalBand.castSucc)
          (G.level G.finalBand.succ) 0,
         Icc.convexComb
          ((G.horizontal G.finalBand).subdivision.point k.castSucc)
          ((G.horizontal G.finalBand).subdivision.point k.succ) t) =
      H (G.level G.finalInterface.castSucc.succ,
        Icc.convexComb
          ((G.horizontal G.finalBand).subdivision.point k.castSucc)
          ((G.horizontal G.finalBand).subdivision.point k.succ) t)
    congr 1
    apply Prod.ext
    · simpa using congrArg G.level hindex.symm
    · rfl
  have hright (t : I) : G.finalBandLowerRightConnector hx₀ C k t =
      C.rightPathIn (hx₀ := hx₀) k t := by
    apply Subtype.ext
    rfl
  have hleftX (t : I) :
      ((G.finalBandLowerLeftConnector hx₀ C k t :
        U (G.finalBandLowerBoundary.label k)) : X) =
        C.path k.castSucc t := by
    exact congrArg Subtype.val (hleft t)
  have hedgeX (t : I) :
      ((G.finalBandBottomEdge k t :
        U (G.finalBandLowerBoundary.label k)) : X) =
        (G.interfacePath G.finalInterface).subpath
          (G.finalBandLowerBoundary.subdivision.point k.castSucc)
          (G.finalBandLowerBoundary.subdivision.point k.succ) t := by
    exact congrArg Subtype.val (hedge t)
  have hrightX (t : I) :
      ((G.finalBandLowerRightConnector hx₀ C k t :
        U (G.finalBandLowerBoundary.label k)) : X) =
        C.path k.succ t := by
    exact congrArg Subtype.val (hright t)
  have heq : closeEdge (G.finalBandLowerLeftConnector hx₀ C k)
      (G.finalBandBottomEdge k) (G.finalBandLowerRightConnector hx₀ C k) =
      C.factor (hx₀ := hx₀) k := by
    apply Path.ext
    funext t
    apply Subtype.ext
    change
      (((closeEdge (G.finalBandLowerLeftConnector hx₀ C k)
        (G.finalBandBottomEdge k) (G.finalBandLowerRightConnector hx₀ C k)).map
          (continuous_subtype_val : Continuous
            (fun z : U (G.finalBandLowerBoundary.label k) => (z : X)))) t) =
        (((C.factor (hx₀ := hx₀) k).map
          (continuous_subtype_val : Continuous
            (fun z : U (G.finalBandLowerBoundary.label k) => (z : X)))) t)
    rw [C.factor_map]
    unfold closeEdge
    simp only [Path.map_coe, Function.comp_apply]
    simp_rw [Path.trans_apply]
    split_ifs <;> simp_all only [Path.symm_apply, Function.comp_apply]
  rw [heq]

theorem finalBandTopClass_eq_factor
    (G : StaggeredCoverGrid U H bottom top)
    (hx₀ : ∀ i, x₀ ∈ U i)
    (C : BoundaryConnectors G.lastBandUpperBoundary)
    (k : Fin G.lastBandUpperBoundary.subdivision.cells) :
    G.finalBandTopClass hx₀ C k =
      (Path.Homotopic.Quotient.mk (C.factor (hx₀ := hx₀) k) :
        CoverGroup U x₀ hx₀ (G.lastBandUpperBoundary.label k)) := by
  apply congrArg FundamentalGroup.fromPath
  apply Path.Homotopic.Quotient.eq.mpr
  have hleft (t : I) : G.finalBandUpperLeftConnector hx₀ C k t =
      C.leftPathIn (hx₀ := hx₀) k t := by
    apply Subtype.ext
    rfl
  have hedge (t : I) : G.finalBandTopEdge k t =
      G.lastBandUpperBoundary.cellPathIn k t := by
    apply Subtype.ext
    change ((G.finalBandTopEdge k t :
        U (G.lastBandUpperBoundary.label k)) : X) =
      G.lastBandUpperPath (Icc.convexComb
        (G.lastBandUpperBoundary.subdivision.point k.castSucc)
        (G.lastBandUpperBoundary.subdivision.point k.succ) t)
    unfold finalBandTopEdge
    rw [Path.map_coe]
    change ((G.bandCellMap G.finalBand k (UnitSquare.upper t)) : X) = _
    unfold UnitSquare.upper
    simp only [Path.prod_coe, Path.refl_apply, UnitSquare.idPath]
    unfold bandCellMap lastBandUpperPath
    change H
        (Icc.convexComb (G.level G.finalBand.castSucc)
          (G.level G.finalBand.succ) 1,
         Icc.convexComb
          ((G.horizontal G.finalBand).subdivision.point k.castSucc)
          ((G.horizontal G.finalBand).subdivision.point k.succ) t) =
      H (G.level (Fin.last (G.extraRows + 3)),
        Icc.convexComb
          ((G.horizontal G.finalBand).subdivision.point k.castSucc)
          ((G.horizontal G.finalBand).subdivision.point k.succ) t)
    congr 1
    apply Prod.ext
    · simp [G.finalBand_succ]
    · rfl
  have hright (t : I) : G.finalBandUpperRightConnector hx₀ C k t =
      C.rightPathIn (hx₀ := hx₀) k t := by
    apply Subtype.ext
    rfl
  have hleftX (t : I) :
      ((G.finalBandUpperLeftConnector hx₀ C k t :
        U (G.lastBandUpperBoundary.label k)) : X) =
        C.path k.castSucc t := by
    exact congrArg Subtype.val (hleft t)
  have hedgeX (t : I) :
      ((G.finalBandTopEdge k t :
        U (G.lastBandUpperBoundary.label k)) : X) =
        G.lastBandUpperPath.subpath
          (G.lastBandUpperBoundary.subdivision.point k.castSucc)
          (G.lastBandUpperBoundary.subdivision.point k.succ) t := by
    exact congrArg Subtype.val (hedge t)
  have hrightX (t : I) :
      ((G.finalBandUpperRightConnector hx₀ C k t :
        U (G.lastBandUpperBoundary.label k)) : X) =
        C.path k.succ t := by
    exact congrArg Subtype.val (hright t)
  have heq : closeEdge (G.finalBandUpperLeftConnector hx₀ C k)
      (G.finalBandTopEdge k) (G.finalBandUpperRightConnector hx₀ C k) =
      C.factor (hx₀ := hx₀) k := by
    apply Path.ext
    funext t
    apply Subtype.ext
    change
      (((closeEdge (G.finalBandUpperLeftConnector hx₀ C k)
        (G.finalBandTopEdge k) (G.finalBandUpperRightConnector hx₀ C k)).map
          (continuous_subtype_val : Continuous
            (fun z : U (G.lastBandUpperBoundary.label k) => (z : X)))) t) =
        (((C.factor (hx₀ := hx₀) k).map
          (continuous_subtype_val : Continuous
            (fun z : U (G.lastBandUpperBoundary.label k) => (z : X)))) t)
    rw [C.factor_map]
    unfold closeEdge
    simp only [Path.map_coe, Function.comp_apply]
    simp_rw [Path.trans_apply]
    split_ifs <;> simp_all only [Path.symm_apply, Function.comp_apply]
  rw [heq]

theorem finalBandLeftClass_zero
    (G : StaggeredCoverGrid U H bottom top)
    (hx₀ : ∀ i, x₀ ∈ U i)
    (C₀ : BoundaryConnectors G.finalBandLowerBoundary)
    (C₁ : BoundaryConnectors G.lastBandUpperBoundary)
    {n : ℕ} (hn : n + 1 = (G.horizontal G.finalBand).subdivision.cells) :
    G.finalBandLeftClass hx₀ C₀ C₁
      (Fin.cast hn (0 : Fin (n + 1))) = 1 := by
  let k₀ := Fin.cast hn (0 : Fin (n + 1))
  have hlower (t : I) :
      ((G.finalBandLowerLeftConnector hx₀ C₀ k₀ t :
        U ((G.horizontal G.finalBand).label k₀)) : X) = x₀ := by
    change C₀.path
      (0 : Fin (G.finalBandLowerBoundary.subdivision.cells + 1)) t = x₀
    rw [C₀.left_eq, Path.cast_coe]
    rfl
  have hedge (t : I) :
      ((G.finalBandLeftEdge k₀ t :
        U ((G.horizontal G.finalBand).label k₀)) : X) = x₀ := by
    unfold finalBandLeftEdge
    rw [Path.map_coe]
    change ((G.bandCellMap G.finalBand k₀ (UnitSquare.left t)) : X) = x₀
    unfold bandCellMap
    change H
        (Icc.convexComb (G.level G.finalBand.castSucc)
          (G.level G.finalBand.succ) (UnitSquare.left t).1,
         Icc.convexComb
          ((G.horizontal G.finalBand).subdivision.point k₀.castSucc)
          ((G.horizontal G.finalBand).subdivision.point k₀.succ)
          (UnitSquare.left t).2) = x₀
    have hk : k₀.castSucc = 0 := by
      ext
      simp [k₀]
    rw [hk, (G.horizontal G.finalBand).subdivision.left]
    simp [UnitSquare.left, UnitSquare.idPath, H.source]
  have hupper (t : I) :
      ((G.finalBandUpperLeftConnector hx₀ C₁ k₀ t :
        U ((G.horizontal G.finalBand).label k₀)) : X) = x₀ := by
    change C₁.path
      (0 : Fin (G.lastBandUpperBoundary.subdivision.cells + 1)) t = x₀
    rw [C₁.left_eq, Path.cast_coe]
    rfl
  have hloop : G.finalBandLeftLoop hx₀ C₀ C₁ k₀ =
      Path.refl (⟨x₀, hx₀ ((G.horizontal G.finalBand).label k₀)⟩ :
        U ((G.horizontal G.finalBand).label k₀)) := by
    apply Path.ext
    funext t
    apply Subtype.ext
    unfold finalBandLeftLoop closeEdge
    simp only [Path.trans_apply, Path.refl_apply]
    split_ifs <;>
      simp_all only [Path.symm_apply, Function.comp_apply]
  unfold finalBandLeftClass
  change FundamentalGroup.fromPath
      (.mk (G.finalBandLeftLoop hx₀ C₀ C₁ k₀)) = 1
  rw [hloop, Path.Homotopic.Quotient.mk_refl]
  rfl

theorem finalBandRightClass_last
    (G : StaggeredCoverGrid U H bottom top)
    (hx₀ : ∀ i, x₀ ∈ U i)
    (C₀ : BoundaryConnectors G.finalBandLowerBoundary)
    (C₁ : BoundaryConnectors G.lastBandUpperBoundary)
    {n : ℕ} (hn : n + 1 = (G.horizontal G.finalBand).subdivision.cells) :
    G.finalBandRightClass hx₀ C₀ C₁
      (Fin.cast hn (Fin.last n)) = 1 := by
  let k₁ := Fin.cast hn (Fin.last n)
  have hk : k₁.succ =
      Fin.last (G.horizontal G.finalBand).subdivision.cells := by
    apply Fin.ext
    simp [k₁]
    omega
  have hlower (t : I) :
      ((G.finalBandLowerRightConnector hx₀ C₀ k₁ t :
        U ((G.horizontal G.finalBand).label k₁)) : X) = x₀ := by
    change C₀.path k₁.succ t = x₀
    rw [hk]
    change C₀.path
      (Fin.last G.finalBandLowerBoundary.subdivision.cells) t = x₀
    rw [C₀.right_eq, Path.cast_coe]
    rfl
  have hedge (t : I) :
      ((G.finalBandRightEdge k₁ t :
        U ((G.horizontal G.finalBand).label k₁)) : X) = x₀ := by
    unfold finalBandRightEdge
    rw [Path.map_coe]
    change ((G.bandCellMap G.finalBand k₁ (UnitSquare.right t)) : X) = x₀
    unfold bandCellMap
    change H
        (Icc.convexComb (G.level G.finalBand.castSucc)
          (G.level G.finalBand.succ) (UnitSquare.right t).1,
         Icc.convexComb
          ((G.horizontal G.finalBand).subdivision.point k₁.castSucc)
          ((G.horizontal G.finalBand).subdivision.point k₁.succ)
          (UnitSquare.right t).2) = x₀
    rw [hk, (G.horizontal G.finalBand).subdivision.right]
    simp [UnitSquare.right, UnitSquare.idPath, H.target]
  have hupper (t : I) :
      ((G.finalBandUpperRightConnector hx₀ C₁ k₁ t :
        U ((G.horizontal G.finalBand).label k₁)) : X) = x₀ := by
    change C₁.path k₁.succ t = x₀
    rw [hk]
    change C₁.path
      (Fin.last G.lastBandUpperBoundary.subdivision.cells) t = x₀
    rw [C₁.right_eq, Path.cast_coe]
    rfl
  have hloop : G.finalBandRightLoop hx₀ C₀ C₁ k₁ =
      Path.refl (⟨x₀, hx₀ ((G.horizontal G.finalBand).label k₁)⟩ :
        U ((G.horizontal G.finalBand).label k₁)) := by
    apply Path.ext
    funext t
    apply Subtype.ext
    unfold finalBandRightLoop closeEdge
    simp only [Path.trans_apply, Path.refl_apply]
    split_ifs <;>
      simp_all only [Path.symm_apply, Function.comp_apply]
  unfold finalBandRightClass
  change FundamentalGroup.fromPath
      (.mk (G.finalBandRightLoop hx₀ C₀ C₁ k₁)) = 1
  rw [hloop, Path.Homotopic.Quotient.mk_refl]
  rfl

/-- The cellular sweep across the final band, from its coarse lower boundary
to the original target subdivision at the top. -/
theorem finalBandCoarseMoves
    (G : StaggeredCoverGrid U H bottom top)
    (hx₀ : ∀ i, x₀ ∈ U i)
    (C₀ : BoundaryConnectors G.finalBandLowerBoundary)
    (C₁ : BoundaryConnectors G.lastBandUpperBoundary) :
    Factorization.Moves
      (C₀.toFactorization (hx₀ := hx₀)).entries
      (C₁.toFactorization (hx₀ := hx₀)).entries := by
  let n := (G.horizontal G.finalBand).subdivision.cells - 1
  have hn : n + 1 = (G.horizontal G.finalBand).subdivision.cells :=
    Nat.sub_add_cancel (G.horizontal G.finalBand).subdivision.cells_pos
  let index : Fin (n + 1) → ι := fun k ↦
    (G.horizontal G.finalBand).label (Fin.cast hn k)
  let bottomClass : ∀ k, CoverGroup U x₀ hx₀ (index k) := fun k ↦
    G.finalBandBottomClass hx₀ C₀ (Fin.cast hn k)
  let topClass : ∀ k, CoverGroup U x₀ hx₀ (index k) := fun k ↦
    G.finalBandTopClass hx₀ C₁ (Fin.cast hn k)
  let leftClass : ∀ k, CoverGroup U x₀ hx₀ (index k) := fun k ↦
    G.finalBandLeftClass hx₀ C₀ C₁ (Fin.cast hn k)
  let rightClass : ∀ k, CoverGroup U x₀ hx₀ (index k) := fun k ↦
    G.finalBandRightClass hx₀ C₀ C₁ (Fin.cast hn k)
  let overlap : ∀ k : Fin n,
      OverlapGroup U x₀ hx₀ (index k.castSucc) (index k.succ) := fun k ↦
    G.finalBandVerticalOverlapClass hx₀ C₀ C₁ hn k
  have hraw := Factorization.moves_of_band_cell_relations
    (U := U) (x₀ := x₀) (hx₀ := hx₀)
    index bottomClass topClass leftClass rightClass overlap
    (fun k ↦ G.finalBandCell_relation hx₀ C₀ C₁ (Fin.cast hn k))
    (fun k ↦ (G.overlapToLeft_finalBandVerticalOverlapClass
      hx₀ C₀ C₁ hn k).symm)
    (fun k ↦ (G.overlapToRight_finalBandVerticalOverlapClass
      hx₀ C₀ C₁ hn k).symm)
    (G.finalBandLeftClass_zero hx₀ C₀ C₁ hn)
    (G.finalBandRightClass_last hx₀ C₀ C₁ hn)
  have hbottom :
      (List.ofFn fun k ↦
        (⟨index k, bottomClass k⟩ : Factorization.Entry U x₀ hx₀)) =
        (C₀.toFactorization (hx₀ := hx₀)).entries := by
    rw [C₀.toFactorization_entries]
    rw [List.ofFn_congr hn]
    congr 1
    funext k
    apply Sigma.ext
    · rfl
    · exact heq_of_eq (G.finalBandBottomClass_eq_factor hx₀ C₀ k)
  have htop : Factorization.bandTopEntries index topClass =
      (C₁.toFactorization (hx₀ := hx₀)).entries := by
    rw [C₁.toFactorization_entries]
    unfold Factorization.bandTopEntries
    rw [List.ofFn_congr hn]
    congr 1
    funext k
    apply Sigma.ext
    · rfl
    · exact heq_of_eq (G.finalBandTopClass_eq_factor hx₀ C₁ k)
  rw [hbottom, htop] at hraw
  exact hraw

end Hatcher.VanKampen.StaggeredCoverGrid
