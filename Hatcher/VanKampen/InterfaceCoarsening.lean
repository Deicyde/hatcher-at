import Hatcher.VanKampen.InterfaceRefinement

noncomputable section

open Set
open scoped unitInterval

namespace Hatcher.VanKampen

universe u v

private theorem path_cast_apply_right {Y : Type*} [TopologicalSpace Y]
    {a b a' b' : Y} (p : Path a b) (ha : a' = a) (hb : b' = b)
    (t : I) : p.cast ha hb t = p t :=
  congrFun (Path.cast_coe p ha hb) t

private theorem ofFn_finCast_right {α : Type*} {m n : ℕ} (h : m = n)
    (f : Fin n → α) :
    List.ofFn (fun j : Fin m ↦ f (Fin.cast h j)) = List.ofFn f := by
  subst n
  rfl

private theorem coverLoopClass_heq_of_index_eq
    {ι : Type u} {X : Type v} [TopologicalSpace X]
    {U : ι → Set X} {x₀ : X} {hx₀ : ∀ i, x₀ ∈ U i}
    {i j : ι} (hij : i = j) (p : Path x₀ x₀)
    (hi : ∀ t, p t ∈ U i) (hj : ∀ t, p t ∈ U j) :
    HEq (Factorization.coverLoopClass (hx₀ := hx₀) i p hi)
      (Factorization.coverLoopClass (hx₀ := hx₀) j p hj) := by
  subst j
  exact heq_of_eq rfl

namespace IntervalSubdivision

theorem commonRefinementRightBlockVertex_strictMono
    (s t : IntervalSubdivision) (i : Fin t.cells) :
    StrictMono (commonRefinementRightBlockVertex s t i) := by
  intro j k hjk
  apply Fin.mk_lt_mk.mpr
  omega

theorem commonRefinementRightBlockPoint_mem_cell
    (s t : IntervalSubdivision) (i : Fin t.cells)
    (j : Fin (commonRefinementRightBlockSize s t i + 1)) :
    (commonRefinement s t).point
        (commonRefinementRightBlockVertex s t i j) ∈ t.cell i := by
  constructor
  · calc
      t.point i.castSucc = (commonRefinement s t).point
          (commonRefinementRightBlockVertex s t i 0) :=
        (commonRefinementRightBlockPoint_zero s t i).symm
      _ ≤ (commonRefinement s t).point
          (commonRefinementRightBlockVertex s t i j) :=
        (commonRefinement s t).strictMono.monotone
          ((commonRefinementRightBlockVertex_strictMono s t i).monotone
            (Fin.zero_le _))
  · calc
      (commonRefinement s t).point
          (commonRefinementRightBlockVertex s t i j) ≤
          (commonRefinement s t).point
            (commonRefinementRightBlockVertex s t i
              (Fin.last (commonRefinementRightBlockSize s t i))) :=
        (commonRefinement s t).strictMono.monotone
          ((commonRefinementRightBlockVertex_strictMono s t i).monotone
            (Fin.le_last _))
      _ = t.point i.succ := commonRefinementRightBlockPoint_last s t i

end IntervalSubdivision

namespace StaggeredCoverGrid

variable {ι : Type u} {X : Type v} [TopologicalSpace X]
  {U : ι → Set X} {x₀ : X} {p q : Path x₀ x₀}
  {H : p.Homotopy q} {bottom : BoundaryCover U p}
  {top : BoundaryCover U q}

/-- The interface path with the coarse subdivision and labels of the row
immediately above it. -/
def lowerCoarseBoundary (G : StaggeredCoverGrid U H bottom top)
    (r : Fin (G.extraRows + 2)) : BoundaryCover U (G.interfacePath r) where
  subdivision := (G.horizontal r.succ).subdivision
  label := (G.horizontal r.succ).label
  mapsTo k x hx := by
    have hlevel : G.level r.succ.castSucc ≤ G.level r.succ.succ :=
      (G.level_strictMono
        (show r.succ.castSucc < r.succ.succ from Fin.castSucc_lt_succ)).le
    exact G.subordinate r.succ k ⟨⟨le_rfl, hlevel⟩, hx⟩

def lowerCoarseVertex (G : StaggeredCoverGrid U H bottom top)
    (r : Fin (G.extraRows + 2))
    (j : Fin ((G.horizontal r.succ).subdivision.cells + 1)) :
    Fin ((G.interfaceSubdivision r).cells + 1) :=
  Fin.cast (by unfold interfaceSubdivision; rfl)
    (IntervalSubdivision.commonRefinementRightVertex
      (G.horizontal r.castSucc).subdivision
      (G.horizontal r.succ).subdivision j)

theorem lowerCoarseVertex_spec (G : StaggeredCoverGrid U H bottom top)
    (r : Fin (G.extraRows + 2))
    (j : Fin ((G.horizontal r.succ).subdivision.cells + 1)) :
    (G.interfaceSubdivision r).point (G.lowerCoarseVertex r j) =
      (G.horizontal r.succ).subdivision.point j := by
  unfold lowerCoarseVertex interfaceSubdivision
  exact IntervalSubdivision.commonRefinementRightVertex_spec _ _ j

@[simp]
theorem lowerCoarseVertex_zero (G : StaggeredCoverGrid U H bottom top)
    (r : Fin (G.extraRows + 2)) : G.lowerCoarseVertex r 0 = 0 := by
  apply (G.interfaceSubdivision r).strictMono.injective
  rw [G.lowerCoarseVertex_spec r, (G.horizontal r.succ).subdivision.left,
    (G.interfaceSubdivision r).left]

@[simp]
theorem lowerCoarseVertex_last (G : StaggeredCoverGrid U H bottom top)
    (r : Fin (G.extraRows + 2)) :
    G.lowerCoarseVertex r
        (Fin.last (G.horizontal r.succ).subdivision.cells) =
      Fin.last (G.interfaceSubdivision r).cells := by
  apply (G.interfaceSubdivision r).strictMono.injective
  rw [G.lowerCoarseVertex_spec r, (G.horizontal r.succ).subdivision.right,
    (G.interfaceSubdivision r).right]

def lowerCoarseConnectorPath
    (G : StaggeredCoverGrid U H bottom top)
    (hx₀ : ∀ i, x₀ ∈ U i)
    (hone : ∀ i, IsPathConnected (U i))
    (htwo : ∀ i j, IsPathConnected (U i ∩ U j))
    (hthree : ∀ i j k, IsPathConnected (U i ∩ U j ∩ U k))
    (r : Fin (G.extraRows + 2))
    (j : Fin ((G.horizontal r.succ).subdivision.cells + 1)) :
    Path x₀
      (G.interfacePath r ((G.horizontal r.succ).subdivision.point j)) :=
  (G.interfaceVertexConnector hx₀ hone htwo hthree r
    (G.lowerCoarseVertex r j)).cast rfl <| by
      exact congrArg (G.interfacePath r) (G.lowerCoarseVertex_spec r j).symm

def lowerCoarseConnectors
    (G : StaggeredCoverGrid U H bottom top)
    (hx₀ : ∀ i, x₀ ∈ U i)
    (hone : ∀ i, IsPathConnected (U i))
    (htwo : ∀ i j, IsPathConnected (U i ∩ U j))
    (hthree : ∀ i j k, IsPathConnected (U i ∩ U j ∩ U k))
    (r : Fin (G.extraRows + 2)) :
    BoundaryConnectors (G.lowerCoarseBoundary r) where
  path := G.lowerCoarseConnectorPath hx₀ hone htwo hthree r
  left_eq := by
    change G.lowerCoarseConnectorPath hx₀ hone htwo hthree r
        (0 : Fin ((G.horizontal r.succ).subdivision.cells + 1)) =
      (Path.refl x₀).cast rfl
        ((congrArg (G.interfacePath r)
          (G.horizontal r.succ).subdivision.left).trans
          (G.interfacePath r).source)
    ext t
    unfold lowerCoarseConnectorPath
    rw [Path.cast_coe]
    have hv := G.lowerCoarseVertex_zero r
    rw [hv]
    unfold interfaceVertexConnector
    rw [dif_pos rfl, Path.cast_coe, Path.cast_coe]
  right_eq := by
    change G.lowerCoarseConnectorPath hx₀ hone htwo hthree r
        (Fin.last (G.horizontal r.succ).subdivision.cells) =
      (Path.refl x₀).cast rfl
        ((congrArg (G.interfacePath r)
          (G.horizontal r.succ).subdivision.right).trans
          (G.interfacePath r).target)
    ext t
    unfold lowerCoarseConnectorPath
    rw [Path.cast_coe]
    have hv := G.lowerCoarseVertex_last r
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
    change Set.range (G.lowerCoarseConnectorPath hx₀ hone htwo hthree r
      k.castSucc) ⊆ U ((G.horizontal r.succ).label k)
    unfold lowerCoarseConnectorPath
    intro y hy
    rcases hy with ⟨t, rfl⟩
    apply G.interfaceVertexConnector_range hx₀ hone htwo hthree r _ ?_ ⟨t, rfl⟩
    unfold interfaceLabels
    apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    refine ⟨k, ?_, rfl⟩
    rw [IntervalSubdivision.mem_incidentCells, G.lowerCoarseVertex_spec r]
    exact ⟨le_rfl,
      ((G.horizontal r.succ).subdivision.strictMono
        Fin.castSucc_lt_succ).le⟩
  range_right k := by
    classical
    change Set.range (G.lowerCoarseConnectorPath hx₀ hone htwo hthree r
      k.succ) ⊆ U ((G.horizontal r.succ).label k)
    unfold lowerCoarseConnectorPath
    intro y hy
    rcases hy with ⟨t, rfl⟩
    apply G.interfaceVertexConnector_range hx₀ hone htwo hthree r _ ?_ ⟨t, rfl⟩
    unfold interfaceLabels
    apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    refine ⟨k, ?_, rfl⟩
    rw [IntervalSubdivision.mem_incidentCells, G.lowerCoarseVertex_spec r]
    exact ⟨((G.horizontal r.succ).subdivision.strictMono
      Fin.castSucc_lt_succ).le, le_rfl⟩

def lowerRefinedBlockPoint (G : StaggeredCoverGrid U H bottom top)
    (r : Fin (G.extraRows + 2))
    (k : Fin (G.horizontal r.succ).subdivision.cells)
    (j : Fin (IntervalSubdivision.commonRefinementRightBlockSize
      (G.horizontal r.castSucc).subdivision
      (G.horizontal r.succ).subdivision k + 1)) : I :=
  (G.interfaceSubdivision r).point
    (IntervalSubdivision.commonRefinementRightBlockVertex
      (G.horizontal r.castSucc).subdivision
      (G.horizontal r.succ).subdivision k j)

theorem lowerRefinedBlockPoint_mem_cell
    (G : StaggeredCoverGrid U H bottom top)
    (r : Fin (G.extraRows + 2))
    (k : Fin (G.horizontal r.succ).subdivision.cells)
    (j : Fin (IntervalSubdivision.commonRefinementRightBlockSize
      (G.horizontal r.castSucc).subdivision
      (G.horizontal r.succ).subdivision k + 1)) :
    G.lowerRefinedBlockPoint r k j ∈
      (G.horizontal r.succ).subdivision.cell k := by
  exact IntervalSubdivision.commonRefinementRightBlockPoint_mem_cell
    (G.horizontal r.castSucc).subdivision
    (G.horizontal r.succ).subdivision k j

theorem lowerRefinedBlockPoint_strictMono
    (G : StaggeredCoverGrid U H bottom top)
    (r : Fin (G.extraRows + 2))
    (k : Fin (G.horizontal r.succ).subdivision.cells) :
    StrictMono (G.lowerRefinedBlockPoint r k) :=
  (G.interfaceSubdivision r).strictMono.comp
    (IntervalSubdivision.commonRefinementRightBlockVertex_strictMono
      (G.horizontal r.castSucc).subdivision
      (G.horizontal r.succ).subdivision k)

theorem lowerRefinedBlockPoint_zero
    (G : StaggeredCoverGrid U H bottom top)
    (r : Fin (G.extraRows + 2))
    (k : Fin (G.horizontal r.succ).subdivision.cells) :
    G.lowerRefinedBlockPoint r k 0 =
      (G.horizontal r.succ).subdivision.point k.castSucc :=
  IntervalSubdivision.commonRefinementRightBlockPoint_zero
    (G.horizontal r.castSucc).subdivision
    (G.horizontal r.succ).subdivision k

theorem lowerRefinedBlockPoint_last
    (G : StaggeredCoverGrid U H bottom top)
    (r : Fin (G.extraRows + 2))
    (k : Fin (G.horizontal r.succ).subdivision.cells) :
    G.lowerRefinedBlockPoint r k
        (Fin.last (IntervalSubdivision.commonRefinementRightBlockSize
          (G.horizontal r.castSucc).subdivision
          (G.horizontal r.succ).subdivision k)) =
      (G.horizontal r.succ).subdivision.point k.succ :=
  IntervalSubdivision.commonRefinementRightBlockPoint_last
    (G.horizontal r.castSucc).subdivision
    (G.horizontal r.succ).subdivision k

def lowerRefinedBlockConnector
    (G : StaggeredCoverGrid U H bottom top)
    (hx₀ : ∀ i, x₀ ∈ U i)
    (hone : ∀ i, IsPathConnected (U i))
    (htwo : ∀ i j, IsPathConnected (U i ∩ U j))
    (hthree : ∀ i j k, IsPathConnected (U i ∩ U j ∩ U k))
    (r : Fin (G.extraRows + 2))
    (k : Fin (G.horizontal r.succ).subdivision.cells)
    (j : Fin (IntervalSubdivision.commonRefinementRightBlockSize
      (G.horizontal r.castSucc).subdivision
      (G.horizontal r.succ).subdivision k + 1)) :
    Path x₀ (G.interfacePath r (G.lowerRefinedBlockPoint r k j)) :=
  G.interfaceVertexConnector hx₀ hone htwo hthree r
    (IntervalSubdivision.commonRefinementRightBlockVertex
      (G.horizontal r.castSucc).subdivision
      (G.horizontal r.succ).subdivision k j)

theorem lowerRefinedBlockConnector_range
    (G : StaggeredCoverGrid U H bottom top)
    (hx₀ : ∀ i, x₀ ∈ U i)
    (hone : ∀ i, IsPathConnected (U i))
    (htwo : ∀ i j, IsPathConnected (U i ∩ U j))
    (hthree : ∀ i j k, IsPathConnected (U i ∩ U j ∩ U k))
    (r : Fin (G.extraRows + 2))
    (k : Fin (G.horizontal r.succ).subdivision.cells)
    (j : Fin (IntervalSubdivision.commonRefinementRightBlockSize
      (G.horizontal r.castSucc).subdivision
      (G.horizontal r.succ).subdivision k + 1)) :
    Set.range (G.lowerRefinedBlockConnector hx₀ hone htwo hthree r k j) ⊆
      U ((G.horizontal r.succ).label k) := by
  classical
  apply G.interfaceVertexConnector_range hx₀ hone htwo hthree r
  unfold interfaceLabels
  apply Finset.mem_union_right
  apply Finset.mem_image.mpr
  refine ⟨k, ?_, rfl⟩
  rw [IntervalSubdivision.mem_incidentCells]
  exact G.lowerRefinedBlockPoint_mem_cell r k j

def lowerRefinedBlockLoop
    (G : StaggeredCoverGrid U H bottom top)
    (hx₀ : ∀ i, x₀ ∈ U i)
    (hone : ∀ i, IsPathConnected (U i))
    (htwo : ∀ i j, IsPathConnected (U i ∩ U j))
    (hthree : ∀ i j k, IsPathConnected (U i ∩ U j ∩ U k))
    (r : Fin (G.extraRows + 2))
    (k : Fin (G.horizontal r.succ).subdivision.cells)
    (j : Fin (IntervalSubdivision.commonRefinementRightBlockSize
      (G.horizontal r.castSucc).subdivision
      (G.horizontal r.succ).subdivision k)) :
    Path
      (⟨x₀, hx₀ ((G.horizontal r.succ).label k)⟩ :
        U ((G.horizontal r.succ).label k))
      ⟨x₀, hx₀ ((G.horizontal r.succ).label k)⟩ :=
  basedSegmentLoopInSet
    (U ((G.horizontal r.succ).label k))
    (hx₀ ((G.horizontal r.succ).label k))
    (G.interfacePath r)
    (G.lowerRefinedBlockPoint r k j.castSucc)
    (G.lowerRefinedBlockPoint r k j.succ)
    ((G.lowerRefinedBlockPoint_strictMono r k) Fin.castSucc_lt_succ).le
    (G.lowerRefinedBlockConnector hx₀ hone htwo hthree r k j.castSucc)
    (G.lowerRefinedBlockConnector hx₀ hone htwo hthree r k j.succ)
    (fun t ↦ G.lowerRefinedBlockConnector_range
      hx₀ hone htwo hthree r k j.castSucc ⟨t, rfl⟩)
    (fun t ↦ G.lowerRefinedBlockConnector_range
      hx₀ hone htwo hthree r k j.succ ⟨t, rfl⟩)
    (fun _x hmem ↦ (G.lowerCoarseBoundary r).mapsTo k
      ⟨(G.lowerRefinedBlockPoint_mem_cell r k j.castSucc).1.trans hmem.1,
        hmem.2.trans (G.lowerRefinedBlockPoint_mem_cell r k j.succ).2⟩)

def lowerRefinedBlockClass
    (G : StaggeredCoverGrid U H bottom top)
    (hx₀ : ∀ i, x₀ ∈ U i)
    (hone : ∀ i, IsPathConnected (U i))
    (htwo : ∀ i j, IsPathConnected (U i ∩ U j))
    (hthree : ∀ i j k, IsPathConnected (U i ∩ U j ∩ U k))
    (r : Fin (G.extraRows + 2))
    (k : Fin (G.horizontal r.succ).subdivision.cells)
    (j : Fin (IntervalSubdivision.commonRefinementRightBlockSize
      (G.horizontal r.castSucc).subdivision
      (G.horizontal r.succ).subdivision k)) :
    CoverGroup U x₀ hx₀ ((G.horizontal r.succ).label k) :=
  FundamentalGroup.fromPath (.mk <|
    G.lowerRefinedBlockLoop hx₀ hone htwo hthree r k j)

theorem reverseProd_lowerRefinedBlockClass_eq
    (G : StaggeredCoverGrid U H bottom top)
    (hx₀ : ∀ i, x₀ ∈ U i)
    (hone : ∀ i, IsPathConnected (U i))
    (htwo : ∀ i j, IsPathConnected (U i ∩ U j))
    (hthree : ∀ i j k, IsPathConnected (U i ∩ U j ∩ U k))
    (r : Fin (G.extraRows + 2))
    (k : Fin (G.horizontal r.succ).subdivision.cells) :
    (List.ofFn fun j ↦
      G.lowerRefinedBlockClass hx₀ hone htwo hthree r k j).reverse.prod =
      FundamentalGroup.fromPath (.mk <|
        basedSegmentLoopInSet
          (U ((G.horizontal r.succ).label k))
          (hx₀ ((G.horizontal r.succ).label k))
          (G.interfacePath r)
          (G.lowerRefinedBlockPoint r k 0)
          (G.lowerRefinedBlockPoint r k
            (Fin.last (IntervalSubdivision.commonRefinementRightBlockSize
              (G.horizontal r.castSucc).subdivision
              (G.horizontal r.succ).subdivision k)))
          ((G.lowerRefinedBlockPoint_strictMono r k).monotone (Fin.zero_le _))
          (G.lowerRefinedBlockConnector hx₀ hone htwo hthree r k 0)
          (G.lowerRefinedBlockConnector hx₀ hone htwo hthree r k
            (Fin.last (IntervalSubdivision.commonRefinementRightBlockSize
              (G.horizontal r.castSucc).subdivision
              (G.horizontal r.succ).subdivision k)))
          (fun t ↦ G.lowerRefinedBlockConnector_range
            hx₀ hone htwo hthree r k 0 ⟨t, rfl⟩)
          (fun t ↦ G.lowerRefinedBlockConnector_range
            hx₀ hone htwo hthree r k
              (Fin.last (IntervalSubdivision.commonRefinementRightBlockSize
                (G.horizontal r.castSucc).subdivision
                (G.horizontal r.succ).subdivision k)) ⟨t, rfl⟩)
          (fun _x hmem ↦ (G.lowerCoarseBoundary r).mapsTo k
            ⟨(G.lowerRefinedBlockPoint_mem_cell r k 0).1.trans hmem.1,
              hmem.2.trans
                (G.lowerRefinedBlockPoint_mem_cell r k
                  (Fin.last (IntervalSubdivision.commonRefinementRightBlockSize
                    (G.horizontal r.castSucc).subdivision
                    (G.horizontal r.succ).subdivision k))).2⟩)) := by
  unfold lowerRefinedBlockClass lowerRefinedBlockLoop
  exact reverseProd_basedSegmentLoopInSet_eq
    (U ((G.horizontal r.succ).label k))
    (hx₀ ((G.horizontal r.succ).label k))
    (G.interfacePath r)
    ((G.horizontal r.succ).subdivision.point k.castSucc)
    ((G.horizontal r.succ).subdivision.point k.succ)
    ((G.horizontal r.succ).subdivision.strictMono Fin.castSucc_lt_succ)
    ((G.lowerCoarseBoundary r).mapsTo k)
    (IntervalSubdivision.commonRefinementRightBlockSize
      (G.horizontal r.castSucc).subdivision
      (G.horizontal r.succ).subdivision k)
    (G.lowerRefinedBlockPoint r k)
    (G.lowerRefinedBlockPoint_mem_cell r k)
    (G.lowerRefinedBlockPoint_strictMono r k)
    (G.lowerRefinedBlockConnector hx₀ hone htwo hthree r k)
    (fun j t ↦ G.lowerRefinedBlockConnector_range
      hx₀ hone htwo hthree r k j ⟨t, rfl⟩)

theorem reverseProd_lowerRefinedBlockClass_eq_lowerCoarseFactor
    (G : StaggeredCoverGrid U H bottom top)
    (hx₀ : ∀ i, x₀ ∈ U i)
    (hone : ∀ i, IsPathConnected (U i))
    (htwo : ∀ i j, IsPathConnected (U i ∩ U j))
    (hthree : ∀ i j k, IsPathConnected (U i ∩ U j ∩ U k))
    (r : Fin (G.extraRows + 2))
    (k : Fin (G.horizontal r.succ).subdivision.cells) :
    (List.ofFn fun j ↦
      G.lowerRefinedBlockClass hx₀ hone htwo hthree r k j).reverse.prod =
      (Path.Homotopic.Quotient.mk
        ((G.lowerCoarseConnectors hx₀ hone htwo hthree r).factor
          (hx₀ := hx₀) k) :
        CoverGroup U x₀ hx₀ ((G.horizontal r.succ).label k)) := by
  rw [G.reverseProd_lowerRefinedBlockClass_eq hx₀ hone htwo hthree r k]
  have hfactor := Factorization.boundaryConnector_factor_eq_coverLoopClass
    (hx₀ := hx₀) (G.lowerCoarseConnectors hx₀ hone htwo hthree r) k
  change _ = (Path.Homotopic.Quotient.mk
    ((G.lowerCoarseConnectors hx₀ hone htwo hthree r).factor
      (hx₀ := hx₀) k) :
    CoverGroup U x₀ hx₀ ((G.lowerCoarseBoundary r).label k))
  rw [hfactor]
  unfold Factorization.coverLoopClass
  apply Path.Homotopic.Quotient.eq.mpr
  have hlocalLeft (t : I) :
      G.lowerRefinedBlockConnector hx₀ hone htwo hthree r k 0 t ∈
        U ((G.horizontal r.succ).label k) :=
    G.lowerRefinedBlockConnector_range hx₀ hone htwo hthree r k 0
      ⟨t, rfl⟩
  have hlocalRight (t : I) :
      G.lowerRefinedBlockConnector hx₀ hone htwo hthree r k
          (Fin.last (IntervalSubdivision.commonRefinementRightBlockSize
            (G.horizontal r.castSucc).subdivision
            (G.horizontal r.succ).subdivision k)) t ∈
        U ((G.horizontal r.succ).label k) :=
    G.lowerRefinedBlockConnector_range hx₀ hone htwo hthree r k _
      ⟨t, rfl⟩
  have hlocalSegment : MapsTo (G.interfacePath r)
      (Icc (G.lowerRefinedBlockPoint r k 0)
        (G.lowerRefinedBlockPoint r k
          (Fin.last (IntervalSubdivision.commonRefinementRightBlockSize
            (G.horizontal r.castSucc).subdivision
            (G.horizontal r.succ).subdivision k))))
      (U ((G.horizontal r.succ).label k)) := by
    intro x hmem
    apply (G.lowerCoarseBoundary r).mapsTo k
    exact ⟨(G.lowerRefinedBlockPoint_mem_cell r k 0).1.trans hmem.1,
      hmem.2.trans
        (G.lowerRefinedBlockPoint_mem_cell r k
          (Fin.last (IntervalSubdivision.commonRefinementRightBlockSize
            (G.horizontal r.castSucc).subdivision
            (G.horizontal r.succ).subdivision k))).2⟩
  have hcoarseLoop (t : I) :
      basedSegmentLoop (G.interfacePath r)
          ((G.lowerCoarseBoundary r).subdivision.point k.castSucc)
          ((G.lowerCoarseBoundary r).subdivision.point k.succ)
          ((G.lowerCoarseConnectors hx₀ hone htwo hthree r).path k.castSucc)
          ((G.lowerCoarseConnectors hx₀ hone htwo hthree r).path k.succ) t ∈
        U ((G.lowerCoarseBoundary r).label k) := by
    apply basedSegmentLoop_mem _ _ _
      ((G.lowerCoarseBoundary r).subdivision.strictMono.monotone
        (Fin.castSucc_le_succ k)) _ _
    · exact fun t ↦ (G.lowerCoarseConnectors hx₀ hone htwo hthree r).range_left k
        ⟨t, rfl⟩
    · exact fun t ↦ (G.lowerCoarseConnectors hx₀ hone htwo hthree r).range_right k
        ⟨t, rfl⟩
    · exact (G.lowerCoarseBoundary r).mapsTo k
  have hpath :
      basedSegmentLoopInSet
          (U ((G.horizontal r.succ).label k))
          (hx₀ ((G.horizontal r.succ).label k))
          (G.interfacePath r)
          (G.lowerRefinedBlockPoint r k 0)
          (G.lowerRefinedBlockPoint r k
            (Fin.last (IntervalSubdivision.commonRefinementRightBlockSize
              (G.horizontal r.castSucc).subdivision
              (G.horizontal r.succ).subdivision k)))
          ((G.lowerRefinedBlockPoint_strictMono r k).monotone (Fin.zero_le _))
          (G.lowerRefinedBlockConnector hx₀ hone htwo hthree r k 0)
          (G.lowerRefinedBlockConnector hx₀ hone htwo hthree r k
            (Fin.last (IntervalSubdivision.commonRefinementRightBlockSize
              (G.horizontal r.castSucc).subdivision
              (G.horizontal r.succ).subdivision k)))
          hlocalLeft hlocalRight hlocalSegment =
        pathInSet
          (basedSegmentLoop (G.interfacePath r)
            ((G.lowerCoarseBoundary r).subdivision.point k.castSucc)
            ((G.lowerCoarseBoundary r).subdivision.point k.succ)
            ((G.lowerCoarseConnectors hx₀ hone htwo hthree r).path k.castSucc)
            ((G.lowerCoarseConnectors hx₀ hone htwo hthree r).path k.succ))
          (U ((G.lowerCoarseBoundary r).label k))
          (hx₀ ((G.lowerCoarseBoundary r).label k))
          (hx₀ ((G.lowerCoarseBoundary r).label k)) hcoarseLoop := by
    have hambient :
        basedSegmentLoop (G.interfacePath r)
            (G.lowerRefinedBlockPoint r k 0)
            (G.lowerRefinedBlockPoint r k
              (Fin.last (IntervalSubdivision.commonRefinementRightBlockSize
                (G.horizontal r.castSucc).subdivision
                (G.horizontal r.succ).subdivision k)))
            (G.lowerRefinedBlockConnector hx₀ hone htwo hthree r k 0)
            (G.lowerRefinedBlockConnector hx₀ hone htwo hthree r k
              (Fin.last (IntervalSubdivision.commonRefinementRightBlockSize
                (G.horizontal r.castSucc).subdivision
                (G.horizontal r.succ).subdivision k))) =
          basedSegmentLoop (G.interfacePath r)
            ((G.lowerCoarseBoundary r).subdivision.point k.castSucc)
            ((G.lowerCoarseBoundary r).subdivision.point k.succ)
            ((G.lowerCoarseConnectors hx₀ hone htwo hthree r).path k.castSucc)
            ((G.lowerCoarseConnectors hx₀ hone htwo hthree r).path k.succ) := by
      have hconnectorZero (t : I) :
          G.lowerRefinedBlockConnector hx₀ hone htwo hthree r k 0 t =
            (G.lowerCoarseConnectors hx₀ hone htwo hthree r).path k.castSucc t := by
        have hv :
            IntervalSubdivision.commonRefinementRightBlockVertex
                (G.horizontal r.castSucc).subdivision
                (G.horizontal r.succ).subdivision k 0 =
              G.lowerCoarseVertex r k.castSucc := by
          unfold lowerCoarseVertex interfaceSubdivision
          simp
        change
          G.interfaceVertexConnector hx₀ hone htwo hthree r
              (IntervalSubdivision.commonRefinementRightBlockVertex
                (G.horizontal r.castSucc).subdivision
                (G.horizontal r.succ).subdivision k 0) t =
            G.lowerCoarseConnectorPath hx₀ hone htwo hthree r k.castSucc t
        calc
          _ = G.interfaceVertexConnector hx₀ hone htwo hthree r
              (G.lowerCoarseVertex r k.castSucc) t :=
            congrArg (fun j ↦
              G.interfaceVertexConnector hx₀ hone htwo hthree r j t) hv
          _ = _ := by
            unfold lowerCoarseConnectorPath
            exact (path_cast_apply_right _ _ _ t).symm
      have hconnectorLast (t : I) :
          G.lowerRefinedBlockConnector hx₀ hone htwo hthree r k
              (Fin.last (IntervalSubdivision.commonRefinementRightBlockSize
                (G.horizontal r.castSucc).subdivision
                (G.horizontal r.succ).subdivision k)) t =
            (G.lowerCoarseConnectors hx₀ hone htwo hthree r).path k.succ t := by
        have hv :
            IntervalSubdivision.commonRefinementRightBlockVertex
                (G.horizontal r.castSucc).subdivision
                (G.horizontal r.succ).subdivision k
                (Fin.last (IntervalSubdivision.commonRefinementRightBlockSize
                  (G.horizontal r.castSucc).subdivision
                  (G.horizontal r.succ).subdivision k)) =
              G.lowerCoarseVertex r k.succ := by
          unfold lowerCoarseVertex interfaceSubdivision
          simp
        change
          G.interfaceVertexConnector hx₀ hone htwo hthree r
              (IntervalSubdivision.commonRefinementRightBlockVertex
                (G.horizontal r.castSucc).subdivision
                (G.horizontal r.succ).subdivision k
                (Fin.last (IntervalSubdivision.commonRefinementRightBlockSize
                  (G.horizontal r.castSucc).subdivision
                  (G.horizontal r.succ).subdivision k))) t =
            G.lowerCoarseConnectorPath hx₀ hone htwo hthree r k.succ t
        calc
          _ = G.interfaceVertexConnector hx₀ hone htwo hthree r
              (G.lowerCoarseVertex r k.succ) t :=
            congrArg (fun j ↦
              G.interfaceVertexConnector hx₀ hone htwo hthree r j t) hv
          _ = _ := by
            unfold lowerCoarseConnectorPath
            exact (path_cast_apply_right _ _ _ t).symm
      have hsegment (t : I) :
          (G.interfacePath r).subpath
              (G.lowerRefinedBlockPoint r k 0)
              (G.lowerRefinedBlockPoint r k
                (Fin.last (IntervalSubdivision.commonRefinementRightBlockSize
                  (G.horizontal r.castSucc).subdivision
                  (G.horizontal r.succ).subdivision k))) t =
            (G.interfacePath r).subpath
              ((G.lowerCoarseBoundary r).subdivision.point k.castSucc)
              ((G.lowerCoarseBoundary r).subdivision.point k.succ) t := by
        change G.interfacePath r
            (Icc.convexComb (G.lowerRefinedBlockPoint r k 0)
              (G.lowerRefinedBlockPoint r k
                (Fin.last (IntervalSubdivision.commonRefinementRightBlockSize
                  (G.horizontal r.castSucc).subdivision
                  (G.horizontal r.succ).subdivision k))) t) =
          G.interfacePath r
            (Icc.convexComb
              ((G.lowerCoarseBoundary r).subdivision.point k.castSucc)
              ((G.lowerCoarseBoundary r).subdivision.point k.succ) t)
        rw [G.lowerRefinedBlockPoint_zero r k,
          G.lowerRefinedBlockPoint_last r k]
        rfl
      ext t
      simp only [basedSegmentLoop, Path.trans_apply]
      split
      · exact hconnectorZero _
      · split
        · exact hsegment _
        · simp only [Path.symm_apply, Function.comp_apply]
          exact hconnectorLast _
    apply Path.ext
    funext t
    apply Subtype.ext
    exact congrArg (fun z ↦ z t) hambient
  rw [hpath]
  exact Path.Homotopic.refl _

def lowerRefinedCoverBlock
    (G : StaggeredCoverGrid U H bottom top)
    (hx₀ : ∀ i, x₀ ∈ U i)
    (hone : ∀ i, IsPathConnected (U i))
    (htwo : ∀ i j, IsPathConnected (U i ∩ U j))
    (hthree : ∀ i j k, IsPathConnected (U i ∩ U j ∩ U k))
    (r : Fin (G.extraRows + 2))
    (k : Fin (G.horizontal r.succ).subdivision.cells) :
    Factorization.CoverBlock (U := U) (x₀ := x₀) (hx₀ := hx₀) := by
  let N := IntervalSubdivision.commonRefinementRightBlockSize
    (G.horizontal r.castSucc).subdivision
    (G.horizontal r.succ).subdivision k
  have hN : N - 1 + 1 = N := Nat.sub_add_cancel <|
    IntervalSubdivision.commonRefinementRightBlockSize_pos
      (G.horizontal r.castSucc).subdivision
      (G.horizontal r.succ).subdivision k
  exact Factorization.coverBlockOfFn ((G.horizontal r.succ).label k)
    (fun j : Fin (N - 1 + 1) ↦
      G.lowerRefinedBlockClass hx₀ hone htwo hthree r k (Fin.cast hN j))

theorem lowerRefinedCoverBlock_coarseEntry
    (G : StaggeredCoverGrid U H bottom top)
    (hx₀ : ∀ i, x₀ ∈ U i)
    (hone : ∀ i, IsPathConnected (U i))
    (htwo : ∀ i j, IsPathConnected (U i ∩ U j))
    (hthree : ∀ i j k, IsPathConnected (U i ∩ U j ∩ U k))
    (r : Fin (G.extraRows + 2))
    (k : Fin (G.horizontal r.succ).subdivision.cells) :
    (G.lowerRefinedCoverBlock hx₀ hone htwo hthree r k).coarseEntry =
      ⟨(G.horizontal r.succ).label k,
        (Path.Homotopic.Quotient.mk
          ((G.lowerCoarseConnectors hx₀ hone htwo hthree r).factor
            (hx₀ := hx₀) k) :
          CoverGroup U x₀ hx₀ ((G.horizontal r.succ).label k))⟩ := by
  unfold lowerRefinedCoverBlock
  dsimp only
  rw [Factorization.coverBlockOfFn_coarseEntry]
  apply Sigma.ext
  · rfl
  · dsimp only
    rw [ofFn_finCast_right]
    exact heq_of_eq <|
      G.reverseProd_lowerRefinedBlockClass_eq_lowerCoarseFactor
        hx₀ hone htwo hthree r k

def lowerRefinedCoverBlocks
    (G : StaggeredCoverGrid U H bottom top)
    (hx₀ : ∀ i, x₀ ∈ U i)
    (hone : ∀ i, IsPathConnected (U i))
    (htwo : ∀ i j, IsPathConnected (U i ∩ U j))
    (hthree : ∀ i j k, IsPathConnected (U i ∩ U j ∩ U k))
    (r : Fin (G.extraRows + 2)) :
    List (Factorization.CoverBlock (U := U) (x₀ := x₀) (hx₀ := hx₀)) :=
  List.ofFn fun k ↦ G.lowerRefinedCoverBlock hx₀ hone htwo hthree r k

theorem lowerRefinedCoverBlocks_coarseEntries
    (G : StaggeredCoverGrid U H bottom top)
    (hx₀ : ∀ i, x₀ ∈ U i)
    (hone : ∀ i, IsPathConnected (U i))
    (htwo : ∀ i j, IsPathConnected (U i ∩ U j))
    (hthree : ∀ i j k, IsPathConnected (U i ∩ U j ∩ U k))
    (r : Fin (G.extraRows + 2)) :
    Factorization.coarseEntries
        (G.lowerRefinedCoverBlocks hx₀ hone htwo hthree r) =
      ((G.lowerCoarseConnectors hx₀ hone htwo hthree r).toFactorization
        (hx₀ := hx₀)).entries := by
  have hcoarse : Factorization.coarseEntries
      (G.lowerRefinedCoverBlocks hx₀ hone htwo hthree r) =
      List.ofFn fun k : Fin (G.horizontal r.succ).subdivision.cells ↦
        (⟨(G.horizontal r.succ).label k,
          (Path.Homotopic.Quotient.mk
            ((G.lowerCoarseConnectors hx₀ hone htwo hthree r).factor
              (hx₀ := hx₀) k) :
            CoverGroup U x₀ hx₀ ((G.horizontal r.succ).label k))⟩ :
          Factorization.Entry U x₀ hx₀) := by
    unfold lowerRefinedCoverBlocks Factorization.coarseEntries
    simp only [List.map_ofFn]
    rw [List.ofFn_inj]
    funext k
    exact G.lowerRefinedCoverBlock_coarseEntry hx₀ hone htwo hthree r k
  rw [hcoarse]
  have hentries :=
    (G.lowerCoarseConnectors hx₀ hone htwo hthree r).toFactorization_entries
      (hx₀ := hx₀)
  change ((G.lowerCoarseConnectors hx₀ hone htwo hthree r).toFactorization
      (hx₀ := hx₀)).entries =
    List.ofFn fun k : Fin (G.horizontal r.succ).subdivision.cells ↦
      (⟨(G.horizontal r.succ).label k,
        (Path.Homotopic.Quotient.mk
          ((G.lowerCoarseConnectors hx₀ hone htwo hthree r).factor
            (hx₀ := hx₀) k) :
          CoverGroup U x₀ hx₀ ((G.horizontal r.succ).label k))⟩ :
        Factorization.Entry U x₀ hx₀) at hentries
  exact hentries.symm

def alignedUpperEntryAtCommonRefinement
    (G : StaggeredCoverGrid U H bottom top)
    (hx₀ : ∀ i, x₀ ∈ U i)
    (hone : ∀ i, IsPathConnected (U i))
    (htwo : ∀ i j, IsPathConnected (U i ∩ U j))
    (hthree : ∀ i j k, IsPathConnected (U i ∩ U j ∩ U k))
    (r : Fin (G.extraRows + 2))
    (c : Fin (IntervalSubdivision.commonRefinement
      (G.horizontal r.castSucc).subdivision
      (G.horizontal r.succ).subdivision).cells) :
    Factorization.Entry U x₀ hx₀ := by
  let D := G.alignedInterface hx₀ hone htwo hthree r
  have hc : (IntervalSubdivision.commonRefinement
      (G.horizontal r.castSucc).subdivision
      (G.horizontal r.succ).subdivision).cells = D.cells := by
    dsimp [D, alignedInterface, Factorization.AlignedInterface.ofGrid,
      interfaceSubdivision]
  let c' : Fin D.cells := Fin.cast hc c
  exact ⟨D.upperLabel c',
    Factorization.coverLoopClass (D.upperLabel c') (D.loop c')
      (D.loop_mem_upper c')⟩

theorem lowerRefinedBlockEntry_eq_alignedUpperEntry
    (G : StaggeredCoverGrid U H bottom top)
    (hx₀ : ∀ i, x₀ ∈ U i)
    (hone : ∀ i, IsPathConnected (U i))
    (htwo : ∀ i j, IsPathConnected (U i ∩ U j))
    (hthree : ∀ i j k, IsPathConnected (U i ∩ U j ∩ U k))
    (r : Fin (G.extraRows + 2))
    (k : Fin (G.horizontal r.succ).subdivision.cells)
    (j : Fin (IntervalSubdivision.commonRefinementRightBlockSize
      (G.horizontal r.castSucc).subdivision
      (G.horizontal r.succ).subdivision k)) :
    (⟨(G.horizontal r.succ).label k,
        G.lowerRefinedBlockClass hx₀ hone htwo hthree r k j⟩ :
      Factorization.Entry U x₀ hx₀) =
      G.alignedUpperEntryAtCommonRefinement hx₀ hone htwo hthree r
        (IntervalSubdivision.commonRefinementRightBlockCell
        (G.horizontal r.castSucc).subdivision
        (G.horizontal r.succ).subdivision k j) := by
  let D := G.alignedInterface hx₀ hone htwo hthree r
  let c := IntervalSubdivision.commonRefinementRightBlockCell
    (G.horizontal r.castSucc).subdivision
    (G.horizontal r.succ).subdivision k j
  unfold alignedUpperEntryAtCommonRefinement
  dsimp only
  change
    (⟨(G.horizontal r.succ).label k,
        G.lowerRefinedBlockClass hx₀ hone htwo hthree r k j⟩ :
      Factorization.Entry U x₀ hx₀) =
      (⟨D.upperLabel c,
        Factorization.coverLoopClass (D.upperLabel c) (D.loop c)
          (D.loop_mem_upper c)⟩ : Factorization.Entry U x₀ hx₀)
  have hfirst : (G.horizontal r.succ).label k = D.upperLabel c := by
    dsimp [D, c, alignedInterface, Factorization.AlignedInterface.ofGrid]
    change (G.horizontal r.succ).label k =
      (G.horizontal r.succ).label
        (IntervalSubdivision.commonRefinementRightCell
          (G.horizontal r.castSucc).subdivision
          (G.horizontal r.succ).subdivision
          (IntervalSubdivision.commonRefinementRightBlockCell
            (G.horizontal r.castSucc).subdivision
            (G.horizontal r.succ).subdivision k j))
    rw [IntervalSubdivision.commonRefinementRightCell_blockCell]
  apply Sigma.ext hfirst
  have hmem (t : I) : D.loop c t ∈ U ((G.horizontal r.succ).label k) := by
    rw [hfirst]
    exact D.loop_mem_upper c t
  have hpath : G.lowerRefinedBlockLoop hx₀ hone htwo hthree r k j =
      pathInSet (D.loop c) (U ((G.horizontal r.succ).label k))
        (hx₀ ((G.horizontal r.succ).label k))
        (hx₀ ((G.horizontal r.succ).label k)) hmem := by
    apply Path.ext
    funext t
    apply Subtype.ext
    change
      basedSegmentLoop (G.interfacePath r)
          (G.lowerRefinedBlockPoint r k j.castSucc)
          (G.lowerRefinedBlockPoint r k j.succ)
          (G.lowerRefinedBlockConnector hx₀ hone htwo hthree r k j.castSucc)
          (G.lowerRefinedBlockConnector hx₀ hone htwo hthree r k j.succ) t =
        D.loop c t
    dsimp [D, c, alignedInterface, Factorization.AlignedInterface.ofGrid]
    unfold Factorization.AlignedInterface.loop lowerRefinedBlockPoint
      lowerRefinedBlockConnector
    rw [IntervalSubdivision.commonRefinementRightBlockVertex_castSucc,
      IntervalSubdivision.commonRefinementRightBlockVertex_succ]
    rfl
  have hclass : G.lowerRefinedBlockClass hx₀ hone htwo hthree r k j =
      Factorization.coverLoopClass (hx₀ := hx₀)
        ((G.horizontal r.succ).label k) (D.loop c) hmem := by
    unfold lowerRefinedBlockClass Factorization.coverLoopClass
    apply Path.Homotopic.Quotient.eq.mpr
    rw [hpath]
  exact (heq_of_eq hclass).trans <|
    coverLoopClass_heq_of_index_eq hfirst (D.loop c) hmem
      (D.loop_mem_upper c)

theorem lowerRefinedCoverBlock_fineEntries
    (G : StaggeredCoverGrid U H bottom top)
    (hx₀ : ∀ i, x₀ ∈ U i)
    (hone : ∀ i, IsPathConnected (U i))
    (htwo : ∀ i j, IsPathConnected (U i ∩ U j))
    (hthree : ∀ i j k, IsPathConnected (U i ∩ U j ∩ U k))
    (r : Fin (G.extraRows + 2))
    (k : Fin (G.horizontal r.succ).subdivision.cells) :
    (G.lowerRefinedCoverBlock hx₀ hone htwo hthree r k).fineEntries =
      (IntervalSubdivision.commonRefinementRightBlockCells
        (G.horizontal r.castSucc).subdivision
        (G.horizontal r.succ).subdivision k).map
        (G.alignedUpperEntryAtCommonRefinement hx₀ hone htwo hthree r) := by
  let N := IntervalSubdivision.commonRefinementRightBlockSize
    (G.horizontal r.castSucc).subdivision
    (G.horizontal r.succ).subdivision k
  have hN : N - 1 + 1 = N := Nat.sub_add_cancel <|
    IntervalSubdivision.commonRefinementRightBlockSize_pos
      (G.horizontal r.castSucc).subdivision
      (G.horizontal r.succ).subdivision k
  let f : Fin N → Factorization.Entry U x₀ hx₀ := fun j ↦
    ⟨(G.horizontal r.succ).label k,
      G.lowerRefinedBlockClass hx₀ hone htwo hthree r k j⟩
  change (Factorization.coverBlockOfFn ((G.horizontal r.succ).label k)
      (fun j : Fin (N - 1 + 1) ↦
        G.lowerRefinedBlockClass hx₀ hone htwo hthree r k
          (Fin.cast hN j))).fineEntries = _
  rw [Factorization.coverBlockOfFn_fineEntries]
  change List.ofFn (fun j : Fin (N - 1 + 1) ↦ f (Fin.cast hN j)) = _
  rw [ofFn_finCast_right hN f]
  unfold IntervalSubdivision.commonRefinementRightBlockCells
  simp only [List.map_ofFn]
  rw [List.ofFn_inj]
  funext j
  simpa using G.lowerRefinedBlockEntry_eq_alignedUpperEntry
    hx₀ hone htwo hthree r k j

theorem alignedUpperEntryAtCommonRefinement_ofFn
    (G : StaggeredCoverGrid U H bottom top)
    (hx₀ : ∀ i, x₀ ∈ U i)
    (hone : ∀ i, IsPathConnected (U i))
    (htwo : ∀ i j, IsPathConnected (U i ∩ U j))
    (hthree : ∀ i j k, IsPathConnected (U i ∩ U j ∩ U k))
    (r : Fin (G.extraRows + 2)) :
    List.ofFn
        (G.alignedUpperEntryAtCommonRefinement hx₀ hone htwo hthree r) =
      (G.alignedInterface hx₀ hone htwo hthree r).upperEntries
        (hx₀ := hx₀) := by
  let D := G.alignedInterface hx₀ hone htwo hthree r
  have hc : (IntervalSubdivision.commonRefinement
      (G.horizontal r.castSucc).subdivision
      (G.horizontal r.succ).subdivision).cells = D.cells := by
    dsimp [D, alignedInterface, Factorization.AlignedInterface.ofGrid,
      interfaceSubdivision]
  let f : Fin D.cells → Factorization.Entry U x₀ hx₀ := fun c ↦
    ⟨D.upperLabel c,
      Factorization.coverLoopClass (D.upperLabel c) (D.loop c)
        (D.loop_mem_upper c)⟩
  change List.ofFn (fun c : Fin
      (IntervalSubdivision.commonRefinement
        (G.horizontal r.castSucc).subdivision
        (G.horizontal r.succ).subdivision).cells ↦
      f (Fin.cast hc c)) = List.ofFn f
  exact ofFn_finCast_right hc f

theorem lowerRefinedCoverBlocks_fineEntries
    (G : StaggeredCoverGrid U H bottom top)
    (hx₀ : ∀ i, x₀ ∈ U i)
    (hone : ∀ i, IsPathConnected (U i))
    (htwo : ∀ i j, IsPathConnected (U i ∩ U j))
    (hthree : ∀ i j k, IsPathConnected (U i ∩ U j ∩ U k))
    (r : Fin (G.extraRows + 2)) :
    Factorization.fineEntries
        (G.lowerRefinedCoverBlocks hx₀ hone htwo hthree r) =
      (G.upperInterfaceFactorization hx₀ hone htwo hthree r).entries := by
  let f := G.alignedUpperEntryAtCommonRefinement hx₀ hone htwo hthree r
  change ((G.lowerRefinedCoverBlocks hx₀ hone htwo hthree r).map
    Factorization.CoverBlock.fineEntries).flatten = _
  unfold lowerRefinedCoverBlocks
  rw [List.map_ofFn]
  change (List.ofFn (fun k : Fin (G.horizontal r.succ).subdivision.cells ↦
    (G.lowerRefinedCoverBlock hx₀ hone htwo hthree r k).fineEntries)).flatten = _
  simp_rw [G.lowerRefinedCoverBlock_fineEntries hx₀ hone htwo hthree r]
  have houter :
      (List.ofFn fun k : Fin (G.horizontal r.succ).subdivision.cells ↦
        (IntervalSubdivision.commonRefinementRightBlockCells
          (G.horizontal r.castSucc).subdivision
          (G.horizontal r.succ).subdivision k).map f) =
        (List.ofFn fun k : Fin (G.horizontal r.succ).subdivision.cells ↦
          IntervalSubdivision.commonRefinementRightBlockCells
            (G.horizontal r.castSucc).subdivision
            (G.horizontal r.succ).subdivision k).map (List.map f) := by
    rw [List.map_ofFn]
    rfl
  rw [houter, ← List.map_flatten,
    IntervalSubdivision.commonRefinementRightBlockCells_flatten]
  rw [List.map_ofFn]
  change List.ofFn f = _
  rw [G.alignedUpperEntryAtCommonRefinement_ofFn hx₀ hone htwo hthree r]
  exact (G.upperInterfaceFactorization_entries
    hx₀ hone htwo hthree r).symm

theorem moves_upperInterfaceEntries_to_lowerCoarseEntries
    (G : StaggeredCoverGrid U H bottom top)
    (hx₀ : ∀ i, x₀ ∈ U i)
    (hone : ∀ i, IsPathConnected (U i))
    (htwo : ∀ i j, IsPathConnected (U i ∩ U j))
    (hthree : ∀ i j k, IsPathConnected (U i ∩ U j ∩ U k))
    (r : Fin (G.extraRows + 2)) :
    Factorization.Moves
      (G.upperInterfaceFactorization hx₀ hone htwo hthree r).entries
      ((G.lowerCoarseConnectors hx₀ hone htwo hthree r).toFactorization
        (hx₀ := hx₀)).entries := by
  have h := (Factorization.moves_split_blocks
    (G.lowerRefinedCoverBlocks hx₀ hone htwo hthree r)).symm
  rw [G.lowerRefinedCoverBlocks_fineEntries hx₀ hone htwo hthree r,
    G.lowerRefinedCoverBlocks_coarseEntries hx₀ hone htwo hthree r] at h
  exact h

theorem upperInterfaceToLowerCoarseSweep
    (G : StaggeredCoverGrid U H bottom top)
    (hx₀ : ∀ i, x₀ ∈ U i)
    (hone : ∀ i, IsPathConnected (U i))
    (htwo : ∀ i j, IsPathConnected (U i ∩ U j))
    (hthree : ∀ i j k, IsPathConnected (U i ∩ U j ∩ U k))
    (r : Fin (G.extraRows + 2)) :
    Factorization.Sweep
      (G.upperInterfaceFactorization hx₀ hone htwo hthree r)
      ((G.lowerCoarseConnectors hx₀ hone htwo hthree r).toFactorization
        (hx₀ := hx₀)) := by
  exact ⟨G.moves_upperInterfaceEntries_to_lowerCoarseEntries
    hx₀ hone htwo hthree r⟩

end StaggeredCoverGrid

end Hatcher.VanKampen
