import Hatcher.VanKampen.BandGeometry
import Hatcher.VanKampen.RefinementProduct

noncomputable section

open Set
open scoped unitInterval

namespace Hatcher.VanKampen

universe u v

private theorem path_cast_apply {Y : Type*} [TopologicalSpace Y]
    {a b a' b' : Y} (p : Path a b) (ha : a' = a) (hb : b' = b)
    (t : I) : p.cast ha hb t = p t :=
  congrFun (Path.cast_coe p ha hb) t

namespace IntervalSubdivision

theorem commonRefinementLeftBlockVertex_strictMono
    (s t : IntervalSubdivision) (i : Fin s.cells) :
    StrictMono (commonRefinementLeftBlockVertex s t i) := by
  intro j k hjk
  apply Fin.mk_lt_mk.mpr
  omega

theorem commonRefinementLeftBlockPoint_mem_cell
    (s t : IntervalSubdivision) (i : Fin s.cells)
    (j : Fin (commonRefinementLeftBlockSize s t i + 1)) :
    (commonRefinement s t).point
        (commonRefinementLeftBlockVertex s t i j) ∈ s.cell i := by
  constructor
  · calc
      s.point i.castSucc = (commonRefinement s t).point
          (commonRefinementLeftBlockVertex s t i 0) :=
        (commonRefinementLeftBlockPoint_zero s t i).symm
      _ ≤ (commonRefinement s t).point
          (commonRefinementLeftBlockVertex s t i j) :=
        (commonRefinement s t).strictMono.monotone
          ((commonRefinementLeftBlockVertex_strictMono s t i).monotone
            (Fin.zero_le _))
  · calc
      (commonRefinement s t).point
          (commonRefinementLeftBlockVertex s t i j) ≤
          (commonRefinement s t).point
            (commonRefinementLeftBlockVertex s t i
              (Fin.last (commonRefinementLeftBlockSize s t i))) :=
        (commonRefinement s t).strictMono.monotone
          ((commonRefinementLeftBlockVertex_strictMono s t i).monotone
            (Fin.le_last _))
      _ = s.point i.succ := commonRefinementLeftBlockPoint_last s t i

end IntervalSubdivision

namespace Factorization

variable {ι : Type u} {X : Type v} [TopologicalSpace X]
  {U : ι → Set X} {x₀ : X} {hx₀ : ∀ i, x₀ ∈ U i}

def coverBlockOfFn (i : ι) {n : ℕ}
    (f : Fin (n + 1) → CoverGroup U x₀ hx₀ i) :
    CoverBlock (U := U) (x₀ := x₀) (hx₀ := hx₀) where
  index := i
  head := f 0
  tail := List.ofFn fun k ↦ f k.succ

@[simp]
theorem coverBlockOfFn_fineEntries (i : ι) {n : ℕ}
    (f : Fin (n + 1) → CoverGroup U x₀ hx₀ i) :
    (coverBlockOfFn i f).fineEntries =
      List.ofFn fun k ↦ (⟨i, f k⟩ : Entry U x₀ hx₀) := by
  simp [coverBlockOfFn, CoverBlock.fineEntries, sameCoverEntries,
    List.ofFn_succ, Function.comp_def]

@[simp]
theorem coverBlockOfFn_coarseEntry (i : ι) {n : ℕ}
    (f : Fin (n + 1) → CoverGroup U x₀ hx₀ i) :
    (coverBlockOfFn i f).coarseEntry =
      ⟨i, (List.ofFn f).reverse.prod⟩ := by
  unfold coverBlockOfFn CoverBlock.coarseEntry
  rw [List.ofFn_succ]

end Factorization

namespace StaggeredCoverGrid

variable {ι : Type u} {X : Type v} [TopologicalSpace X]
  {U : ι → Set X} {x₀ : X} {p q : Path x₀ x₀}
  {H : p.Homotopy q} {bottom : BoundaryCover U p}
  {top : BoundaryCover U q}

def upperRefinedBlockPoint (G : StaggeredCoverGrid U H bottom top)
    (r : Fin (G.extraRows + 2))
    (k : Fin (G.horizontal r.castSucc).subdivision.cells)
    (j : Fin (IntervalSubdivision.commonRefinementLeftBlockSize
      (G.horizontal r.castSucc).subdivision
      (G.horizontal r.succ).subdivision k + 1)) : I :=
  (G.interfaceSubdivision r).point
    (IntervalSubdivision.commonRefinementLeftBlockVertex
      (G.horizontal r.castSucc).subdivision
      (G.horizontal r.succ).subdivision k j)

theorem upperRefinedBlockPoint_mem_cell
    (G : StaggeredCoverGrid U H bottom top)
    (r : Fin (G.extraRows + 2))
    (k : Fin (G.horizontal r.castSucc).subdivision.cells)
    (j : Fin (IntervalSubdivision.commonRefinementLeftBlockSize
      (G.horizontal r.castSucc).subdivision
      (G.horizontal r.succ).subdivision k + 1)) :
    G.upperRefinedBlockPoint r k j ∈
      (G.horizontal r.castSucc).subdivision.cell k := by
  exact IntervalSubdivision.commonRefinementLeftBlockPoint_mem_cell
    (G.horizontal r.castSucc).subdivision
    (G.horizontal r.succ).subdivision k j

theorem upperRefinedBlockPoint_strictMono
    (G : StaggeredCoverGrid U H bottom top)
    (r : Fin (G.extraRows + 2))
    (k : Fin (G.horizontal r.castSucc).subdivision.cells) :
    StrictMono (G.upperRefinedBlockPoint r k) :=
  (G.interfaceSubdivision r).strictMono.comp
    (IntervalSubdivision.commonRefinementLeftBlockVertex_strictMono
      (G.horizontal r.castSucc).subdivision
      (G.horizontal r.succ).subdivision k)

theorem upperRefinedBlockPoint_zero
    (G : StaggeredCoverGrid U H bottom top)
    (r : Fin (G.extraRows + 2))
    (k : Fin (G.horizontal r.castSucc).subdivision.cells) :
    G.upperRefinedBlockPoint r k 0 =
      (G.horizontal r.castSucc).subdivision.point k.castSucc :=
  IntervalSubdivision.commonRefinementLeftBlockPoint_zero
    (G.horizontal r.castSucc).subdivision
    (G.horizontal r.succ).subdivision k

theorem upperRefinedBlockPoint_last
    (G : StaggeredCoverGrid U H bottom top)
    (r : Fin (G.extraRows + 2))
    (k : Fin (G.horizontal r.castSucc).subdivision.cells) :
    G.upperRefinedBlockPoint r k
        (Fin.last (IntervalSubdivision.commonRefinementLeftBlockSize
          (G.horizontal r.castSucc).subdivision
          (G.horizontal r.succ).subdivision k)) =
      (G.horizontal r.castSucc).subdivision.point k.succ :=
  IntervalSubdivision.commonRefinementLeftBlockPoint_last
    (G.horizontal r.castSucc).subdivision
    (G.horizontal r.succ).subdivision k

def upperRefinedBlockConnector
    (G : StaggeredCoverGrid U H bottom top)
    (hx₀ : ∀ i, x₀ ∈ U i)
    (hone : ∀ i, IsPathConnected (U i))
    (htwo : ∀ i j, IsPathConnected (U i ∩ U j))
    (hthree : ∀ i j k, IsPathConnected (U i ∩ U j ∩ U k))
    (r : Fin (G.extraRows + 2))
    (k : Fin (G.horizontal r.castSucc).subdivision.cells)
    (j : Fin (IntervalSubdivision.commonRefinementLeftBlockSize
      (G.horizontal r.castSucc).subdivision
      (G.horizontal r.succ).subdivision k + 1)) :
    Path x₀ (G.interfacePath r (G.upperRefinedBlockPoint r k j)) :=
  G.interfaceVertexConnector hx₀ hone htwo hthree r
    (IntervalSubdivision.commonRefinementLeftBlockVertex
      (G.horizontal r.castSucc).subdivision
      (G.horizontal r.succ).subdivision k j)

theorem upperRefinedBlockConnector_range
    (G : StaggeredCoverGrid U H bottom top)
    (hx₀ : ∀ i, x₀ ∈ U i)
    (hone : ∀ i, IsPathConnected (U i))
    (htwo : ∀ i j, IsPathConnected (U i ∩ U j))
    (hthree : ∀ i j k, IsPathConnected (U i ∩ U j ∩ U k))
    (r : Fin (G.extraRows + 2))
    (k : Fin (G.horizontal r.castSucc).subdivision.cells)
    (j : Fin (IntervalSubdivision.commonRefinementLeftBlockSize
      (G.horizontal r.castSucc).subdivision
      (G.horizontal r.succ).subdivision k + 1)) :
    Set.range (G.upperRefinedBlockConnector hx₀ hone htwo hthree r k j) ⊆
      U ((G.horizontal r.castSucc).label k) := by
  classical
  apply G.interfaceVertexConnector_range hx₀ hone htwo hthree r
  unfold interfaceLabels
  apply Finset.mem_union_left
  apply Finset.mem_image.mpr
  refine ⟨k, ?_, rfl⟩
  rw [IntervalSubdivision.mem_incidentCells]
  exact G.upperRefinedBlockPoint_mem_cell r k j

def upperRefinedBlockLoop
    (G : StaggeredCoverGrid U H bottom top)
    (hx₀ : ∀ i, x₀ ∈ U i)
    (hone : ∀ i, IsPathConnected (U i))
    (htwo : ∀ i j, IsPathConnected (U i ∩ U j))
    (hthree : ∀ i j k, IsPathConnected (U i ∩ U j ∩ U k))
    (r : Fin (G.extraRows + 2))
    (k : Fin (G.horizontal r.castSucc).subdivision.cells)
    (j : Fin (IntervalSubdivision.commonRefinementLeftBlockSize
      (G.horizontal r.castSucc).subdivision
      (G.horizontal r.succ).subdivision k)) :
    Path
      (⟨x₀, hx₀ ((G.horizontal r.castSucc).label k)⟩ :
        U ((G.horizontal r.castSucc).label k))
      ⟨x₀, hx₀ ((G.horizontal r.castSucc).label k)⟩ :=
  basedSegmentLoopInSet
    (U ((G.horizontal r.castSucc).label k))
    (hx₀ ((G.horizontal r.castSucc).label k))
    (G.interfacePath r)
    (G.upperRefinedBlockPoint r k j.castSucc)
    (G.upperRefinedBlockPoint r k j.succ)
    ((G.upperRefinedBlockPoint_strictMono r k) Fin.castSucc_lt_succ).le
    (G.upperRefinedBlockConnector hx₀ hone htwo hthree r k j.castSucc)
    (G.upperRefinedBlockConnector hx₀ hone htwo hthree r k j.succ)
    (fun t ↦ G.upperRefinedBlockConnector_range
      hx₀ hone htwo hthree r k j.castSucc ⟨t, rfl⟩)
    (fun t ↦ G.upperRefinedBlockConnector_range
      hx₀ hone htwo hthree r k j.succ ⟨t, rfl⟩)
    (fun _x hmem ↦ (G.bandUpperBoundary r).mapsTo k
      ⟨(G.upperRefinedBlockPoint_mem_cell r k j.castSucc).1.trans hmem.1,
        hmem.2.trans (G.upperRefinedBlockPoint_mem_cell r k j.succ).2⟩)

def upperRefinedBlockClass
    (G : StaggeredCoverGrid U H bottom top)
    (hx₀ : ∀ i, x₀ ∈ U i)
    (hone : ∀ i, IsPathConnected (U i))
    (htwo : ∀ i j, IsPathConnected (U i ∩ U j))
    (hthree : ∀ i j k, IsPathConnected (U i ∩ U j ∩ U k))
    (r : Fin (G.extraRows + 2))
    (k : Fin (G.horizontal r.castSucc).subdivision.cells)
    (j : Fin (IntervalSubdivision.commonRefinementLeftBlockSize
      (G.horizontal r.castSucc).subdivision
      (G.horizontal r.succ).subdivision k)) :
    CoverGroup U x₀ hx₀ ((G.horizontal r.castSucc).label k) :=
  FundamentalGroup.fromPath (.mk <|
    G.upperRefinedBlockLoop hx₀ hone htwo hthree r k j)

theorem reverseProd_upperRefinedBlockClass_eq
    (G : StaggeredCoverGrid U H bottom top)
    (hx₀ : ∀ i, x₀ ∈ U i)
    (hone : ∀ i, IsPathConnected (U i))
    (htwo : ∀ i j, IsPathConnected (U i ∩ U j))
    (hthree : ∀ i j k, IsPathConnected (U i ∩ U j ∩ U k))
    (r : Fin (G.extraRows + 2))
    (k : Fin (G.horizontal r.castSucc).subdivision.cells) :
    (List.ofFn fun j ↦
      G.upperRefinedBlockClass hx₀ hone htwo hthree r k j).reverse.prod =
      FundamentalGroup.fromPath (.mk <|
        basedSegmentLoopInSet
          (U ((G.horizontal r.castSucc).label k))
          (hx₀ ((G.horizontal r.castSucc).label k))
          (G.interfacePath r)
          (G.upperRefinedBlockPoint r k 0)
          (G.upperRefinedBlockPoint r k
            (Fin.last (IntervalSubdivision.commonRefinementLeftBlockSize
              (G.horizontal r.castSucc).subdivision
              (G.horizontal r.succ).subdivision k)))
          ((G.upperRefinedBlockPoint_strictMono r k).monotone (Fin.zero_le _))
          (G.upperRefinedBlockConnector hx₀ hone htwo hthree r k 0)
          (G.upperRefinedBlockConnector hx₀ hone htwo hthree r k
            (Fin.last (IntervalSubdivision.commonRefinementLeftBlockSize
              (G.horizontal r.castSucc).subdivision
              (G.horizontal r.succ).subdivision k)))
          (fun t ↦ G.upperRefinedBlockConnector_range
            hx₀ hone htwo hthree r k 0 ⟨t, rfl⟩)
          (fun t ↦ G.upperRefinedBlockConnector_range
            hx₀ hone htwo hthree r k
              (Fin.last (IntervalSubdivision.commonRefinementLeftBlockSize
                (G.horizontal r.castSucc).subdivision
                (G.horizontal r.succ).subdivision k)) ⟨t, rfl⟩)
          (fun _x hmem ↦ (G.bandUpperBoundary r).mapsTo k
            ⟨(G.upperRefinedBlockPoint_mem_cell r k 0).1.trans hmem.1,
              hmem.2.trans
                (G.upperRefinedBlockPoint_mem_cell r k
                  (Fin.last (IntervalSubdivision.commonRefinementLeftBlockSize
                    (G.horizontal r.castSucc).subdivision
                    (G.horizontal r.succ).subdivision k))).2⟩)) := by
  unfold upperRefinedBlockClass upperRefinedBlockLoop
  exact reverseProd_basedSegmentLoopInSet_eq
    (U ((G.horizontal r.castSucc).label k))
    (hx₀ ((G.horizontal r.castSucc).label k))
    (G.interfacePath r)
    ((G.horizontal r.castSucc).subdivision.point k.castSucc)
    ((G.horizontal r.castSucc).subdivision.point k.succ)
    ((G.horizontal r.castSucc).subdivision.strictMono Fin.castSucc_lt_succ)
    ((G.bandUpperBoundary r).mapsTo k)
    (IntervalSubdivision.commonRefinementLeftBlockSize
      (G.horizontal r.castSucc).subdivision
      (G.horizontal r.succ).subdivision k)
    (G.upperRefinedBlockPoint r k)
    (G.upperRefinedBlockPoint_mem_cell r k)
    (G.upperRefinedBlockPoint_strictMono r k)
    (G.upperRefinedBlockConnector hx₀ hone htwo hthree r k)
    (fun j t ↦ G.upperRefinedBlockConnector_range
      hx₀ hone htwo hthree r k j ⟨t, rfl⟩)

theorem reverseProd_upperRefinedBlockClass_eq_upperCoarseFactor
    (G : StaggeredCoverGrid U H bottom top)
    (hx₀ : ∀ i, x₀ ∈ U i)
    (hone : ∀ i, IsPathConnected (U i))
    (htwo : ∀ i j, IsPathConnected (U i ∩ U j))
    (hthree : ∀ i j k, IsPathConnected (U i ∩ U j ∩ U k))
    (r : Fin (G.extraRows + 2))
    (k : Fin (G.horizontal r.castSucc).subdivision.cells) :
    (List.ofFn fun j ↦
      G.upperRefinedBlockClass hx₀ hone htwo hthree r k j).reverse.prod =
      (Path.Homotopic.Quotient.mk
        ((G.upperCoarseConnectors hx₀ hone htwo hthree r).factor
          (hx₀ := hx₀) k) :
        CoverGroup U x₀ hx₀ ((G.horizontal r.castSucc).label k)) := by
  rw [G.reverseProd_upperRefinedBlockClass_eq hx₀ hone htwo hthree r k]
  have hfactor := Factorization.boundaryConnector_factor_eq_coverLoopClass
    (hx₀ := hx₀) (G.upperCoarseConnectors hx₀ hone htwo hthree r) k
  change _ = (Path.Homotopic.Quotient.mk
    ((G.upperCoarseConnectors hx₀ hone htwo hthree r).factor
      (hx₀ := hx₀) k) :
    CoverGroup U x₀ hx₀ ((G.bandUpperBoundary r).label k))
  rw [hfactor]
  unfold Factorization.coverLoopClass
  apply Path.Homotopic.Quotient.eq.mpr
  have hlocalLeft (t : I) :
      G.upperRefinedBlockConnector hx₀ hone htwo hthree r k 0 t ∈
        U ((G.horizontal r.castSucc).label k) :=
    G.upperRefinedBlockConnector_range hx₀ hone htwo hthree r k 0
      ⟨t, rfl⟩
  have hlocalRight (t : I) :
      G.upperRefinedBlockConnector hx₀ hone htwo hthree r k
          (Fin.last (IntervalSubdivision.commonRefinementLeftBlockSize
            (G.horizontal r.castSucc).subdivision
            (G.horizontal r.succ).subdivision k)) t ∈
        U ((G.horizontal r.castSucc).label k) :=
    G.upperRefinedBlockConnector_range hx₀ hone htwo hthree r k _
      ⟨t, rfl⟩
  have hlocalSegment : MapsTo (G.interfacePath r)
      (Icc (G.upperRefinedBlockPoint r k 0)
        (G.upperRefinedBlockPoint r k
          (Fin.last (IntervalSubdivision.commonRefinementLeftBlockSize
            (G.horizontal r.castSucc).subdivision
            (G.horizontal r.succ).subdivision k))))
      (U ((G.horizontal r.castSucc).label k)) := by
    intro x hmem
    apply (G.bandUpperBoundary r).mapsTo k
    exact ⟨(G.upperRefinedBlockPoint_mem_cell r k 0).1.trans hmem.1,
      hmem.2.trans
        (G.upperRefinedBlockPoint_mem_cell r k
          (Fin.last (IntervalSubdivision.commonRefinementLeftBlockSize
            (G.horizontal r.castSucc).subdivision
            (G.horizontal r.succ).subdivision k))).2⟩
  have hcoarseLoop (t : I) :
      basedSegmentLoop (G.interfacePath r)
          ((G.bandUpperBoundary r).subdivision.point k.castSucc)
          ((G.bandUpperBoundary r).subdivision.point k.succ)
          ((G.upperCoarseConnectors hx₀ hone htwo hthree r).path k.castSucc)
          ((G.upperCoarseConnectors hx₀ hone htwo hthree r).path k.succ) t ∈
        U ((G.bandUpperBoundary r).label k) := by
    apply basedSegmentLoop_mem _ _ _
      ((G.bandUpperBoundary r).subdivision.strictMono.monotone
        (Fin.castSucc_le_succ k)) _ _
    · exact fun t ↦ (G.upperCoarseConnectors hx₀ hone htwo hthree r).range_left k
        ⟨t, rfl⟩
    · exact fun t ↦ (G.upperCoarseConnectors hx₀ hone htwo hthree r).range_right k
        ⟨t, rfl⟩
    · exact (G.bandUpperBoundary r).mapsTo k
  have hpath :
      basedSegmentLoopInSet
          (U ((G.horizontal r.castSucc).label k))
          (hx₀ ((G.horizontal r.castSucc).label k))
          (G.interfacePath r)
          (G.upperRefinedBlockPoint r k 0)
          (G.upperRefinedBlockPoint r k
            (Fin.last (IntervalSubdivision.commonRefinementLeftBlockSize
              (G.horizontal r.castSucc).subdivision
              (G.horizontal r.succ).subdivision k)))
          ((G.upperRefinedBlockPoint_strictMono r k).monotone (Fin.zero_le _))
          (G.upperRefinedBlockConnector hx₀ hone htwo hthree r k 0)
          (G.upperRefinedBlockConnector hx₀ hone htwo hthree r k
            (Fin.last (IntervalSubdivision.commonRefinementLeftBlockSize
              (G.horizontal r.castSucc).subdivision
              (G.horizontal r.succ).subdivision k)))
          hlocalLeft hlocalRight hlocalSegment =
        pathInSet
          (basedSegmentLoop (G.interfacePath r)
            ((G.bandUpperBoundary r).subdivision.point k.castSucc)
            ((G.bandUpperBoundary r).subdivision.point k.succ)
            ((G.upperCoarseConnectors hx₀ hone htwo hthree r).path k.castSucc)
            ((G.upperCoarseConnectors hx₀ hone htwo hthree r).path k.succ))
          (U ((G.bandUpperBoundary r).label k))
          (hx₀ ((G.bandUpperBoundary r).label k))
          (hx₀ ((G.bandUpperBoundary r).label k)) hcoarseLoop := by
    have hambient :
        basedSegmentLoop (G.interfacePath r)
            (G.upperRefinedBlockPoint r k 0)
            (G.upperRefinedBlockPoint r k
              (Fin.last (IntervalSubdivision.commonRefinementLeftBlockSize
                (G.horizontal r.castSucc).subdivision
                (G.horizontal r.succ).subdivision k)))
            (G.upperRefinedBlockConnector hx₀ hone htwo hthree r k 0)
            (G.upperRefinedBlockConnector hx₀ hone htwo hthree r k
              (Fin.last (IntervalSubdivision.commonRefinementLeftBlockSize
                (G.horizontal r.castSucc).subdivision
                (G.horizontal r.succ).subdivision k))) =
          basedSegmentLoop (G.interfacePath r)
            ((G.bandUpperBoundary r).subdivision.point k.castSucc)
            ((G.bandUpperBoundary r).subdivision.point k.succ)
            ((G.upperCoarseConnectors hx₀ hone htwo hthree r).path k.castSucc)
            ((G.upperCoarseConnectors hx₀ hone htwo hthree r).path k.succ) := by
      have hconnectorZero (t : I) :
          G.upperRefinedBlockConnector hx₀ hone htwo hthree r k 0 t =
            (G.upperCoarseConnectors hx₀ hone htwo hthree r).path k.castSucc t := by
        have hv :
            IntervalSubdivision.commonRefinementLeftBlockVertex
                (G.horizontal r.castSucc).subdivision
                (G.horizontal r.succ).subdivision k 0 =
              G.upperCoarseVertex r k.castSucc := by
          unfold upperCoarseVertex interfaceSubdivision
          simp
        change
          G.interfaceVertexConnector hx₀ hone htwo hthree r
              (IntervalSubdivision.commonRefinementLeftBlockVertex
                (G.horizontal r.castSucc).subdivision
                (G.horizontal r.succ).subdivision k 0) t =
            G.upperCoarseConnectorPath hx₀ hone htwo hthree r k.castSucc t
        calc
          _ = G.interfaceVertexConnector hx₀ hone htwo hthree r
              (G.upperCoarseVertex r k.castSucc) t :=
            congrArg (fun j ↦
              G.interfaceVertexConnector hx₀ hone htwo hthree r j t) hv
          _ = _ := by
            unfold upperCoarseConnectorPath
            exact (path_cast_apply _ _ _ t).symm
      have hconnectorLast (t : I) :
          G.upperRefinedBlockConnector hx₀ hone htwo hthree r k
              (Fin.last (IntervalSubdivision.commonRefinementLeftBlockSize
                (G.horizontal r.castSucc).subdivision
                (G.horizontal r.succ).subdivision k)) t =
            (G.upperCoarseConnectors hx₀ hone htwo hthree r).path k.succ t := by
        have hv :
            IntervalSubdivision.commonRefinementLeftBlockVertex
                (G.horizontal r.castSucc).subdivision
                (G.horizontal r.succ).subdivision k
                (Fin.last (IntervalSubdivision.commonRefinementLeftBlockSize
                  (G.horizontal r.castSucc).subdivision
                  (G.horizontal r.succ).subdivision k)) =
              G.upperCoarseVertex r k.succ := by
          unfold upperCoarseVertex interfaceSubdivision
          simp
        change
          G.interfaceVertexConnector hx₀ hone htwo hthree r
              (IntervalSubdivision.commonRefinementLeftBlockVertex
                (G.horizontal r.castSucc).subdivision
                (G.horizontal r.succ).subdivision k
                (Fin.last (IntervalSubdivision.commonRefinementLeftBlockSize
                  (G.horizontal r.castSucc).subdivision
                  (G.horizontal r.succ).subdivision k))) t =
            G.upperCoarseConnectorPath hx₀ hone htwo hthree r k.succ t
        calc
          _ = G.interfaceVertexConnector hx₀ hone htwo hthree r
              (G.upperCoarseVertex r k.succ) t :=
            congrArg (fun j ↦
              G.interfaceVertexConnector hx₀ hone htwo hthree r j t) hv
          _ = _ := by
            unfold upperCoarseConnectorPath
            exact (path_cast_apply _ _ _ t).symm
      have hsegment (t : I) :
          (G.interfacePath r).subpath
              (G.upperRefinedBlockPoint r k 0)
              (G.upperRefinedBlockPoint r k
                (Fin.last (IntervalSubdivision.commonRefinementLeftBlockSize
                  (G.horizontal r.castSucc).subdivision
                  (G.horizontal r.succ).subdivision k))) t =
            (G.interfacePath r).subpath
              ((G.bandUpperBoundary r).subdivision.point k.castSucc)
              ((G.bandUpperBoundary r).subdivision.point k.succ) t := by
        change G.interfacePath r
            (Icc.convexComb (G.upperRefinedBlockPoint r k 0)
              (G.upperRefinedBlockPoint r k
                (Fin.last (IntervalSubdivision.commonRefinementLeftBlockSize
                  (G.horizontal r.castSucc).subdivision
                  (G.horizontal r.succ).subdivision k))) t) =
          G.interfacePath r
            (Icc.convexComb
              ((G.bandUpperBoundary r).subdivision.point k.castSucc)
              ((G.bandUpperBoundary r).subdivision.point k.succ) t)
        rw [G.upperRefinedBlockPoint_zero r k,
          G.upperRefinedBlockPoint_last r k]
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

end StaggeredCoverGrid

end Hatcher.VanKampen
