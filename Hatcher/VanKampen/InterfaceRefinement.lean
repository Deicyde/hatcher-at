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

private theorem ofFn_finCast {α : Type*} {m n : ℕ} (h : m = n)
    (f : Fin n → α) :
    List.ofFn (fun j : Fin m ↦ f (Fin.cast h j)) = List.ofFn f := by
  subst n
  rfl

private theorem coverLoopClass_heq_of_eq
    {i j : ι} (hij : i = j) (p q : Path x₀ x₀)
    (hp : ∀ t, p t ∈ U i) (hq : ∀ t, q t ∈ U j) (hpq : p = q) :
    HEq (Factorization.coverLoopClass (hx₀ := hx₀) i p hp)
      (Factorization.coverLoopClass (hx₀ := hx₀) j q hq) := by
  subst j
  subst q
  rfl

/-- The nonempty block of refined upper-edge factors inside one coarse
horizontal cell. -/
def upperRefinedCoverBlock
    (G : StaggeredCoverGrid U H bottom top)
    (hx₀ : ∀ i, x₀ ∈ U i)
    (hone : ∀ i, IsPathConnected (U i))
    (htwo : ∀ i j, IsPathConnected (U i ∩ U j))
    (hthree : ∀ i j k, IsPathConnected (U i ∩ U j ∩ U k))
    (r : Fin (G.extraRows + 2))
    (k : Fin (G.horizontal r.castSucc).subdivision.cells) :
    Factorization.CoverBlock (U := U) (x₀ := x₀) (hx₀ := hx₀) := by
  let N := IntervalSubdivision.commonRefinementLeftBlockSize
    (G.horizontal r.castSucc).subdivision
    (G.horizontal r.succ).subdivision k
  have hN : N - 1 + 1 = N := Nat.sub_add_cancel <|
    IntervalSubdivision.commonRefinementLeftBlockSize_pos
      (G.horizontal r.castSucc).subdivision
      (G.horizontal r.succ).subdivision k
  exact Factorization.coverBlockOfFn ((G.horizontal r.castSucc).label k)
    (fun j : Fin (N - 1 + 1) ↦
      G.upperRefinedBlockClass hx₀ hone htwo hthree r k (Fin.cast hN j))

theorem upperRefinedCoverBlock_coarseEntry
    (G : StaggeredCoverGrid U H bottom top)
    (hx₀ : ∀ i, x₀ ∈ U i)
    (hone : ∀ i, IsPathConnected (U i))
    (htwo : ∀ i j, IsPathConnected (U i ∩ U j))
    (hthree : ∀ i j k, IsPathConnected (U i ∩ U j ∩ U k))
    (r : Fin (G.extraRows + 2))
    (k : Fin (G.horizontal r.castSucc).subdivision.cells) :
    (G.upperRefinedCoverBlock hx₀ hone htwo hthree r k).coarseEntry =
      ⟨(G.horizontal r.castSucc).label k,
        (Path.Homotopic.Quotient.mk
          ((G.upperCoarseConnectors hx₀ hone htwo hthree r).factor
            (hx₀ := hx₀) k) :
          CoverGroup U x₀ hx₀ ((G.horizontal r.castSucc).label k))⟩ := by
  unfold upperRefinedCoverBlock
  dsimp only
  rw [Factorization.coverBlockOfFn_coarseEntry]
  apply Sigma.ext
  · rfl
  · dsimp only
    rw [ofFn_finCast]
    exact heq_of_eq <|
      G.reverseProd_upperRefinedBlockClass_eq_upperCoarseFactor
        hx₀ hone htwo hthree r k

theorem upperRefinedCoverBlock_fineEntries
    (G : StaggeredCoverGrid U H bottom top)
    (hx₀ : ∀ i, x₀ ∈ U i)
    (hone : ∀ i, IsPathConnected (U i))
    (htwo : ∀ i j, IsPathConnected (U i ∩ U j))
    (hthree : ∀ i j k, IsPathConnected (U i ∩ U j ∩ U k))
    (r : Fin (G.extraRows + 2))
    (k : Fin (G.horizontal r.castSucc).subdivision.cells) :
    (G.upperRefinedCoverBlock hx₀ hone htwo hthree r k).fineEntries =
      List.ofFn fun j ↦
        (⟨(G.horizontal r.castSucc).label k,
          G.upperRefinedBlockClass hx₀ hone htwo hthree r k j⟩ :
          Factorization.Entry U x₀ hx₀) := by
  let N := IntervalSubdivision.commonRefinementLeftBlockSize
    (G.horizontal r.castSucc).subdivision
    (G.horizontal r.succ).subdivision k
  have hN : N - 1 + 1 = N := Nat.sub_add_cancel <|
    IntervalSubdivision.commonRefinementLeftBlockSize_pos
      (G.horizontal r.castSucc).subdivision
      (G.horizontal r.succ).subdivision k
  change (Factorization.coverBlockOfFn
    ((G.horizontal r.castSucc).label k)
    (fun j : Fin (N - 1 + 1) ↦
      G.upperRefinedBlockClass hx₀ hone htwo hthree r k
        (Fin.cast hN j))).fineEntries = _
  rw [Factorization.coverBlockOfFn_fineEntries]
  exact ofFn_finCast hN (fun j ↦
    (⟨(G.horizontal r.castSucc).label k,
      G.upperRefinedBlockClass hx₀ hone htwo hthree r k j⟩ :
      Factorization.Entry U x₀ hx₀))

theorem upperRefinedBlockEntry_eq_alignedLowerEntry
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
    (⟨(G.horizontal r.castSucc).label k,
      G.upperRefinedBlockClass hx₀ hone htwo hthree r k j⟩ :
      Factorization.Entry U x₀ hx₀) =
    let D := G.alignedInterface hx₀ hone htwo hthree r
    let c := IntervalSubdivision.commonRefinementLeftBlockCell
      (G.horizontal r.castSucc).subdivision
      (G.horizontal r.succ).subdivision k j
    ⟨D.lowerLabel c,
      Factorization.coverLoopClass (D.lowerLabel c) (D.loop c)
        (D.loop_mem_lower c)⟩ := by
  dsimp only
  have hlabel :
      (G.alignedInterface hx₀ hone htwo hthree r).lowerLabel
          (IntervalSubdivision.commonRefinementLeftBlockCell
            (G.horizontal r.castSucc).subdivision
            (G.horizontal r.succ).subdivision k j) =
        (G.horizontal r.castSucc).label k := by
    simp [alignedInterface, Factorization.AlignedInterface.ofGrid,
      lowerInterfaceBoundary]
  apply Sigma.ext
  · exact hlabel.symm
  · dsimp only
    let c := IntervalSubdivision.commonRefinementLeftBlockCell
      (G.horizontal r.castSucc).subdivision
      (G.horizontal r.succ).subdivision k j
    let localLoop := basedSegmentLoop (G.interfacePath r)
      (G.upperRefinedBlockPoint r k j.castSucc)
      (G.upperRefinedBlockPoint r k j.succ)
      (G.upperRefinedBlockConnector hx₀ hone htwo hthree r k j.castSucc)
      (G.upperRefinedBlockConnector hx₀ hone htwo hthree r k j.succ)
    have hlocalMem (t : I) :
        localLoop t ∈ U ((G.horizontal r.castSucc).label k) := by
      exact basedSegmentLoop_mem _ _ _
        ((G.upperRefinedBlockPoint_strictMono r k)
          Fin.castSucc_lt_succ).le _ _ _
        (fun t ↦ G.upperRefinedBlockConnector_range
          hx₀ hone htwo hthree r k j.castSucc ⟨t, rfl⟩)
        (fun t ↦ G.upperRefinedBlockConnector_range
          hx₀ hone htwo hthree r k j.succ ⟨t, rfl⟩)
        (fun _x hmem ↦ (G.bandUpperBoundary r).mapsTo k
          ⟨(G.upperRefinedBlockPoint_mem_cell r k j.castSucc).1.trans hmem.1,
            hmem.2.trans (G.upperRefinedBlockPoint_mem_cell r k j.succ).2⟩) t
    have hlocalClass :
        G.upperRefinedBlockClass hx₀ hone htwo hthree r k j =
          Factorization.coverLoopClass
            ((G.horizontal r.castSucc).label k) localLoop hlocalMem := by
      rfl
    have hloop : localLoop =
        (G.alignedInterface hx₀ hone htwo hthree r).loop c := by
      have hv₀ :
          IntervalSubdivision.commonRefinementLeftBlockVertex
              (G.horizontal r.castSucc).subdivision
              (G.horizontal r.succ).subdivision k j.castSucc = c.castSucc :=
        IntervalSubdivision.commonRefinementLeftBlockVertex_castSucc _ _ _ _
      have hv₁ :
          IntervalSubdivision.commonRefinementLeftBlockVertex
              (G.horizontal r.castSucc).subdivision
              (G.horizontal r.succ).subdivision k j.succ = c.succ :=
        IntervalSubdivision.commonRefinementLeftBlockVertex_succ _ _ _ _
      have hleft (t : I) :
          G.upperRefinedBlockConnector hx₀ hone htwo hthree r k j.castSucc t =
            (G.alignedInterface hx₀ hone htwo hthree r).connector c.castSucc t := by
        exact congrArg (fun z ↦
          G.interfaceVertexConnector hx₀ hone htwo hthree r z t) hv₀
      have hright (t : I) :
          G.upperRefinedBlockConnector hx₀ hone htwo hthree r k j.succ t =
            (G.alignedInterface hx₀ hone htwo hthree r).connector c.succ t := by
        exact congrArg (fun z ↦
          G.interfaceVertexConnector hx₀ hone htwo hthree r z t) hv₁
      have hsegment (t : I) :
          (G.interfacePath r).subpath
              (G.upperRefinedBlockPoint r k j.castSucc)
              (G.upperRefinedBlockPoint r k j.succ) t =
            (G.interfacePath r).subpath
              ((G.alignedInterface hx₀ hone htwo hthree r).point c.castSucc)
              ((G.alignedInterface hx₀ hone htwo hthree r).point c.succ) t := by
        change G.interfacePath r
            (Icc.convexComb
              ((G.interfaceSubdivision r).point _)
              ((G.interfaceSubdivision r).point _) t) =
          G.interfacePath r
            (Icc.convexComb
              ((G.interfaceSubdivision r).point _)
              ((G.interfaceSubdivision r).point _) t)
        rw [hv₀, hv₁]
      apply Path.ext
      funext t
      simp only [localLoop, Factorization.AlignedInterface.loop,
        basedSegmentLoop, Path.trans_apply]
      split
      · exact hleft _
      · split
        · exact hsegment _
        · simp only [Path.symm_apply, Function.comp_apply]
          exact hright _
    exact (heq_of_eq hlocalClass).trans <|
      coverLoopClass_heq_of_eq hlabel.symm localLoop
        ((G.alignedInterface hx₀ hone htwo hthree r).loop c)
        hlocalMem ((G.alignedInterface hx₀ hone htwo hthree r).loop_mem_lower c)
        hloop

/-- The coarse upper-row cells, each carrying its ordered block of interface
refinement factors. -/
def upperRefinedCoverBlocks
    (G : StaggeredCoverGrid U H bottom top)
    (hx₀ : ∀ i, x₀ ∈ U i)
    (hone : ∀ i, IsPathConnected (U i))
    (htwo : ∀ i j, IsPathConnected (U i ∩ U j))
    (hthree : ∀ i j k, IsPathConnected (U i ∩ U j ∩ U k))
    (r : Fin (G.extraRows + 2)) :
    List (Factorization.CoverBlock (U := U) (x₀ := x₀) (hx₀ := hx₀)) :=
  List.ofFn fun k ↦
    G.upperRefinedCoverBlock hx₀ hone htwo hthree r k

theorem upperRefinedCoverBlocks_coarseEntries
    (G : StaggeredCoverGrid U H bottom top)
    (hx₀ : ∀ i, x₀ ∈ U i)
    (hone : ∀ i, IsPathConnected (U i))
    (htwo : ∀ i j, IsPathConnected (U i ∩ U j))
    (hthree : ∀ i j k, IsPathConnected (U i ∩ U j ∩ U k))
    (r : Fin (G.extraRows + 2)) :
    Factorization.coarseEntries
        (G.upperRefinedCoverBlocks hx₀ hone htwo hthree r) =
      ((G.upperCoarseConnectors hx₀ hone htwo hthree r).toFactorization
        (hx₀ := hx₀)).entries := by
  rw [BoundaryConnectors.toFactorization_entries]
  unfold upperRefinedCoverBlocks Factorization.coarseEntries
  simp only [List.map_ofFn]
  change (List.ofFn fun k : Fin (G.horizontal r.castSucc).subdivision.cells ↦
      (G.upperRefinedCoverBlock hx₀ hone htwo hthree r k).coarseEntry) =
    List.ofFn fun k : Fin (G.horizontal r.castSucc).subdivision.cells ↦
      (⟨(G.horizontal r.castSucc).label k,
        (Path.Homotopic.Quotient.mk
          ((G.upperCoarseConnectors hx₀ hone htwo hthree r).factor
            (hx₀ := hx₀) k) :
          CoverGroup U x₀ hx₀ ((G.horizontal r.castSucc).label k))⟩ :
        Factorization.Entry U x₀ hx₀)
  rw [List.ofFn_inj]
  funext k
  exact G.upperRefinedCoverBlock_coarseEntry hx₀ hone htwo hthree r k

theorem upperRefinedCoverBlocks_fineEntries
    (G : StaggeredCoverGrid U H bottom top)
    (hx₀ : ∀ i, x₀ ∈ U i)
    (hone : ∀ i, IsPathConnected (U i))
    (htwo : ∀ i j, IsPathConnected (U i ∩ U j))
    (hthree : ∀ i j k, IsPathConnected (U i ∩ U j ∩ U k))
    (r : Fin (G.extraRows + 2)) :
    Factorization.fineEntries
        (G.upperRefinedCoverBlocks hx₀ hone htwo hthree r) =
      (G.alignedInterface hx₀ hone htwo hthree r).lowerEntries
        (hx₀ := hx₀) := by
  change ((G.upperRefinedCoverBlocks hx₀ hone htwo hthree r).map
    Factorization.CoverBlock.fineEntries).flatten = _
  unfold upperRefinedCoverBlocks
  rw [List.map_ofFn]
  change (List.ofFn fun k : Fin (G.horizontal r.castSucc).subdivision.cells ↦
    (G.upperRefinedCoverBlock hx₀ hone htwo hthree r k).fineEntries).flatten = _
  simp_rw [G.upperRefinedCoverBlock_fineEntries hx₀ hone htwo hthree r]
  simp_rw [G.upperRefinedBlockEntry_eq_alignedLowerEntry
    hx₀ hone htwo hthree r]
  unfold Factorization.AlignedInterface.lowerEntries
  let entry : Fin (IntervalSubdivision.commonRefinement
      (G.horizontal r.castSucc).subdivision
      (G.horizontal r.succ).subdivision).cells →
      Factorization.Entry U x₀ hx₀ := fun c ↦
    let D := G.alignedInterface hx₀ hone htwo hthree r
    ⟨D.lowerLabel c,
      Factorization.coverLoopClass (D.lowerLabel c) (D.loop c)
        (D.loop_mem_lower c)⟩
  change (List.ofFn fun k : Fin (G.horizontal r.castSucc).subdivision.cells ↦
      List.ofFn fun j : Fin (IntervalSubdivision.commonRefinementLeftBlockSize
        (G.horizontal r.castSucc).subdivision
        (G.horizontal r.succ).subdivision k) ↦
        entry (IntervalSubdivision.commonRefinementLeftBlockCell
          (G.horizontal r.castSucc).subdivision
          (G.horizontal r.succ).subdivision k j)).flatten =
    List.ofFn entry
  have hblocks :
      (List.ofFn fun k : Fin (G.horizontal r.castSucc).subdivision.cells ↦
        List.ofFn fun j : Fin (IntervalSubdivision.commonRefinementLeftBlockSize
          (G.horizontal r.castSucc).subdivision
          (G.horizontal r.succ).subdivision k) ↦
          entry (IntervalSubdivision.commonRefinementLeftBlockCell
            (G.horizontal r.castSucc).subdivision
            (G.horizontal r.succ).subdivision k j)) =
        List.ofFn fun k : Fin (G.horizontal r.castSucc).subdivision.cells ↦
          (IntervalSubdivision.commonRefinementLeftBlockCells
            (G.horizontal r.castSucc).subdivision
            (G.horizontal r.succ).subdivision k).map entry := by
    rw [List.ofFn_inj]
    funext k
    unfold IntervalSubdivision.commonRefinementLeftBlockCells
    rw [List.map_ofFn]
    rfl
  rw [hblocks]
  have houter :
      (List.ofFn fun k : Fin (G.horizontal r.castSucc).subdivision.cells ↦
        (IntervalSubdivision.commonRefinementLeftBlockCells
          (G.horizontal r.castSucc).subdivision
          (G.horizontal r.succ).subdivision k).map entry) =
        (List.ofFn fun k : Fin (G.horizontal r.castSucc).subdivision.cells ↦
          IntervalSubdivision.commonRefinementLeftBlockCells
            (G.horizontal r.castSucc).subdivision
            (G.horizontal r.succ).subdivision k).map (List.map entry) := by
    rw [List.map_ofFn]
    rfl
  rw [houter]
  rw [← List.map_flatten,
    IntervalSubdivision.commonRefinementLeftBlockCells_flatten]
  rw [List.map_ofFn]
  rfl

/-- Splitting each coarse upper-row factor into its common-refinement block
produces the lower-labeled entries of the aligned interface. -/
theorem moves_upperCoarseEntries_to_alignedLowerEntries
    (G : StaggeredCoverGrid U H bottom top)
    (hx₀ : ∀ i, x₀ ∈ U i)
    (hone : ∀ i, IsPathConnected (U i))
    (htwo : ∀ i j, IsPathConnected (U i ∩ U j))
    (hthree : ∀ i j k, IsPathConnected (U i ∩ U j ∩ U k))
    (r : Fin (G.extraRows + 2)) :
    Factorization.Moves
      ((G.upperCoarseConnectors hx₀ hone htwo hthree r).toFactorization
        (hx₀ := hx₀)).entries
      ((G.alignedInterface hx₀ hone htwo hthree r).lowerEntries
        (hx₀ := hx₀)) := by
  have h := Factorization.moves_split_blocks
    (G.upperRefinedCoverBlocks hx₀ hone htwo hthree r)
  rw [G.upperRefinedCoverBlocks_coarseEntries hx₀ hone htwo hthree r,
    G.upperRefinedCoverBlocks_fineEntries hx₀ hone htwo hthree r] at h
  exact h

/-- The coarse upper boundary of a band refines to the lower-labeled
factorization at the next interface. -/
theorem upperCoarseToLowerInterfaceSweep
    (G : StaggeredCoverGrid U H bottom top)
    (hx₀ : ∀ i, x₀ ∈ U i)
    (hone : ∀ i, IsPathConnected (U i))
    (htwo : ∀ i j, IsPathConnected (U i ∩ U j))
    (hthree : ∀ i j k, IsPathConnected (U i ∩ U j ∩ U k))
    (r : Fin (G.extraRows + 2)) :
    Factorization.Sweep
      ((G.upperCoarseConnectors hx₀ hone htwo hthree r).toFactorization
        (hx₀ := hx₀))
      (G.lowerInterfaceFactorization hx₀ hone htwo hthree r) := by
  constructor
  rw [G.lowerInterfaceFactorization_entries hx₀ hone htwo hthree r]
  exact G.moves_upperCoarseEntries_to_alignedLowerEntries
    hx₀ hone htwo hthree r

end StaggeredCoverGrid

end Hatcher.VanKampen
