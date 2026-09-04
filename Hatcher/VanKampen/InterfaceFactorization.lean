import Hatcher.VanKampen.BoundaryFactorization

noncomputable section

open Set
open scoped unitInterval

namespace Hatcher.VanKampen

universe u v

/-- Restrict an ambient path to a subspace containing its whole image. -/
def pathInSet {X : Type v} [TopologicalSpace X] {a b : X}
    (p : Path a b) (S : Set X) (ha : a ∈ S) (hb : b ∈ S)
    (hp : ∀ t, p t ∈ S) : Path (⟨a, ha⟩ : S) ⟨b, hb⟩ where
  toFun t := ⟨p t, hp t⟩
  continuous_toFun := p.continuous.subtype_mk _
  source' := Subtype.ext p.source
  target' := Subtype.ext p.target

/-- Close a subpath to the basepoint using chosen connector paths at its two
endpoints. -/
def basedSegmentLoop {X : Type v} [TopologicalSpace X] {x₀ : X}
    (p : Path x₀ x₀) (a b : I)
    (ca : Path x₀ (p a)) (cb : Path x₀ (p b)) : Path x₀ x₀ :=
  (ca.trans (p.subpath a b)).trans cb.symm

theorem basedSegmentLoop_mem {X : Type v} [TopologicalSpace X]
    {x₀ : X} (p : Path x₀ x₀) (a b : I) (hab : a ≤ b)
    (ca : Path x₀ (p a)) (cb : Path x₀ (p b)) (S : Set X)
    (hca : ∀ t, ca t ∈ S) (hcb : ∀ t, cb t ∈ S)
    (hp : MapsTo p (Icc a b) S) (t : I) :
    basedSegmentLoop p a b ca cb t ∈ S := by
  have hseg : Set.range (p.subpath a b) ⊆ S := by
    rw [Path.range_subpath_of_le p a b hab]
    exact image_subset_iff.mpr hp
  have hrange : Set.range (basedSegmentLoop p a b ca cb) ⊆ S := by
    rw [basedSegmentLoop, Path.trans_range, Path.trans_range, Path.symm_range]
    exact union_subset (union_subset (range_subset_iff.mpr hca) hseg)
      (range_subset_iff.mpr hcb)
  exact hrange ⟨t, rfl⟩

namespace StaggeredCoverGrid

variable {ι : Type u} {X : Type v} [TopologicalSpace X]
  {U : ι → Set X} {x₀ : X} {p q : Path x₀ x₀}
  {H : p.Homotopy q} {bottom : BoundaryCover U p}
  {top : BoundaryCover U q}

/-- The horizontal path at one interface between adjacent grid bands. -/
def interfacePath (G : StaggeredCoverGrid U H bottom top)
    (r : Fin (G.extraRows + 2)) : Path x₀ x₀ :=
  H.eval (G.level r.castSucc.succ)

/-- The common refinement of the horizontal subdivisions immediately below
and above one interface. -/
def interfaceSubdivision (G : StaggeredCoverGrid U H bottom top)
    (r : Fin (G.extraRows + 2)) : IntervalSubdivision :=
  IntervalSubdivision.commonRefinement
    (G.horizontal r.castSucc).subdivision
    (G.horizontal r.succ).subdivision

/-- The interface path labeled by the cells immediately below it. -/
def lowerInterfaceBoundary (G : StaggeredCoverGrid U H bottom top)
    (r : Fin (G.extraRows + 2)) : BoundaryCover U (G.interfacePath r) := by
  let lower := G.horizontal r.castSucc
  let upper := G.horizontal r.succ
  refine
    { subdivision := G.interfaceSubdivision r
      label := fun k ↦ lower.label
        (IntervalSubdivision.commonRefinementLeftCell
          lower.subdivision upper.subdivision k)
      mapsTo := ?_ }
  intro k x hx
  exact G.subordinate r.castSucc
    (IntervalSubdivision.commonRefinementLeftCell
      lower.subdivision upper.subdivision k)
    ⟨⟨(G.level_strictMono Fin.castSucc_lt_succ).le, le_rfl⟩,
      IntervalSubdivision.commonRefinementLeftCell_spec
        lower.subdivision upper.subdivision k hx⟩

/-- The interface path labeled by the cells immediately above it. -/
def upperInterfaceBoundary (G : StaggeredCoverGrid U H bottom top)
    (r : Fin (G.extraRows + 2)) : BoundaryCover U (G.interfacePath r) := by
  let lower := G.horizontal r.castSucc
  let upper := G.horizontal r.succ
  refine
    { subdivision := G.interfaceSubdivision r
      label := fun k ↦ upper.label
        (IntervalSubdivision.commonRefinementRightCell
          lower.subdivision upper.subdivision k)
      mapsTo := ?_ }
  intro k x hx
  have hlevel : G.level r.succ.castSucc ≤ G.level r.succ.succ :=
    (G.level_strictMono
      (show r.succ.castSucc < r.succ.succ from Fin.castSucc_lt_succ)).le
  exact G.subordinate r.succ
    (IntervalSubdivision.commonRefinementRightCell
      lower.subdivision upper.subdivision k)
    ⟨⟨le_rfl, hlevel⟩,
      IntervalSubdivision.commonRefinementRightCell_spec
        lower.subdivision upper.subdivision k hx⟩

theorem lowerLabel_mem_interfaceLabels
    (G : StaggeredCoverGrid U H bottom top)
    (r : Fin (G.extraRows + 2))
    (k : Fin (G.lowerInterfaceBoundary r).subdivision.cells)
    (x : I) (hx : x ∈ (G.lowerInterfaceBoundary r).subdivision.cell k) :
    (G.lowerInterfaceBoundary r).label k ∈ G.interfaceLabels r x := by
  classical
  unfold lowerInterfaceBoundary
  dsimp only
  unfold interfaceLabels
  apply Finset.mem_union_left
  apply Finset.mem_image.mpr
  refine ⟨IntervalSubdivision.commonRefinementLeftCell
    (G.horizontal r.castSucc).subdivision
    (G.horizontal r.succ).subdivision k, ?_, rfl⟩
  rw [IntervalSubdivision.mem_incidentCells]
  exact IntervalSubdivision.commonRefinementLeftCell_spec
    (G.horizontal r.castSucc).subdivision
    (G.horizontal r.succ).subdivision k hx

theorem upperLabel_mem_interfaceLabels
    (G : StaggeredCoverGrid U H bottom top)
    (r : Fin (G.extraRows + 2))
    (k : Fin (G.upperInterfaceBoundary r).subdivision.cells)
    (x : I) (hx : x ∈ (G.upperInterfaceBoundary r).subdivision.cell k) :
    (G.upperInterfaceBoundary r).label k ∈ G.interfaceLabels r x := by
  classical
  unfold upperInterfaceBoundary
  dsimp only
  unfold interfaceLabels
  apply Finset.mem_union_right
  apply Finset.mem_image.mpr
  refine ⟨IntervalSubdivision.commonRefinementRightCell
    (G.horizontal r.castSucc).subdivision
    (G.horizontal r.succ).subdivision k, ?_, rfl⟩
  rw [IntervalSubdivision.mem_incidentCells]
  exact IntervalSubdivision.commonRefinementRightCell_spec
    (G.horizontal r.castSucc).subdivision
    (G.horizontal r.succ).subdivision k hx

/-- The interface connector, normalized to the constant path at the two
endpoints of the horizontal path. -/
noncomputable def interfaceVertexConnector
    (G : StaggeredCoverGrid U H bottom top)
    (hx₀ : ∀ i, x₀ ∈ U i)
    (hone : ∀ i, IsPathConnected (U i))
    (htwo : ∀ i j, IsPathConnected (U i ∩ U j))
    (hthree : ∀ i j k, IsPathConnected (U i ∩ U j ∩ U k))
    (r : Fin (G.extraRows + 2))
    (j : Fin (G.interfaceSubdivision r).cells.succ) :
    Path x₀ ((G.interfacePath r) ((G.interfaceSubdivision r).point j)) := by
  by_cases hj0 : j = 0
  · have hpoint : (G.interfaceSubdivision r).point j = 0 :=
      (congrArg (G.interfaceSubdivision r).point hj0).trans
        (G.interfaceSubdivision r).left
    exact (Path.refl x₀).cast rfl
      ((congrArg (G.interfacePath r) hpoint).trans (G.interfacePath r).source)
  by_cases hj1 : j = Fin.last (G.interfaceSubdivision r).cells
  · have hpoint : (G.interfaceSubdivision r).point j = 1 :=
      (congrArg (G.interfaceSubdivision r).point hj1).trans
        (G.interfaceSubdivision r).right
    exact (Path.refl x₀).cast rfl
      ((congrArg (G.interfacePath r) hpoint).trans (G.interfacePath r).target)
  exact G.interfaceConnector hx₀ hone htwo hthree r
    ((G.interfaceSubdivision r).point j)

theorem interfaceVertexConnector_range
    (G : StaggeredCoverGrid U H bottom top)
    (hx₀ : ∀ i, x₀ ∈ U i)
    (hone : ∀ i, IsPathConnected (U i))
    (htwo : ∀ i j, IsPathConnected (U i ∩ U j))
    (hthree : ∀ i j k, IsPathConnected (U i ∩ U j ∩ U k))
    (r : Fin (G.extraRows + 2))
    (j : Fin (G.interfaceSubdivision r).cells.succ) {i : ι}
    (hi : i ∈ G.interfaceLabels r ((G.interfaceSubdivision r).point j)) :
    Set.range (G.interfaceVertexConnector hx₀ hone htwo hthree r j) ⊆ U i := by
  unfold interfaceVertexConnector
  split
  · rw [Path.cast_coe, Path.refl_range, singleton_subset_iff]
    exact hx₀ i
  · split
    · rw [Path.cast_coe, Path.refl_range, singleton_subset_iff]
      exact hx₀ i
    · exact G.interfaceConnector_range hx₀ hone htwo hthree r _ hi

/-- Connectors for the lower labeling of an interface. -/
def lowerInterfaceConnectors
    (G : StaggeredCoverGrid U H bottom top)
    (hx₀ : ∀ i, x₀ ∈ U i)
    (hone : ∀ i, IsPathConnected (U i))
    (htwo : ∀ i j, IsPathConnected (U i ∩ U j))
    (hthree : ∀ i j k, IsPathConnected (U i ∩ U j ∩ U k))
    (r : Fin (G.extraRows + 2)) :
    BoundaryConnectors (G.lowerInterfaceBoundary r) where
  path := G.interfaceVertexConnector hx₀ hone htwo hthree r
  left_eq := by
    change G.interfaceVertexConnector hx₀ hone htwo hthree r
        (0 : Fin (G.interfaceSubdivision r).cells.succ) =
      (Path.refl x₀).cast rfl
        ((congrArg (G.interfacePath r) (G.interfaceSubdivision r).left).trans
          (G.interfacePath r).source)
    unfold interfaceVertexConnector
    rw [dif_pos rfl]
  right_eq := by
    change G.interfaceVertexConnector hx₀ hone htwo hthree r
        (Fin.last (G.interfaceSubdivision r).cells) =
      (Path.refl x₀).cast rfl
        ((congrArg (G.interfacePath r) (G.interfaceSubdivision r).right).trans
          (G.interfacePath r).target)
    unfold interfaceVertexConnector
    have hne : (Fin.last (G.interfaceSubdivision r).cells :
        Fin (G.interfaceSubdivision r).cells.succ) ≠ 0 := by
      intro h
      have hval : (G.interfaceSubdivision r).cells = 0 := by
        simpa using congrArg Fin.val h
      exact (Nat.ne_of_gt (G.interfaceSubdivision r).cells_pos) hval
    rw [dif_neg hne, dif_pos rfl]
  range_left k := by
    apply G.interfaceVertexConnector_range hx₀ hone htwo hthree r
    apply G.lowerLabel_mem_interfaceLabels r k
    exact ⟨le_rfl,
      ((G.lowerInterfaceBoundary r).subdivision.strictMono
        Fin.castSucc_lt_succ).le⟩
  range_right k := by
    apply G.interfaceVertexConnector_range hx₀ hone htwo hthree r
    apply G.lowerLabel_mem_interfaceLabels r k
    exact ⟨((G.lowerInterfaceBoundary r).subdivision.strictMono
      Fin.castSucc_lt_succ).le, le_rfl⟩

/-- Connectors for the upper labeling of an interface. -/
def upperInterfaceConnectors
    (G : StaggeredCoverGrid U H bottom top)
    (hx₀ : ∀ i, x₀ ∈ U i)
    (hone : ∀ i, IsPathConnected (U i))
    (htwo : ∀ i j, IsPathConnected (U i ∩ U j))
    (hthree : ∀ i j k, IsPathConnected (U i ∩ U j ∩ U k))
    (r : Fin (G.extraRows + 2)) :
    BoundaryConnectors (G.upperInterfaceBoundary r) where
  path := G.interfaceVertexConnector hx₀ hone htwo hthree r
  left_eq := by
    change G.interfaceVertexConnector hx₀ hone htwo hthree r
        (0 : Fin (G.interfaceSubdivision r).cells.succ) =
      (Path.refl x₀).cast rfl
        ((congrArg (G.interfacePath r) (G.interfaceSubdivision r).left).trans
          (G.interfacePath r).source)
    unfold interfaceVertexConnector
    rw [dif_pos rfl]
  right_eq := by
    change G.interfaceVertexConnector hx₀ hone htwo hthree r
        (Fin.last (G.interfaceSubdivision r).cells) =
      (Path.refl x₀).cast rfl
        ((congrArg (G.interfacePath r) (G.interfaceSubdivision r).right).trans
          (G.interfacePath r).target)
    unfold interfaceVertexConnector
    have hne : (Fin.last (G.interfaceSubdivision r).cells :
        Fin (G.interfaceSubdivision r).cells.succ) ≠ 0 := by
      intro h
      have hval : (G.interfaceSubdivision r).cells = 0 := by
        simpa using congrArg Fin.val h
      exact (Nat.ne_of_gt (G.interfaceSubdivision r).cells_pos) hval
    rw [dif_neg hne, dif_pos rfl]
  range_left k := by
    apply G.interfaceVertexConnector_range hx₀ hone htwo hthree r
    apply G.upperLabel_mem_interfaceLabels r k
    exact ⟨le_rfl,
      ((G.upperInterfaceBoundary r).subdivision.strictMono
        Fin.castSucc_lt_succ).le⟩
  range_right k := by
    apply G.interfaceVertexConnector_range hx₀ hone htwo hthree r
    apply G.upperLabel_mem_interfaceLabels r k
    exact ⟨((G.upperInterfaceBoundary r).subdivision.strictMono
      Fin.castSucc_lt_succ).le, le_rfl⟩

end StaggeredCoverGrid

namespace Factorization

variable {ι : Type u} {X : Type v} [TopologicalSpace X]
  {U : ι → Set X} {x₀ : X} {hx₀ : ∀ i, x₀ ∈ U i}

/-- One coarse cover-group entry together with a nonempty same-cover
subdivision of that entry. -/
structure CoverBlock where
  index : ι
  head : CoverGroup U x₀ hx₀ index
  tail : List (CoverGroup U x₀ hx₀ index)

namespace CoverBlock

def coarseEntry (b : CoverBlock (U := U) (x₀ := x₀) (hx₀ := hx₀)) :
    Entry U x₀ hx₀ :=
  ⟨b.index, (b.head :: b.tail).reverse.prod⟩

def fineEntries (b : CoverBlock (U := U) (x₀ := x₀) (hx₀ := hx₀)) :
    List (Entry U x₀ hx₀) :=
  sameCoverEntries b.index (b.head :: b.tail)

end CoverBlock

def coarseEntries
    (bs : List (CoverBlock (U := U) (x₀ := x₀) (hx₀ := hx₀))) :
    List (Entry U x₀ hx₀) :=
  bs.map CoverBlock.coarseEntry

def fineEntries
    (bs : List (CoverBlock (U := U) (x₀ := x₀) (hx₀ := hx₀))) :
    List (Entry U x₀ hx₀) :=
  bs.flatMap CoverBlock.fineEntries

/-- Split every coarse entry into its prescribed nonempty block of
same-cover entries. -/
theorem moves_split_blocks
    (bs : List (CoverBlock (U := U) (x₀ := x₀) (hx₀ := hx₀))) :
    Moves (coarseEntries bs) (fineEntries bs) := by
  induction bs with
  | nil => exact Relation.ReflTransGen.refl
  | cons b bs ih =>
      have hfirst := moves_split_sameCover
        (U := U) (x₀ := x₀) (hx₀ := hx₀)
        ([] : List (Entry U x₀ hx₀)) (coarseEntries bs)
        b.index b.head b.tail
      have hrest := ih.prefix b.fineEntries
      have hfirst' : Moves (coarseEntries (b :: bs))
          (b.fineEntries ++ coarseEntries bs) := by
        simpa [coarseEntries, fineEntries, CoverBlock.coarseEntry,
          CoverBlock.fineEntries] using hfirst
      have hrest' : Moves (b.fineEntries ++ coarseEntries bs)
          (fineEntries (b :: bs)) := by
        simpa [coarseEntries, fineEntries, CoverBlock.fineEntries,
          List.append_assoc] using hrest
      exact hfirst'.trans hrest'

/-- The list of overlap changes attached to corresponding refined cells on
the two sides of an interface. -/
def pointwiseCoverChanges (n : ℕ) (lower upper : Fin n → ι)
    (overlap : ∀ k, OverlapGroup U x₀ hx₀ (lower k) (upper k)) :
    List (CoverChange (U := U) (x₀ := x₀) (hx₀ := hx₀)) :=
  List.ofFn fun k ↦ ⟨lower k, upper k, overlap k⟩

/-- Pointwise overlap witnesses relabel an aligned list of refined cells. -/
theorem moves_changeCover_ofFn (n : ℕ) (lower upper : Fin n → ι)
    (overlap : ∀ k, OverlapGroup U x₀ hx₀ (lower k) (upper k)) :
    Moves
      (List.ofFn fun k ↦
        ⟨lower k, overlapToLeft U x₀ hx₀ (lower k) (upper k) (overlap k)⟩)
      (List.ofFn fun k ↦
        ⟨upper k, overlapToRight U x₀ hx₀ (lower k) (upper k) (overlap k)⟩) := by
  simpa [pointwiseCoverChanges, CoverChange.leftEntry,
    CoverChange.rightEntry, Function.comp_def] using
    (moves_changeCover_list (U := U) (x₀ := x₀) (hx₀ := hx₀)
      ([] : List (Entry U x₀ hx₀)) ([] : List (Entry U x₀ hx₀))
      (pointwiseCoverChanges n lower upper overlap))

/-- The cover-group class of an ambient based loop known to stay in one
cover member. -/
def coverLoopClass (i : ι) (p : Path x₀ x₀) (hp : ∀ t, p t ∈ U i) :
    CoverGroup U x₀ hx₀ i :=
  Path.Homotopic.Quotient.mk (pathInSet p (U i) (hx₀ i) (hx₀ i) hp)

/-- The overlap-group class of an ambient based loop known to stay in two
cover members. -/
def overlapLoopClass (i j : ι) (p : Path x₀ x₀)
    (hp : ∀ t, p t ∈ U i ∩ U j) : OverlapGroup U x₀ hx₀ i j :=
  Path.Homotopic.Quotient.mk
    (pathInSet p (U i ∩ U j) ⟨hx₀ i, hx₀ j⟩ ⟨hx₀ i, hx₀ j⟩ hp)

theorem overlapToLeft_overlapLoopClass (i j : ι) (p : Path x₀ x₀)
    (hp : ∀ t, p t ∈ U i ∩ U j) :
    overlapToLeft U x₀ hx₀ i j (overlapLoopClass i j p hp) =
      coverLoopClass i p (fun t ↦ (hp t).1) := by
  simp only [overlapToLeft, overlapLoopClass, coverLoopClass]
  congr 1

theorem overlapToRight_overlapLoopClass (i j : ι) (p : Path x₀ x₀)
    (hp : ∀ t, p t ∈ U i ∩ U j) :
    overlapToRight U x₀ hx₀ i j (overlapLoopClass i j p hp) =
      coverLoopClass j p (fun t ↦ (hp t).2) := by
  simp only [overlapToRight, overlapLoopClass, coverLoopClass]
  congr 1

/-- A common refinement of the subdivisions on the two sides of one
interface, together with connector paths at every refined vertex. -/
structure AlignedInterface (p : Path x₀ x₀) where
  cells : ℕ
  point : Fin (cells + 1) → I
  strictMono : StrictMono point
  lowerLabel : Fin cells → ι
  upperLabel : Fin cells → ι
  lowerSegment : ∀ k,
    MapsTo p (Icc (point k.castSucc) (point k.succ)) (U (lowerLabel k))
  upperSegment : ∀ k,
    MapsTo p (Icc (point k.castSucc) (point k.succ)) (U (upperLabel k))
  connector : ∀ j, Path x₀ (p (point j))
  connector_lower_left : ∀ k t, connector k.castSucc t ∈ U (lowerLabel k)
  connector_lower_right : ∀ k t, connector k.succ t ∈ U (lowerLabel k)
  connector_upper_left : ∀ k t, connector k.castSucc t ∈ U (upperLabel k)
  connector_upper_right : ∀ k t, connector k.succ t ∈ U (upperLabel k)

namespace AlignedInterface

def loop (D : AlignedInterface (U := U) (x₀ := x₀) p)
    (k : Fin D.cells) : Path x₀ x₀ :=
  basedSegmentLoop p (D.point k.castSucc) (D.point k.succ)
    (D.connector k.castSucc) (D.connector k.succ)

theorem loop_mem_lower
    (D : AlignedInterface (U := U) (x₀ := x₀) p)
    (k : Fin D.cells) (t : I) : D.loop k t ∈ U (D.lowerLabel k) := by
  apply basedSegmentLoop_mem p _ _
    (D.strictMono.monotone (Fin.castSucc_le_succ k))
    (D.connector k.castSucc) (D.connector k.succ)
  · exact D.connector_lower_left k
  · exact D.connector_lower_right k
  · exact D.lowerSegment k

theorem loop_mem_upper
    (D : AlignedInterface (U := U) (x₀ := x₀) p)
    (k : Fin D.cells) (t : I) : D.loop k t ∈ U (D.upperLabel k) := by
  apply basedSegmentLoop_mem p _ _
    (D.strictMono.monotone (Fin.castSucc_le_succ k))
    (D.connector k.castSucc) (D.connector k.succ)
  · exact D.connector_upper_left k
  · exact D.connector_upper_right k
  · exact D.upperSegment k

def overlapClass
    (D : AlignedInterface (U := U) (x₀ := x₀) p)
    (k : Fin D.cells) :
    OverlapGroup U x₀ hx₀ (D.lowerLabel k) (D.upperLabel k) :=
  overlapLoopClass (D.lowerLabel k) (D.upperLabel k) (D.loop k)
    (fun t ↦ ⟨D.loop_mem_lower k t, D.loop_mem_upper k t⟩)

theorem overlapClass_left
    (D : AlignedInterface (U := U) (x₀ := x₀) p)
    (k : Fin D.cells) :
    overlapToLeft U x₀ hx₀ (D.lowerLabel k) (D.upperLabel k)
        (D.overlapClass k) =
      coverLoopClass (D.lowerLabel k) (D.loop k) (D.loop_mem_lower k) :=
  overlapToLeft_overlapLoopClass _ _ _ _

theorem overlapClass_right
    (D : AlignedInterface (U := U) (x₀ := x₀) p)
    (k : Fin D.cells) :
    overlapToRight U x₀ hx₀ (D.lowerLabel k) (D.upperLabel k)
        (D.overlapClass k) =
      coverLoopClass (D.upperLabel k) (D.loop k) (D.loop_mem_upper k) :=
  overlapToRight_overlapLoopClass _ _ _ _

/-- Corresponding refined entries immediately below and above one interface
are related by pointwise changes of cover. -/
theorem moves (D : AlignedInterface (U := U) (x₀ := x₀) p) :
    Moves
      (List.ofFn fun k ↦
        (⟨D.lowerLabel k,
          coverLoopClass (hx₀ := hx₀) (D.lowerLabel k) (D.loop k)
            (D.loop_mem_lower k)⟩ : Entry U x₀ hx₀))
      (List.ofFn fun k ↦
        (⟨D.upperLabel k,
          coverLoopClass (hx₀ := hx₀) (D.upperLabel k) (D.loop k)
            (D.loop_mem_upper k)⟩ : Entry U x₀ hx₀)) := by
  have h := moves_changeCover_ofFn (hx₀ := hx₀) D.cells
    D.lowerLabel D.upperLabel (D.overlapClass (hx₀ := hx₀))
  have hl :
      (List.ofFn fun k ↦
        (⟨D.lowerLabel k,
          overlapToLeft U x₀ hx₀ (D.lowerLabel k) (D.upperLabel k)
            (D.overlapClass (hx₀ := hx₀) k)⟩ : Entry U x₀ hx₀)) =
      List.ofFn fun k ↦
        (⟨D.lowerLabel k,
          coverLoopClass (hx₀ := hx₀) (D.lowerLabel k) (D.loop k)
            (D.loop_mem_lower k)⟩ : Entry U x₀ hx₀) := by
    rw [List.ofFn_inj]
    funext k
    rw [D.overlapClass_left k]
  have hu :
      (List.ofFn fun k ↦
        (⟨D.upperLabel k,
          overlapToRight U x₀ hx₀ (D.lowerLabel k) (D.upperLabel k)
            (D.overlapClass (hx₀ := hx₀) k)⟩ : Entry U x₀ hx₀)) =
      List.ofFn fun k ↦
        (⟨D.upperLabel k,
          coverLoopClass (hx₀ := hx₀) (D.upperLabel k) (D.loop k)
            (D.loop_mem_upper k)⟩ : Entry U x₀ hx₀) := by
    rw [List.ofFn_inj]
    funext k
    rw [D.overlapClass_right k]
  rw [hl, hu] at h
  exact h

/-- Build the aligned refined interface of two adjacent rows of a staggered
grid. -/
def ofGrid
    {p q : Path x₀ x₀} {H : p.Homotopy q}
    {bottom : BoundaryCover U p} {top : BoundaryCover U q}
    (G : StaggeredCoverGrid U H bottom top) (hx₀ : ∀ i, x₀ ∈ U i)
    (hone : ∀ i, IsPathConnected (U i))
    (htwo : ∀ i j, IsPathConnected (U i ∩ U j))
    (hthree : ∀ i j k, IsPathConnected (U i ∩ U j ∩ U k))
    (r : Fin (G.extraRows + 2)) :
    AlignedInterface (U := U) (x₀ := x₀)
      (H.eval (G.level r.castSucc.succ)) := by
  classical
  let lower := G.horizontal r.castSucc
  let upper := G.horizontal r.succ
  let refined := IntervalSubdivision.commonRefinement
    lower.subdivision upper.subdivision
  refine
    { cells := refined.cells
      point := refined.point
      strictMono := refined.strictMono
      lowerLabel := fun k ↦ lower.label
        (IntervalSubdivision.commonRefinementLeftCell
          lower.subdivision upper.subdivision k)
      upperLabel := fun k ↦ upper.label
        (IntervalSubdivision.commonRefinementRightCell
          lower.subdivision upper.subdivision k)
      lowerSegment := ?_
      upperSegment := ?_
      connector := fun j ↦
        G.interfaceVertexConnector hx₀ hone htwo hthree r j
      connector_lower_left := ?_
      connector_lower_right := ?_
      connector_upper_left := ?_
      connector_upper_right := ?_ }
  · intro k x hx
    change H (G.level r.castSucc.succ, x) ∈ U
      (lower.label (IntervalSubdivision.commonRefinementLeftCell
        lower.subdivision upper.subdivision k))
    apply G.subordinate r.castSucc
      (IntervalSubdivision.commonRefinementLeftCell
        lower.subdivision upper.subdivision k)
    exact ⟨⟨(G.level_strictMono Fin.castSucc_lt_succ).le, le_rfl⟩,
      IntervalSubdivision.commonRefinementLeftCell_spec
        lower.subdivision upper.subdivision k hx⟩
  · intro k x hx
    change H (G.level r.castSucc.succ, x) ∈ U
      (upper.label (IntervalSubdivision.commonRefinementRightCell
        lower.subdivision upper.subdivision k))
    apply G.subordinate r.succ
      (IntervalSubdivision.commonRefinementRightCell
        lower.subdivision upper.subdivision k)
    refine ⟨⟨le_rfl, ?_⟩,
      IntervalSubdivision.commonRefinementRightCell_spec
        lower.subdivision upper.subdivision k hx⟩
    rw [show r.castSucc.succ = r.succ.castSucc by rfl]
    exact (G.level_strictMono Fin.castSucc_lt_succ).le
  · intro k t
    refine G.interfaceVertexConnector_range hx₀ hone htwo hthree r
      k.castSucc ?_ ⟨t, rfl⟩
    unfold StaggeredCoverGrid.interfaceLabels
    apply Finset.mem_union_left
    apply Finset.mem_image.mpr
    refine ⟨IntervalSubdivision.commonRefinementLeftCell
      lower.subdivision upper.subdivision k, ?_, rfl⟩
    rw [IntervalSubdivision.mem_incidentCells]
    apply IntervalSubdivision.commonRefinementLeftCell_spec
    exact ⟨le_rfl, (refined.strictMono Fin.castSucc_lt_succ).le⟩
  · intro k t
    refine G.interfaceVertexConnector_range hx₀ hone htwo hthree r
      k.succ ?_ ⟨t, rfl⟩
    unfold StaggeredCoverGrid.interfaceLabels
    apply Finset.mem_union_left
    apply Finset.mem_image.mpr
    refine ⟨IntervalSubdivision.commonRefinementLeftCell
      lower.subdivision upper.subdivision k, ?_, rfl⟩
    rw [IntervalSubdivision.mem_incidentCells]
    apply IntervalSubdivision.commonRefinementLeftCell_spec
    exact ⟨(refined.strictMono Fin.castSucc_lt_succ).le, le_rfl⟩
  · intro k t
    refine G.interfaceVertexConnector_range hx₀ hone htwo hthree r
      k.castSucc ?_ ⟨t, rfl⟩
    unfold StaggeredCoverGrid.interfaceLabels
    apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    refine ⟨IntervalSubdivision.commonRefinementRightCell
      lower.subdivision upper.subdivision k, ?_, rfl⟩
    rw [IntervalSubdivision.mem_incidentCells]
    apply IntervalSubdivision.commonRefinementRightCell_spec
    exact ⟨le_rfl, (refined.strictMono Fin.castSucc_lt_succ).le⟩
  · intro k t
    refine G.interfaceVertexConnector_range hx₀ hone htwo hthree r
      k.succ ?_ ⟨t, rfl⟩
    unfold StaggeredCoverGrid.interfaceLabels
    apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    refine ⟨IntervalSubdivision.commonRefinementRightCell
      lower.subdivision upper.subdivision k, ?_, rfl⟩
    rw [IntervalSubdivision.mem_incidentCells]
    apply IntervalSubdivision.commonRefinementRightCell_spec
    exact ⟨(refined.strictMono Fin.castSucc_lt_succ).le, le_rfl⟩

end AlignedInterface

/-- Algebraic data produced by one geometric interface. -/
structure InterfaceMoveData where
  lowerBlocks : List (CoverBlock (U := U) (x₀ := x₀) (hx₀ := hx₀))
  upperBlocks : List (CoverBlock (U := U) (x₀ := x₀) (hx₀ := hx₀))
  refinedCells : ℕ
  lowerLabel : Fin refinedCells → ι
  upperLabel : Fin refinedCells → ι
  overlap : ∀ k, OverlapGroup U x₀ hx₀ (lowerLabel k) (upperLabel k)
  lower_fineEntries : fineEntries lowerBlocks =
    List.ofFn fun k ↦
      ⟨lowerLabel k,
        overlapToLeft U x₀ hx₀ (lowerLabel k) (upperLabel k) (overlap k)⟩
  upper_fineEntries : fineEntries upperBlocks =
    List.ofFn fun k ↦
      ⟨upperLabel k,
        overlapToRight U x₀ hx₀ (lowerLabel k) (upperLabel k) (overlap k)⟩

namespace InterfaceMoveData

/-- The split, relabel, and combine chain across one interface. -/
theorem moves (D : InterfaceMoveData (U := U) (x₀ := x₀) (hx₀ := hx₀)) :
    Moves (coarseEntries D.lowerBlocks) (coarseEntries D.upperBlocks) := by
  have hlower := moves_split_blocks D.lowerBlocks
  have hchange := moves_changeCover_ofFn D.refinedCells
    D.lowerLabel D.upperLabel D.overlap
  have hupper := (moves_split_blocks D.upperBlocks).symm
  rw [D.lower_fineEntries] at hlower
  rw [D.upper_fineEntries] at hupper
  exact hlower.trans (hchange.trans hupper)

end InterfaceMoveData

/-- One aligned geometric interface together with the coarse blocks obtained
by grouping its refined loops according to the lower and upper row cells. -/
structure InterfaceFactorizationData (p : Path x₀ x₀) where
  aligned : AlignedInterface (U := U) (x₀ := x₀) p
  lowerBlocks : List (CoverBlock (U := U) (x₀ := x₀) (hx₀ := hx₀))
  upperBlocks : List (CoverBlock (U := U) (x₀ := x₀) (hx₀ := hx₀))
  lower_fineEntries : fineEntries lowerBlocks =
    List.ofFn fun k ↦
      ⟨aligned.lowerLabel k,
        coverLoopClass (aligned.lowerLabel k) (aligned.loop k)
          (aligned.loop_mem_lower k)⟩
  upper_fineEntries : fineEntries upperBlocks =
    List.ofFn fun k ↦
      ⟨aligned.upperLabel k,
        coverLoopClass (aligned.upperLabel k) (aligned.loop k)
          (aligned.loop_mem_upper k)⟩

namespace InterfaceFactorizationData

def moveData
    (D : InterfaceFactorizationData (U := U) (x₀ := x₀) (hx₀ := hx₀) p) :
    InterfaceMoveData (U := U) (x₀ := x₀) (hx₀ := hx₀) where
  lowerBlocks := D.lowerBlocks
  upperBlocks := D.upperBlocks
  refinedCells := D.aligned.cells
  lowerLabel := D.aligned.lowerLabel
  upperLabel := D.aligned.upperLabel
  overlap := D.aligned.overlapClass
  lower_fineEntries := D.lower_fineEntries.trans <| by
    rw [List.ofFn_inj]
    funext k
    rw [D.aligned.overlapClass_left k]
  upper_fineEntries := D.upper_fineEntries.trans <| by
    rw [List.ofFn_inj]
    funext k
    rw [D.aligned.overlapClass_right k]

theorem moves
    (D : InterfaceFactorizationData (U := U) (x₀ := x₀) (hx₀ := hx₀) p) :
    Moves (coarseEntries D.lowerBlocks) (coarseEntries D.upperBlocks) :=
  D.moveData.moves

end InterfaceFactorizationData

end Factorization
end Hatcher.VanKampen
