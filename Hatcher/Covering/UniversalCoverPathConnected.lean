import Hatcher.Covering.UniversalCoverBasis
import Mathlib.Topology.Order.T5
import Mathlib.Topology.Subpath

noncomputable section

open Set Topology TopologicalSpace
open scoped unitInterval

namespace Hatcher.UniversalCover

universe u

variable {X : Type u} [TopologicalSpace X] {x₀ x : X}

/-- The initial segment of a path, cast to start at its declared source. -/
def initialPath (γ : Path x₀ x) (t : I) : Path x₀ (γ t) :=
  (γ.subpath 0 t).cast γ.source.symm rfl

/-- The point of the path-class space represented by the initial segment of `γ` ending at `t`. -/
def initialSegment (γ : Path x₀ x) (t : I) : UniversalCover X x₀ :=
  ⟨γ t, Path.Homotopic.Quotient.mk (initialPath γ t)⟩

private def subpathIn (U : Set X) (γ : Path x₀ x) (t s : I)
    (ht : γ t ∈ U) (hs : γ s ∈ U) (hγ : Set.range (γ.subpath t s) ⊆ U) :
    Path (⟨γ t, ht⟩ : U) ⟨γ s, hs⟩ where
  toFun r := ⟨γ.subpath t s r, hγ (Set.mem_range_self r)⟩
  continuous_toFun := (γ.subpath t s).continuous.subtype_mk _
  source' := Subtype.ext (γ.subpath t s).source
  target' := Subtype.ext (γ.subpath t s).target

private theorem subpathIn_map (U : Set X) (γ : Path x₀ x) (t s : I)
    (ht : γ t ∈ U) (hs : γ s ∈ U) (hγ : Set.range (γ.subpath t s) ⊆ U) :
    (subpathIn U γ t s ht hs hγ).map continuous_subtype_val = γ.subpath t s := by
  ext r
  rfl

private theorem initialSegment_trans_subpath (U : Set X) (γ : Path x₀ x) (t s : I)
    (ht : γ t ∈ U) (hs : γ s ∈ U) (hγ : Set.range (γ.subpath t s) ⊆ U) :
    (initialSegment γ s).2 = (initialSegment γ t).2.trans
      ((Path.Homotopic.Quotient.mk (subpathIn U γ t s ht hs hγ)).map
        ⟨Subtype.val, continuous_subtype_val⟩) := by
  change Path.Homotopic.Quotient.mk (initialPath γ s) =
    (Path.Homotopic.Quotient.mk (initialPath γ t)).trans
      ((Path.Homotopic.Quotient.mk (subpathIn U γ t s ht hs hγ)).map
        ⟨Subtype.val, continuous_subtype_val⟩)
  rw [← Path.Homotopic.Quotient.mk_map, subpathIn_map,
    ← Path.Homotopic.Quotient.mk_trans]
  symm
  apply Quotient.sound
  let F := Path.Homotopy.subpathTransSubpath γ 0 t s
  refine ⟨F.pathCast γ.source.symm rfl |>.cast ?_ rfl⟩
  exact Path.cast_trans _ _ _ _ _

private theorem range_subpath_subset_of_mem_ordConnectedComponent
    (U : Set X) (γ : Path x₀ x) {t s : I}
    (hs : s ∈ Set.ordConnectedComponent (γ ⁻¹' U) t) :
    Set.range (γ.subpath t s) ⊆ U := by
  rw [Path.range_subpath]
  rintro _ ⟨r, hr, rfl⟩
  exact (Set.mem_ordConnectedComponent.mp hs) hr

/-- The family of initial path segments is continuous in Hatcher's basic-open topology. -/
theorem continuous_initialSegment [LocPathConnectedSpace X]
    [SemilocallySimplyConnectedSpace X] (γ : Path x₀ x) :
    Continuous (initialSegment γ) := by
  rw [(isTopologicalBasis_basicOpen (X := X) (x₀ := x₀)).continuous_iff]
  intro S hS
  obtain ⟨U, hU, y, hy, η, rfl⟩ := hS
  apply isOpen_iff_mem_nhds.mpr
  intro t ht
  let htU : γ t ∈ U := ht.choose
  have hpre : γ ⁻¹' U ∈ nhds t :=
    γ.continuous.continuousAt.preimage_mem_nhds (hU.1.mem_nhds htU)
  have hcomp : Set.ordConnectedComponent (γ ⁻¹' U) t ∈ nhds t :=
    Set.ordConnectedComponent_mem_nhds.mpr hpre
  refine Filter.mem_of_superset hcomp ?_
  intro s hs
  rw [basicOpen_eq_of_mem hy η htU ht]
  have hsPre : s ∈ γ ⁻¹' U :=
    Set.ordConnectedComponent_subset (s := γ ⁻¹' U) (x := t) hs
  have hsU : γ s ∈ U := hsPre
  let hγ := range_subpath_subset_of_mem_ordConnectedComponent U γ hs
  refine ⟨hsU, Path.Homotopic.Quotient.mk (subpathIn U γ t s htU hsU hγ), ?_⟩
  exact initialSegment_trans_subpath U γ t s htU hsU hγ

/-- The path in the path-class space obtained from the initial segments of `γ`. -/
def initialSegmentPath [LocPathConnectedSpace X]
    [SemilocallySimplyConnectedSpace X] (γ : Path x₀ x) :
    Path (basepoint (X := X) (x₀ := x₀))
      ⟨x, Path.Homotopic.Quotient.mk γ⟩ where
  toFun := initialSegment γ
  continuous_toFun := continuous_initialSegment γ
  source' := by
    apply Sigma.ext γ.source
    apply Path.Homotopic.hpath_hext
    intro t
    simp [initialPath, γ.source]
  target' := by
    apply Sigma.ext γ.target
    apply Path.Homotopic.hpath_hext
    intro t
    simp [initialPath]

private theorem joined_basepoint [LocPathConnectedSpace X]
    [SemilocallySimplyConnectedSpace X] (q : UniversalCover X x₀) :
    Joined (basepoint (X := X) (x₀ := x₀)) q := by
  rcases q with ⟨y, q⟩
  induction q using Path.Homotopic.Quotient.ind with
  | mk γ => exact ⟨initialSegmentPath γ⟩

/-- The universal-cover path-class space is path-connected. -/
instance pathConnectedSpace [PathConnectedSpace X] [LocPathConnectedSpace X]
    [SemilocallySimplyConnectedSpace X] :
    PathConnectedSpace (UniversalCover X x₀) where
  nonempty := ⟨basepoint (X := X) (x₀ := x₀)⟩
  joined q r := (joined_basepoint q).symm.trans (joined_basepoint r)


end Hatcher.UniversalCover
