import Hatcher.Covering.DeckRealization
import Mathlib.Topology.Covering.Quotient

open Topology

namespace Hatcher

universe u v

/-- A group action is a covering-space action if every point has a neighborhood disjoint
from each of its nontrivial translates. -/
def IsCoveringSpaceAction (G : Type u) (Y : Type v) [Group G]
    [MulAction G Y] [TopologicalSpace Y] : Prop :=
  ∀ y : Y, ∃ U ∈ nhds y, ∀ g : G, ((g • ·) '' U ∩ U).Nonempty → g = 1

/-- The local disjointness condition is equivalent to pairwise disjointness of all translates. -/
theorem isCoveringSpaceAction_iff_pairwiseDisjointTranslates
    (G : Type u) (Y : Type v) [Group G] [MulAction G Y] [TopologicalSpace Y] :
    IsCoveringSpaceAction G Y ↔
      ∀ y : Y, ∃ U ∈ nhds y, ∀ g h : G, g ≠ h →
        Disjoint ((g • ·) '' U) ((h • ·) '' U) := by
  constructor
  · intro hact y
    obtain ⟨U, hyU, hU⟩ := hact y
    refine ⟨U, hyU, fun g h hne ↦ ?_⟩
    rw [Set.disjoint_left]
    rintro z ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
    have hinter : ((((h⁻¹ * g) • ·) '' U) ∩ U).Nonempty := by
      refine ⟨b, ⟨⟨a, ha, ?_⟩, hb⟩⟩
      simpa [mul_smul] using (congrArg (h⁻¹ • ·) hab).symm
    apply hne
    have hone := hU (h⁻¹ * g) hinter
    simpa using congrArg (h * ·) hone
  · intro hpair y
    obtain ⟨U, hyU, hU⟩ := hpair y
    refine ⟨U, hyU, fun g hg ↦ ?_⟩
    by_contra hne
    obtain ⟨z, hzg, hzU⟩ := hg
    exact (Set.disjoint_left.mp (hU g 1 hne)) hzg ⟨z, hzU, one_smul G z⟩

namespace IsCoveringSpaceAction

variable {G : Type u} {Y : Type v} [Group G] [MulAction G Y]
  [TopologicalSpace Y] [ContinuousConstSMul G Y]

/-- The orbit projection of a covering-space action is a quotient covering map. -/
theorem isQuotientCoveringMap_orbitQuotient (h : IsCoveringSpaceAction G Y) :
    IsQuotientCoveringMap (Quotient.mk <| MulAction.orbitRel G Y) G where
  __ := MulAction.isOpenQuotientMap_quotientMk.isQuotientMap
  continuous_const_smul := continuous_const_smul
  apply_eq_iff_mem_orbit := Quotient.eq''
  disjoint := h

end IsCoveringSpaceAction

namespace Covering

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {p : E → X}

/-- The deck action of a covering with path-connected total space is a covering-space action. -/
theorem deck_isCoveringSpaceAction (cov : IsCoveringMap p) [PathConnectedSpace E] :
    IsCoveringSpaceAction (deck p) E := by
  intro e
  obtain ⟨U, hUopen, heU, hinj⟩ := cov.isLocalHomeomorph.isLocallyInjective e
  refine ⟨U, hUopen.mem_nhds heU, fun d hd ↦ ?_⟩
  obtain ⟨z, ⟨a, ha, rfl⟩, hda⟩ := hd
  have hfix : d • a = a := hinj hda ha (deck.proj_smul d a)
  apply deck.ext_of_eq_at cov (e := a)
  simpa using hfix

/-- The original action induces deck transformations of its orbit projection. -/
def actionToDeck (G : Type u) (Y : Type v) [Group G] [MulAction G Y]
    [TopologicalSpace Y] [ContinuousConstSMul G Y] :
    G →* deck (Quotient.mk <| MulAction.orbitRel G Y) where
  toFun g := ⟨Homeomorph.smul g, by
    funext y
    exact Quotient.sound ⟨g, rfl⟩⟩
  map_one' := by
    apply Subtype.ext
    ext y
    exact one_smul G y
  map_mul' g h := by
    apply Subtype.ext
    ext y
    exact mul_smul g h y

end Covering

end Hatcher
