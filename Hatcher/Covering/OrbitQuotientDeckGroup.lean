import Hatcher.Covering.CoveringSpaceAction

open Topology

namespace Hatcher.Covering

universe u v

variable {G : Type u} {Y : Type v} [Group G] [MulAction G Y]
  [TopologicalSpace Y] [ContinuousConstSMul G Y]

/-- The orbit covering of a covering-space action is normal. -/
theorem isNormal_orbitQuotient (h : Hatcher.IsCoveringSpaceAction G Y) :
    IsNormal (Quotient.mk <| MulAction.orbitRel G Y) := by
  let q : Y → Quotient (MulAction.orbitRel G Y) := Quotient.mk _
  let hq := h.isQuotientCoveringMap_orbitQuotient
  refine {
    isCoveringMap := hq.isCoveringMap
    surjective := hq.surjective
    isPretransitive := fun x ↦ ?_ }
  letI := deck.mulActionFiber q x
  letI := hq.mulActionFiber x
  have htrans := hq.mulActionFiber_isPretransitive x
  constructor
  intro e e'
  obtain ⟨g, hg⟩ := htrans.exists_smul_eq e e'
  refine ⟨actionToDeck G Y g, ?_⟩
  apply Subtype.ext
  exact congrArg Subtype.val hg

/-- For a path-connected covering-space action, the acting group is the full deck group. -/
noncomputable def actionEquivDeck (h : Hatcher.IsCoveringSpaceAction G Y)
    [PathConnectedSpace Y] :
    G ≃* deck (Quotient.mk <| MulAction.orbitRel G Y) := by
  let q : Y → Quotient (MulAction.orbitRel G Y) := Quotient.mk _
  let hq := h.isQuotientCoveringMap_orbitQuotient
  apply MulEquiv.ofBijective (actionToDeck G Y)
  constructor
  · intro g g' hgg'
    let y : Y := Classical.choice (inferInstance : Nonempty Y)
    have hy := congrArg (fun d : deck q ↦ d • y) hgg'
    haveI := hq.isCancelSMul
    exact IsCancelSMul.right_cancel g g' y hy
  · intro d
    let y : Y := Classical.choice (inferInstance : Nonempty Y)
    obtain ⟨g, hg⟩ := hq.apply_eq_iff_mem_orbit.mp (deck.proj_smul d y)
    refine ⟨g, ?_⟩
    apply deck.ext_of_eq_at hq.isCoveringMap (e := y)
    exact hg

end Hatcher.Covering

