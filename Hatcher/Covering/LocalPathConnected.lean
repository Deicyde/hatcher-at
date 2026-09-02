/-
Hatcher, *Algebraic Topology*, §1.3 (page 63).
-/
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Connected.LocPathConnected

open Filter Function Set Topology

namespace Hatcher.Covering

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {p : E → X}

/-- Local path-connectedness ascends from the base of a covering map to its
total space. -/
theorem locPathConnectedSpace_total (hp : IsCoveringMap p)
    [LocPathConnectedSpace X] : LocPathConnectedSpace E := by
  refine ⟨fun x ↦ ?_⟩
  obtain ⟨e, hx, _⟩ := hp.isLocalHomeomorph x
  let x' : e.source := ⟨x, hx⟩
  letI : LocPathConnectedSpace e.source :=
    e.isOpenEmbedding_restrict.locPathConnectedSpace
  have hb := (path_connected_basis x').map ((↑) : e.source → E)
  rw [e.open_source.isOpenEmbedding_subtypeVal.map_nhds_eq x'] at hb
  refine hb.to_hasBasis ?_ ?_
  · intro s hs
    exact ⟨Subtype.val '' s,
      ⟨hb.mem_of_mem hs, hs.2.image continuous_subtype_val⟩, subset_rfl⟩
  · intro t ht
    exact hb.mem_iff.mp ht.1

end Hatcher.Covering
