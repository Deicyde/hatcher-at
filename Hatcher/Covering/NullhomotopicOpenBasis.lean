import Hatcher.Covering.SemilocallySimplyConnected
import Mathlib.Topology.Bases
import Mathlib.Topology.Connected.LocPathConnected

noncomputable section

open CategoryTheory Set Topology TopologicalSpace

namespace Hatcher

variable {X : Type*} [TopologicalSpace X]

private theorem trivial_fundamentalGroupMap_of_subset
    {U V : Set X} (hUV : U ⊆ V) {x : X} (hx : x ∈ U)
    (htrivial : (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(V, X)) (⟨x, hUV hx⟩ : V)).range = ⊥) :
    (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)) (⟨x, hx⟩ : U)).range = ⊥ := by
  rw [MonoidHom.range_eq_bot_iff] at htrivial ⊢
  let i : C(U, V) := ⟨fun y ↦ ⟨y.1, hUV y.2⟩, continuous_subtype_val.subtype_mk _⟩
  ext g
  have hg := DFunLike.congr_fun htrivial (FundamentalGroup.map i ⟨x, hx⟩ g)
  obtain ⟨p⟩ := g
  exact hg

/-- The path-connected open sets whose inclusions kill fundamental groups form
a basis in a locally path-connected, semilocally simply connected space. -/
theorem isTopologicalBasis_nullhomotopicOpens
    {X : Type*} [TopologicalSpace X] [LocPathConnectedSpace X]
    [SemilocallySimplyConnectedSpace X] :
    IsTopologicalBasis {U : Set X | IsNullhomotopicOpen U} := by
  apply isTopologicalBasis_of_isOpen_of_nhds
  · intro U hU
    exact hU.1
  · intro x O hxO hO
    obtain ⟨V, hxV, hVopen, hVtrivial⟩ :=
      SemilocallySimplyConnectedSpace.exists_open_neighborhood x
    let W : Set X := pathComponentIn (V ∩ O) x
    have hxVO : x ∈ V ∩ O := ⟨hxV, hxO⟩
    have hxW : x ∈ W := mem_pathComponentIn_self hxVO
    have hWopen : IsOpen W := (hVopen.inter hO).pathComponentIn x
    have hWpath : IsPathConnected W := isPathConnected_pathComponentIn hxVO
    have hWV : W ⊆ V := pathComponentIn_subset.trans inter_subset_left
    have hWO : W ⊆ O := pathComponentIn_subset.trans inter_subset_right
    have hWtrivial :
        (FundamentalGroup.map
          (⟨Subtype.val, continuous_subtype_val⟩ : C(W, X)) (⟨x, hxW⟩ : W)).range = ⊥ :=
      trivial_fundamentalGroupMap_of_subset hWV hxW hVtrivial
    refine ⟨W, ?_, hxW, hWO⟩
    refine ⟨hWopen, hWpath, ?_⟩
    intro y
    exact trivial_fundamentalGroupMap_of_isPathConnected hWpath hxW y.2 hWtrivial

end Hatcher
