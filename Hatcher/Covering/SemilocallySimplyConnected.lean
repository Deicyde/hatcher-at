import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.Topology.Connected.PathConnected

noncomputable section

open CategoryTheory Set

namespace Hatcher

variable {X : Type*} [TopologicalSpace X]

/-- A space is semilocally simply connected if each point has an open
neighborhood whose inclusion induces the trivial map on fundamental groups. -/
class SemilocallySimplyConnectedSpace (X : Type*) [TopologicalSpace X] : Prop where
  exists_open_neighborhood : ∀ x : X, ∃ (U : Set X) (hx : x ∈ U), IsOpen U ∧
    (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)) (⟨x, hx⟩ : U)).range = ⊥

/-- An open, path-connected set whose inclusion induces the trivial map on
fundamental groups at every basepoint. -/
def IsNullhomotopicOpen (U : Set X) : Prop :=
  IsOpen U ∧ IsPathConnected U ∧
    ∀ x : U,
      (FundamentalGroup.map
        (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)) x).range = ⊥

private theorem map_fundamentalGroupMulEquivOfPath
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (f : C(A, B)) {x y : A} (p : Path x y) (g : FundamentalGroup A x) :
    FundamentalGroup.map f y (FundamentalGroup.fundamentalGroupMulEquivOfPath p g) =
      FundamentalGroup.fundamentalGroupMulEquivOfPath (p.map f.continuous)
        (FundamentalGroup.map f x g) := by
  exact (FundamentalGroupoid.map f).map_conj
    ((Groupoid.isoEquivHom _ _).symm ⟦p⟧) g

/-- Triviality of the inclusion-induced fundamental-group map is independent
of the basepoint inside a path-connected subspace. -/
theorem trivial_fundamentalGroupMap_of_isPathConnected
    {U : Set X} (hU : IsPathConnected U) {x y : X} (hx : x ∈ U) (hy : y ∈ U)
    (htrivial : (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)) (⟨x, hx⟩ : U)).range = ⊥) :
    (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)) (⟨y, hy⟩ : U)).range = ⊥ := by
  letI : PathConnectedSpace U := isPathConnected_iff_pathConnectedSpace.mp hU
  let p : Path (⟨x, hx⟩ : U) ⟨y, hy⟩ := PathConnectedSpace.somePath _ _
  rw [MonoidHom.range_eq_bot_iff] at htrivial ⊢
  ext g
  obtain ⟨g, rfl⟩ := (FundamentalGroup.fundamentalGroupMulEquivOfPath p).surjective g
  rw [map_fundamentalGroupMulEquivOfPath, htrivial]
  exact map_one (FundamentalGroup.fundamentalGroupMulEquivOfPath
    (p.map (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)).continuous))

end Hatcher
