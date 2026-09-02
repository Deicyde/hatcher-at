import Hatcher.Covering.Deck
import Hatcher.Covering.Rigidity

noncomputable section

namespace deck

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {p : E → X}

/-- Two deck transformations of a covering with preconnected total space are
equal if they agree at one point. -/
theorem ext_of_eq_at (cov : IsCoveringMap p) [PreconnectedSpace E]
    {f g : deck p} {e : E} (h : f • e = g • e) : f = g := by
  apply Subtype.ext
  apply Homeomorph.ext
  intro x
  exact congrFun (cov.eq_of_comp_eq f.1.continuous g.1.continuous
    ((deck.comp_eq f).trans (deck.comp_eq g).symm) e h) x

end deck

namespace Hatcher.BasedConnectedCover

universe u v

variable {X : Type v} [TopologicalSpace X] {x₀ : X}

/-- Change the chosen point of a pointed connected cover without changing its
total space or projection. -/
def rebase (C : Hatcher.BasedConnectedCover.{u, v} X x₀) (e : C.proj ⁻¹' {x₀}) :
    Hatcher.BasedConnectedCover.{u, v} X x₀ where
  E := C.E
  topology := C.topology
  proj := C.proj
  isCoveringMap := C.isCoveringMap
  basepoint := e.1
  proj_basepoint := e.2
  pathConnectedSpace := C.pathConnectedSpace

/-- A fiber point is the image of the chosen point under a unique deck
transformation exactly when rebasing there preserves the image subgroup. -/
theorem existsUnique_deck_apply_basepoint_iff_range_eq
    [PathConnectedSpace X] [LocPathConnectedSpace X]
    (C : Hatcher.BasedConnectedCover.{u, v} X x₀) (e₁ : C.proj ⁻¹' {x₀}) :
    (∃! h : deck C.proj, h • C.basepoint = e₁.1) ↔
      C.fundamentalGroupRange = (C.rebase e₁).fundamentalGroupRange := by
  constructor
  · rintro ⟨h, hh, _⟩
    apply (nonempty_iso_iff_range_eq C (C.rebase e₁)).mp
    exact ⟨{
      toHomeomorph := h.1
      proj_comp := deck.comp_eq h
      map_basepoint := hh }⟩
  · intro h
    obtain ⟨e⟩ := (nonempty_iso_iff_range_eq C (C.rebase e₁)).mpr h
    let d : deck C.proj := ⟨e.toHomeomorph, e.proj_comp⟩
    refine ⟨d, e.map_basepoint, ?_⟩
    intro g hg
    apply deck.ext_of_eq_at C.isCoveringMap
    exact hg.trans e.map_basepoint.symm

end Hatcher.BasedConnectedCover
