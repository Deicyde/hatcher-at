import Hatcher.Covering.ConnectedCover
import Hatcher.Covering.LiftingCriterion
import Hatcher.Covering.LocalPathConnected

noncomputable section

namespace Hatcher.BasedConnectedCover

universe u v w

variable {X : Type v} [TopologicalSpace X] {x₀ : X}

private theorem mapOfEq_trans {A : Type u} [TopologicalSpace A]
    (f : C(A, X)) {a : A} {x y : X} (h : f a = x) (k : x = y) :
    FundamentalGroup.mapOfEq f (h.trans k) =
      ((CategoryTheory.eqToIso (congrArg FundamentalGroupoid.mk k)).conj.toMonoidHom).comp
        (FundamentalGroup.mapOfEq f h) := by
  ext γ
  change (CategoryTheory.eqToIso
      (congrArg FundamentalGroupoid.mk (h.trans k))).conj
        ((FundamentalGroup.map f a) γ) =
    (CategoryTheory.eqToIso (congrArg FundamentalGroupoid.mk k)).conj
      ((CategoryTheory.eqToIso (congrArg FundamentalGroupoid.mk h)).conj
        ((FundamentalGroup.map f a) γ))
  rw [← CategoryTheory.Iso.trans_conj, CategoryTheory.eqToIso_trans]

/-- The projection of a pointed connected cover as a continuous map. -/
def projMap (C : Hatcher.BasedConnectedCover.{u, v} X x₀) : C(C.E, X) :=
  ⟨C.proj, C.isCoveringMap.continuous⟩

/-- The image subgroup of a pointed connected cover. -/
def fundamentalGroupRange (C : Hatcher.BasedConnectedCover.{u, v} X x₀) :
    Subgroup (FundamentalGroup X x₀) :=
  (FundamentalGroup.mapOfEq C.projMap C.proj_basepoint).range

/-- A pointed covering isomorphism gives inclusion of image subgroups. -/
theorem fundamentalGroupRange_le_of_iso
    {C : Hatcher.BasedConnectedCover.{u, v} X x₀}
    {D : Hatcher.BasedConnectedCover.{w, v} X x₀} (e : C.Iso D) :
    C.fundamentalGroupRange ≤ D.fundamentalGroupRange := by
  rintro _ ⟨δ, rfl⟩
  obtain ⟨δ, rfl⟩ := Path.Homotopic.Quotient.mk_surjective δ.toPath
  let η : Path D.basepoint D.basepoint :=
    (δ.map e.toHomeomorph.continuous).cast e.map_basepoint.symm e.map_basepoint.symm
  refine ⟨FundamentalGroup.fromPath (.mk η), ?_⟩
  rw [FundamentalGroup.mapOfEq_apply, FundamentalGroup.mapOfEq_apply]
  apply congrArg FundamentalGroup.fromPath
  apply congrArg Path.Homotopic.Quotient.mk
  ext t
  exact e.proj_apply (δ t)

private theorem map_range_le_mapOfEq_of_fundamentalGroupRange_le
    {C : Hatcher.BasedConnectedCover.{u, v} X x₀}
    {D : Hatcher.BasedConnectedCover.{w, v} X x₀}
    (h : C.fundamentalGroupRange ≤ D.fundamentalGroupRange) :
    (FundamentalGroup.map C.projMap C.basepoint).range ≤
      (FundamentalGroup.mapOfEq D.projMap
        (D.proj_basepoint.trans C.proj_basepoint.symm)).range := by
  rintro _ ⟨δ, rfl⟩
  let τ : FundamentalGroup X (C.proj C.basepoint) ≃* FundamentalGroup X x₀ :=
    (CategoryTheory.eqToIso
      (congrArg FundamentalGroupoid.mk C.proj_basepoint)).conj
  have hmem : τ ((FundamentalGroup.map C.projMap C.basepoint) δ) ∈
      C.fundamentalGroupRange := by
    refine ⟨δ, ?_⟩
    rfl
  obtain ⟨ε, hε⟩ := h hmem
  refine ⟨ε, ?_⟩
  apply τ.injective
  let he : D.proj D.basepoint = C.proj C.basepoint :=
    D.proj_basepoint.trans C.proj_basepoint.symm
  have htrans := DFunLike.congr_fun
    (mapOfEq_trans D.projMap he C.proj_basepoint) ε
  calc
    τ ((FundamentalGroup.mapOfEq D.projMap he) ε) =
        (FundamentalGroup.mapOfEq D.projMap (he.trans C.proj_basepoint)) ε :=
      htrans.symm
    _ = (FundamentalGroup.mapOfEq D.projMap D.proj_basepoint) ε := by
      congr
    _ = τ ((FundamentalGroup.map C.projMap C.basepoint) δ) := hε

/-- Two pointed path-connected covers are isomorphic exactly when their image
subgroups agree. This is Hatcher, Proposition 1.37. -/
theorem nonempty_iso_iff_range_eq
    [PathConnectedSpace X] [LocPathConnectedSpace X]
    (C : Hatcher.BasedConnectedCover.{u, v} X x₀)
    (D : Hatcher.BasedConnectedCover.{w, v} X x₀) :
    Nonempty (C.Iso D) ↔ C.fundamentalGroupRange = D.fundamentalGroupRange := by
  constructor
  · rintro ⟨e⟩
    exact le_antisymm (fundamentalGroupRange_le_of_iso e)
      (fundamentalGroupRange_le_of_iso e.symm)
  · intro h
    letI : LocPathConnectedSpace C.E :=
      Hatcher.Covering.locPathConnectedSpace_total C.isCoveringMap
    letI : LocPathConnectedSpace D.E :=
      Hatcher.Covering.locPathConnectedSpace_total D.isCoveringMap
    let hCD : D.proj D.basepoint = C.proj C.basepoint :=
      D.proj_basepoint.trans C.proj_basepoint.symm
    let hDC : C.proj C.basepoint = D.proj D.basepoint := hCD.symm
    obtain ⟨F, hF₀, hF⟩ :=
      (Hatcher.Covering.exists_lift_iff_range_le D.isCoveringMap C.projMap
        C.basepoint D.basepoint hCD).2
        (map_range_le_mapOfEq_of_fundamentalGroupRange_le h.le)
    obtain ⟨G, hG₀, hG⟩ :=
      (Hatcher.Covering.exists_lift_iff_range_le C.isCoveringMap D.projMap
        D.basepoint C.basepoint hDC).2
        (map_range_le_mapOfEq_of_fundamentalGroupRange_le h.ge)
    have hGF : G ∘ F = id := by
      apply C.isCoveringMap.eq_of_comp_eq (G.comp F).continuous
        (ContinuousMap.id C.E).continuous
        (by
          funext x
          exact (congrFun hG (F x)).trans (congrFun hF x)) C.basepoint
      simp only [ContinuousMap.comp_apply, ContinuousMap.id_apply, hF₀, hG₀]
    have hFG : F ∘ G = id := by
      apply D.isCoveringMap.eq_of_comp_eq (F.comp G).continuous
        (ContinuousMap.id D.E).continuous
        (by
          funext x
          exact (congrFun hF (G x)).trans (congrFun hG x)) D.basepoint
      simp only [ContinuousMap.comp_apply, ContinuousMap.id_apply, hG₀, hF₀]
    let e : C.E ≃ₜ D.E := {
      toEquiv := {
        toFun := F
        invFun := G
        left_inv := fun x ↦ congrFun hGF x
        right_inv := fun x ↦ congrFun hFG x }
      continuous_toFun := F.continuous
      continuous_invFun := G.continuous }
    exact ⟨{
      toHomeomorph := e
      proj_comp := hF
      map_basepoint := hF₀ }⟩

end Hatcher.BasedConnectedCover
