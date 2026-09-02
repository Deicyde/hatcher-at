import Hatcher.Covering.DeckGroupCalculation
import Hatcher.Covering.OrbitQuotientDeckGroup
import Mathlib.GroupTheory.QuotientGroup.Basic

open Topology

namespace Hatcher.Covering

universe u v

variable {G : Type u} {Y : Type v} [Group G] [MulAction G Y]
  [TopologicalSpace Y] [ContinuousConstSMul G Y]

private theorem fundamentalGroup_mapOfEq_rfl {A B : Type*}
    [TopologicalSpace A] [TopologicalSpace B] (f : C(A, B)) (a : A) :
    FundamentalGroup.mapOfEq f rfl = FundamentalGroup.map f a := by
  ext δ
  change (CategoryTheory.Iso.refl _).conj ((FundamentalGroup.map f a) δ) = _
  rw [CategoryTheory.Iso.refl_conj]

/-- For a path-connected, locally path-connected covering-space action, the fundamental
group of the orbit space modulo the image of the total-space fundamental group is the
acting group. -/
noncomputable def orbitQuotientFundamentalGroupEquiv
    (h : Hatcher.IsCoveringSpaceAction G Y) [PathConnectedSpace Y]
    [LocPathConnectedSpace Y] (y₀ : Y) :
    let q : Y → Quotient (MulAction.orbitRel G Y) := Quotient.mk _
    let hq := h.isQuotientCoveringMap_orbitQuotient
    let C : Hatcher.BasedConnectedCover
        (Quotient (MulAction.orbitRel G Y)) (q y₀) := {
      E := Y
      topology := inferInstance
      proj := q
      isCoveringMap := hq.isCoveringMap
      basepoint := y₀
      proj_basepoint := rfl
      pathConnectedSpace := inferInstance }
    let H := (FundamentalGroup.map ⟨q, hq.isCoveringMap.continuous⟩ y₀).range
    letI : H.Normal := by
      have hC := C.isNormal_iff_range_normal.mp (isNormal_orbitQuotient h)
      change (FundamentalGroup.mapOfEq
        ⟨q, hq.isCoveringMap.continuous⟩ rfl).range.Normal at hC
      simpa only [fundamentalGroup_mapOfEq_rfl] using hC
    FundamentalGroup (Quotient (MulAction.orbitRel G Y)) (q y₀) ⧸ H ≃* G := by
  dsimp only
  let q : Y → Quotient (MulAction.orbitRel G Y) := Quotient.mk _
  let hq := h.isQuotientCoveringMap_orbitQuotient
  let C : Hatcher.BasedConnectedCover
      (Quotient (MulAction.orbitRel G Y)) (q y₀) := {
    E := Y
    topology := inferInstance
    proj := q
    isCoveringMap := hq.isCoveringMap
    basepoint := y₀
    proj_basepoint := rfl
    pathConnectedSpace := inferInstance }
  let H := (FundamentalGroup.map ⟨q, hq.isCoveringMap.continuous⟩ y₀).range
  have hRange : C.fundamentalGroupRange = H := by
    change (FundamentalGroup.mapOfEq
      ⟨q, hq.isCoveringMap.continuous⟩ rfl).range = H
    rw [fundamentalGroup_mapOfEq_rfl]
  let hnormal := isNormal_orbitQuotient h
  letI : C.fundamentalGroupRange.Normal :=
    C.isNormal_iff_range_normal.mp hnormal
  letI : H.Normal := hRange ▸ (inferInstance : C.fundamentalGroupRange.Normal)
  exact (QuotientGroup.quotientMulEquivOfEq hRange.symm).trans
    ((C.fundamentalGroupQuotientEquivDeck hnormal).trans
      (actionEquivDeck h).symm)

end Hatcher.Covering

