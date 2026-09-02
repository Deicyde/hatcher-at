import Hatcher.Covering.Monodromy
import Mathlib.GroupTheory.GroupAction.Basic

noncomputable section

namespace Hatcher.Covering

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {p : E → X}

/-- The fundamental-group class obtained by projecting a path between two
points in the same covering fiber. -/
def projectedPathClass (cov : IsCoveringMap p) {x : X}
    (e₀ e₁ : p ⁻¹' {x}) (α : Path e₀.1 e₁.1) : FundamentalGroup X x :=
  FundamentalGroup.fromPath <| Path.Homotopic.Quotient.mk <|
    (α.map cov.continuous).cast
      (Set.mem_singleton_iff.mp e₀.property).symm
      (Set.mem_singleton_iff.mp e₁.property).symm

/-- The projected class of a path in the total space transports its starting
point to its endpoint under monodromy. -/
theorem monodromy_projectedPathClass (cov : IsCoveringMap p) {x : X}
    (e₀ e₁ : p ⁻¹' {x}) (α : Path e₀.1 e₁.1) :
    cov.monodromyPerm x (projectedPathClass cov e₀ e₁ α) e₀ = e₁ := by
  apply Subtype.ext
  let β : Path x x := (α.map cov.continuous).cast
    (Set.mem_singleton_iff.mp e₀.property).symm
    (Set.mem_singleton_iff.mp e₁.property).symm
  let hstart : β 0 = p e₀.1 :=
    β.source.trans (Set.mem_singleton_iff.mp e₀.property).symm
  change cov.liftPath β e₀.1 hstart 1 = e₁.1
  have hlift : α.toContinuousMap = cov.liftPath β e₀.1 hstart := by
    apply (cov.eq_liftPath_iff' (γ := β) (e := e₀.1) (γ_0 := hstart)).2
    constructor
    · ext t
      rfl
    · exact α.source
  exact (DFunLike.congr_fun hlift 1).symm.trans α.target

/-- The image subgroup based at a point of the fiber is its monodromy
stabilizer. -/
theorem range_mapOfEq_eq_stabilizer
    (cov : IsCoveringMap p) {x : X} (e : p ⁻¹' {x}) :
    (FundamentalGroup.mapOfEq ⟨p, cov.continuous⟩
      (Set.mem_singleton_iff.mp e.property)).range =
      @MulAction.stabilizer (FundamentalGroup X x) _ _
        (cov.fundamentalGroupMulAction x) e := by
  rcases e with ⟨e, he⟩
  have he' : p e = x := Set.mem_singleton_iff.mp he
  subst x
  letI := cov.fundamentalGroupMulAction (p e)
  have hmap :
      FundamentalGroup.mapOfEq ⟨p, cov.continuous⟩ rfl =
        FundamentalGroup.map ⟨p, cov.continuous⟩ e := by
    ext δ
    change (CategoryTheory.Iso.refl _).conj
        ((FundamentalGroup.map ⟨p, cov.continuous⟩ e) δ) = _
    rw [CategoryTheory.Iso.refl_conj]
  rw [hmap]
  ext γ
  rw [mem_range_map_iff_monodromy_fixed cov e,
    MulAction.mem_stabilizer_iff]
  rfl

/-- If monodromy carries one fiber point to another, their image subgroups are
conjugate by the transporting loop class. -/
theorem range_mapOfEq_of_monodromy
    (cov : IsCoveringMap p) {x : X} (e₀ e₁ : p ⁻¹' {x})
    (g : FundamentalGroup X x) (hg : cov.monodromyPerm x g e₀ = e₁) :
    (FundamentalGroup.mapOfEq ⟨p, cov.continuous⟩
      (Set.mem_singleton_iff.mp e₁.property)).range =
      (FundamentalGroup.mapOfEq ⟨p, cov.continuous⟩
        (Set.mem_singleton_iff.mp e₀.property)).range.map
        (MulAut.conj g) := by
  letI := cov.fundamentalGroupMulAction x
  have hb : e₁ = g • e₀ := hg.symm
  calc
    (FundamentalGroup.mapOfEq ⟨p, cov.continuous⟩
        (Set.mem_singleton_iff.mp e₁.property)).range =
        MulAction.stabilizer (FundamentalGroup X x) e₁ :=
      range_mapOfEq_eq_stabilizer cov e₁
    _ = MulAction.stabilizer (FundamentalGroup X x) (g • e₀) := by rw [hb]
    _ = (MulAction.stabilizer (FundamentalGroup X x) e₀).map
        (MulAut.conj g).toMonoidHom :=
      MulAction.stabilizer_smul_eq_stabilizer_map_conj g e₀
    _ = (FundamentalGroup.mapOfEq ⟨p, cov.continuous⟩
        (Set.mem_singleton_iff.mp e₀.property)).range.map
        (MulAut.conj g).toMonoidHom := by
      rw [range_mapOfEq_eq_stabilizer cov e₀]

/-- Changing the lifted basepoint along a path conjugates the covering
subgroup. The multiplication convention makes this `g H g⁻¹` in Lean. -/
theorem range_mapOfEq_basepointChange
    (cov : IsCoveringMap p) {x : X} (e₀ e₁ : p ⁻¹' {x})
    (α : Path e₀.1 e₁.1) :
    (FundamentalGroup.mapOfEq ⟨p, cov.continuous⟩
      (Set.mem_singleton_iff.mp e₁.property)).range =
      (FundamentalGroup.mapOfEq ⟨p, cov.continuous⟩
        (Set.mem_singleton_iff.mp e₀.property)).range.map
        (MulAut.conj (projectedPathClass cov e₀ e₁ α)) :=
  range_mapOfEq_of_monodromy cov e₀ e₁
    (projectedPathClass cov e₀ e₁ α)
    (monodromy_projectedPathClass cov e₀ e₁ α)

/-- Every conjugate of the covering subgroup is realized by changing the
chosen point in the fiber. -/
theorem exists_basepoint_range_eq_map_conj
    (cov : IsCoveringMap p) {x : X} (e₀ : p ⁻¹' {x})
    (g : FundamentalGroup X x) :
    ∃ e₁ : p ⁻¹' {x},
      (FundamentalGroup.mapOfEq ⟨p, cov.continuous⟩
        (Set.mem_singleton_iff.mp e₁.property)).range =
        (FundamentalGroup.mapOfEq ⟨p, cov.continuous⟩
          (Set.mem_singleton_iff.mp e₀.property)).range.map
          (MulAut.conj g) := by
  let e₁ := cov.monodromyPerm x g e₀
  exact ⟨e₁, range_mapOfEq_of_monodromy cov e₀ e₁ g rfl⟩

end Hatcher.Covering
