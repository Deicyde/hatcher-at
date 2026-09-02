import Hatcher.Covering.BasepointChange
import Hatcher.Covering.DeckRealization

noncomputable section

namespace deck

universe u v

variable {E : Type u} {X : Type v} [TopologicalSpace E] [TopologicalSpace X]
  {p : E → X}

/-- Deck transformations commute with endpoint transport along paths. -/
theorem smul_monodromy (cov : IsCoveringMap p) (d : deck p)
    {x y : X} (g : Path.Homotopic.Quotient x y) (e : p ⁻¹' {x}) :
    d • (cov.monodromy g e).1 =
      (cov.monodromy g
        ⟨d • e.1, (deck.proj_smul d e.1).trans e.2⟩).1 := by
  obtain ⟨γ⟩ := g
  let Γ : C(unitInterval, E) :=
    ⟨fun t ↦ d • cov.liftPath γ e.1 (γ.source.trans e.2.symm) t,
      d.1.continuous.comp (cov.liftPath γ e.1 (γ.source.trans e.2.symm)).continuous⟩
  have hΓ : Γ = cov.liftPath γ (d • e.1)
      (γ.source.trans ((deck.proj_smul d e.1).trans e.2).symm) := by
    apply (cov.eq_liftPath_iff' _).2
    constructor
    · funext t
      exact (deck.proj_smul d _).trans
        (congrFun (cov.liftPath_lifts γ e.1 (γ.source.trans e.2.symm)) t)
    · exact congrArg (d • ·) (cov.liftPath_zero γ e.1 (γ.source.trans e.2.symm))
  exact DFunLike.congr_fun hΓ 1

/-- Deck transformations commute with monodromy permutations of a fiber. -/
theorem smul_monodromyPerm (cov : IsCoveringMap p) (d : deck p)
    {x : X} (g : FundamentalGroup X x) (e : p ⁻¹' {x}) :
    d • (cov.monodromyPerm x g e).1 =
      (cov.monodromyPerm x g
        ⟨d • e.1, (deck.proj_smul d e.1).trans e.2⟩).1 :=
  smul_monodromy cov d g e

end deck

namespace Hatcher.BasedConnectedCover

universe u v

variable {X : Type v} [TopologicalSpace X] {x₀ : X}

private def normalizerEndpoint
    (C : Hatcher.BasedConnectedCover.{u, v} X x₀)
    (g : Subgroup.normalizer
      (C.fundamentalGroupRange : Set (FundamentalGroup X x₀))) : C.proj ⁻¹' {x₀} :=
  C.isCoveringMap.monodromyPerm x₀ ((g : FundamentalGroup X x₀)⁻¹)
    ⟨C.basepoint, C.proj_basepoint⟩

private theorem fundamentalGroupRange_rebase_normalizerEndpoint
    [PathConnectedSpace X] [LocPathConnectedSpace X]
    (C : Hatcher.BasedConnectedCover.{u, v} X x₀)
    (g : Subgroup.normalizer
      (C.fundamentalGroupRange : Set (FundamentalGroup X x₀))) :
    C.fundamentalGroupRange =
      (C.rebase (normalizerEndpoint C g)).fundamentalGroupRange := by
  have hchange := Hatcher.Covering.range_mapOfEq_of_monodromy
    C.isCoveringMap ⟨C.basepoint, C.proj_basepoint⟩
      (normalizerEndpoint C g) ((g : FundamentalGroup X x₀)⁻¹) rfl
  have hnormal :
      C.fundamentalGroupRange.map
          (MulAut.conj ((g : FundamentalGroup X x₀)⁻¹)) =
        C.fundamentalGroupRange :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (g⁻¹).property
  exact (hchange.trans hnormal).symm

private def normalizerDeck
    [PathConnectedSpace X] [LocPathConnectedSpace X]
    (C : Hatcher.BasedConnectedCover.{u, v} X x₀)
    (g : Subgroup.normalizer
      (C.fundamentalGroupRange : Set (FundamentalGroup X x₀))) : deck C.proj :=
  Classical.choose <|
    (C.existsUnique_deck_apply_basepoint_iff_range_eq (normalizerEndpoint C g)).2
      (fundamentalGroupRange_rebase_normalizerEndpoint C g)

private theorem normalizerDeck_apply_basepoint
    [PathConnectedSpace X] [LocPathConnectedSpace X]
    (C : Hatcher.BasedConnectedCover.{u, v} X x₀)
    (g : Subgroup.normalizer
      (C.fundamentalGroupRange : Set (FundamentalGroup X x₀))) :
    normalizerDeck C g • C.basepoint = (normalizerEndpoint C g).1 :=
  (Classical.choose_spec <|
    (C.existsUnique_deck_apply_basepoint_iff_range_eq (normalizerEndpoint C g)).2
      (fundamentalGroupRange_rebase_normalizerEndpoint C g)).1

/-- The normalizer of a connected covering's image subgroup maps to its deck
transformation group. -/
def normalizerToDeck
    [PathConnectedSpace X] [LocPathConnectedSpace X]
    (C : Hatcher.BasedConnectedCover.{u, v} X x₀) :
    Subgroup.normalizer
        (C.fundamentalGroupRange : Set (FundamentalGroup X x₀)) →* deck C.proj where
  toFun := normalizerDeck C
  map_one' := by
    apply deck.ext_of_eq_at C.isCoveringMap (e := C.basepoint)
    rw [normalizerDeck_apply_basepoint]
    simp [normalizerEndpoint]
  map_mul' g h := by
    apply deck.ext_of_eq_at C.isCoveringMap (e := C.basepoint)
    rw [normalizerDeck_apply_basepoint, mul_smul, normalizerDeck_apply_basepoint]
    let e₀ : C.proj ⁻¹' {x₀} := ⟨C.basepoint, C.proj_basepoint⟩
    have hcomm := deck.smul_monodromyPerm C.isCoveringMap (normalizerDeck C g)
      ((h : FundamentalGroup X x₀)⁻¹) e₀
    change (C.isCoveringMap.monodromyPerm x₀
      (((g * h : _) : FundamentalGroup X x₀)⁻¹) e₀).1 =
      normalizerDeck C g •
        (C.isCoveringMap.monodromyPerm x₀
          ((h : FundamentalGroup X x₀)⁻¹) e₀).1
    rw [hcomm]
    have hstart :
        ⟨normalizerDeck C g • e₀.1,
          (deck.proj_smul (normalizerDeck C g) e₀.1).trans e₀.2⟩ =
        C.isCoveringMap.monodromyPerm x₀
          ((g : FundamentalGroup X x₀)⁻¹) e₀ := by
      apply Subtype.ext
      exact normalizerDeck_apply_basepoint C g
    rw [hstart]
    rw [Subgroup.coe_mul, mul_inv_rev, map_mul]
    rfl

/-- The normalizer map sends an element to the unique deck transformation
whose value at the chosen point is its inverse-monodromy endpoint. -/
@[simp]
theorem normalizerToDeck_smul_basepoint
    [PathConnectedSpace X] [LocPathConnectedSpace X]
    (C : Hatcher.BasedConnectedCover.{u, v} X x₀)
    (g : Subgroup.normalizer
      (C.fundamentalGroupRange : Set (FundamentalGroup X x₀))) :
    C.normalizerToDeck g • C.basepoint =
      (C.isCoveringMap.monodromyPerm x₀ ((g : FundamentalGroup X x₀)⁻¹)
        ⟨C.basepoint, C.proj_basepoint⟩).1 :=
  normalizerDeck_apply_basepoint C g

end Hatcher.BasedConnectedCover
