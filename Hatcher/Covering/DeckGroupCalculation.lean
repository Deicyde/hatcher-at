import Hatcher.Covering.NormalizerToDeckExactness
import Mathlib.GroupTheory.QuotientGroup.Basic

noncomputable section

namespace Hatcher.BasedConnectedCover

universe u v

variable {X : Type v} [TopologicalSpace X] {x₀ : X}

/-- The deck group of a connected covering is the quotient of the normalizer
of its image subgroup by that subgroup. -/
noncomputable def normalizerQuotientEquivDeck
    [PathConnectedSpace X] [LocPathConnectedSpace X]
    (C : Hatcher.BasedConnectedCover.{u, v} X x₀) :
    Subgroup.normalizer
          (C.fundamentalGroupRange : Set (FundamentalGroup X x₀)) ⧸
        C.fundamentalGroupRange.subgroupOf
          (Subgroup.normalizer
            (C.fundamentalGroupRange : Set (FundamentalGroup X x₀))) ≃*
      deck C.proj :=
  let h := C.normalizerToDeck_ker_and_surjective
  (QuotientGroup.quotientMulEquivOfEq h.1.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective C.normalizerToDeck h.2)

/-- The projection of a pointed connected covering over a path-connected base
is surjective. -/
theorem proj_surjective [PathConnectedSpace X]
    (C : Hatcher.BasedConnectedCover.{u, v} X x₀) :
    Function.Surjective C.proj := by
  intro x
  let γ : Path x₀ x := PathConnectedSpace.somePath x₀ x
  let Γ := C.isCoveringMap.liftPath γ C.basepoint
    (γ.source.trans C.proj_basepoint.symm)
  refine ⟨Γ 1, ?_⟩
  exact (congrFun (C.isCoveringMap.liftPath_lifts γ C.basepoint
    (γ.source.trans C.proj_basepoint.symm)) 1).trans γ.target

private theorem deck_isPretransitive_baseFiber
    [PathConnectedSpace X] [LocPathConnectedSpace X]
    (C : Hatcher.BasedConnectedCover.{u, v} X x₀)
    (hH : C.fundamentalGroupRange.Normal) :
    letI := deck.mulActionFiber C.proj x₀
    MulAction.IsPretransitive (deck C.proj) (C.proj ⁻¹' {x₀}) := by
  letI := deck.mulActionFiber C.proj x₀
  let e₀ : C.proj ⁻¹' {x₀} := ⟨C.basepoint, C.proj_basepoint⟩
  apply MulAction.IsPretransitive.of_orbit (x₀ := e₀)
  intro e
  let α : Path C.basepoint e.1 :=
    PathConnectedSpace.somePath C.basepoint e.1
  let g : FundamentalGroup X x₀ :=
    Hatcher.Covering.projectedPathClass C.isCoveringMap e₀ e α
  have hg : C.isCoveringMap.monodromyPerm x₀ g e₀ = e :=
    Hatcher.Covering.monodromy_projectedPathClass C.isCoveringMap e₀ e α
  have hmem : g⁻¹ ∈ Subgroup.normalizer
      (C.fundamentalGroupRange : Set (FundamentalGroup X x₀)) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hH]
    exact Subgroup.mem_top g⁻¹
  let n : Subgroup.normalizer
      (C.fundamentalGroupRange : Set (FundamentalGroup X x₀)) := ⟨g⁻¹, hmem⟩
  refine ⟨C.normalizerToDeck n, ?_⟩
  apply Subtype.ext
  change C.normalizerToDeck n • C.basepoint = e.1
  rw [C.normalizerToDeck_smul_basepoint]
  simpa [n, g, e₀] using congrArg Subtype.val hg

private theorem deck_isPretransitive_fiber
    [PathConnectedSpace X] [LocPathConnectedSpace X]
    (C : Hatcher.BasedConnectedCover.{u, v} X x₀)
    (hH : C.fundamentalGroupRange.Normal) (x : X) :
    letI := deck.mulActionFiber C.proj x
    MulAction.IsPretransitive (deck C.proj) (C.proj ⁻¹' {x}) := by
  letI := deck.mulActionFiber C.proj x
  let γ : Path.Homotopic.Quotient x₀ x :=
    ⟦PathConnectedSpace.somePath x₀ x⟧
  have hsurj : Function.Surjective (C.isCoveringMap.monodromy γ) :=
    (C.isCoveringMap.monodromy_bijective γ).2
  constructor
  intro e e'
  obtain ⟨a, ha⟩ := hsurj e
  obtain ⟨b, hb⟩ := hsurj e'
  letI := deck.mulActionFiber C.proj x₀
  obtain ⟨d, hd⟩ :=
    (deck_isPretransitive_baseFiber C hH).exists_smul_eq a b
  refine ⟨d, ?_⟩
  apply Subtype.ext
  change d • e.1 = e'.1
  let da : C.proj ⁻¹' {x₀} :=
    ⟨d • a.1, (deck.proj_smul d a.1).trans a.2⟩
  have hab : da = b := by
    apply Subtype.ext
    exact congrArg Subtype.val hd
  calc
    d • e.1 = d • (C.isCoveringMap.monodromy γ a).1 := by rw [ha]
    _ = (C.isCoveringMap.monodromy γ da).1 :=
      deck.smul_monodromy C.isCoveringMap d γ a
    _ = (C.isCoveringMap.monodromy γ b).1 := by rw [hab]
    _ = e'.1 := congrArg Subtype.val hb

/-- A connected covering is normal exactly when its fundamental-group image
is a normal subgroup. -/
theorem isNormal_iff_range_normal
    [PathConnectedSpace X] [LocPathConnectedSpace X]
    (C : Hatcher.BasedConnectedCover.{u, v} X x₀) :
    Hatcher.Covering.IsNormal C.proj ↔ C.fundamentalGroupRange.Normal := by
  constructor
  · intro hnormal
    apply Subgroup.normalizer_eq_top_iff.mp
    rw [Subgroup.eq_top_iff']
    intro g
    let e₀ : C.proj ⁻¹' {x₀} := ⟨C.basepoint, C.proj_basepoint⟩
    let e₁ : C.proj ⁻¹' {x₀} :=
      C.isCoveringMap.monodromyPerm x₀ g⁻¹ e₀
    letI := deck.mulActionFiber C.proj x₀
    obtain ⟨d, hd⟩ := (hnormal.isPretransitive x₀).exists_smul_eq e₀ e₁
    apply (exists_deck_smul_eq_monodromy_inv_iff_mem_normalizer C g).1
    exact ⟨d, congrArg Subtype.val hd⟩
  · intro hH
    exact {
      isCoveringMap := C.isCoveringMap
      surjective := C.proj_surjective
      isPretransitive := deck_isPretransitive_fiber C hH }

private def toNormalizerOfNormal
    (C : Hatcher.BasedConnectedCover.{u, v} X x₀)
    (hH : C.fundamentalGroupRange.Normal) :
    FundamentalGroup X x₀ →*
      Subgroup.normalizer
        (C.fundamentalGroupRange : Set (FundamentalGroup X x₀)) where
  toFun g := ⟨g, by
    rw [Subgroup.normalizer_eq_top_iff.mpr hH]
    exact Subgroup.mem_top g⟩
  map_one' := rfl
  map_mul' _ _ := rfl

private def fundamentalGroupToDeckOfNormal
    [PathConnectedSpace X] [LocPathConnectedSpace X]
    (C : Hatcher.BasedConnectedCover.{u, v} X x₀)
    (hH : C.fundamentalGroupRange.Normal) :
    FundamentalGroup X x₀ →* deck C.proj :=
  C.normalizerToDeck.comp (toNormalizerOfNormal C hH)

private theorem fundamentalGroupToDeckOfNormal_ker_and_surjective
    [PathConnectedSpace X] [LocPathConnectedSpace X]
    (C : Hatcher.BasedConnectedCover.{u, v} X x₀)
    (hH : C.fundamentalGroupRange.Normal) :
    (fundamentalGroupToDeckOfNormal C hH).ker =
        C.fundamentalGroupRange ∧
      Function.Surjective (fundamentalGroupToDeckOfNormal C hH) := by
  have hnormalizer := C.normalizerToDeck_ker_and_surjective
  constructor
  · ext g
    change toNormalizerOfNormal C hH g ∈ C.normalizerToDeck.ker ↔
      g ∈ C.fundamentalGroupRange
    rw [hnormalizer.1]
    rfl
  · intro d
    obtain ⟨g, rfl⟩ := hnormalizer.2 d
    exact ⟨g.1, rfl⟩

/-- For a normal connected covering, the deck group is the fundamental group
modulo the covering subgroup. -/
noncomputable def fundamentalGroupQuotientEquivDeck
    [PathConnectedSpace X] [LocPathConnectedSpace X]
    (C : Hatcher.BasedConnectedCover.{u, v} X x₀)
    (hnormal : Hatcher.Covering.IsNormal C.proj) :
    letI : C.fundamentalGroupRange.Normal :=
      C.isNormal_iff_range_normal.mp hnormal
    FundamentalGroup X x₀ ⧸ C.fundamentalGroupRange ≃* deck C.proj := by
  let hH := C.isNormal_iff_range_normal.mp hnormal
  letI : C.fundamentalGroupRange.Normal := hH
  let φ := fundamentalGroupToDeckOfNormal C hH
  have h := fundamentalGroupToDeckOfNormal_ker_and_surjective C hH
  exact (QuotientGroup.quotientMulEquivOfEq h.1.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ h.2)

end Hatcher.BasedConnectedCover
