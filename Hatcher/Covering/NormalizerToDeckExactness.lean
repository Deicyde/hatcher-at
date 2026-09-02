import Hatcher.Covering.NormalizerToDeck

noncomputable section

namespace Hatcher.BasedConnectedCover

universe u v

variable {X : Type v} [TopologicalSpace X] {x₀ : X}

/-- A loop class lies in the normalizer exactly when inverse monodromy at the
chosen point is realized by a deck transformation. -/
theorem exists_deck_smul_eq_monodromy_inv_iff_mem_normalizer
    [PathConnectedSpace X] [LocPathConnectedSpace X]
    (C : Hatcher.BasedConnectedCover.{u, v} X x₀)
    (g : FundamentalGroup X x₀) :
    (∃ d : deck C.proj,
      d • C.basepoint =
        (C.isCoveringMap.monodromyPerm x₀ g⁻¹
          ⟨C.basepoint, C.proj_basepoint⟩).1) ↔
      g ∈ Subgroup.normalizer
        (C.fundamentalGroupRange : Set (FundamentalGroup X x₀)) := by
  let e₀ : C.proj ⁻¹' {x₀} := ⟨C.basepoint, C.proj_basepoint⟩
  let e₁ : C.proj ⁻¹' {x₀} := C.isCoveringMap.monodromyPerm x₀ g⁻¹ e₀
  constructor
  · rintro ⟨d, hd⟩
    have hu : ∃! d' : deck C.proj, d' • C.basepoint = e₁.1 := by
      refine ⟨d, hd, ?_⟩
      intro d' hd'
      apply deck.ext_of_eq_at C.isCoveringMap (e := C.basepoint)
      exact hd'.trans hd.symm
    have hrange : C.fundamentalGroupRange =
        (C.rebase e₁).fundamentalGroupRange :=
      (C.existsUnique_deck_apply_basepoint_iff_range_eq e₁).1 hu
    have hchange := Hatcher.Covering.range_mapOfEq_of_monodromy
      C.isCoveringMap e₀ e₁ g⁻¹ rfl
    have hinv : g⁻¹ ∈ Subgroup.normalizer
        (C.fundamentalGroupRange : Set (FundamentalGroup X x₀)) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr
        (hrange.trans hchange).symm
    simpa using hinv
  · intro hg
    exact ⟨C.normalizerToDeck ⟨g, hg⟩,
      C.normalizerToDeck_smul_basepoint ⟨g, hg⟩⟩

/-- The normalizer map is onto the deck group, and its kernel is the covering
subgroup viewed inside its normalizer. -/
theorem normalizerToDeck_ker_and_surjective
    [PathConnectedSpace X] [LocPathConnectedSpace X]
    (C : Hatcher.BasedConnectedCover.{u, v} X x₀) :
    C.normalizerToDeck.ker =
        C.fundamentalGroupRange.subgroupOf
          (Subgroup.normalizer
            (C.fundamentalGroupRange : Set (FundamentalGroup X x₀))) ∧
      Function.Surjective C.normalizerToDeck := by
  letI := C.isCoveringMap.fundamentalGroupMulAction x₀
  let e₀ : C.proj ⁻¹' {x₀} := ⟨C.basepoint, C.proj_basepoint⟩
  constructor
  · ext g
    rw [MonoidHom.mem_ker]
    change C.normalizerToDeck g = 1 ↔
      (g : FundamentalGroup X x₀) ∈ C.fundamentalGroupRange
    constructor
    · intro hg
      have ha := congrArg (fun d : deck C.proj ↦ d • C.basepoint) hg
      rw [C.normalizerToDeck_smul_basepoint] at ha
      simp only [one_smul] at ha
      have hfix : C.isCoveringMap.monodromyPerm x₀
          ((g : FundamentalGroup X x₀)⁻¹) e₀ = e₀ :=
        Subtype.ext ha
      have hmemstab : (g : FundamentalGroup X x₀)⁻¹ ∈
          MulAction.stabilizer (FundamentalGroup X x₀) e₀ := by
        rw [MulAction.mem_stabilizer_iff]
        exact hfix
      have hinv' : (g : FundamentalGroup X x₀)⁻¹ ∈
          (FundamentalGroup.mapOfEq
            ⟨C.proj, C.isCoveringMap.continuous⟩ C.proj_basepoint).range := by
        rw [Hatcher.Covering.range_mapOfEq_eq_stabilizer C.isCoveringMap e₀]
        exact hmemstab
      have hinv : (g : FundamentalGroup X x₀)⁻¹ ∈ C.fundamentalGroupRange := by
        simpa [fundamentalGroupRange, projMap] using hinv'
      simpa using hinv
    · intro hg
      apply deck.ext_of_eq_at C.isCoveringMap (e := C.basepoint)
      rw [C.normalizerToDeck_smul_basepoint]
      simp only [one_smul]
      have hinv : (g : FundamentalGroup X x₀)⁻¹ ∈ C.fundamentalGroupRange := by
        simpa using hg
      have hinv' : (g : FundamentalGroup X x₀)⁻¹ ∈
          (FundamentalGroup.mapOfEq
            ⟨C.proj, C.isCoveringMap.continuous⟩ C.proj_basepoint).range := by
        simpa [fundamentalGroupRange, projMap] using hinv
      have hmemstab : (g : FundamentalGroup X x₀)⁻¹ ∈
          MulAction.stabilizer (FundamentalGroup X x₀) e₀ := by
        rw [← Hatcher.Covering.range_mapOfEq_eq_stabilizer C.isCoveringMap e₀]
        exact hinv'
      have hfix : C.isCoveringMap.monodromyPerm x₀
          ((g : FundamentalGroup X x₀)⁻¹) e₀ = e₀ :=
        MulAction.mem_stabilizer_iff.mp hmemstab
      simpa [e₀] using congrArg Subtype.val hfix
  · intro d
    let e₁ : C.proj ⁻¹' {x₀} :=
      ⟨d • C.basepoint, (deck.proj_smul d C.basepoint).trans C.proj_basepoint⟩
    let α : Path C.basepoint (d • C.basepoint) :=
      PathConnectedSpace.somePath C.basepoint (d • C.basepoint)
    let a : FundamentalGroup X x₀ :=
      Hatcher.Covering.projectedPathClass C.isCoveringMap e₀ e₁ α
    have ha : C.isCoveringMap.monodromyPerm x₀ a e₀ = e₁ :=
      Hatcher.Covering.monodromy_projectedPathClass C.isCoveringMap e₀ e₁ α
    let g₀ : FundamentalGroup X x₀ := a⁻¹
    have hg₀ : g₀ ∈ Subgroup.normalizer
        (C.fundamentalGroupRange : Set (FundamentalGroup X x₀)) :=
      (exists_deck_smul_eq_monodromy_inv_iff_mem_normalizer C g₀).1 ⟨d, by
        simpa [g₀] using congrArg Subtype.val ha.symm⟩
    let g : Subgroup.normalizer
        (C.fundamentalGroupRange : Set (FundamentalGroup X x₀)) := ⟨g₀, hg₀⟩
    refine ⟨g, ?_⟩
    apply deck.ext_of_eq_at C.isCoveringMap (e := C.basepoint)
    rw [C.normalizerToDeck_smul_basepoint]
    simpa [g, g₀] using congrArg Subtype.val ha

end Hatcher.BasedConnectedCover
