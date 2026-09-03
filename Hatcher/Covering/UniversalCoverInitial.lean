import Hatcher.Covering.ConnectedCover
import Hatcher.Covering.LiftingCriterion
import Hatcher.Covering.LocalPathConnected
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

noncomputable section

open Function Set Topology

namespace Hatcher.Covering

universe u v w

variable {A : Type u} {E : Type w} {X : Type v}
variable [TopologicalSpace A] [TopologicalSpace E] [TopologicalSpace X]
variable {q : A → X} {p : E → X}

private theorem surjective_of_comp_eq_of_covering
    [PathConnectedSpace E]
    (hq : IsCoveringMap q) (hp : IsCoveringMap p)
    (F : C(A, E)) (hF : p ∘ F = q) (a₀ : A) (e₀ : E)
    (hbase : F a₀ = e₀) : Function.Surjective F := by
  intro e
  let γ : Path e₀ e := PathConnectedSpace.somePath _ _
  let δ : Path (q a₀) (p e) :=
    (γ.map hp.continuous).cast
      ((congrFun hF a₀).symm.trans (congrArg p hbase)) rfl
  let Γ : Path a₀ (hq.liftPath δ a₀ δ.source 1) :=
    ⟨hq.liftPath δ a₀ δ.source, hq.liftPath_zero δ a₀ δ.source, rfl⟩
  have hEq : F ∘ Γ = γ := by
    refine hp.eq_of_comp_eq (F.continuous.comp Γ.continuous) γ.continuous
      ?_ 0 ?_
    · funext t
      change p (F (Γ t)) = p (γ t)
      calc
        p (F (Γ t)) = q (Γ t) := congrFun hF (Γ t)
        _ = δ t := congrFun (hq.liftPath_lifts δ a₀ δ.source) t
        _ = p (γ t) := by simp [δ]
    · calc
        F (Γ 0) = F a₀ := congrArg F Γ.source
        _ = e₀ := hbase
        _ = γ 0 := γ.source.symm
  exact ⟨Γ 1, (congrFun hEq 1).trans γ.target⟩

private theorem isCoveringMap_of_comp_eq
    [PathConnectedSpace E] [LocPathConnectedSpace X]
    (hq : IsCoveringMap q) (hp : IsCoveringMap p)
    (F : C(A, E)) (hF : p ∘ F = q) (a₀ : A) (e₀ : E)
    (hbase : F a₀ = e₀) : IsCoveringMap F := by
  have hsurj : Function.Surjective F :=
    surjective_of_comp_eq_of_covering hq hp F hF a₀ e₀ hbase
  have hlocal : IsLocalHomeomorph F := by
    apply IsLocalHomeomorph.of_comp
        (g := p) (f := F)
        (hF.symm ▸ hq.isLocalHomeomorph) hp.isLocalHomeomorph
        F.continuous
  intro e
  obtain ⟨u₀, hu₀⟩ := hsurj e
  let x := p e
  have hqu₀ : q u₀ = x := by
    rw [← hF]
    simp [Function.comp_apply, hu₀, x]
  letI : Nonempty (q ⁻¹' ({x} : Set X)) := ⟨⟨u₀, hqu₀⟩⟩
  letI : Nonempty (p ⁻¹' ({x} : Set X)) := ⟨⟨e, rfl⟩⟩
  letI : DiscreteTopology (q ⁻¹' ({x} : Set X)) :=
    (hq x).discreteTopology_fiber
  letI : DiscreteTopology (p ⁻¹' ({x} : Set X)) :=
    (hp x).discreteTopology_fiber
  let tA := (hq x).toTrivialization
  let tE := (hp x).toTrivialization
  have hxA : x ∈ tA.baseSet := (hq x).mem_toTrivialization_baseSet
  have hxE : x ∈ tE.baseSet := (hp x).mem_toTrivialization_baseSet
  have hnhds : tA.baseSet ∩ tE.baseSet ∈ 𝓝 x :=
    Filter.inter_mem (tA.open_baseSet.mem_nhds hxA)
      (tE.open_baseSet.mem_nhds hxE)
  obtain ⟨W, ⟨hWopen, hxW, hWpath⟩, hWsub⟩ :=
    (isOpen_isPathConnected_basis x).mem_iff.mp hnhds
  let iE := (tE e).2
  let V : Set E := tE.source ∩ tE ⁻¹' (W ×ˢ ({iE} : Set (p ⁻¹' {x})))
  let S (u : F ⁻¹' ({e} : Set E)) : Set A :=
    tA.source ∩ tA ⁻¹' (W ×ˢ ({(tA u.1).2} : Set (q ⁻¹' {x})))
  have hVopen : IsOpen V :=
    tE.isOpen_inter_preimage (hWopen.prod (isOpen_discrete _))
  have hSopen (u : F ⁻¹' ({e} : Set E)) : IsOpen (S u) :=
    tA.isOpen_inter_preimage (hWopen.prod (isOpen_discrete _))
  let secA (i : q ⁻¹' ({x} : Set X)) (z : X) : A := tA.invFun (z, i)
  let secE (z : X) : E := tE.invFun (z, iE)
  have hsecA_cont (i : q ⁻¹' ({x} : Set X)) : ContinuousOn (secA i) W := by
    apply tA.continuousOn_invFun.comp
        (continuous_id.prodMk continuous_const).continuousOn
    intro z hz
    rw [tA.target_eq]
    exact ⟨(hWsub hz).1, Set.mem_univ _⟩
  have hsecE_cont : ContinuousOn secE W := by
    apply tE.continuousOn_invFun.comp
        (continuous_id.prodMk continuous_const).continuousOn
    intro z hz
    rw [tE.target_eq]
    exact ⟨(hWsub hz).2, Set.mem_univ _⟩
  have hq_secA (i : q ⁻¹' ({x} : Set X)) {z : X} (hz : z ∈ W) :
      q (secA i z) = z := by
    exact tA.proj_symm_apply' (hWsub hz).1
  have hp_secE {z : X} (hz : z ∈ W) : p (secE z) = z := by
    exact tE.proj_symm_apply' (hWsub hz).2
  have hsec_unique (i : q ⁻¹' ({x} : Set X)) {z₀ : X}
      (hz₀ : z₀ ∈ W) (heq : F (secA i z₀) = secE z₀) :
      Set.EqOn (F ∘ secA i) secE W := by
    apply hp.eqOn_of_comp_eqOn hWpath.isConnected.isPreconnected
        (F.continuous.comp_continuousOn (hsecA_cont _)) hsecE_cont
    · intro z hz
      change p (F (secA i z)) = p (secE z)
      calc
        p (F (secA i z)) = q (secA i z) := congrFun hF _
        _ = z := hq_secA _ hz
        _ = p (secE z) := (hp_secE hz).symm
    · exact hz₀
    · exact heq
  have huq (u : F ⁻¹' ({e} : Set E)) : q u.1 = x := by
    calc
      q u.1 = p (F u.1) := (congrFun hF u.1).symm
      _ = p e := congrArg p (Set.mem_singleton_iff.mp u.2)
      _ = x := rfl
  have hsec_eq (u : F ⁻¹' ({e} : Set E)) :
      Set.EqOn (F ∘ secA (tA u.1).2) secE W := by
    apply hsec_unique _ hxW
    have hu_source : u.1 ∈ tA.source := tA.mem_source.mpr (by
      simpa [huq u] using hxA)
    have he_source : e ∈ tE.source := tE.mem_source.mpr (by
      simpa [x] using hxE)
    change F (secA (tA u.1).2 x) = secE x
    rw [show secA (tA u.1).2 x = u.1 by
      simpa [secA, huq u] using tA.symm_apply_mk_proj hu_source]
    rw [show secE x = e by
      simpa [secE, iE, x] using tE.symm_apply_mk_proj he_source]
    exact Set.mem_singleton_iff.mp u.2
  have he_source : e ∈ tE.source := tE.mem_source.mpr (by
    simpa [x] using hxE)
  have heV : e ∈ V := by
    refine ⟨he_source, ?_⟩
    change tE e ∈ W ×ˢ ({iE} : Set (p ⁻¹' {x}))
    refine ⟨?_, rfl⟩
    have hfst : (tE e).1 = x := tE.proj_toFun e he_source
    exact hfst.symm ▸ hxW
  have hu_source (u : F ⁻¹' ({e} : Set E)) : u.1 ∈ tA.source :=
    tA.mem_source.mpr (by simpa [huq u] using hxA)
  have huS (u : F ⁻¹' ({e} : Set E)) : u.1 ∈ S u := by
    refine ⟨hu_source u, ?_⟩
    change tA u.1 ∈ W ×ˢ ({(tA u.1).2} : Set (q ⁻¹' {x}))
    refine ⟨?_, rfl⟩
    have hfst : (tA u.1).1 = x :=
      (tA.proj_toFun u.1 (hu_source u)).trans (huq u)
    exact hfst.symm ▸ hxW
  have hsecA_self (u : F ⁻¹' ({e} : Set E)) {z : A} (hz : z ∈ S u) :
      secA (tA u.1).2 (q z) = z := by
    have hcoord : (tA z).2 = (tA u.1).2 :=
      Set.mem_singleton_iff.mp hz.2.2
    dsimp only [secA]
    rw [← hcoord]
    exact tA.symm_apply_mk_proj hz.1
  have hsecE_self {z : E} (hz : z ∈ V) : secE (p z) = z := by
    have hcoord : (tE z).2 = iE := Set.mem_singleton_iff.mp hz.2.2
    dsimp only [secE]
    rw [← hcoord]
    exact tE.symm_apply_mk_proj hz.1
  have hzW_of_mem_S (u : F ⁻¹' ({e} : Set E)) {z : A} (hz : z ∈ S u) :
      q z ∈ W := by
    rw [← tA.proj_toFun z hz.1]
    exact hz.2.1
  have hF_on (u : F ⁻¹' ({e} : Set E)) {z : A} (hz : z ∈ S u) :
      F z = secE (q z) := by
    calc
      F z = F (secA (tA u.1).2 (q z)) := congrArg F (hsecA_self u hz).symm
      _ = secE (q z) := hsec_eq u (hzW_of_mem_S u hz)
  have hmaps (u : F ⁻¹' ({e} : Set E)) : Set.MapsTo F (S u) V := by
    intro z hz
    rw [hF_on u hz]
    have hzW := hzW_of_mem_S u hz
    have htarget : (q z, iE) ∈ tE.target := by
      rw [tE.target_eq]
      exact ⟨(hWsub hzW).2, Set.mem_univ _⟩
    refine ⟨tE.map_target htarget, ?_⟩
    change tE (secE (q z)) ∈ W ×ˢ ({iE} : Set (p ⁻¹' {x}))
    rw [show tE (secE (q z)) = (q z, iE) by
      exact tE.apply_symm_apply htarget]
    exact ⟨hzW, rfl⟩
  have hsurjOn (u : F ⁻¹' ({e} : Set E)) : Set.SurjOn F (S u) V := by
    intro z hz
    have hzW : p z ∈ W := by
      have hfst : (tE z).1 = p z := tE.proj_toFun z hz.1
      exact hfst ▸ hz.2.1
    let a : A := secA (tA u.1).2 (p z)
    have htargetA : (p z, (tA u.1).2) ∈ tA.target := by
      rw [tA.target_eq]
      exact ⟨(hWsub hzW).1, Set.mem_univ _⟩
    have ha_source : a ∈ tA.source := tA.map_target htargetA
    have haS : a ∈ S u := by
      refine ⟨ha_source, ?_⟩
      change tA a ∈ W ×ˢ ({(tA u.1).2} : Set (q ⁻¹' {x}))
      rw [show tA a = (p z, (tA u.1).2) by
        exact tA.apply_symm_apply htargetA]
      exact ⟨hzW, rfl⟩
    refine ⟨a, haS, ?_⟩
    calc
      F a = secE (p z) := hsec_eq u hzW
      _ = z := hsecE_self hz
  have hinjOn (u : F ⁻¹' ({e} : Set E)) : Set.InjOn F (S u) := by
    intro z hz z' hz' hzz'
    apply tA.injOn hz.1 hz'.1
    apply Prod.ext
    · calc
        (tA z).1 = q z := tA.proj_toFun z hz.1
        _ = p (F z) := (congrFun hF z).symm
        _ = p (F z') := congrArg p hzz'
        _ = q z' := congrFun hF z'
        _ = (tA z').1 := (tA.proj_toFun z' hz'.1).symm
    · exact (Set.mem_singleton_iff.mp hz.2.2).trans
        (Set.mem_singleton_iff.mp hz'.2.2).symm
  have hdisjoint : Pairwise (Disjoint on S) := by
    intro u v huv
    change Disjoint (S u) (S v)
    rw [Set.disjoint_left]
    intro z hzu hzv
    apply huv
    apply Subtype.ext
    apply tA.injOn (hu_source u) (hu_source v)
    apply Prod.ext
    · calc
        (tA u.1).1 = q u.1 := tA.proj_toFun u.1 (hu_source u)
        _ = x := huq u
        _ = q v.1 := (huq v).symm
        _ = (tA v.1).1 := (tA.proj_toFun v.1 (hu_source v)).symm
    · exact (Set.mem_singleton_iff.mp hzu.2.2).symm.trans
        (Set.mem_singleton_iff.mp hzv.2.2)
  have hexhaustive : F ⁻¹' V ⊆ ⋃ u, S u := by
    intro z hz
    have hzW : q z ∈ W := by
      have hfst : (tE (F z)).1 = p (F z) := tE.proj_toFun (F z) hz.1
      have hpFzW : p (F z) ∈ W := hfst ▸ hz.2.1
      exact congrFun hF z ▸ hpFzW
    have hz_source : z ∈ tA.source :=
      tA.mem_source.mpr ((hWsub hzW).1)
    let i := (tA z).2
    have hsecA_z : secA i (q z) = z := by
      dsimp only [secA, i]
      exact tA.symm_apply_mk_proj hz_source
    have hagree : F (secA i (q z)) = secE (q z) := by
      rw [hsecA_z]
      have hpF : p (F z) = q z := congrFun hF z
      rw [← hpF]
      exact (hsecE_self hz).symm
    have hsections := hsec_unique i hzW hagree
    let u' : A := secA i x
    have hFu' : F u' = e := by
      calc
        F u' = secE x := hsections hxW
        _ = e := hsecE_self heV
    let u : F ⁻¹' ({e} : Set E) := ⟨u', by simpa using hFu'⟩
    apply Set.mem_iUnion.mpr
    refine ⟨u, ?_⟩
    refine ⟨hz_source, ?_⟩
    change tA z ∈ W ×ˢ ({(tA u.1).2} : Set (q ⁻¹' {x}))
    refine ⟨?_, ?_⟩
    · have hfst : (tA z).1 = q z := tA.proj_toFun z hz_source
      exact hfst ▸ hzW
    · have htarget : (x, i) ∈ tA.target := by
        rw [tA.target_eq]
        exact ⟨(hWsub hxW).1, Set.mem_univ _⟩
      have htu' : tA u' = (x, i) := tA.apply_symm_apply htarget
      exact Set.mem_singleton_iff.mpr (by simpa [u, u', i] using congrArg Prod.snd htu'.symm)
  have hopen_iff (u : F ⁻¹' ({e} : Set E)) {T : Set E} (hTV : T ⊆ V) :
      IsOpen T ↔ IsOpen (F ⁻¹' T ∩ S u) := by
    constructor
    · intro hT
      exact (hT.preimage F.continuous).inter (hSopen u)
    · intro hpre
      have himage : T = F '' (F ⁻¹' T ∩ S u) := by
        ext z
        constructor
        · intro hzT
          obtain ⟨a, haS, hFa⟩ := hsurjOn u (hTV hzT)
          refine ⟨a, ⟨?_, haS⟩, hFa⟩
          show F a ∈ T
          rw [hFa]
          exact hzT
        · rintro ⟨a, ⟨haT, -⟩, rfl⟩
          exact haT
      rw [himage]
      exact hlocal.isOpenMap _ hpre
  letI : Nonempty (E → A) := ⟨fun z => Classical.choose (hsurj z)⟩
  letI : Nonempty (F ⁻¹' ({e} : Set E)) := ⟨⟨u₀, by simpa using hu₀⟩⟩
  have himage_fiber : F '' (F ⁻¹' ({e} : Set E)) = {e} := by
    ext z
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ha
    · intro hz
      have hze : z = e := Set.mem_singleton_iff.mp hz
      subst z
      exact ⟨u₀, by simpa using hu₀, hu₀⟩
  letI : DiscreteTopology (F ⁻¹' ({e} : Set E)) := by
    have hlocOn : IsLocalHomeomorphOn F (F ⁻¹' ({e} : Set E)) :=
      hlocal.isLocalHomeomorphOn.mono (Set.subset_univ _)
    letI : DiscreteTopology (F '' (F ⁻¹' ({e} : Set E))) :=
      himage_fiber.symm ▸ inferInstance
    exact hlocOn.discreteTopology_of_image
  let t := hVopen.trivializationDiscrete S V hopen_iff hinjOn hsurjOn
    hdisjoint hexhaustive
  exact IsEvenlyCovered.of_trivialization (t := t) heV

end Hatcher.Covering

namespace Hatcher.BasedConnectedCover

universe u v w

variable {X : Type v} [TopologicalSpace X] {x₀ : X}

theorem existsUnique_map_fromSimplyConnected_core
    [PathConnectedSpace X] [LocPathConnectedSpace X]
    (U : BasedConnectedCover.{u, v} X x₀)
    (E : BasedConnectedCover.{w, v} X x₀)
    [SimplyConnectedSpace U.E] :
    ∃! F : C(U.E, E.E),
      F U.basepoint = E.basepoint ∧ E.proj ∘ F = U.proj := by
  letI : LocPathConnectedSpace U.E :=
    Hatcher.Covering.locPathConnectedSpace_total U.isCoveringMap
  let pU : C(U.E, X) := ⟨U.proj, U.isCoveringMap.continuous⟩
  have he : E.proj E.basepoint = pU U.basepoint :=
    E.proj_basepoint.trans U.proj_basepoint.symm
  have hsource : (FundamentalGroup.map pU U.basepoint).range = ⊥ := by
    rw [MonoidHom.range_eq_bot_iff]
    ext g
    rw [Subsingleton.elim g 1]
    exact map_one _
  obtain ⟨F, hFbase, hFproj⟩ :=
    (Hatcher.Covering.exists_lift_iff_range_le E.isCoveringMap pU
      U.basepoint E.basepoint he).2 (hsource.le.trans bot_le)
  refine ⟨F, ⟨hFbase, hFproj⟩, ?_⟩
  intro G hG
  have hFG : (F : U.E → E.E) = G := by
    exact E.isCoveringMap.eq_of_comp_eq F.continuous G.continuous
      (hFproj.trans hG.2.symm) U.basepoint (hFbase.trans hG.1.symm)
  exact ContinuousMap.ext fun a ↦ (congrFun hFG a).symm

/-- A simply-connected pointed cover admits a unique pointed map to every
pointed connected cover, and this comparison map is itself a covering map. -/
theorem existsUnique_map_fromSimplyConnected
    [PathConnectedSpace X] [LocPathConnectedSpace X]
    (U : BasedConnectedCover.{u, v} X x₀)
    (E : BasedConnectedCover.{w, v} X x₀)
    [SimplyConnectedSpace U.E] :
    ∃! F : C(U.E, E.E),
      F U.basepoint = E.basepoint ∧ E.proj ∘ F = U.proj ∧ IsCoveringMap F := by
  obtain ⟨F, hF, huniq⟩ := existsUnique_map_fromSimplyConnected_core U E
  refine ⟨F, ⟨hF.1, hF.2, ?_⟩, ?_⟩
  · exact Hatcher.Covering.isCoveringMap_of_comp_eq
      U.isCoveringMap E.isCoveringMap F hF.2 U.basepoint E.basepoint hF.1
  · intro G hG
    exact huniq G ⟨hG.1, hG.2.1⟩

/-- Any two pointed simply-connected covers are isomorphic over the base. -/
theorem nonempty_iso_of_simplyConnected
    [PathConnectedSpace X] [LocPathConnectedSpace X]
    (U : BasedConnectedCover.{u, v} X x₀)
    (E : BasedConnectedCover.{w, v} X x₀)
    [SimplyConnectedSpace U.E] [SimplyConnectedSpace E.E] :
    Nonempty (U.Iso E) := by
  obtain ⟨F, hF, -⟩ := existsUnique_map_fromSimplyConnected U E
  obtain ⟨G, hG, -⟩ := existsUnique_map_fromSimplyConnected E U
  have hGF : G ∘ F = id := by
    apply U.isCoveringMap.eq_of_comp_eq (G.comp F).continuous
      (ContinuousMap.id U.E).continuous
      (by
        funext x
        exact (congrFun hG.2.1 (F x)).trans (congrFun hF.2.1 x)) U.basepoint
    simp only [ContinuousMap.comp_apply, ContinuousMap.id_apply, hF.1, hG.1]
  have hFG : F ∘ G = id := by
    apply E.isCoveringMap.eq_of_comp_eq (F.comp G).continuous
      (ContinuousMap.id E.E).continuous
      (by
        funext x
        exact (congrFun hF.2.1 (G x)).trans (congrFun hG.2.1 x)) E.basepoint
    simp only [ContinuousMap.comp_apply, ContinuousMap.id_apply, hG.1, hF.1]
  exact ⟨{
    toHomeomorph := {
      toEquiv := {
        toFun := F
        invFun := G
        left_inv := fun x ↦ congrFun hGF x
        right_inv := fun x ↦ congrFun hFG x }
      continuous_toFun := F.continuous
      continuous_invFun := G.continuous }
    proj_comp := hF.2.1
    map_basepoint := hF.1 }⟩

end Hatcher.BasedConnectedCover

