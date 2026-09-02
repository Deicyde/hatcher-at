import Hatcher.Covering.UniversalCoverBasis
import Mathlib.Topology.Covering.Basic

noncomputable section

open Set TopologicalSpace Topology

namespace Hatcher.UniversalCover

universe u

variable {X : Type u} [TopologicalSpace X] {x₀ : X}

private theorem map_symm
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {a b : A} (f : C(A, B)) (γ : Path.Homotopic.Quotient a b) :
    γ.symm.map f = (γ.map f).symm := by
  induction γ using Path.Homotopic.Quotient.ind with
  | mk γ =>
    rfl

theorem isOpen_basicOpen
    [LocPathConnectedSpace X] [SemilocallySimplyConnectedSpace X]
    {U : Set X} (hU : IsNullhomotopicOpen U) {x : X} (hx : x ∈ U)
    (γ : Path.Homotopic.Quotient x₀ x) : IsOpen (basicOpen U hx γ) :=
  isTopologicalBasis_basicOpen.isOpen ⟨U, hU, x, hx, γ, rfl⟩

theorem continuous_proj
    [LocPathConnectedSpace X] [SemilocallySimplyConnectedSpace X] :
    Continuous (proj : UniversalCover X x₀ → X) := by
  rw [Hatcher.isTopologicalBasis_nullhomotopicOpens.continuous_iff]
  intro U hU
  rw [isTopologicalBasis_basicOpen.isOpen_iff]
  intro q hqU
  refine ⟨basicOpen U hqU q.2, ⟨U, hU, q.1, hqU, q.2, rfl⟩,
    self_mem_basicOpen U hqU q.2, ?_⟩
  intro r hr
  exact (bijOn_proj_basicOpen hU hqU q.2).mapsTo hr

private theorem isOpen_iff_preimage_inter_basicOpen
    [LocPathConnectedSpace X] [SemilocallySimplyConnectedSpace X]
    {U W : Set X} (hU : IsNullhomotopicOpen U) (hWU : W ⊆ U)
    {x : X} (hx : x ∈ U) (γ : Path.Homotopic.Quotient x₀ x) :
    IsOpen W ↔ IsOpen (proj ⁻¹' W ∩ basicOpen U hx γ) := by
  constructor
  · intro hW
    exact (hW.preimage continuous_proj).inter (isOpen_basicOpen hU hx γ)
  · intro hopen
    rw [isOpen_iff_mem_nhds]
    intro y hy
    obtain ⟨q, hq, hqproj⟩ := (bijOn_proj_basicOpen hU hx γ).surjOn (hWU hy)
    have hqopen : q ∈ proj ⁻¹' W ∩ basicOpen U hx γ := by
      constructor
      · change proj q ∈ W
        exact hqproj.symm ▸ hy
      · exact hq
    obtain ⟨V, hV, hqV, hVsub⟩ :=
      isTopologicalBasis_basicOpen.exists_subset_of_mem_open hqopen hopen
    obtain ⟨V, hV, z, hz, η, rfl⟩ := hV
    have hyV : y ∈ V := by
      have hmap := (bijOn_proj_basicOpen hV hz η).mapsTo hqV
      exact hqproj ▸ hmap
    refine mem_nhds_iff.mpr ⟨V, ?_, hV.1, hyV⟩
    intro z hzV
    obtain ⟨r, hr, hrproj⟩ := (bijOn_proj_basicOpen hV hz η).surjOn hzV
    have hr' := hVsub hr
    exact hrproj ▸ hr'.1

theorem discreteTopology_fiber_proj
    [LocPathConnectedSpace X] [SemilocallySimplyConnectedSpace X] (x : X) :
    DiscreteTopology ((proj : UniversalCover X x₀ → X) ⁻¹' ({x} : Set X)) := by
  rw [discreteTopology_iff_isOpen_singleton]
  rintro ⟨⟨y, eγ⟩, hey⟩
  change y = x at hey
  subst y
  let e : (proj : UniversalCover X x₀ → X) ⁻¹' ({x} : Set X) :=
    ⟨⟨x, eγ⟩, rfl⟩
  change IsOpen ({e} : Set ((proj : UniversalCover X x₀ → X) ⁻¹' ({x} : Set X)))
  obtain ⟨U, hU, hxU, -⟩ :=
    Hatcher.isTopologicalBasis_nullhomotopicOpens.exists_subset_of_mem_open
      (show x ∈ (Set.univ : Set X) from Set.mem_univ x) isOpen_univ
  have hopen : IsOpen
      (Subtype.val ⁻¹' basicOpen U hxU eγ :
        Set ((proj : UniversalCover X x₀ → X) ⁻¹' ({x} : Set X))) :=
    (isOpen_basicOpen hU hxU eγ).preimage continuous_subtype_val
  convert hopen using 1
  ext e'
  constructor
  · intro he'
    rw [Set.mem_singleton_iff] at he'
    subst e'
    exact self_mem_basicOpen U hxU eγ
  · intro he'
    rw [Set.mem_singleton_iff]
    apply Subtype.ext
    apply (bijOn_proj_basicOpen hU hxU eγ).injOn he'
      (self_mem_basicOpen U hxU eγ)
    exact e'.2.trans e.2.symm

private def fiberEndpointMem {x : X} {U : Set X} (hx : x ∈ U)
    (e : (proj : UniversalCover X x₀ → X) ⁻¹' ({x} : Set X)) : e.1.1 ∈ U := by
  have he : proj e.1 = x := e.2
  change proj e.1 ∈ U
  rw [he]
  exact hx

private def sheet {x : X} (U : Set X) (hx : x ∈ U)
    (e : (proj : UniversalCover X x₀ → X) ⁻¹' ({x} : Set X)) :
    Set (UniversalCover X x₀) :=
  basicOpen U (fiberEndpointMem hx e) e.1.2

private theorem pairwise_disjoint_sheet
    [LocPathConnectedSpace X] [SemilocallySimplyConnectedSpace X]
    {x : X} {U : Set X} (hU : IsNullhomotopicOpen U) (hx : x ∈ U) :
    Pairwise fun e e' :
        (proj : UniversalCover X x₀ → X) ⁻¹' ({x} : Set X) ↦
      Disjoint (sheet (x₀ := x₀) (x := x) U hx e)
        (sheet (x₀ := x₀) (x := x) U hx e') := by
  intro e e' hne
  rw [Set.disjoint_left]
  intro q hqe hqe'
  let hqU : q.1 ∈ U := hqe.choose
  have hsame : sheet (x₀ := x₀) (x := x) U hx e =
      sheet (x₀ := x₀) (x := x) U hx e' :=
    (basicOpen_eq_of_mem (fiberEndpointMem hx e) e.1.2 hqU hqe).trans
      (basicOpen_eq_of_mem (fiberEndpointMem hx e') e'.1.2 hqU hqe').symm
  have he'mem : e'.1 ∈ sheet (x₀ := x₀) (x := x) U hx e := by
    rw [hsame]
    exact self_mem_basicOpen U (fiberEndpointMem hx e') e'.1.2
  apply hne
  apply Subtype.ext
  apply (bijOn_proj_basicOpen hU (fiberEndpointMem hx e) e.1.2).injOn
    (self_mem_basicOpen U (fiberEndpointMem hx e) e.1.2)
    he'mem
  exact e.2.trans e'.2.symm

private theorem preimage_subset_iUnion_sheet
    [LocPathConnectedSpace X] [SemilocallySimplyConnectedSpace X]
    {x : X} {U : Set X} (hU : IsNullhomotopicOpen U) (hx : x ∈ U) :
    (proj : UniversalCover X x₀ → X) ⁻¹' U ⊆
      ⋃ e : (proj : UniversalCover X x₀ → X) ⁻¹' ({x} : Set X),
        sheet (x₀ := x₀) (x := x) U hx e := by
  intro q hqU
  letI : PathConnectedSpace U := isPathConnected_iff_pathConnectedSpace.mp hU.2.1
  let δ : Path.Homotopic.Quotient (⟨q.1, hqU⟩ : U) ⟨x, hx⟩ :=
    ⟦PathConnectedSpace.somePath _ _⟧
  let δX := δ.map (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X))
  let e : (proj : UniversalCover X x₀ → X) ⁻¹' ({x} : Set X) :=
    ⟨⟨x, q.2.trans δX⟩, rfl⟩
  apply Set.mem_iUnion.mpr
  refine ⟨e, ?_⟩
  refine ⟨hqU, δ.symm, ?_⟩
  dsimp only [e, sheet, δX]
  rw [map_symm, Path.Homotopic.Quotient.trans_assoc,
    Path.Homotopic.Quotient.trans_symm, Path.Homotopic.Quotient.trans_refl]

theorem surjective_proj [PathConnectedSpace X] :
    Function.Surjective (proj : UniversalCover X x₀ → X) := by
  intro x
  let γ : Path.Homotopic.Quotient x₀ x := ⟦PathConnectedSpace.somePath x₀ x⟧
  exact ⟨⟨x, γ⟩, rfl⟩

/-- The endpoint projection from Hatcher's path-class space is a covering map. -/
theorem isCoveringMap_proj
    [PathConnectedSpace X] [LocPathConnectedSpace X]
    [SemilocallySimplyConnectedSpace X] :
    IsCoveringMap (proj : UniversalCover X x₀ → X) := by
  intro x
  obtain ⟨U, hU, hx, -⟩ :=
    Hatcher.isTopologicalBasis_nullhomotopicOpens.exists_subset_of_mem_open
      (show x ∈ (Set.univ : Set X) from Set.mem_univ x) isOpen_univ
  let F := (proj : UniversalCover X x₀ → X) ⁻¹' ({x} : Set X)
  letI : Nonempty (UniversalCover X x₀) := ⟨basepoint⟩
  letI : Nonempty F := by
    obtain ⟨q, hq⟩ := surjective_proj (x₀ := x₀) x
    exact ⟨⟨q, hq⟩⟩
  letI : DiscreteTopology F := discreteTopology_fiber_proj (x₀ := x₀) x
  let t : Bundle.Trivialization F (proj : UniversalCover X x₀ → X) :=
    hU.1.trivializationDiscrete
      (sheet (x₀ := x₀) (x := x) U hx) U
      (fun e _ hWU ↦ isOpen_iff_preimage_inter_basicOpen hU hWU
        (fiberEndpointMem hx e) e.1.2)
      (fun e ↦ (bijOn_proj_basicOpen hU (fiberEndpointMem hx e) e.1.2).injOn)
      (fun e ↦ (bijOn_proj_basicOpen hU (fiberEndpointMem hx e) e.1.2).surjOn)
      (pairwise_disjoint_sheet hU hx)
      (preimage_subset_iUnion_sheet hU hx)
  apply IsEvenlyCovered.of_trivialization (t := t)
  simpa [t] using hx

end Hatcher.UniversalCover
