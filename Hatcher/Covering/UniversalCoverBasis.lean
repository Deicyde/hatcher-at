import Hatcher.Covering.NullhomotopicOpenBasis
import Hatcher.Covering.UniversalCoverPathSpace

noncomputable section

open Set TopologicalSpace

namespace Hatcher.UniversalCover

universe u


variable {X : Type u} [TopologicalSpace X] {x₀ : X}

private theorem map_trans
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {a b c : A} (f : C(A, B))
    (γ : Path.Homotopic.Quotient a b) (δ : Path.Homotopic.Quotient b c) :
    (γ.trans δ).map f = (γ.map f).trans (δ.map f) := by
  induction γ using Path.Homotopic.Quotient.ind with
  | mk γ =>
    induction δ using Path.Homotopic.Quotient.ind with
    | mk δ =>
      simpa only [← Path.Homotopic.Quotient.mk_trans,
        ← Path.Homotopic.Quotient.mk_map] using
          congrArg Path.Homotopic.Quotient.mk (Path.map_trans γ δ f.continuous)

private theorem map_symm
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {a b : A} (f : C(A, B)) (γ : Path.Homotopic.Quotient a b) :
    γ.symm.map f = (γ.map f).symm := by
  induction γ using Path.Homotopic.Quotient.ind with
  | mk γ =>
    rfl

private theorem map_eq_map_of_range_eq_bot
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {a b : A} (f : C(A, B))
    (htrivial : (FundamentalGroup.map f a).range = ⊥)
    (δ η : Path.Homotopic.Quotient a b) :
    δ.map f = η.map f := by
  rw [MonoidHom.range_eq_bot_iff] at htrivial
  have hloop := DFunLike.congr_fun htrivial
    (FundamentalGroup.fromPath (δ.trans η.symm))
  change (δ.trans η.symm).map f = Path.Homotopic.Quotient.refl (f a) at hloop
  rw [map_trans, map_symm] at hloop
  calc
    δ.map f = ((δ.map f).trans (η.map f).symm).trans (η.map f) := by simp
    _ = (Path.Homotopic.Quotient.refl (f a)).trans (η.map f) :=
      congrArg (fun θ ↦ θ.trans (η.map f)) hloop
    _ = η.map f := Path.Homotopic.Quotient.refl_trans _

private def inclusionOfSubset {U V : Set X} (hVU : V ⊆ U) : C(V, U) :=
  ⟨fun z ↦ ⟨z.1, hVU z.2⟩, continuous_subtype_val.subtype_mk _⟩

private theorem map_inclusionOfSubset
    {U V : Set X} (hVU : V ⊆ U) {a b : X} (ha : a ∈ V) (hb : b ∈ V)
    (δ : Path.Homotopic.Quotient (⟨a, ha⟩ : V) ⟨b, hb⟩) :
    ((δ.map (inclusionOfSubset hVU)).map
        (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X))) =
      δ.map (⟨Subtype.val, continuous_subtype_val⟩ : C(V, X)) := by
  rw [← Path.Homotopic.Quotient.map_comp]
  congr 1

theorem self_mem_basicOpen (U : Set X) {x : X} (hx : x ∈ U)
    (γ : Path.Homotopic.Quotient x₀ x) :
    (⟨x, γ⟩ : UniversalCover X x₀) ∈ basicOpen U hx γ := by
  refine ⟨hx, Path.Homotopic.Quotient.refl (⟨x, hx⟩ : U), ?_⟩
  change γ = γ.trans
    ((Path.Homotopic.Quotient.refl (⟨x, hx⟩ : U)).map
      ⟨Subtype.val, continuous_subtype_val⟩)
  rw [show (Path.Homotopic.Quotient.refl (⟨x, hx⟩ : U)).map
      ⟨Subtype.val, continuous_subtype_val⟩ =
        Path.Homotopic.Quotient.refl x by rfl]
  exact (Path.Homotopic.Quotient.trans_refl γ).symm

theorem basicOpen_subset_of_mem_of_subset
    {U V : Set X} {x : X} (hx : x ∈ U)
    (γ : Path.Homotopic.Quotient x₀ x) {q : UniversalCover X x₀}
    (hq : q ∈ basicOpen U hx γ) (hqV : q.1 ∈ V) (hVU : V ⊆ U) :
    basicOpen V hqV q.2 ⊆ basicOpen U hx γ := by
  rcases q with ⟨y, qγ⟩
  change y ∈ V at hqV
  rintro ⟨z, rγ⟩ ⟨hrV, η, hr⟩
  change z ∈ V at hrV
  change Path.Homotopic.Quotient (⟨y, hqV⟩ : V) ⟨z, hrV⟩ at η
  change rγ = qγ.trans
    (η.map (⟨Subtype.val, continuous_subtype_val⟩ : C(V, X))) at hr
  obtain ⟨hqU, δ, hqeq⟩ := hq
  change Path.Homotopic.Quotient (⟨x, hx⟩ : U) ⟨y, hqU⟩ at δ
  change qγ = γ.trans
    (δ.map (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X))) at hqeq
  have hqU_eq : hqU = hVU hqV := Subsingleton.elim _ _
  subst hqU
  let ηU := η.map (inclusionOfSubset hVU)
  refine ⟨hVU hrV, δ.trans ηU, ?_⟩
  rw [hr, hqeq, map_trans]
  dsimp only [ηU]
  have hη := map_inclusionOfSubset (X := X) hVU hqV hrV η
  calc
    _ = γ.trans ((δ.map
          (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X))).trans
        (η.map (⟨Subtype.val, continuous_subtype_val⟩ : C(V, X)))) :=
      Path.Homotopic.Quotient.trans_assoc _ _ _
    _ = _ := congrArg
      (fun θ ↦ γ.trans ((δ.map
        (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X))).trans θ)) hη.symm

theorem basicOpen_eq_of_mem
    {U : Set X} {x : X} (hx : x ∈ U)
    (γ : Path.Homotopic.Quotient x₀ x) {q : UniversalCover X x₀}
    (hqU : q.1 ∈ U) (hq : q ∈ basicOpen U hx γ) :
    basicOpen U hx γ = basicOpen U hqU q.2 := by
  rcases q with ⟨y, qγ⟩
  change y ∈ U at hqU
  have hnew_old := basicOpen_subset_of_mem_of_subset hx γ hq hqU subset_rfl
  obtain ⟨hqU', δ, hqeq⟩ := hq
  change Path.Homotopic.Quotient (⟨x, hx⟩ : U) ⟨y, hqU'⟩ at δ
  change qγ = γ.trans
    (δ.map (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X))) at hqeq
  have hqU_eq : hqU' = hqU := Subsingleton.elim _ _
  subst hqU'
  have hback : (⟨x, γ⟩ : UniversalCover X x₀) ∈ basicOpen U hqU qγ := by
    refine ⟨hx, δ.symm, ?_⟩
    rw [hqeq, map_symm, Path.Homotopic.Quotient.trans_assoc,
      Path.Homotopic.Quotient.trans_symm, Path.Homotopic.Quotient.trans_refl]
  apply Subset.antisymm
  · exact basicOpen_subset_of_mem_of_subset hqU qγ hback hx subset_rfl
  · exact hnew_old

/-- Hatcher's basic sets form a basis for the path-class topology. -/
theorem isTopologicalBasis_basicOpen
    [LocPathConnectedSpace X] [SemilocallySimplyConnectedSpace X] :
    IsTopologicalBasis {s | ∃ (U : Set X) (_ : IsNullhomotopicOpen U)
      (x : X) (hx : x ∈ U) (γ : Path.Homotopic.Quotient x₀ x),
      s = basicOpen U hx γ} := by
  refine {
    exists_subset_inter := ?_
    sUnion_eq := ?_
    eq_generateFrom := rfl }
  · rintro _ ⟨U, hU, x, hx, γ, rfl⟩ _ ⟨V, hV, y, hy, η, rfl⟩ q ⟨hqU, hqV⟩
    let qU : q.1 ∈ U := hqU.choose
    let qV : q.1 ∈ V := hqV.choose
    obtain ⟨W, hW, hqW, hWsub⟩ :=
      Hatcher.isTopologicalBasis_nullhomotopicOpens.exists_subset_of_mem_open
        (show q.1 ∈ U ∩ V from ⟨qU, qV⟩) (hU.1.inter hV.1)
    refine ⟨basicOpen W hqW q.2, ⟨W, hW, q.1, hqW, q.2, rfl⟩,
      self_mem_basicOpen W hqW q.2, ?_⟩
    intro r hr
    exact ⟨
      basicOpen_subset_of_mem_of_subset hx γ hqU hqW
        (hWsub.trans inter_subset_left) hr,
      basicOpen_subset_of_mem_of_subset hy η hqV hqW
        (hWsub.trans inter_subset_right) hr⟩
  · apply sUnion_eq_univ_iff.mpr
    intro q
    obtain ⟨U, hU, hqU, -⟩ :=
      Hatcher.isTopologicalBasis_nullhomotopicOpens.exists_subset_of_mem_open
        (show q.1 ∈ (Set.univ : Set X) from Set.mem_univ q.1) isOpen_univ
    refine ⟨basicOpen U hqU q.2, ⟨U, hU, q.1, hqU, q.2, rfl⟩, ?_⟩
    exact self_mem_basicOpen U hqU q.2

/-- Endpoint projection maps each basic open bijectively onto its base open. -/
theorem bijOn_proj_basicOpen
    {U : Set X} (hU : IsNullhomotopicOpen U) {x : X} (hx : x ∈ U)
    (γ : Path.Homotopic.Quotient x₀ x) :
    Set.BijOn proj (basicOpen U hx γ) U := by
  refine ⟨?_, ?_, ?_⟩
  · rintro q ⟨hqU, -, -⟩
    exact hqU
  · rintro ⟨y, qγ⟩ hq ⟨z, rγ⟩ hr hyz
    change y = z at hyz
    subst z
    obtain ⟨hqU, δ, hqeq⟩ := hq
    obtain ⟨hrU, η, hreq⟩ := hr
    change Path.Homotopic.Quotient (⟨x, hx⟩ : U) ⟨y, hqU⟩ at δ
    change Path.Homotopic.Quotient (⟨x, hx⟩ : U) ⟨y, hrU⟩ at η
    have hproof : hrU = hqU := Subsingleton.elim _ _
    subst hrU
    have hδη := map_eq_map_of_range_eq_bot
      (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X))
      (hU.2.2 ⟨x, hx⟩) δ η
    congr 1
    exact hqeq.trans ((congrArg (γ.trans ·) hδη).trans hreq.symm)
  · intro y hy
    letI : PathConnectedSpace U := isPathConnected_iff_pathConnectedSpace.mp hU.2.1
    let δ : Path.Homotopic.Quotient (⟨x, hx⟩ : U) ⟨y, hy⟩ :=
      ⟦PathConnectedSpace.somePath _ _⟧
    let q : UniversalCover X x₀ :=
      ⟨y, γ.trans (δ.map ⟨Subtype.val, continuous_subtype_val⟩)⟩
    refine ⟨q, ⟨hy, δ, rfl⟩, rfl⟩

end Hatcher.UniversalCover
