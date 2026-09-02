import Hatcher.Covering.SubgroupCoverSpace
import Hatcher.Covering.UniversalCoverIsCovering
import Hatcher.Covering.UniversalCoverPathConnected

noncomputable section

open CategoryTheory Set TopologicalSpace Topology

namespace Hatcher.SubgroupCover

universe u

variable {X : Type u} [TopologicalSpace X] {x₀ : X}
variable (H : Subgroup (FundamentalGroup X x₀))

private theorem map_symm
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {a b : A} (f : C(A, B)) (d : Path.Homotopic.Quotient a b) :
    d.symm.map f = (d.map f).symm := by
  induction d using Path.Homotopic.Quotient.ind with
  | mk d => rfl

/-- The quotient map from the path-class space to the subgroup cover. -/
def mk : UniversalCover X x₀ → SubgroupCover H :=
  Quotient.mk (subgroupCoverSetoid H)

@[simp]
theorem proj_mk (q : UniversalCover X x₀) :
    proj H (mk H q) = UniversalCover.proj q :=
  rfl

theorem continuous_proj
    [LocPathConnectedSpace X] [SemilocallySimplyConnectedSpace X] :
    Continuous (proj H) := by
  exact (UniversalCover.continuous_proj (X := X) (x₀ := x₀)).quotient_lift
    (fun a b h ↦ (show subgroupCoverRel H a b from h).choose)

/-- The subgroup-cover quotient is path-connected. -/
instance pathConnectedSpace [PathConnectedSpace X] [LocPathConnectedSpace X]
    [SemilocallySimplyConnectedSpace X] : PathConnectedSpace (SubgroupCover H) :=
  (Quotient.mk_surjective.pathConnectedSpace continuous_quot_mk)

private theorem subgroupCoverRel_trans_right {x y : X}
    (a b : Path.Homotopic.Quotient x₀ x)
    (d : Path.Homotopic.Quotient x y)
    (hab : subgroupCoverRel H ⟨x, a⟩ ⟨x, b⟩) :
    subgroupCoverRel H ⟨y, a.trans d⟩ ⟨y, b.trans d⟩ := by
  rcases hab with ⟨hxx, hab⟩
  refine ⟨rfl, ?_⟩
  simp only [Path.Homotopic.Quotient.cast_rfl_rfl] at hab ⊢
  let a' : FundamentalGroupoid.mk x₀ ⟶ FundamentalGroupoid.mk x := a
  let b' : FundamentalGroupoid.mk x₀ ⟶ FundamentalGroupoid.mk x := b
  let d' : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y := d
  change ((a' ≫ d') ≫ Groupoid.inv (b' ≫ d')) ∈ H
  change (a' ≫ Groupoid.inv b') ∈ H at hab
  simpa [CategoryTheory.Category.assoc] using hab

private theorem subgroupCoverRel_of_trans_right {x y : X}
    (a b : Path.Homotopic.Quotient x₀ x)
    (d : Path.Homotopic.Quotient x y)
    (hab : subgroupCoverRel H ⟨y, a.trans d⟩ ⟨y, b.trans d⟩) :
    subgroupCoverRel H ⟨x, a⟩ ⟨x, b⟩ := by
  rcases hab with ⟨hyy, hab⟩
  refine ⟨rfl, ?_⟩
  simp only [Path.Homotopic.Quotient.cast_rfl_rfl] at hab ⊢
  let a' : FundamentalGroupoid.mk x₀ ⟶ FundamentalGroupoid.mk x := a
  let b' : FundamentalGroupoid.mk x₀ ⟶ FundamentalGroupoid.mk x := b
  let d' : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y := d
  change ((a' ≫ d') ≫ Groupoid.inv (b' ≫ d')) ∈ H at hab
  change (a' ≫ Groupoid.inv b') ∈ H
  simpa [CategoryTheory.Category.assoc] using hab

private theorem subgroupCoverRel_of_mem_basicOpen
    [LocPathConnectedSpace X] [SemilocallySimplyConnectedSpace X]
    {U : Set X} (hU : IsNullhomotopicOpen U)
    {a b q r : UniversalCover X x₀} (haU : a.1 ∈ U) (hbU : b.1 ∈ U)
    (hab : subgroupCoverRel H a b)
    (hqa : q ∈ UniversalCover.basicOpen U haU a.2)
    (hrb : r ∈ UniversalCover.basicOpen U hbU b.2)
    (hqr : q.1 = r.1) : subgroupCoverRel H q r := by
  rcases a with ⟨x, a⟩
  rcases b with ⟨y, b⟩
  rcases q with ⟨z, q⟩
  rcases r with ⟨w, r⟩
  change x ∈ U at haU
  change y ∈ U at hbU
  rcases hab with ⟨hxy, hab⟩
  change x = y at hxy
  subst y
  change z = w at hqr
  subst w
  have hUxy : hbU = haU := Subsingleton.elim _ _
  subst hbU
  obtain ⟨qU, d, hq⟩ := hqa
  let dX : Path.Homotopic.Quotient x z :=
    d.map (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X))
  let s : UniversalCover X x₀ := ⟨z, b.trans dX⟩
  have hs : s ∈ UniversalCover.basicOpen U haU b := ⟨qU, d, rfl⟩
  have hrs : (⟨z, r⟩ : UniversalCover X x₀) = s :=
    (UniversalCover.bijOn_proj_basicOpen hU haU b).injOn hrb hs rfl
  have hbase : subgroupCoverRel H (⟨x, a⟩ : UniversalCover X x₀) ⟨x, b⟩ :=
    ⟨rfl, by simpa only [Path.Homotopic.Quotient.cast_rfl_rfl] using hab⟩
  have hext := subgroupCoverRel_trans_right H a b dX hbase
  have hqs : (⟨z, q⟩ : UniversalCover X x₀) = ⟨z, a.trans dX⟩ := by
    exact congrArg (fun p : Path.Homotopic.Quotient x₀ z ↦
      (⟨z, p⟩ : UniversalCover X x₀)) hq
  rw [hqs, hrs]
  exact hext

private theorem subgroupCoverRel_base_of_mem_basicOpen
    [LocPathConnectedSpace X] [SemilocallySimplyConnectedSpace X]
    {U : Set X} (hU : IsNullhomotopicOpen U)
    {a b q r : UniversalCover X x₀} (haU : a.1 ∈ U) (hbU : b.1 ∈ U)
    (habEnd : a.1 = b.1)
    (hqa : q ∈ UniversalCover.basicOpen U haU a.2)
    (hrb : r ∈ UniversalCover.basicOpen U hbU b.2)
    (hqr : subgroupCoverRel H q r) : subgroupCoverRel H a b := by
  rcases a with ⟨x, a⟩
  rcases b with ⟨y, b⟩
  rcases q with ⟨z, q⟩
  rcases r with ⟨w, r⟩
  change x = y at habEnd
  subst y
  have hUxy : hbU = haU := Subsingleton.elim _ _
  subst hbU
  rcases hqr with ⟨hzw, hqr⟩
  change z = w at hzw
  subst w
  obtain ⟨qU, d, hq⟩ := hqa
  let dX : Path.Homotopic.Quotient x z :=
    d.map (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X))
  let s : UniversalCover X x₀ := ⟨z, b.trans dX⟩
  have hs : s ∈ UniversalCover.basicOpen U haU b := ⟨qU, d, rfl⟩
  have hrs : (⟨z, r⟩ : UniversalCover X x₀) = s :=
    (UniversalCover.bijOn_proj_basicOpen hU haU b).injOn hrb hs rfl
  have hqs : (⟨z, q⟩ : UniversalCover X x₀) = ⟨z, a.trans dX⟩ :=
    congrArg (fun p : Path.Homotopic.Quotient x₀ z ↦
      (⟨z, p⟩ : UniversalCover X x₀)) hq
  have hbs : (⟨z, r⟩ : UniversalCover X x₀) = ⟨z, b.trans dX⟩ := by
    simpa only [s] using hrs
  have hqrRel : subgroupCoverRel H (⟨z, q⟩ : UniversalCover X x₀) ⟨z, r⟩ :=
    ⟨rfl, by simpa only [Path.Homotopic.Quotient.cast_rfl_rfl] using hqr⟩
  have hext : subgroupCoverRel H ⟨z, a.trans dX⟩ ⟨z, b.trans dX⟩ := by
    exact hqs ▸ hbs ▸ hqrRel
  exact subgroupCoverRel_of_trans_right H a b dX hext

private theorem image_basicOpen_eq_of_rel
    [LocPathConnectedSpace X] [SemilocallySimplyConnectedSpace X]
    {U : Set X} (hU : IsNullhomotopicOpen U)
    {a b : UniversalCover X x₀} (haU : a.1 ∈ U) (hbU : b.1 ∈ U)
    (hab : subgroupCoverRel H a b) :
    mk H '' UniversalCover.basicOpen U haU a.2 =
      mk H '' UniversalCover.basicOpen U hbU b.2 := by
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    let hpU : p.1 ∈ U := hp.choose
    obtain ⟨r, hr, hproj⟩ :=
      (UniversalCover.bijOn_proj_basicOpen hU hbU b.2).surjOn hpU
    refine ⟨r, hr, ?_⟩
    exact (Quotient.sound
      (subgroupCoverRel_of_mem_basicOpen H hU haU hbU hab hp hr hproj.symm)).symm
  · rintro ⟨r, hr, rfl⟩
    let hrU : r.1 ∈ U := hr.choose
    obtain ⟨p, hp, hproj⟩ :=
      (UniversalCover.bijOn_proj_basicOpen hU haU a.2).surjOn hrU
    refine ⟨p, hp, ?_⟩
    exact (Quotient.sound (subgroupCoverRel_of_mem_basicOpen H hU hbU haU
      ((subgroupCoverSetoid H).symm hab) hr hp hproj.symm)).symm

private noncomputable def representative (q : SubgroupCover H) : UniversalCover X x₀ :=
  Quotient.out q

@[simp]
private theorem mk_representative (q : SubgroupCover H) :
    mk H (representative H q) = q :=
  Quotient.out_eq q

private theorem proj_representative (q : SubgroupCover H) :
    UniversalCover.proj (representative H q) = proj H q := by
  calc
    UniversalCover.proj (representative H q) = proj H (mk H (representative H q)) :=
      (proj_mk H _).symm
    _ = proj H q := congrArg (proj H) (mk_representative H q)

private theorem isOpen_image_basicOpen
    [LocPathConnectedSpace X] [SemilocallySimplyConnectedSpace X]
    {U : Set X} (hU : IsNullhomotopicOpen U)
    {x : X} (hx : x ∈ U) (a : Path.Homotopic.Quotient x₀ x) :
    IsOpen (mk H '' UniversalCover.basicOpen U hx a) := by
  apply (isQuotientMap_quot_mk (r := (subgroupCoverSetoid H).r)).isOpen_preimage.mp
  rw [UniversalCover.isTopologicalBasis_basicOpen.isOpen_iff]
  intro p hp
  obtain ⟨r, hr, hrp⟩ := hp
  have hrpRel : subgroupCoverRel H r p := Quotient.eq''.mp hrp
  let hrU : r.1 ∈ U := hr.choose
  let hpU : p.1 ∈ U := hrpRel.choose ▸ hrU
  refine ⟨UniversalCover.basicOpen U hpU p.2,
    ⟨U, hU, p.1, hpU, p.2, rfl⟩,
    UniversalCover.self_mem_basicOpen U hpU p.2, ?_⟩
  intro s hs
  have hsame : UniversalCover.basicOpen U hx a =
      UniversalCover.basicOpen U hrU r.2 :=
    UniversalCover.basicOpen_eq_of_mem hx a hrU hr
  let hsU : s.1 ∈ U := hs.choose
  obtain ⟨s', hs', hsProj⟩ :=
    (UniversalCover.bijOn_proj_basicOpen hU hrU r.2).surjOn hsU
  refine ⟨s', ?_, ?_⟩
  · rw [hsame]
    exact hs'
  · apply Quotient.sound
    exact subgroupCoverRel_of_mem_basicOpen H hU hrU hpU hrpRel hs' hs hsProj

private def fiberRepresentativeMem {x : X} {U : Set X} (hx : x ∈ U)
    (e : (proj H) ⁻¹' ({x} : Set X)) : (representative H e.1).1 ∈ U := by
  change UniversalCover.proj (representative H e.1) ∈ U
  rw [proj_representative H e.1, e.2]
  exact hx

private def sheet {x : X} (U : Set X) (hx : x ∈ U)
    (e : (proj H) ⁻¹' ({x} : Set X)) : Set (SubgroupCover H) :=
  mk H '' UniversalCover.basicOpen U (fiberRepresentativeMem H hx e)
    (representative H e.1).2

private theorem isOpen_sheet
    [LocPathConnectedSpace X] [SemilocallySimplyConnectedSpace X]
    {x : X} {U : Set X} (hU : IsNullhomotopicOpen U) (hx : x ∈ U)
    (e : (proj H) ⁻¹' ({x} : Set X)) : IsOpen (sheet H U hx e) :=
  isOpen_image_basicOpen H hU (fiberRepresentativeMem H hx e)
    (representative H e.1).2

private theorem bijOn_proj_sheet
    [LocPathConnectedSpace X] [SemilocallySimplyConnectedSpace X]
    {x : X} {U : Set X} (hU : IsNullhomotopicOpen U) (hx : x ∈ U)
    (e : (proj H) ⁻¹' ({x} : Set X)) :
    Set.BijOn (proj H) (sheet H U hx e) U := by
  let B := UniversalCover.basicOpen U (fiberRepresentativeMem H hx e)
    (representative H e.1).2
  have hB := UniversalCover.bijOn_proj_basicOpen hU
    (fiberRepresentativeMem H hx e) (representative H e.1).2
  refine ⟨?_, ?_, ?_⟩
  · rintro q ⟨p, hp, rfl⟩
    exact hB.mapsTo hp
  · rintro q ⟨p, hp, rfl⟩ r ⟨s, hs, rfl⟩ hproj
    apply congrArg (mk H)
    apply hB.injOn hp hs
    simpa only [proj_mk] using hproj
  · intro y hy
    obtain ⟨p, hp, hproj⟩ := hB.surjOn hy
    refine ⟨mk H p, ⟨p, hp, rfl⟩, ?_⟩
    simpa only [proj_mk] using hproj

private theorem self_mem_sheet
    {x : X} {U : Set X} (hx : x ∈ U)
    (e : (proj H) ⁻¹' ({x} : Set X)) : e.1 ∈ sheet H U hx e := by
  refine ⟨representative H e.1, ?_, mk_representative H e.1⟩
  exact UniversalCover.self_mem_basicOpen U (fiberRepresentativeMem H hx e)
    (representative H e.1).2

theorem discreteTopology_fiber_proj
    [LocPathConnectedSpace X] [SemilocallySimplyConnectedSpace X] (x : X) :
    DiscreteTopology ((proj H) ⁻¹' ({x} : Set X)) := by
  rw [discreteTopology_iff_isOpen_singleton]
  intro e
  obtain ⟨U, hU, hx, -⟩ :=
    Hatcher.isTopologicalBasis_nullhomotopicOpens.exists_subset_of_mem_open
      (show x ∈ (Set.univ : Set X) from Set.mem_univ x) isOpen_univ
  have hopen : IsOpen
      (Subtype.val ⁻¹' sheet H U hx e : Set ((proj H) ⁻¹' ({x} : Set X))) :=
    (isOpen_sheet H hU hx e).preimage continuous_subtype_val
  convert hopen using 1
  ext e'
  constructor
  · intro he'
    rw [Set.mem_singleton_iff] at he'
    subst e'
    exact self_mem_sheet H hx e
  · intro he'
    rw [Set.mem_singleton_iff]
    apply Subtype.ext
    apply (bijOn_proj_sheet H hU hx e).injOn he'
      (self_mem_sheet H hx e)
    exact e'.2.trans e.2.symm

private theorem isOpen_iff_preimage_inter_sheet
    [LocPathConnectedSpace X] [SemilocallySimplyConnectedSpace X]
    {x : X} {U W : Set X} (hU : IsNullhomotopicOpen U) (hWU : W ⊆ U)
    (hx : x ∈ U) (e : (proj H) ⁻¹' ({x} : Set X)) :
    IsOpen W ↔ IsOpen (proj H ⁻¹' W ∩ sheet H U hx e) := by
  constructor
  · intro hW
    exact (hW.preimage (continuous_proj H)).inter (isOpen_sheet H hU hx e)
  · intro hopen
    rw [isOpen_iff_mem_nhds]
    intro y hy
    obtain ⟨q, hq, hqproj⟩ := (bijOn_proj_sheet H hU hx e).surjOn (hWU hy)
    have hqopen : q ∈ proj H ⁻¹' W ∩ sheet H U hx e := by
      refine ⟨?_, hq⟩
      change proj H q ∈ W
      exact hqproj.symm ▸ hy
    let p := representative H q
    have hpopen : p ∈ mk H ⁻¹' (proj H ⁻¹' W ∩ sheet H U hx e) := by
      change mk H p ∈ proj H ⁻¹' W ∩ sheet H U hx e
      simpa only [p, mk_representative] using hqopen
    have hopen' : IsOpen (mk H ⁻¹' (proj H ⁻¹' W ∩ sheet H U hx e)) :=
      hopen.preimage continuous_quot_mk
    obtain ⟨V, hV, hpV, hVsub⟩ :=
      UniversalCover.isTopologicalBasis_basicOpen.exists_subset_of_mem_open hpopen hopen'
    obtain ⟨V, hV, z, hz, a, rfl⟩ := hV
    have hyV : y ∈ V := by
      have hmap := (UniversalCover.bijOn_proj_basicOpen hV hz a).mapsTo hpV
      rw [proj_representative H q] at hmap
      exact hqproj ▸ hmap
    refine mem_nhds_iff.mpr ⟨V, ?_, hV.1, hyV⟩
    intro z hzV
    obtain ⟨r, hr, hrproj⟩ :=
      (UniversalCover.bijOn_proj_basicOpen hV hz a).surjOn hzV
    have hr' := hVsub hr
    have hrW := hr'.1
    change proj H (mk H r) ∈ W at hrW
    rw [proj_mk H, hrproj] at hrW
    exact hrW

private theorem pairwise_disjoint_sheet
    [LocPathConnectedSpace X] [SemilocallySimplyConnectedSpace X]
    {x : X} {U : Set X} (hU : IsNullhomotopicOpen U) (hx : x ∈ U) :
    Pairwise fun e e' : (proj H) ⁻¹' ({x} : Set X) ↦
      Disjoint (sheet H U hx e) (sheet H U hx e') := by
  intro e e' hne
  rw [Set.disjoint_left]
  intro q hqe hqe'
  obtain ⟨a, ha, haq⟩ := hqe
  obtain ⟨b, hb, hbq⟩ := hqe'
  have hab : subgroupCoverRel H a b := Quotient.eq''.mp (haq.trans hbq.symm)
  have hrepEnd : (representative H e.1).1 = (representative H e'.1).1 := by
    change UniversalCover.proj (representative H e.1) =
      UniversalCover.proj (representative H e'.1)
    rw [proj_representative H e.1, proj_representative H e'.1, e.2, e'.2]
  have hrepRel := subgroupCoverRel_base_of_mem_basicOpen H hU
    (fiberRepresentativeMem H hx e) (fiberRepresentativeMem H hx e')
    hrepEnd ha hb hab
  apply hne
  apply Subtype.ext
  calc
    e.1 = mk H (representative H e.1) := (mk_representative H e.1).symm
    _ = mk H (representative H e'.1) := Quotient.sound hrepRel
    _ = e'.1 := mk_representative H e'.1

private theorem preimage_subset_iUnion_sheet
    [LocPathConnectedSpace X] [SemilocallySimplyConnectedSpace X]
    {x : X} {U : Set X} (hU : IsNullhomotopicOpen U) (hx : x ∈ U) :
    proj H ⁻¹' U ⊆ ⋃ e : (proj H) ⁻¹' ({x} : Set X), sheet H U hx e := by
  intro q hqU
  let p := representative H q
  have hpU : p.1 ∈ U := by
    change UniversalCover.proj p ∈ U
    rw [proj_representative H q]
    exact hqU
  letI : PathConnectedSpace U := isPathConnected_iff_pathConnectedSpace.mp hU.2.1
  let d : Path.Homotopic.Quotient (⟨p.1, hpU⟩ : U) ⟨x, hx⟩ :=
    ⟦PathConnectedSpace.somePath _ _⟧
  let dX : Path.Homotopic.Quotient p.1 x :=
    d.map (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X))
  let a : UniversalCover X x₀ := ⟨x, p.2.trans dX⟩
  let e : (proj H) ⁻¹' ({x} : Set X) := ⟨mk H a, rfl⟩
  apply Set.mem_iUnion.mpr
  refine ⟨e, ?_⟩
  have hp : p ∈ UniversalCover.basicOpen U hx a.2 := by
    refine ⟨hpU, d.symm, ?_⟩
    dsimp only [a, dX]
    rw [map_symm, Path.Homotopic.Quotient.trans_assoc,
      Path.Homotopic.Quotient.trans_symm, Path.Homotopic.Quotient.trans_refl]
  have hrepEq : mk H (representative H e.1) = mk H a := by
    calc
      mk H (representative H e.1) = e.1 := mk_representative H e.1
      _ = mk H a := rfl
  have hrepRel : subgroupCoverRel H (representative H e.1) a :=
    Quotient.eq''.mp hrepEq
  rw [sheet, image_basicOpen_eq_of_rel H hU (fiberRepresentativeMem H hx e) hx hrepRel]
  exact ⟨p, hp, mk_representative H q⟩

theorem surjective_proj [PathConnectedSpace X] : Function.Surjective (proj H) := by
  intro x
  obtain ⟨q, hq⟩ := UniversalCover.surjective_proj (x₀ := x₀) x
  refine ⟨mk H q, ?_⟩
  simpa only [proj_mk] using hq

/-- The endpoint projection from the covering associated to `H` is a covering map. -/
theorem isCoveringMap_proj
    [PathConnectedSpace X] [LocPathConnectedSpace X]
    [SemilocallySimplyConnectedSpace X] : IsCoveringMap (proj H) := by
  intro x
  obtain ⟨U, hU, hx, -⟩ :=
    Hatcher.isTopologicalBasis_nullhomotopicOpens.exists_subset_of_mem_open
      (show x ∈ (Set.univ : Set X) from Set.mem_univ x) isOpen_univ
  let F := (proj H) ⁻¹' ({x} : Set X)
  letI : Nonempty (SubgroupCover H) := ⟨basepoint H⟩
  letI : Nonempty F := by
    obtain ⟨q, hq⟩ := surjective_proj H x
    exact ⟨⟨q, hq⟩⟩
  letI : DiscreteTopology F := discreteTopology_fiber_proj H x
  let t : Bundle.Trivialization F (proj H) :=
    hU.1.trivializationDiscrete
      (sheet H U hx) U
      (fun e _ hWU ↦ isOpen_iff_preimage_inter_sheet H hU hWU hx e)
      (fun e ↦ (bijOn_proj_sheet H hU hx e).injOn)
      (fun e ↦ (bijOn_proj_sheet H hU hx e).surjOn)
      (pairwise_disjoint_sheet H hU hx)
      (preimage_subset_iUnion_sheet H hU hx)
  apply IsEvenlyCovered.of_trivialization (t := t)
  simpa [t] using hx

end Hatcher.SubgroupCover
