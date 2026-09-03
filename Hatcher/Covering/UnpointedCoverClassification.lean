import Hatcher.Covering.BasepointChange
import Hatcher.Covering.PointedCoverClassification

noncomputable section

open Function Set Topology
open scoped Pointwise

namespace Hatcher.ConnectedCover

universe u v w

variable {X : Type v} [TopologicalSpace X] {x₀ : X}

/-- Two subgroups are equivalent when they lie in the same conjugation orbit. -/
abbrev SubgroupConjugacySetoid (G : Type u) [Group G] : Setoid (Subgroup G) :=
  MulAction.orbitRel (ConjAct G) (Subgroup G)

/-- Conjugacy classes of subgroups of a group. -/
abbrev SubgroupConjugacyClasses (G : Type u) [Group G] :=
  Quotient (SubgroupConjugacySetoid G)

/-- The conjugacy relation in its native orbit orientation. -/
theorem subgroupConjugacy_iff_native {G : Type u} [Group G] (H K : Subgroup G) :
    SubgroupConjugacySetoid G H K ↔
      ∃ g : G, H = K.map (MulAut.conj g) := by
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨ConjAct.ofConjAct g, by
      rw [Subgroup.pointwise_smul_def]
      rfl⟩
  · rintro ⟨g, rfl⟩
    refine ⟨ConjAct.toConjAct g, ?_⟩
    rw [Subgroup.pointwise_smul_def]
    rfl

/-- The conjugacy relation in the orientation used by basepoint change. -/
theorem subgroupConjugacy_iff {G : Type u} [Group G] (H K : Subgroup G) :
    SubgroupConjugacySetoid G H K ↔
      ∃ g : G, K = H.map (MulAut.conj g) := by
  constructor
  · intro h
    exact (subgroupConjugacy_iff_native K H).mp <|
      (SubgroupConjugacySetoid G).symm h
  · intro h
    exact (SubgroupConjugacySetoid G).symm <|
      (subgroupConjugacy_iff_native K H).mpr h

/-- Isomorphism classes of connected covers whose total spaces live in the
same universe as the base. -/
abbrev IsomorphismClasses (X : Type u) [TopologicalSpace X] :=
  Quotient (@isomorphicSetoid.{u, u} X _)

/-- Regard a connected cover as pointed at a specified point of the fiber. -/
def basedAt (C : ConnectedCover.{u, v} X) (e : C.proj ⁻¹' {x₀}) :
    BasedConnectedCover.{u, v} X x₀ where
  E := C.E
  topology := C.topology
  proj := C.proj
  isCoveringMap := C.isCoveringMap
  basepoint := e.1
  proj_basepoint := Set.mem_singleton_iff.mp e.2
  pathConnectedSpace := C.pathConnectedSpace

/-- The projection of a connected cover onto a path-connected base is surjective. -/
theorem surjective_proj [PathConnectedSpace X] (C : ConnectedCover.{u, v} X) :
    Function.Surjective C.proj := by
  intro x
  let e₀ : C.E := Classical.choice (inferInstance : Nonempty C.E)
  let γ : Path (C.proj e₀) x := PathConnectedSpace.somePath _ _
  let Γ := C.isCoveringMap.liftPath γ e₀ γ.source
  refine ⟨Γ 1, ?_⟩
  exact (congrFun (C.isCoveringMap.liftPath_lifts γ e₀ γ.source) 1).trans γ.target

/-- A chosen point over the basepoint. -/
def chosenFiberPoint [PathConnectedSpace X] (C : ConnectedCover.{u, v} X) :
    C.proj ⁻¹' {x₀} :=
  ⟨Classical.choose (C.surjective_proj x₀),
    Set.mem_singleton_iff.mpr (Classical.choose_spec (C.surjective_proj x₀))⟩

/-- An unpointed cover isomorphism becomes pointed after transporting the source point. -/
def Iso.toBasedIso {C : ConnectedCover.{u, v} X} {D : ConnectedCover.{w, v} X}
    (F : C.Iso D) (e : C.proj ⁻¹' {x₀}) :
    (C.basedAt e).Iso
      (D.basedAt ⟨F e.1, Set.mem_singleton_iff.mpr <|
        (F.proj_apply e.1).trans (Set.mem_singleton_iff.mp e.2)⟩) where
  toHomeomorph := F.toHomeomorph
  proj_comp := F.proj_comp
  map_basepoint := rfl

/-- Forgetting a pointed-cover isomorphism gives an unpointed one. -/
def _root_.Hatcher.BasedConnectedCover.Iso.toConnectedCoverIso
    {C : BasedConnectedCover.{u, v} X x₀}
    {D : BasedConnectedCover.{w, v} X x₀} (F : C.Iso D) :
    C.toConnectedCover.Iso D.toConnectedCover where
  toHomeomorph := F.toHomeomorph
  proj_comp := F.proj_comp

/-- An unpointed isomorphism makes the image subgroups at arbitrary fiber
points conjugate. -/
theorem exists_conj_fundamentalGroupRange_eq_of_iso
    [PathConnectedSpace X] [LocPathConnectedSpace X]
    {C : ConnectedCover.{u, v} X} {D : ConnectedCover.{w, v} X}
    (F : C.Iso D) (c : C.proj ⁻¹' {x₀}) (d : D.proj ⁻¹' {x₀}) :
    ∃ g : FundamentalGroup X x₀,
      (D.basedAt d).fundamentalGroupRange =
        (C.basedAt c).fundamentalGroupRange.map (MulAut.conj g) := by
  let Fc : D.proj ⁻¹' {x₀} :=
    ⟨F c.1, Set.mem_singleton_iff.mpr <|
      (F.proj_apply c.1).trans (Set.mem_singleton_iff.mp c.2)⟩
  let α : Path Fc.1 d.1 := PathConnectedSpace.somePath _ _
  let g := Hatcher.Covering.projectedPathClass D.isCoveringMap Fc d α
  refine ⟨g, ?_⟩
  have hIso : (C.basedAt c).fundamentalGroupRange =
      (D.basedAt Fc).fundamentalGroupRange :=
    (Hatcher.BasedConnectedCover.nonempty_iso_iff_range_eq
      (C.basedAt c) (D.basedAt Fc)).mp ⟨F.toBasedIso c⟩
  have hChange := Hatcher.Covering.range_mapOfEq_basepointChange
    D.isCoveringMap Fc d α
  change (D.basedAt d).fundamentalGroupRange =
    (D.basedAt Fc).fundamentalGroupRange.map (MulAut.conj g) at hChange
  simpa [hIso] using hChange

/-- Conjugate subgroups give isomorphic unpointed canonical covers. -/
theorem isomorphic_toConnectedCover_of_eq_map_conj
    {X : Type u} [TopologicalSpace X] {x₀ : X}
    [PathConnectedSpace X] [LocPathConnectedSpace X]
    [Hatcher.SemilocallySimplyConnectedSpace X]
    (H K : Subgroup (FundamentalGroup X x₀)) (g : FundamentalGroup X x₀)
    (hK : K = H.map (MulAut.conj g)) :
    ConnectedCover.Isomorphic
      (Hatcher.BasedConnectedCover.ofSubgroup H).toConnectedCover
      (Hatcher.BasedConnectedCover.ofSubgroup K).toConnectedCover := by
  let C := Hatcher.BasedConnectedCover.ofSubgroup H
  let e₀ : C.proj ⁻¹' {x₀} :=
    ⟨C.basepoint, Set.mem_singleton_iff.mpr C.proj_basepoint⟩
  obtain ⟨e₁, he₁⟩ := Hatcher.Covering.exists_basepoint_range_eq_map_conj
    C.isCoveringMap e₀ g
  let C₁ := C.toConnectedCover.basedAt e₁
  have hC₁ : C₁.fundamentalGroupRange =
      C.fundamentalGroupRange.map (MulAut.conj g) := he₁
  have hRange : C₁.fundamentalGroupRange =
      (Hatcher.BasedConnectedCover.ofSubgroup K).fundamentalGroupRange := by
    calc
      C₁.fundamentalGroupRange = C.fundamentalGroupRange.map (MulAut.conj g) := hC₁
      _ = H.map (MulAut.conj g) := by
        rw [Hatcher.BasedConnectedCover.fundamentalGroupRange_ofSubgroup H]
      _ = K := hK.symm
      _ = (Hatcher.BasedConnectedCover.ofSubgroup K).fundamentalGroupRange :=
        (Hatcher.BasedConnectedCover.fundamentalGroupRange_ofSubgroup K).symm
  obtain ⟨F⟩ := (Hatcher.BasedConnectedCover.nonempty_iso_iff_range_eq C₁
    (Hatcher.BasedConnectedCover.ofSubgroup K)).mpr hRange
  exact ⟨F.toConnectedCoverIso⟩

/-- Every connected cover, in any universe, is unpointedly isomorphic to the
canonical cover of the subgroup obtained from a chosen point over `x₀`. -/
theorem isomorphic_ofSubgroup_chosenRange
    {X : Type u} [TopologicalSpace X] (x₀ : X)
    [PathConnectedSpace X] [LocPathConnectedSpace X]
    [Hatcher.SemilocallySimplyConnectedSpace X]
    (C : ConnectedCover.{w, u} X) :
    ConnectedCover.Isomorphic C
      (Hatcher.BasedConnectedCover.ofSubgroup
        (C.basedAt (C.chosenFiberPoint (x₀ := x₀))).fundamentalGroupRange).toConnectedCover := by
  obtain ⟨F⟩ := Hatcher.BasedConnectedCover.isomorphic_ofSubgroup_fundamentalGroupRange
    (C.basedAt (C.chosenFiberPoint (x₀ := x₀)))
  exact ⟨F.toConnectedCoverIso⟩

section Classification

variable {X : Type u} [TopologicalSpace X]

/-- The image subgroup, modulo conjugacy, of an unpointed connected cover. -/
private noncomputable def fundamentalGroupRangeConjugacyClass
    [PathConnectedSpace X] [LocPathConnectedSpace X] (x₀ : X) :
    IsomorphismClasses X → SubgroupConjugacyClasses (FundamentalGroup X x₀) :=
  Quotient.lift
    (fun C ↦ Quotient.mk (SubgroupConjugacySetoid (FundamentalGroup X x₀))
      (C.basedAt (C.chosenFiberPoint (x₀ := x₀))).fundamentalGroupRange)
    (fun C D h ↦ Quotient.sound <| (subgroupConjugacy_iff _ _).mpr <|
      exists_conj_fundamentalGroupRange_eq_of_iso h.some
        (C.chosenFiberPoint (x₀ := x₀)) (D.chosenFiberPoint (x₀ := x₀)))

/-- The unpointed canonical cover attached to a subgroup descends to a
conjugacy class of subgroups. -/
private noncomputable def coverClassOfSubgroupConjugacyClass
    [PathConnectedSpace X] [LocPathConnectedSpace X]
    [Hatcher.SemilocallySimplyConnectedSpace X] (x₀ : X) :
    SubgroupConjugacyClasses (FundamentalGroup X x₀) → IsomorphismClasses X :=
  Quotient.lift
    (fun H ↦ Quotient.mk (@isomorphicSetoid.{u, u} X _)
      (Hatcher.BasedConnectedCover.ofSubgroup H).toConnectedCover)
    (fun H K h ↦ by
      obtain ⟨g, hK⟩ := (subgroupConjugacy_iff H K).mp h
      exact Quotient.sound (isomorphic_toConnectedCover_of_eq_map_conj H K g hK))

/-- Fixed-universe classification of connected covers by conjugacy classes of
subgroups of the fundamental group. -/
noncomputable def classificationEquivConjClasses
    [PathConnectedSpace X] [LocPathConnectedSpace X]
    [Hatcher.SemilocallySimplyConnectedSpace X] (x₀ : X) :
    IsomorphismClasses X ≃ SubgroupConjugacyClasses (FundamentalGroup X x₀) where
  toFun := fundamentalGroupRangeConjugacyClass x₀
  invFun := coverClassOfSubgroupConjugacyClass x₀
  left_inv q := by
    induction q using Quotient.inductionOn with
    | _ C =>
        apply Quotient.sound
        obtain ⟨F⟩ := isomorphic_ofSubgroup_chosenRange x₀ C
        exact ⟨F.symm⟩
  right_inv q := by
    induction q using Quotient.inductionOn with
    | _ H =>
        apply Quotient.sound
        let C := Hatcher.BasedConnectedCover.ofSubgroup H
        let c : C.proj ⁻¹' {x₀} :=
          C.toConnectedCover.chosenFiberPoint (x₀ := x₀)
        let d : C.proj ⁻¹' {x₀} :=
          ⟨C.basepoint, Set.mem_singleton_iff.mpr C.proj_basepoint⟩
        obtain ⟨g, hg⟩ := exists_conj_fundamentalGroupRange_eq_of_iso
          (Iso.refl C.toConnectedCover) c d
        apply (subgroupConjugacy_iff _ _).mpr
        refine ⟨g, ?_⟩
        calc
          H = C.fundamentalGroupRange :=
            (Hatcher.BasedConnectedCover.fundamentalGroupRange_ofSubgroup H).symm
          _ = (C.toConnectedCover.basedAt d).fundamentalGroupRange := by rfl
          _ = (C.toConnectedCover.basedAt c).fundamentalGroupRange.map
              (MulAut.conj g) := hg

end Classification

end Hatcher.ConnectedCover
