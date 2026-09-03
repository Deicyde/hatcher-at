import Hatcher.Covering.Rigidity
import Hatcher.Covering.SubgroupCoverImage

noncomputable section

namespace Hatcher.BasedConnectedCover

universe u w

variable {X : Type u} [TopologicalSpace X] {x₀ : X}

/-- Isomorphism classes of pointed connected covers whose total spaces live
in the same universe as the base. -/
abbrev IsomorphismClasses (X : Type u) [TopologicalSpace X] (x₀ : X) :=
  Quotient (@isomorphicSetoid.{u, u} X _ x₀)

/-- The canonical pointed connected cover realizing a subgroup. -/
abbrev ofSubgroup [PathConnectedSpace X] [LocPathConnectedSpace X]
    [Hatcher.SemilocallySimplyConnectedSpace X]
    (H : Subgroup (FundamentalGroup X x₀)) :
    BasedConnectedCover.{u, u} X x₀ where
  E := Hatcher.SubgroupCover H
  topology := Hatcher.SubgroupCover.instTopologicalSpace H
  proj := Hatcher.SubgroupCover.proj H
  isCoveringMap := Hatcher.SubgroupCover.isCoveringMap_proj H
  basepoint := Hatcher.SubgroupCover.basepoint H
  proj_basepoint := Hatcher.SubgroupCover.proj_basepoint H
  pathConnectedSpace := Hatcher.SubgroupCover.pathConnectedSpace H

private theorem mapOfEq_rfl {A B : Type*}
    [TopologicalSpace A] [TopologicalSpace B] (f : C(A, B)) (a : A) :
    FundamentalGroup.mapOfEq f rfl = FundamentalGroup.map f a := by
  ext γ
  change (CategoryTheory.Iso.refl _).conj ((FundamentalGroup.map f a) γ) = _
  rw [CategoryTheory.Iso.refl_conj]

/-- The canonical subgroup cover has the requested image subgroup. -/
theorem fundamentalGroupRange_ofSubgroup
    [PathConnectedSpace X] [LocPathConnectedSpace X]
    [Hatcher.SemilocallySimplyConnectedSpace X]
    (H : Subgroup (FundamentalGroup X x₀)) :
    (ofSubgroup H).fundamentalGroupRange = H := by
  rw [fundamentalGroupRange]
  have hmap : FundamentalGroup.mapOfEq (ofSubgroup H).projMap
      (ofSubgroup H).proj_basepoint =
      FundamentalGroup.map (ofSubgroup H).projMap (ofSubgroup H).basepoint := by
    have hp : (ofSubgroup H).proj_basepoint = rfl := Subsingleton.elim _ _
    rw [hp]
    exact mapOfEq_rfl _ _
  calc
    _ = (FundamentalGroup.map (ofSubgroup H).projMap
        (ofSubgroup H).basepoint).range := congrArg MonoidHom.range hmap
    _ = H := by
      change (FundamentalGroup.map
        ⟨Hatcher.SubgroupCover.proj H,
          Hatcher.SubgroupCover.continuous_proj H⟩
        (Hatcher.SubgroupCover.basepoint H)).range = H
      exact Hatcher.SubgroupCover.range_map_eq H

/-- Every pointed connected cover, in any universe, is represented by the
canonical small subgroup cover attached to its image subgroup. -/
theorem isomorphic_ofSubgroup_fundamentalGroupRange
    [PathConnectedSpace X] [LocPathConnectedSpace X]
    [Hatcher.SemilocallySimplyConnectedSpace X]
    (C : BasedConnectedCover.{w, u} X x₀) :
    Isomorphic C (ofSubgroup C.fundamentalGroupRange) :=
  (nonempty_iso_iff_range_eq C
    (ofSubgroup C.fundamentalGroupRange)).mpr
      (fundamentalGroupRange_ofSubgroup C.fundamentalGroupRange).symm

/-- The image subgroup descends to pointed-cover isomorphism classes. -/
def fundamentalGroupRangeClass
    [PathConnectedSpace X] [LocPathConnectedSpace X] :
    IsomorphismClasses X x₀ → Subgroup (FundamentalGroup X x₀) :=
  Quotient.lift fundamentalGroupRange fun C D h =>
    (nonempty_iso_iff_range_eq C D).mp
      (show Isomorphic C D from h)

private noncomputable def classificationEquiv_of_subgroupCover_range
    [PathConnectedSpace X] [LocPathConnectedSpace X]
    [Hatcher.SemilocallySimplyConnectedSpace X]
    (hrealize : ∀ H : Subgroup (FundamentalGroup X x₀),
      (ofSubgroup H).fundamentalGroupRange = H) :
    IsomorphismClasses X x₀ ≃ Subgroup (FundamentalGroup X x₀) where
  toFun := fundamentalGroupRangeClass
  invFun H := Quotient.mk (@isomorphicSetoid.{u, u} X _ x₀) (ofSubgroup H)
  left_inv C := by
    induction C using Quotient.inductionOn with
    | _ C =>
        apply Quotient.sound
        change Isomorphic (ofSubgroup C.fundamentalGroupRange) C
        exact (nonempty_iso_iff_range_eq
          (ofSubgroup C.fundamentalGroupRange) C).mpr (hrealize _)
  right_inv H := hrealize H

/-- Fixed-universe classification of pointed connected covers by subgroups of
the fundamental group. Every cover in another universe is represented by a
canonical cover in this universe via `isomorphic_ofSubgroup_fundamentalGroupRange`. -/
noncomputable def classificationEquiv
    [PathConnectedSpace X] [LocPathConnectedSpace X]
    [Hatcher.SemilocallySimplyConnectedSpace X] :
    IsomorphismClasses X x₀ ≃ Subgroup (FundamentalGroup X x₀) :=
  classificationEquiv_of_subgroupCover_range fundamentalGroupRange_ofSubgroup

end Hatcher.BasedConnectedCover
