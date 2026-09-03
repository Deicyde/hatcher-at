import Hatcher.Covering.Monodromy
import Hatcher.Covering.SubgroupCoverIsCovering

noncomputable section

open Set Topology

namespace Hatcher.SubgroupCover

universe u

variable {X : Type u} [TopologicalSpace X] {x₀ : X}
variable (H : Subgroup (FundamentalGroup X x₀))

private theorem mk_loop_eq_basepoint_iff (g : FundamentalGroup X x₀) :
    mk H ⟨x₀, g.toPath⟩ = basepoint H ↔ g ∈ H := by
  rw [show basepoint H = mk H (UniversalCover.basepoint (X := X) (x₀ := x₀)) from rfl]
  change (Quotient.mk (subgroupCoverSetoid H)
      (⟨x₀, g.toPath⟩ : UniversalCover X x₀) =
    Quotient.mk (subgroupCoverSetoid H)
      (UniversalCover.basepoint (X := X) (x₀ := x₀)) ↔ g ∈ H)
  rw [Quotient.eq'']
  change subgroupCoverRel H ⟨x₀, g.toPath⟩
    (UniversalCover.basepoint (X := X) (x₀ := x₀)) ↔ g ∈ H
  constructor
  · rintro ⟨h, hg⟩
    cases h
    change FundamentalGroup.fromPath
      (g.toPath.trans (Path.Homotopic.Quotient.refl x₀).symm) ∈ H at hg
    rw [show (Path.Homotopic.Quotient.refl x₀).symm =
      Path.Homotopic.Quotient.refl x₀ by rfl,
      Path.Homotopic.Quotient.trans_refl] at hg
    exact hg
  · intro hg
    refine ⟨rfl, ?_⟩
    change FundamentalGroup.fromPath
      (g.toPath.trans (Path.Homotopic.Quotient.refl x₀).symm) ∈ H
    rw [show (Path.Homotopic.Quotient.refl x₀).symm =
      Path.Homotopic.Quotient.refl x₀ by rfl,
      Path.Homotopic.Quotient.trans_refl]
    exact hg

private def subgroupLift [LocPathConnectedSpace X]
    [SemilocallySimplyConnectedSpace X] (g : Path x₀ x₀) :
    Path (basepoint H)
      (mk H ⟨x₀, Path.Homotopic.Quotient.mk g⟩) :=
  (UniversalCover.initialSegmentPath g).map continuous_quot_mk

private theorem subgroupLift_map [LocPathConnectedSpace X]
    [SemilocallySimplyConnectedSpace X] (g : Path x₀ x₀) :
    (subgroupLift H g).map (continuous_proj H) = g := by
  ext t
  rfl

private theorem monodromy_basepoint [PathConnectedSpace X]
    [LocPathConnectedSpace X] [SemilocallySimplyConnectedSpace X]
    (g : FundamentalGroup X x₀) :
    (isCoveringMap_proj H).monodromyPerm x₀ g ⟨basepoint H, rfl⟩ =
      ⟨mk H ⟨x₀, g.toPath⟩, rfl⟩ := by
  obtain ⟨g⟩ := g
  let d := subgroupLift H g
  have hmap : (Path.Homotopic.Quotient.mk d).map
      ⟨proj H, (isCoveringMap_proj H).continuous⟩ =
      Path.Homotopic.Quotient.mk g := by
    rw [← Path.Homotopic.Quotient.mk_map]
    exact congrArg Path.Homotopic.Quotient.mk (subgroupLift_map H g)
  change (isCoveringMap_proj H).monodromy (Path.Homotopic.Quotient.mk g)
    ⟨basepoint H, rfl⟩ = ⟨mk H ⟨x₀, Path.Homotopic.Quotient.mk g⟩, rfl⟩
  apply Subtype.ext
  have hm := congrArg Subtype.val
    ((isCoveringMap_proj H).monodromy_map (Path.Homotopic.Quotient.mk d))
  rw [hmap] at hm
  convert hm using 1
  congr 2

/-- The subgroup covering realizes the subgroup used in its construction. -/
theorem range_map_eq [PathConnectedSpace X] [LocPathConnectedSpace X]
    [SemilocallySimplyConnectedSpace X] :
    (FundamentalGroup.map
      ⟨proj H, (isCoveringMap_proj H).continuous⟩ (basepoint H)).range = H := by
  ext g
  rw [Hatcher.Covering.mem_range_map_iff_monodromy_fixed
    (isCoveringMap_proj H) (basepoint H) g]
  change (isCoveringMap_proj H).monodromyPerm x₀ g
      (⟨basepoint H, rfl⟩ : (proj H) ⁻¹' ({x₀} : Set X)) =
    (⟨basepoint H, rfl⟩ : (proj H) ⁻¹' ({x₀} : Set X)) ↔ g ∈ H
  rw [monodromy_basepoint H g]
  rw [Subtype.mk.injEq]
  exact mk_loop_eq_basepoint_iff H g

end Hatcher.SubgroupCover
