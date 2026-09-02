import Hatcher.Covering.UniversalCoverIsCovering
import Hatcher.Covering.UniversalCoverPathConnected
import Mathlib.Topology.Homotopy.Lifting

noncomputable section

open Set Topology TopologicalSpace
open scoped unitInterval

namespace Hatcher.UniversalCover

universe u

variable {X : Type u} [TopologicalSpace X] {x₀ : X}

private theorem projected_path_eq_coordinate
    [PathConnectedSpace X] [LocPathConnectedSpace X]
    [SemilocallySimplyConnectedSpace X]
    {y : X} (q : Path.Homotopic.Quotient x₀ y)
    (γ : Path (basepoint (X := X) (x₀ := x₀)) ⟨y, q⟩) :
    Path.Homotopic.Quotient.mk
        (γ.map (continuous_proj (X := X) (x₀ := x₀))) = q := by
  let δ : Path x₀ y := γ.map (continuous_proj (X := X) (x₀ := x₀))
  let Γ : Path (basepoint (X := X) (x₀ := x₀))
      ⟨y, Path.Homotopic.Quotient.mk δ⟩ := initialSegmentPath δ
  have hΓ : (γ : I → UniversalCover X x₀) = Γ := by
    exact (isCoveringMap_proj (X := X) (x₀ := x₀)).eq_of_comp_eq
      γ.continuous Γ.continuous (by funext t; rfl) 0
      (γ.source.trans Γ.source.symm)
  have hend := congr_fun hΓ 1
  have hp : (⟨y, q⟩ : UniversalCover X x₀) =
      ⟨y, Path.Homotopic.Quotient.mk δ⟩ := by
    exact γ.target.symm.trans (hend.trans Γ.target)
  injection hp with _ hq
  change Path.Homotopic.Quotient.mk δ = q
  exact hq.symm

private theorem projected_path_eq_coordinate'
    [PathConnectedSpace X] [LocPathConnectedSpace X]
    [SemilocallySimplyConnectedSpace X]
    (q : UniversalCover X x₀)
    (γ : Path (basepoint (X := X) (x₀ := x₀)) q) :
    Path.Homotopic.Quotient.mk
        (γ.map (continuous_proj (X := X) (x₀ := x₀))) = q.2 := by
  rcases q with ⟨y, q⟩
  exact projected_path_eq_coordinate q γ

private theorem projected_loop_eq_refl
    [PathConnectedSpace X] [LocPathConnectedSpace X]
    [SemilocallySimplyConnectedSpace X]
    (e : UniversalCover X x₀) (γ : Path e e) :
    Path.Homotopic.Quotient.mk
        (γ.map (continuous_proj (X := X) (x₀ := x₀))) =
      Path.Homotopic.Quotient.refl (proj e) := by
  let η : Path (basepoint (X := X) (x₀ := x₀)) e :=
    PathConnectedSpace.somePath _ _
  let ηX : Path x₀ (proj e) :=
    η.map (continuous_proj (X := X) (x₀ := x₀))
  let γX : Path (proj e) (proj e) :=
    γ.map (continuous_proj (X := X) (x₀ := x₀))
  let ηγX : Path x₀ (proj e) :=
    (η.trans γ).map (continuous_proj (X := X) (x₀ := x₀))
  let a : Path.Homotopic.Quotient x₀ (proj e) :=
    Path.Homotopic.Quotient.mk ηX
  let b : Path.Homotopic.Quotient (proj e) (proj e) :=
    Path.Homotopic.Quotient.mk γX
  have ha : a = e.2 := projected_path_eq_coordinate' e η
  have hab : a.trans b = e.2 := by
    have hmap : ηγX = ηX.trans γX := by
      exact Path.map_trans η γ _
    rw [← Path.Homotopic.Quotient.mk_trans]
    rw [← hmap]
    exact projected_path_eq_coordinate' e (η.trans γ)
  have hab' : a.trans b = a := ha ▸ hab
  have hcancel := congrArg (fun z => a.symm.trans z) hab'
  change b = Path.Homotopic.Quotient.refl (proj e)
  simpa [← Path.Homotopic.Quotient.trans_assoc] using hcancel

/-- The path-class universal cover is simply connected. -/
theorem simplyConnectedSpace
    [PathConnectedSpace X] [LocPathConnectedSpace X]
    [SemilocallySimplyConnectedSpace X] :
    SimplyConnectedSpace (UniversalCover X x₀) := by
  rw [simply_connected_iff_loops_nullhomotopic]
  refine ⟨inferInstance, ?_⟩
  intro e γ
  rw [← Path.Homotopic.Quotient.eq]
  let c : C(UniversalCover X x₀, X) :=
    ⟨proj, continuous_proj (X := X) (x₀ := x₀)⟩
  apply (isCoveringMap_proj (X := X) (x₀ := x₀)).injective_path_homotopic_map
  calc
    (Path.Homotopic.Quotient.mk γ).map c =
        Path.Homotopic.Quotient.mk (γ.map c.continuous) :=
      (Path.Homotopic.Quotient.mk_map γ c).symm
    _ = Path.Homotopic.Quotient.refl (proj e) :=
      projected_loop_eq_refl e γ
    _ = (Path.Homotopic.Quotient.mk (Path.refl e)).map c := by
      rfl

end Hatcher.UniversalCover
