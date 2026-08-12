/-
Hatcher, *Algebraic Topology*, §1.1, inside the proof of Theorem 1.9 (page 31).

There is no retraction `D² → S¹`. Hatcher phrases this through induced
homomorphisms: a retraction would factor the identity of `π₁(S¹) ≅ ℤ` through
`π₁(D²) = 0`. This file runs the same argument directly on path classes, since
the pinned Mathlib has `FundamentalGroup.map` but no functoriality lemmas for
it.

Concretely: the boundary loop `ω` becomes nullhomotopic once pushed into the
disc, because the disc is convex and hence contractible. Pushing that
nullhomotopy back down through the retraction would make `ω` nullhomotopic in
`S¹`, contradicting that its winding number is one.
-/
import Hatcher.Circle.FundamentalGroup
import Mathlib.Analysis.Normed.Module.Convex

open Real unitInterval

namespace Hatcher.Disc

/-- Hatcher's `D²`, the closed unit disc in `ℂ`. -/
abbrev unitDisc : Set ℂ := Metric.closedBall 0 1

instance : ContractibleSpace unitDisc :=
  (convex_closedBall (0 : ℂ) 1).contractibleSpace ⟨0, by simp⟩

/-- The boundary inclusion `S¹ ↪ D²`. -/
noncomputable def incl : C(_root_.Circle, unitDisc) where
  toFun z := ⟨(z : ℂ), by
    simp only [unitDisc, Metric.mem_closedBall, dist_zero_right]
    exact (Circle.norm_coe z).le⟩
  continuous_toFun := by fun_prop

@[simp] theorem incl_coe (z : _root_.Circle) : ((incl z : unitDisc) : ℂ) = (z : ℂ) := rfl

/-- **Hatcher, §1.1, page 31.** `S¹` is not a retract of `D²`. -/
theorem not_exists_retraction :
    ¬ ∃ r : C(unitDisc, _root_.Circle), ∀ z : _root_.Circle, r (incl z) = z := by
  rintro ⟨r, hr⟩
  set ω : Path (1 : _root_.Circle) 1 := Hatcher.Circle.loopOfInt 1 with hω
  have hr1 : r (incl 1) = 1 := hr 1
  -- pushed into the disc, ω is nullhomotopic: the disc is contractible
  have h1 : (Path.Homotopic.Quotient.mk (ω.map incl.continuous) :
        Path.Homotopic.Quotient (incl 1) (incl 1))
      = Path.Homotopic.Quotient.mk (Path.refl (incl 1)) := Subsingleton.elim _ _
  -- push the nullhomotopy back down through the retraction
  have h2 : Path.Homotopic.Quotient.mk ((ω.map incl.continuous).map r.continuous)
      = Path.Homotopic.Quotient.mk ((Path.refl (incl 1)).map r.continuous) := by
    rw [Path.Homotopic.Quotient.mk_map (ω.map incl.continuous) r,
        Path.Homotopic.Quotient.mk_map (Path.refl (incl 1)) r, h1]
  -- both sides live in `Path (r (incl 1)) (r (incl 1))`; transport to `Path 1 1`
  have hleft : ω = ((ω.map incl.continuous).map r.continuous).cast hr1.symm hr1.symm :=
    DFunLike.ext _ _ fun t => by
      rw [show (((ω.map incl.continuous).map r.continuous).cast hr1.symm hr1.symm) t
        = ((ω.map incl.continuous).map r.continuous) t from congr_fun (Path.cast_coe _ _ _) t]
      exact (hr (ω t)).symm
  have hright : Path.refl (1 : _root_.Circle)
      = ((Path.refl (incl 1)).map r.continuous).cast hr1.symm hr1.symm :=
    DFunLike.ext _ _ fun t => by
      rw [show (((Path.refl (incl 1)).map r.continuous).cast hr1.symm hr1.symm) t
        = ((Path.refl (incl 1)).map r.continuous) t from congr_fun (Path.cast_coe _ _ _) t]
      exact hr1.symm
  -- so ω is nullhomotopic in S¹ itself
  have hnull : (Path.Homotopic.Quotient.mk ω : Path.Homotopic.Quotient (1 : _root_.Circle) 1)
      = Path.Homotopic.Quotient.mk (Path.refl 1) := by
    rw [hleft, hright]
    show (Path.Homotopic.Quotient.mk ((ω.map incl.continuous).map r.continuous)).cast _ _
      = (Path.Homotopic.Quotient.mk ((Path.refl (incl 1)).map r.continuous)).cast _ _
    rw [h2]
  -- but its winding number is one
  have : (1 : ℤ) = 0 :=
    calc (1 : ℤ)
        = Hatcher.Circle.windingNumberFun
            (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk ω)) :=
          Hatcher.Circle.windingNumberFun_loopOfInt_one.symm
      _ = Hatcher.Circle.windingNumberFun
            (FundamentalGroup.fromPath
              (Path.Homotopic.Quotient.mk (Path.refl (1 : _root_.Circle)))) := by rw [hnull]
      _ = 0 := Hatcher.Circle.windingNumberFun_one
  exact one_ne_zero this

end Hatcher.Disc
