/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Hatcher.Euclidean.LocalHomology
import Mathlib.Algebra.Category.Grp.Zero

/-!
# Invariance of dimension for Euclidean open sets

Integral local homology detects the dimension of every nonempty open subset of
Euclidean space.  Dimension zero is handled separately, by the elementary fact
that a nonempty open subset of positive-dimensional Euclidean space has two
distinct points.
-/

noncomputable section

set_option maxHeartbeats 800000

open CategoryTheory Limits Set
open scoped EuclideanSpace

namespace Hatcher.Euclidean

universe w v u

/-- A nonempty open subset of positive-dimensional Euclidean space contains
two distinct points. -/
private theorem not_subsingleton_open_positive
    (d : ℕ) (U : Set (EuclideanSpace ℝ (Fin (d + 1))))
    (hU : IsOpen U) (hne : U.Nonempty) : ¬ Subsingleton U := by
  rintro hsub
  obtain ⟨x, hx⟩ := hne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU x hx
  let w : EuclideanSpace ℝ (Fin (d + 1)) :=
    EuclideanSpace.single 0 (ε / 2)
  have hw_ne : w ≠ 0 := by
    intro hw
    have hnorm := congrArg norm hw
    have hhalf : ε / 2 = 0 := by
      simpa [w, Real.norm_eq_abs,
        abs_of_pos (half_pos hε)] using hnorm
    linarith
  have hxw_ball : x + w ∈ Metric.ball x ε := by
    rw [Metric.mem_ball]
    calc
      dist (x + w) x = dist (x + w) (x + 0) := by rw [add_zero]
      _ = dist w 0 := dist_add_left x w 0
      _ = ‖w‖ := by simp
      _ = ε / 2 := by
        simp [w, Real.norm_eq_abs, abs_of_nonneg hε.le]
      _ < ε := by linarith
  have hxw : x + w ∈ U := hball hxw_ball
  have hpoints : (⟨x + w, hxw⟩ : U) = ⟨x, hx⟩ :=
    @Subsingleton.elim U hsub _ _
  have hval := congrArg Subtype.val hpoints
  have hw : w = 0 := by
    have htranslated := congrArg
      (fun z : EuclideanSpace ℝ (Fin (d + 1)) => -x + z) hval
    simpa [add_assoc] using htranslated
  exact hw_ne hw

/-- Vanishing of local homology transports between the ambient spaces of
homeomorphic open neighborhoods.  Keeping the target category abstract makes
the three canonical isomorphisms explicit without unfolding its instances. -/
private theorem isZero_ambientLocalHomology_of_homeomorphic_open
    {X Y : TopCat.{w}} [T1Space X] [T1Space Y]
    (U : Set X) (V : Set Y) (hU : IsOpen U) (hV : IsOpen V)
    (f : U ≃ₜ V) (x : U)
    {C : Type u} [Category.{v} C] [Preadditive C]
    [HasCoproducts.{w} C] [CategoryWithHomology C]
    (R : C) (i : ℕ)
    (hY : IsZero ((Hatcher.Relative.homologyFunctor R i).obj
      (Hatcher.Relative.puncturedPair Y (f x).1))) :
    IsZero ((Hatcher.Relative.homologyFunctor R i).obj
      (Hatcher.Relative.puncturedPair X x.1)) := by
  let mapU := Hatcher.Relative.localHomologyOpenNeighborhoodMap
    (X := X) x.1 U x.2 R i
  let mapV := Hatcher.Relative.localHomologyOpenNeighborhoodMap
    (X := Y) (f x).1 V (f x).2 R i
  let _ : IsIso mapU :=
    Hatcher.Relative.localHomologyOpenNeighborhoodMap_isIso_of_t1
      x.1 U x.2 hU R i
  let _ : IsIso mapV :=
    Hatcher.Relative.localHomologyOpenNeighborhoodMap_isIso_of_t1
      (f x).1 V (f x).2 hV R i
  have hVlocal : IsZero ((Hatcher.Relative.homologyFunctor R i).obj
      (Hatcher.Relative.puncturedPair (TopCat.of V) (f x))) :=
    IsZero.of_mono mapV hY
  let pairIso := Hatcher.Relative.puncturedPairHomologyIso
    (X := TopCat.of U) (Y := TopCat.of V) (x := x) (y := f x)
    f rfl R i
  have hUlocal : IsZero ((Hatcher.Relative.homologyFunctor R i).obj
      (Hatcher.Relative.puncturedPair (TopCat.of U) x)) :=
    IsZero.of_mono pairIso.hom hVlocal
  exact IsZero.of_epi mapU hUlocal

private theorem positive_dimensions_equal
    (d e : ℕ)
    (U : Set (EuclideanSpace ℝ (Fin (d + 1))))
    (V : Set (EuclideanSpace ℝ (Fin (e + 1))))
    (hU : IsOpen U) (hV : IsOpen V) (hne : U.Nonempty)
    (f : U ≃ₜ V) : d = e := by
  by_contra hde
  obtain ⟨x, hx⟩ := hne
  let xU : U := ⟨x, hx⟩
  have htarget : IsZero
      ((Hatcher.Relative.homologyFunctor
        (AddCommGrpCat.of ℤ) (d + 1)).obj
          (Hatcher.Relative.puncturedPair
            (TopCat.of (EuclideanSpace ℝ (Fin (e + 1)))) (f xU).1)) := by
    exact (localHomology_int e (f xU).1).2 (d + 1)
      (fun h => hde (Nat.add_right_cancel h))
  have hsource : IsZero
      ((Hatcher.Relative.homologyFunctor
        (AddCommGrpCat.of ℤ) (d + 1)).obj
          (Hatcher.Relative.puncturedPair
            (TopCat.of (EuclideanSpace ℝ (Fin (d + 1)))) xU.1)) :=
    isZero_ambientLocalHomology_of_homeomorphic_open
      (X := TopCat.of (EuclideanSpace ℝ (Fin (d + 1))))
      (Y := TopCat.of (EuclideanSpace ℝ (Fin (e + 1))))
      (C := AddCommGrpCat.{0})
      U V hU hV f xU (AddCommGrpCat.of ℤ) (d + 1) htarget
  obtain ⟨ed⟩ := (localHomology_int d xU.1).1
  have hInt : IsZero (AddCommGrpCat.of ℤ) := IsZero.of_epi ed.hom hsource
  have hsub : Subsingleton (AddCommGrpCat.of ℤ) :=
    AddCommGrpCat.subsingleton_of_isZero hInt
  exact zero_ne_one (@Subsingleton.elim ℤ hsub 0 1)

/-- **Hatcher, Theorem 2.26 (page 126).** Homeomorphic nonempty open
subsets of Euclidean spaces have the same dimension. -/
theorem invarianceOfDimension_open
    {m n : ℕ}
    (U : Set (EuclideanSpace ℝ (Fin m)))
    (V : Set (EuclideanSpace ℝ (Fin n)))
    (hU : IsOpen U) (hV : IsOpen V)
    (hU_nonempty : U.Nonempty) (hV_nonempty : V.Nonempty)
    (f : U ≃ₜ V) : m = n := by
  cases m with
  | zero =>
      cases n with
      | zero => rfl
      | succ e =>
          exfalso
          have hU_sub : Subsingleton U := inferInstance
          have hV_sub : Subsingleton V :=
            ⟨fun a b => f.symm.injective
              (@Subsingleton.elim U hU_sub (f.symm a) (f.symm b))⟩
          exact (not_subsingleton_open_positive e V hV hV_nonempty) hV_sub
  | succ d =>
      cases n with
      | zero =>
          exfalso
          have hV_sub : Subsingleton V := inferInstance
          have hU_sub : Subsingleton U :=
            ⟨fun a b => f.injective (@Subsingleton.elim V hV_sub (f a) (f b))⟩
          exact (not_subsingleton_open_positive d U hU hU_nonempty) hU_sub
      | succ e =>
          exact congrArg Nat.succ
            (positive_dimensions_equal d e U V hU hV hU_nonempty f)

end Hatcher.Euclidean
