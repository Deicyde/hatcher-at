import Hatcher.Sphere.BorsukUlam

open Fin Function Set
open scoped EuclideanSpace

namespace Hatcher.Sphere

local notation "S2" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

/-- Distance to a set, totalized to be one when the set is empty. -/
private noncomputable def closedSetDistance (A : Set S2) : C(S2, ℝ) := by
  classical
  by_cases hA : A.Nonempty
  · exact ⟨fun x => Metric.infDist x A, Metric.continuous_infDist_pt A⟩
  · exact ContinuousMap.const S2 1

private theorem closedSetDistance_eq_zero_iff
    {A : Set S2} (hA : IsClosed A) (x : S2) :
    closedSetDistance A x = 0 ↔ x ∈ A := by
  classical
  by_cases hne : A.Nonempty
  · simpa [closedSetDistance, hne] using
      (hA.mem_iff_infDist_zero hne (x := x)).symm
  · have hempty : A = ∅ := not_nonempty_iff_eq_empty.mp hne
    simp [closedSetDistance, hempty]

/-- If the two-sphere is the union of three closed sets, one of them contains
a pair of antipodal points. -/
theorem exists_antipodal_pair_of_three_closed_sets
    (A₁ A₂ A₃ : Set S2) (hA₁ : IsClosed A₁) (hA₂ : IsClosed A₂)
    (_hA₃ : IsClosed A₃) (hcover : A₁ ∪ A₂ ∪ A₃ = univ) :
    ∃ x, (x ∈ A₁ ∧ -x ∈ A₁) ∨ (x ∈ A₂ ∧ -x ∈ A₂) ∨
      (x ∈ A₃ ∧ -x ∈ A₃) := by
  let f : C(S2, EuclideanSpace ℝ (Fin 2)) :=
    ⟨fun x => !₂[closedSetDistance A₁ x, closedSetDistance A₂ x], by
      fun_prop⟩
  obtain ⟨x, hx⟩ := exists_eq_neg f
  have h₁ : closedSetDistance A₁ x = closedSetDistance A₁ (-x) := by
    simpa [f] using congrArg (fun y : EuclideanSpace ℝ (Fin 2) => y 0) hx
  have h₂ : closedSetDistance A₂ x = closedSetDistance A₂ (-x) := by
    simpa [f] using congrArg (fun y : EuclideanSpace ℝ (Fin 2) => y 1) hx
  by_cases hz₁ : closedSetDistance A₁ x = 0
  · refine ⟨x, Or.inl ⟨(closedSetDistance_eq_zero_iff hA₁ x).mp hz₁, ?_⟩⟩
    exact (closedSetDistance_eq_zero_iff hA₁ (-x)).mp (h₁ ▸ hz₁)
  by_cases hz₂ : closedSetDistance A₂ x = 0
  · refine ⟨x, Or.inr <| Or.inl ⟨
      (closedSetDistance_eq_zero_iff hA₂ x).mp hz₂, ?_⟩⟩
    exact (closedSetDistance_eq_zero_iff hA₂ (-x)).mp (h₂ ▸ hz₂)
  refine ⟨x, Or.inr <| Or.inr ⟨?_, ?_⟩⟩
  · have hxcover : x ∈ A₁ ∪ A₂ ∪ A₃ := by
      rw [hcover]
      exact mem_univ x
    rcases hxcover with (hx₁ | hx₂) | hx₃
    · exact (hz₁ ((closedSetDistance_eq_zero_iff hA₁ x).mpr hx₁)).elim
    · exact (hz₂ ((closedSetDistance_eq_zero_iff hA₂ x).mpr hx₂)).elim
    · exact hx₃
  · have hnxcover : -x ∈ A₁ ∪ A₂ ∪ A₃ := by
      rw [hcover]
      exact mem_univ (-x)
    rcases hnxcover with (hnx₁ | hnx₂) | hnx₃
    · exact (hz₁
        (h₁.trans ((closedSetDistance_eq_zero_iff hA₁ (-x)).mpr hnx₁))).elim
    · exact (hz₂
        (h₂.trans ((closedSetDistance_eq_zero_iff hA₂ (-x)).mpr hnx₂))).elim
    · exact hnx₃

end Hatcher.Sphere
