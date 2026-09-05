import Hatcher.Sphere.SimplyConnected
import Hatcher.Circle.FundamentalGroup
import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv

open Set Metric
open scoped EuclideanSpace ContinuousMap

namespace Hatcher

private noncomputable def sphereProdIoiHomotopyEquiv (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] :
    (sphere (0 : E) 1 × Ioi (0 : ℝ)) ≃ₕ sphere (0 : E) 1 := by
  letI : ContractibleSpace (Ioi (0 : ℝ)) :=
    (convex_Ioi (0 : ℝ)).contractibleSpace ⟨1, by simp⟩
  exact ((ContinuousMap.HomotopyEquiv.refl (sphere (0 : E) 1)).prodCongr
      (ContractibleSpace.hequiv (Ioi (0 : ℝ)) Unit).some).trans
    (Homeomorph.prodUnique (sphere (0 : E) 1) Unit).toHomotopyEquiv

private noncomputable def puncturedHomotopyEquivSphere (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ({0}ᶜ : Set E) ≃ₕ sphere (0 : E) 1 :=
  (homeomorphUnitSphereProd E).toHomotopyEquiv.trans
    (sphereProdIoiHomotopyEquiv E)

private noncomputable def euclideanTwoSphereEquivCircle :
    sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ≃ₜ _root_.Circle :=
  Complex.orthonormalBasisOneI.repr.symm.toHomeomorph.subtype fun x => by
    change x ∈ sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ↔
      Complex.orthonormalBasisOneI.repr.symm x ∈ sphere (0 : ℂ) 1
    rw [mem_sphere_zero_iff_norm, mem_sphere_zero_iff_norm]
    change ‖x‖ = 1 ↔ ‖Complex.orthonormalBasisOneI.repr.symm x‖ = 1
    rw [Complex.orthonormalBasisOneI.repr.symm.norm_map]

private theorem not_simplyConnectedSpace_circle :
    ¬ SimplyConnectedSpace _root_.Circle := by
  intro h
  letI : SimplyConnectedSpace _root_.Circle := h
  have hclasses :
      (1 : FundamentalGroup _root_.Circle 1) =
        FundamentalGroup.fromPath
          (Path.Homotopic.Quotient.mk (Circle.loopOfInt 1)) :=
    Subsingleton.elim _ _
  have himages := congrArg Circle.fundamentalGroupEquivInt hclasses
  have himages' := congrArg Multiplicative.toAdd himages
  norm_num [Circle.fundamentalGroupEquivInt_apply,
    Circle.windingNumberFun_loopOfInt] at himages'

private theorem not_simplyConnectedSpace_puncturedEuclideanTwo :
    ¬ SimplyConnectedSpace
      ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 2))) := by
  intro h
  have hsphere : SimplyConnectedSpace
      (sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
    (puncturedHomotopyEquivSphere
      (EuclideanSpace ℝ (Fin 2))).simplyConnectedSpace_iff.mp h
  have hcircle : SimplyConnectedSpace _root_.Circle :=
    euclideanTwoSphereEquivCircle.toHomotopyEquiv
      |>.simplyConnectedSpace_iff.mp hsphere
  exact not_simplyConnectedSpace_circle hcircle

private theorem simplyConnectedSpace_puncturedEuclidean (k : ℕ) :
    SimplyConnectedSpace
      ({0}ᶜ : Set (EuclideanSpace ℝ (Fin (k + 3)))) := by
  letI : SimplyConnectedSpace
      (sphere (0 : EuclideanSpace ℝ (Fin (k + 3))) 1) :=
    Sphere.simplyConnectedSpace k
  exact (puncturedHomotopyEquivSphere
    (EuclideanSpace ℝ (Fin (k + 3)))).simplyConnectedSpace

/-- Euclidean two-space is not homeomorphic to Euclidean space of dimension
at least three. -/
theorem not_nonempty_homeomorph_euclideanTwo_euclideanHigher (k : ℕ) :
    ¬ Nonempty
      (EuclideanSpace ℝ (Fin 2) ≃ₜ
        EuclideanSpace ℝ (Fin (k + 3))) := by
  rintro ⟨e⟩
  let e₀ : EuclideanSpace ℝ (Fin 2) ≃ₜ
      EuclideanSpace ℝ (Fin (k + 3)) :=
    e.trans (Homeomorph.addRight (-(e 0)))
  have he₀ : e₀ 0 = 0 := by simp [e₀]
  let ep : ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 2))) ≃ₜ
      ({0}ᶜ : Set (EuclideanSpace ℝ (Fin (k + 3)))) :=
    e₀.subtype fun x => by
      simp only [mem_compl_iff, mem_singleton_iff]
      rw [← he₀]
      exact e₀.injective.ne_iff.symm
  haveI : SimplyConnectedSpace
      ({0}ᶜ : Set (EuclideanSpace ℝ (Fin (k + 3)))) :=
    simplyConnectedSpace_puncturedEuclidean k
  exact not_simplyConnectedSpace_puncturedEuclideanTwo
    ep.toHomotopyEquiv.simplyConnectedSpace

private theorem not_pathConnectedSpace_puncturedEuclideanOne :
    ¬ PathConnectedSpace
      ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 1))) := by
  intro h
  letI : PathConnectedSpace
      ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 1))) := h
  let v : EuclideanSpace ℝ (Fin 1) := EuclideanSpace.single 0 1
  let p : ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 1))) :=
    ⟨v, by simp [v]⟩
  let q : ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 1))) :=
    ⟨-v, by simp [v]⟩
  let f : ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 1))) → ℝ :=
    fun x => x.1 0
  have hf : Continuous f := by
    exact (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)).continuous.comp
      continuous_subtype_val
  have hz : (0 : ℝ) ∈ Icc (f q) (f p) := by
    simp [f, p, q, v]
  obtain ⟨x, hx⟩ := (intermediate_value_univ q p hf) hz
  apply x.2
  ext i
  fin_cases i
  simpa [f] using hx

private theorem not_nonempty_homeomorph_euclideanTwo_euclideanZero :
    ¬ Nonempty
      (EuclideanSpace ℝ (Fin 2) ≃ₜ EuclideanSpace ℝ (Fin 0)) := by
  rintro ⟨e⟩
  let v : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 0 1
  have hv : v ≠ 0 := by simp [v]
  exact hv (e.injective (Subsingleton.elim (e v) (e 0)))

private theorem not_nonempty_homeomorph_euclideanTwo_euclideanOne :
    ¬ Nonempty
      (EuclideanSpace ℝ (Fin 2) ≃ₜ EuclideanSpace ℝ (Fin 1)) := by
  rintro ⟨e⟩
  let e₀ : EuclideanSpace ℝ (Fin 2) ≃ₜ EuclideanSpace ℝ (Fin 1) :=
    e.trans (Homeomorph.addRight (-(e 0)))
  have he₀ : e₀ 0 = 0 := by simp [e₀]
  let ep : ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 2))) ≃ₜ
      ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 1))) :=
    e₀.subtype fun x => by
      simp only [mem_compl_iff, mem_singleton_iff]
      rw [← he₀]
      exact e₀.injective.ne_iff.symm
  letI : PathConnectedSpace
      ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 2))) :=
    isPathConnected_iff_pathConnectedSpace.mp <|
      isPathConnected_compl_singleton_of_one_lt_rank (by
        rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
        norm_num) 0
  have htarget : PathConnectedSpace
      ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 1))) :=
    ep.surjective.pathConnectedSpace ep.continuous
  exact not_pathConnectedSpace_puncturedEuclideanOne htarget

/-- Euclidean two-space is not homeomorphic to Euclidean `n`-space when
`n ≠ 2`. -/
theorem not_nonempty_homeomorph_euclideanTwo (n : ℕ) (hn : n ≠ 2) :
    ¬ Nonempty
      (EuclideanSpace ℝ (Fin 2) ≃ₜ EuclideanSpace ℝ (Fin n)) := by
  rcases n with _ | _ | _ | k
  · exact not_nonempty_homeomorph_euclideanTwo_euclideanZero
  · exact not_nonempty_homeomorph_euclideanTwo_euclideanOne
  · exact (hn rfl).elim
  · exact not_nonempty_homeomorph_euclideanTwo_euclideanHigher k

end Hatcher
