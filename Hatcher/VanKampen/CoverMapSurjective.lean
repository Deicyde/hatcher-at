import Hatcher.Sphere.LoopInOpenCover
import Hatcher.VanKampen.CoverGroupPresentation

noncomputable section

namespace Hatcher.VanKampen

universe u v

variable {ι : Type u} {X : Type v} [TopologicalSpace X]

private def pathInCover
    (U : ι → Set X) (x₀ : X) (hx₀ : ∀ i, x₀ ∈ U i)
    (i : ι) (γ : Path x₀ x₀) (hγ : Set.range γ ⊆ U i) :
    Path (⟨x₀, hx₀ i⟩ : U i) (⟨x₀, hx₀ i⟩ : U i) where
  toFun t := ⟨γ t, hγ (Set.mem_range_self t)⟩
  continuous_toFun := γ.continuous.subtype_mk _
  source' := Subtype.ext γ.source
  target' := Subtype.ext γ.target

private theorem coverMap_of_pathInCover
    (U : ι → Set X) (x₀ : X) (hx₀ : ∀ i, x₀ ∈ U i)
    (i : ι) (γ : Path x₀ x₀) (hγ : Set.range γ ⊆ U i) :
    coverMap U x₀ hx₀
        (Monoid.CoprodI.of
          (FundamentalGroup.fromPath
            (.mk (pathInCover U x₀ hx₀ i γ hγ)))) =
      FundamentalGroup.fromPath (.mk γ) := by
  simp only [coverMap, Monoid.CoprodI.lift_of]
  rfl

private theorem loopClass_mem_coverMap_range
    (U : ι → Set X) (x₀ : X) (hx₀ : ∀ i, x₀ ∈ U i)
    (i : ι) (γ : Path x₀ x₀) (hγ : Set.range γ ⊆ U i) :
    FundamentalGroup.fromPath (.mk γ) ∈ (coverMap U x₀ hx₀).range := by
  rw [MonoidHom.mem_range]
  exact ⟨Monoid.CoprodI.of
    (FundamentalGroup.fromPath (.mk (pathInCover U x₀ hx₀ i γ hγ))),
    coverMap_of_pathInCover U x₀ hx₀ i γ hγ⟩

private theorem fromPath_trans (x₀ : X) (p q : Path x₀ x₀) :
    FundamentalGroup.fromPath (.mk (p.trans q)) =
      FundamentalGroup.fromPath (.mk q) * FundamentalGroup.fromPath (.mk p) := by
  rw [Path.Homotopic.Quotient.mk_trans]
  rfl

private theorem concat_mem_coverMap_range
    (U : ι → Set X) (x₀ : X) (hx₀ : ∀ i, x₀ ∈ U i)
    (n : ℕ) (D : Fin n → Path x₀ x₀)
    (hD : ∀ k, ∃ i : ι, Set.range (D k) ⊆ U i) :
    FundamentalGroup.fromPath (.mk (Path.concat (fun _ => x₀) D)) ∈
      (coverMap U x₀ hx₀).range := by
  induction n with
  | zero =>
      rw [Path.concat_zero, Path.Homotopic.Quotient.mk_refl]
      exact (coverMap U x₀ hx₀).range.one_mem
  | succ n ih =>
      have hconcat : Path.concat (fun _ => x₀) D =
          (Path.concat (fun _ => x₀) (fun k => D k.castSucc)).trans
            (D (Fin.last n)) := by
        simp only [Path.concat_succ, Function.comp_def]
      rw [hconcat, fromPath_trans]
      obtain ⟨i, hi⟩ := hD (Fin.last n)
      apply (coverMap U x₀ hx₀).range.mul_mem
        (loopClass_mem_coverMap_range U x₀ hx₀ i (D (Fin.last n)) hi)
      simpa only [Function.comp_apply] using
        ih (fun k => D k.castSucc) (fun k => hD k.castSucc)

/-- **Hatcher, Theorem 1.20, first clause (page 43).** For an open cover whose
members contain the basepoint and whose pairwise intersections are
path-connected, the canonical map from the indexed free product of the
cover-member fundamental groups onto the ambient fundamental group is
surjective. -/
theorem coverMap_surjective
    (U : ι → Set X) (x₀ : X)
    (hUopen : ∀ i, IsOpen (U i))
    (hUcover : Set.univ ⊆ ⋃ i, U i)
    (hUinter : ∀ i j, IsPathConnected (U i ∩ U j))
    (hx₀ : ∀ i, x₀ ∈ U i) :
    Function.Surjective (coverMap U x₀ hx₀) := by
  intro g
  induction g using Path.Homotopic.Quotient.ind with
  | mk γ =>
      obtain ⟨n, D, hDhom, hD⟩ :=
        Hatcher.loop_homotopic_prod_of_isOpenCover
          hUopen hUcover hUinter hx₀ γ
      obtain ⟨w, hw⟩ := MonoidHom.mem_range.mp
        (concat_mem_coverMap_range U x₀ hx₀ (n + 1) D hD)
      exact ⟨w, hw.trans (Path.Homotopic.Quotient.eq.mpr hDhom)⟩

end Hatcher.VanKampen
