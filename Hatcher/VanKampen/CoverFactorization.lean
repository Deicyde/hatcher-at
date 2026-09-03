import Hatcher.VanKampen.CoverGroupPresentation
import Mathlib.Topology.Subpath

noncomputable section

namespace Hatcher.VanKampen

universe u v

variable {ι : Type u} {X : Type v} [TopologicalSpace X]

/-- A finite factorization of a based loop into loops carried by members of a
pointed cover. -/
structure Factorization (U : ι → Set X) (x₀ : X) (hx₀ : ∀ i, x₀ ∈ U i)
    (γ : Path x₀ x₀) where
  /-- One less than the number of factors. -/
  n : ℕ
  /-- The cover member carrying each factor. -/
  index : Fin (n + 1) → ι
  /-- Each factor, regarded as a loop in its chosen cover member. -/
  factor : ∀ k, Path (⟨x₀, hx₀ (index k)⟩ : U (index k))
    ⟨x₀, hx₀ (index k)⟩
  /-- Concatenating the factors in the ambient space recovers the original
  loop up to endpoint-preserving homotopy. -/
  homotopic :
    (Path.concat (fun _ : Fin (n + 2) ↦ x₀)
      (fun k ↦ (factor k).map continuous_subtype_val)).Homotopic γ

namespace Factorization

variable {U : ι → Set X} {x₀ : X} {hx₀ : ∀ i, x₀ ∈ U i}
  {γ : Path x₀ x₀}

/-- A factorization factor regarded as a loop in the ambient space. -/
def ambientFactor (F : Factorization U x₀ hx₀ γ) (k : Fin (F.n + 1)) :
    Path x₀ x₀ :=
  (F.factor k).map continuous_subtype_val

/-- The free-product word represented by a cover factorization. -/
def word (F : Factorization U x₀ hx₀ γ) : CoverFreeProduct U x₀ hx₀ :=
  (List.ofFn fun k ↦
    Monoid.CoprodI.of
      (Path.Homotopic.Quotient.mk (F.factor k) :
        CoverGroup U x₀ hx₀ (F.index k))).reverse.prod

private theorem fromPath_trans (p q : Path x₀ x₀) :
    FundamentalGroup.fromPath (.mk (p.trans q)) =
      FundamentalGroup.fromPath (.mk q) * FundamentalGroup.fromPath (.mk p) := by
  rw [Path.Homotopic.Quotient.mk_trans]
  rfl

private theorem coverMap_of_factor
    (i : ι) (p : Path (⟨x₀, hx₀ i⟩ : U i) ⟨x₀, hx₀ i⟩) :
    coverMap U x₀ hx₀
        (Monoid.CoprodI.of
          (Path.Homotopic.Quotient.mk p : CoverGroup U x₀ hx₀ i)) =
      FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk (p.map continuous_subtype_val)) := by
  rfl

private theorem coverMap_reverseProd_eq_concat
    (n : ℕ) (index : Fin n → ι)
    (factor : ∀ k, Path (⟨x₀, hx₀ (index k)⟩ : U (index k))
      ⟨x₀, hx₀ (index k)⟩) :
    coverMap U x₀ hx₀
        ((List.ofFn fun k ↦ Monoid.CoprodI.of (i := index k)
          (Path.Homotopic.Quotient.mk (factor k) :
            CoverGroup U x₀ hx₀ (index k))).reverse.prod) =
      FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk
          (Path.concat (fun _ : Fin (n + 1) ↦ x₀)
            (fun k ↦ (factor k).map continuous_subtype_val))) := by
  induction n with
  | zero =>
      rw [Path.concat_zero, Path.Homotopic.Quotient.mk_refl]
      rfl
  | succ n ih =>
      let p : Path x₀ x₀ :=
        Path.concat (fun _ : Fin (n + 1) ↦ x₀)
          (fun k ↦ (factor k.castSucc).map continuous_subtype_val)
      let q : Path x₀ x₀ :=
        (factor (Fin.last n)).map continuous_subtype_val
      calc
        coverMap U x₀ hx₀
            ((List.ofFn fun k ↦ Monoid.CoprodI.of (i := index k)
              (Path.Homotopic.Quotient.mk (factor k) :
                CoverGroup U x₀ hx₀ (index k))).reverse.prod) =
            coverMap U x₀ hx₀
                (Monoid.CoprodI.of (i := index (Fin.last n))
                  (Path.Homotopic.Quotient.mk (factor (Fin.last n)) :
                    CoverGroup U x₀ hx₀ (index (Fin.last n)))) *
              coverMap U x₀ hx₀
                ((List.ofFn fun k ↦ Monoid.CoprodI.of
                  (Path.Homotopic.Quotient.mk (factor k.castSucc) :
                    CoverGroup U x₀ hx₀ (index k.castSucc))).reverse.prod) := by
              rw [List.ofFn_succ_last, List.reverse_append, List.reverse_singleton,
                List.prod_append, List.prod_singleton, map_mul]
        _ = FundamentalGroup.fromPath (.mk q) *
            FundamentalGroup.fromPath (.mk p) := by
              rw [coverMap_of_factor]
              exact congrArg (fun z ↦ FundamentalGroup.fromPath (.mk q) * z)
                (ih (fun k ↦ index k.castSucc) (fun k ↦ factor k.castSucc))
        _ = FundamentalGroup.fromPath (.mk (p.trans q)) :=
          (fromPath_trans p q).symm
        _ = FundamentalGroup.fromPath
            (Path.Homotopic.Quotient.mk
              (Path.concat (fun _ : Fin (n + 2) ↦ x₀)
                (fun k ↦ (factor k).map continuous_subtype_val))) := by
              rw [Path.concat_succ]
              rfl

/-- The canonical cover map sends a factorization word to the homotopy class
of the loop represented by that factorization. -/
theorem coverMap_word (F : Factorization U x₀ hx₀ γ) :
    coverMap U x₀ hx₀ F.word = FundamentalGroup.fromPath (.mk γ) := by
  rw [word, coverMap_reverseProd_eq_concat]
  exact Path.Homotopic.Quotient.eq.mpr F.homotopic

end Factorization

end Hatcher.VanKampen
