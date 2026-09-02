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

end Factorization

end Hatcher.VanKampen
