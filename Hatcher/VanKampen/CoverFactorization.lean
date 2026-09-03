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

private noncomputable def representative
    {i : ι} (g : CoverGroup U x₀ hx₀ i) :
    Path (⟨x₀, hx₀ i⟩ : U i) ⟨x₀, hx₀ i⟩ :=
  Quotient.out g.toPath

@[simp]
private theorem mk_representative
    {i : ι} (g : CoverGroup U x₀ hx₀ i) :
    (Path.Homotopic.Quotient.mk (representative g) :
      CoverGroup U x₀ hx₀ i) = g :=
  Quotient.out_eq g.toPath

private noncomputable def prepend
    (F : Factorization U x₀ hx₀ γ) (i : ι)
    (g : CoverGroup U x₀ hx₀ i) :
    Σ δ : Path x₀ x₀, Factorization U x₀ hx₀ δ := by
  let entry : (k : Fin (F.n + 2)) →
      Σ j, Path (⟨x₀, hx₀ j⟩ : U j) ⟨x₀, hx₀ j⟩ :=
    Fin.cases ⟨i, representative g⟩ (fun k ↦ ⟨F.index k, F.factor k⟩)
  let δ : Path x₀ x₀ :=
    Path.concat (fun _ : Fin (F.n + 3) ↦ x₀)
      (fun k ↦ (entry k).2.map continuous_subtype_val)
  exact ⟨δ, {
    n := F.n + 1
    index := fun k ↦ (entry k).1
    factor := fun k ↦ (entry k).2
    homotopic := Path.Homotopic.refl δ }⟩

@[simp]
private theorem word_prepend
    (F : Factorization U x₀ hx₀ γ) (i : ι)
    (g : CoverGroup U x₀ hx₀ i) :
    (prepend F i g).2.word = F.word * Monoid.CoprodI.of g := by
  have hletter :
      (Monoid.CoprodI.of
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (representative g)) :
          CoverGroup U x₀ hx₀ i) : CoverFreeProduct U x₀ hx₀) =
        Monoid.CoprodI.of g :=
    congrArg (fun z : CoverGroup U x₀ hx₀ i ↦
      (Monoid.CoprodI.of z : CoverFreeProduct U x₀ hx₀)) (mk_representative g)
  simp [prepend, word, List.ofFn_succ, mul_assoc]
  congr 2

private noncomputable def one (i : ι) :
    Factorization U x₀ hx₀ (Path.refl x₀) where
  n := 0
  index := fun _ ↦ i
  factor := fun _ ↦ Path.refl _
  homotopic := Path.Homotopic.concat_one _ _

@[simp]
private theorem word_one (i : ι) :
    (one (U := U) (x₀ := x₀) (hx₀ := hx₀) i).word = 1 := by
  change (Monoid.CoprodI.of (1 : CoverGroup U x₀ hx₀ i) :
    CoverFreeProduct U x₀ hx₀) = 1
  exact map_one _

/-- Every indexed free-product word is represented by a cover factorization. -/
theorem exists_of_word [Nonempty ι]
    (w : CoverFreeProduct U x₀ hx₀) :
    ∃ γ : Path x₀ x₀, ∃ F : Factorization U x₀ hx₀ γ, F.word = w := by
  let motive : CoverFreeProduct U x₀ hx₀ → Prop := fun w ↦
    ∃ γ : Path x₀ x₀, ∃ F : Factorization U x₀ hx₀ γ, F.word = w
  have hind : ∀ w, motive w⁻¹ := by
    intro w
    induction w using Monoid.CoprodI.induction_left with
    | one =>
        let i := Classical.choice (inferInstance : Nonempty ι)
        exact ⟨Path.refl x₀, one i, by simp⟩
    | mul g w ih =>
        obtain ⟨γ, F, hF⟩ := ih
        let P := prepend F _ g⁻¹
        refine ⟨P.1, P.2, ?_⟩
        rw [word_prepend, hF]
        simp
  simpa only [inv_inv] using hind w⁻¹

end Factorization

end Hatcher.VanKampen
