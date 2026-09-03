import Hatcher.VanKampen.CoverFactorization
import Mathlib.GroupTheory.QuotientGroup.Basic

noncomputable section

namespace Hatcher.VanKampen

universe u v

variable {ι : Type u} {X : Type v} [TopologicalSpace X]

local instance relationSubgroupNormal
    {U : ι → Set X} {x₀ : X} {hx₀ : ∀ i, x₀ ∈ U i} :
    (relationSubgroup U x₀ hx₀).Normal := by
  unfold relationSubgroup
  infer_instance

namespace Factorization

variable {U : ι → Set X} {x₀ : X} {hx₀ : ∀ i, x₀ ∈ U i}
  {γ : Path x₀ x₀}

/-- A cover index together with a loop class in that cover member. -/
abbrev Entry (U : ι → Set X) (x₀ : X) (hx₀ : ∀ i, x₀ ∈ U i) :=
  Σ i, CoverGroup U x₀ hx₀ i

/-- The factor classes of a cover factorization, in geometric concatenation order. -/
def entries (F : Factorization U x₀ hx₀ γ) : List (Entry U x₀ hx₀) :=
  List.ofFn fun k ↦
    ⟨F.index k,
      (Path.Homotopic.Quotient.mk (F.factor k) :
        CoverGroup U x₀ hx₀ (F.index k))⟩

@[simp]
theorem retarget_entries {δ : Path x₀ x₀} (F : Factorization U x₀ hx₀ γ)
    (h : γ.Homotopic δ) : (F.retarget h).entries = F.entries := rfl

private def entryWord (e : Entry U x₀ hx₀) : CoverFreeProduct U x₀ hx₀ :=
  match e with
  | ⟨_, g⟩ => Monoid.CoprodI.of g

private def wordOfEntries (es : List (Entry U x₀ hx₀)) :
    CoverFreeProduct U x₀ hx₀ :=
  (es.reverse.map entryWord).prod

private def orientedWord (F : Factorization U x₀ hx₀ γ) :
    CoverFreeProduct U x₀ hx₀ :=
  wordOfEntries F.entries

private theorem word_eq_orientedWord
    (F : Factorization U x₀ hx₀ γ) : F.word = orientedWord F := by
  unfold word orientedWord wordOfEntries entries
  rw [List.map_reverse, List.map_ofFn]
  congr 2

/-- One elementary change to a list of factor classes: combine two adjacent
factors carried by the same cover member, change the cover label of a factor
carried by an overlap, or reverse either operation. -/
inductive Move (U : ι → Set X) (x₀ : X) (hx₀ : ∀ i, x₀ ∈ U i) :
    List (Entry U x₀ hx₀) → List (Entry U x₀ hx₀) → Prop
  | combine (before after : List (Entry U x₀ hx₀)) (i : ι)
      (a b : CoverGroup U x₀ hx₀ i) :
      Move U x₀ hx₀
        (before ++ ⟨i, a⟩ :: ⟨i, b⟩ :: after)
        (before ++ ⟨i, b * a⟩ :: after)
  | changeCover (before after : List (Entry U x₀ hx₀)) (i j : ι)
      (ω : OverlapGroup U x₀ hx₀ i j) :
      Move U x₀ hx₀
        (before ++ ⟨i, overlapToLeft U x₀ hx₀ i j ω⟩ :: after)
        (before ++ ⟨j, overlapToRight U x₀ hx₀ i j ω⟩ :: after)
  | symm {es es' : List (Entry U x₀ hx₀)} :
      Move U x₀ hx₀ es es' → Move U x₀ hx₀ es' es

private theorem wordOfEntries_eq_of_combine
    (before after : List (Entry U x₀ hx₀)) (i : ι)
    (a b : CoverGroup U x₀ hx₀ i) :
    wordOfEntries (before ++ ⟨i, a⟩ :: ⟨i, b⟩ :: after) =
      wordOfEntries (before ++ ⟨i, b * a⟩ :: after) := by
  simp [wordOfEntries, entryWord, List.reverse_append, map_mul, mul_assoc]

private theorem quotient_overlap_eq (i j : ι)
    (ω : OverlapGroup U x₀ hx₀ i j) :
    QuotientGroup.mk' (relationSubgroup U x₀ hx₀)
        (Monoid.CoprodI.of (overlapToLeft U x₀ hx₀ i j ω)) =
      QuotientGroup.mk' (relationSubgroup U x₀ hx₀)
        (Monoid.CoprodI.of (overlapToRight U x₀ hx₀ i j ω)) := by
  let a : CoverFreeProduct U x₀ hx₀ :=
    Monoid.CoprodI.of (overlapToLeft U x₀ hx₀ i j ω)
  let b : CoverFreeProduct U x₀ hx₀ :=
    Monoid.CoprodI.of (overlapToRight U x₀ hx₀ i j ω)
  change QuotientGroup.mk' (relationSubgroup U x₀ hx₀) a =
    QuotientGroup.mk' (relationSubgroup U x₀ hx₀) b
  apply QuotientGroup.eq_iff_div_mem.mpr
  change overlapRelation U x₀ hx₀ i j ω ∈ relationSubgroup U x₀ hx₀
  apply Subgroup.subset_normalClosure
  exact ⟨i, j, ω, rfl⟩

private theorem quotient_wordOfEntries_eq_of_move
    {es es' : List (Entry U x₀ hx₀)}
    (h : Move U x₀ hx₀ es es') :
    QuotientGroup.mk' (relationSubgroup U x₀ hx₀) (wordOfEntries es) =
      QuotientGroup.mk' (relationSubgroup U x₀ hx₀) (wordOfEntries es') := by
  induction h with
  | combine before after i a b =>
      exact congrArg (QuotientGroup.mk' (relationSubgroup U x₀ hx₀))
        (wordOfEntries_eq_of_combine before after i a b)
  | changeCover before after i j ω =>
      simp only [wordOfEntries, List.reverse_append, List.reverse_cons,
        List.map_append, List.map_cons, List.map_nil, List.prod_append,
        List.prod_cons, List.prod_nil, entryWord, map_mul, mul_one]
      rw [quotient_overlap_eq i j ω]
  | symm h ih => exact ih.symm

/-- A sweep is a finite chain of elementary changes between the entry lists
of two factorizations. Intermediate lists need not be packaged as paths. -/
structure Sweep {δ : Path x₀ x₀} (F : Factorization U x₀ hx₀ γ)
    (G : Factorization U x₀ hx₀ δ) : Prop where
  moves : Relation.ReflTransGen (Move U x₀ hx₀) F.entries G.entries

private theorem quotient_wordOfEntries_eq_of_moves
    {es es' : List (Entry U x₀ hx₀)}
    (h : Relation.ReflTransGen (Move U x₀ hx₀) es es') :
    QuotientGroup.mk' (relationSubgroup U x₀ hx₀) (wordOfEntries es) =
      QuotientGroup.mk' (relationSubgroup U x₀ hx₀) (wordOfEntries es') := by
  induction h with
  | refl => rfl
  | tail _ hmove ih => exact ih.trans (quotient_wordOfEntries_eq_of_move hmove)

end Factorization

/-- An elementary move does not change the class of a factorization word
modulo the normal subgroup generated by overlap relations. -/
theorem factorization_quotient_eq_of_move
    {U : ι → Set X} {x₀ : X} {hx₀ : ∀ i, x₀ ∈ U i}
    {γ : Path x₀ x₀} (F G : Factorization U x₀ hx₀ γ)
    (h : Factorization.Move U x₀ hx₀ F.entries G.entries) :
    QuotientGroup.mk' (relationSubgroup U x₀ hx₀) F.word =
      QuotientGroup.mk' (relationSubgroup U x₀ hx₀) G.word := by
  rw [Factorization.word_eq_orientedWord,
    Factorization.word_eq_orientedWord]
  exact Factorization.quotient_wordOfEntries_eq_of_move h

/-- A finite sweep of elementary changes preserves the factorization class. -/
theorem factorization_quotient_eq_of_sweep
    {U : ι → Set X} {x₀ : X} {hx₀ : ∀ i, x₀ ∈ U i}
    {γ δ : Path x₀ x₀} (F : Factorization U x₀ hx₀ γ)
    (G : Factorization U x₀ hx₀ δ)
    (h : Factorization.Sweep F G) :
    QuotientGroup.mk' (relationSubgroup U x₀ hx₀) F.word =
      QuotientGroup.mk' (relationSubgroup U x₀ hx₀) G.word := by
  rw [Factorization.word_eq_orientedWord,
    Factorization.word_eq_orientedWord]
  exact Factorization.quotient_wordOfEntries_eq_of_moves h.moves

end Hatcher.VanKampen
