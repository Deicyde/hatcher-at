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

/-- The reflexive-transitive closure of elementary factorization moves. -/
abbrev Moves (es es' : List (Entry U x₀ hx₀)) : Prop :=
  Relation.ReflTransGen (Move U x₀ hx₀) es es'

/-- A move remains valid after adding an arbitrary common prefix. -/
theorem Move.prefix {es es' : List (Entry U x₀ hx₀)}
    (h : Move U x₀ hx₀ es es') (pre : List (Entry U x₀ hx₀)) :
    Move U x₀ hx₀ (pre ++ es) (pre ++ es') := by
  induction h with
  | combine before after i a b =>
      simpa only [List.append_assoc] using
        Move.combine (pre ++ before) after i a b
  | changeCover before after i j ω =>
      simpa only [List.append_assoc] using
        Move.changeCover (pre ++ before) after i j ω
  | symm h ih => exact Move.symm ih

/-- A move remains valid after adding an arbitrary common suffix. -/
theorem Move.suffix {es es' : List (Entry U x₀ hx₀)}
    (h : Move U x₀ hx₀ es es') (suffix : List (Entry U x₀ hx₀)) :
    Move U x₀ hx₀ (es ++ suffix) (es' ++ suffix) := by
  induction h with
  | combine before after i a b =>
      simpa only [List.append_assoc, List.cons_append] using
        Move.combine before (after ++ suffix) i a b
  | changeCover before after i j ω =>
      simpa only [List.append_assoc, List.cons_append] using
        Move.changeCover before (after ++ suffix) i j ω
  | symm h ih => exact Move.symm ih

/-- A move remains valid inside an arbitrary list context. -/
theorem Move.context {es es' : List (Entry U x₀ hx₀)}
    (h : Move U x₀ hx₀ es es')
    (pre suffix : List (Entry U x₀ hx₀)) :
    Move U x₀ hx₀ (pre ++ es ++ suffix) (pre ++ es' ++ suffix) :=
  (h.prefix pre).suffix suffix

/-- A chain of moves remains valid after adding an arbitrary common prefix. -/
theorem Moves.prefix {es es' : List (Entry U x₀ hx₀)}
    (h : Moves es es') (pre : List (Entry U x₀ hx₀)) :
    Moves (pre ++ es) (pre ++ es') := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hmove ih => exact ih.tail (hmove.prefix pre)

/-- A chain of moves remains valid after adding an arbitrary common suffix. -/
theorem Moves.suffix {es es' : List (Entry U x₀ hx₀)}
    (h : Moves es es') (suffix : List (Entry U x₀ hx₀)) :
    Moves (es ++ suffix) (es' ++ suffix) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hmove ih => exact ih.tail (hmove.suffix suffix)

/-- A chain of moves remains valid inside an arbitrary list context. -/
theorem Moves.context {es es' : List (Entry U x₀ hx₀)}
    (h : Moves es es') (pre suffix : List (Entry U x₀ hx₀)) :
    Moves (pre ++ es ++ suffix) (pre ++ es' ++ suffix) :=
  (h.prefix pre).suffix suffix

/-- Reverse a finite chain. `Move` already contains its inverse constructor. -/
theorem Moves.symm {es es' : List (Entry U x₀ hx₀)}
    (h : Moves es es') : Moves es' es := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hmove ih =>
      exact (Relation.ReflTransGen.single (Move.symm hmove)).trans ih

/-- Entries all carrying the same cover index. -/
def sameCoverEntries (i : ι) (as : List (CoverGroup U x₀ hx₀ i)) :
    List (Entry U x₀ hx₀) :=
  as.map fun a ↦ ⟨i, a⟩

/-- Repeatedly combining adjacent entries with a common cover index collapses
a nonempty block to its reverse-order product. -/
theorem moves_combine_sameCover (before after : List (Entry U x₀ hx₀))
    (i : ι) (a : CoverGroup U x₀ hx₀ i) :
    ∀ as : List (CoverGroup U x₀ hx₀ i),
      Moves
        (before ++ sameCoverEntries i (a :: as) ++ after)
        (before ++ [⟨i, (a :: as).reverse.prod⟩] ++ after) := by
  intro as
  induction as generalizing a with
  | nil =>
      simpa [sameCoverEntries] using
        (Relation.ReflTransGen.refl :
          Moves (before ++ [⟨i, a⟩] ++ after) _)
  | cons b bs ih =>
      have hfirst : Move U x₀ hx₀
          (before ++ sameCoverEntries i (a :: b :: bs) ++ after)
          (before ++ sameCoverEntries i ((b * a) :: bs) ++ after) := by
        simpa [sameCoverEntries, List.append_assoc] using
          Move.combine before (sameCoverEntries i bs ++ after) i a b
      refine (Relation.ReflTransGen.single hfirst).trans ?_
      simpa [List.reverse_cons, List.prod_append, sameCoverEntries, mul_assoc] using
        ih (a := b * a)

/-- Split one cover-group entry into a prescribed nonempty list whose
reverse-order product is that entry. -/
theorem moves_split_sameCover (before after : List (Entry U x₀ hx₀))
    (i : ι) (a : CoverGroup U x₀ hx₀ i)
    (as : List (CoverGroup U x₀ hx₀ i)) :
    Moves
      (before ++ [⟨i, (a :: as).reverse.prod⟩] ++ after)
      (before ++ sameCoverEntries i (a :: as) ++ after) :=
  (moves_combine_sameCover before after i a as).symm

/-- Split one entry into an arbitrary nonempty same-cover block. -/
theorem moves_split_sameCover_nonempty
    (before after : List (Entry U x₀ hx₀)) (i : ι)
    (as : List (CoverGroup U x₀ hx₀ i)) (has : as ≠ []) :
    Moves
      (before ++ [⟨i, as.reverse.prod⟩] ++ after)
      (before ++ sameCoverEntries i as ++ after) := by
  cases as with
  | nil => exact (has rfl).elim
  | cons a tail => exact moves_split_sameCover before after i a tail

/-- Replace a coarse entry by a nonempty refined block once its class is the
reverse-order product of the refined classes. -/
theorem moves_replace_by_sameCover_block
    (before after : List (Entry U x₀ hx₀)) (i : ι)
    (coarse : CoverGroup U x₀ hx₀ i)
    (refined : List (CoverGroup U x₀ hx₀ i))
    (hrefined : refined ≠ [])
    (hprod : refined.reverse.prod = coarse) :
    Moves
      (before ++ [⟨i, coarse⟩] ++ after)
      (before ++ sameCoverEntries i refined ++ after) := by
  rw [← hprod]
  exact moves_split_sameCover_nonempty before after i refined hrefined

/-- One possibly index-varying change of cover label, certified by a loop in
the corresponding overlap. -/
abbrev CoverChange :=
  Σ i : ι, Σ j : ι, OverlapGroup U x₀ hx₀ i j

namespace CoverChange

def leftEntry (c : CoverChange (U := U) (x₀ := x₀) (hx₀ := hx₀)) :
    Entry U x₀ hx₀ :=
  ⟨c.1, overlapToLeft U x₀ hx₀ c.1 c.2.1 c.2.2⟩

def rightEntry (c : CoverChange (U := U) (x₀ := x₀) (hx₀ := hx₀)) :
    Entry U x₀ hx₀ :=
  ⟨c.2.1, overlapToRight U x₀ hx₀ c.1 c.2.1 c.2.2⟩

end CoverChange

/-- Change the cover label pointwise across a list of overlap classes. -/
theorem moves_changeCover_list (before after : List (Entry U x₀ hx₀)) :
    ∀ changes : List (CoverChange (U := U) (x₀ := x₀) (hx₀ := hx₀)),
      Moves
        (before ++ changes.map CoverChange.leftEntry ++ after)
        (before ++ changes.map CoverChange.rightEntry ++ after) := by
  intro changes
  induction changes generalizing before with
  | nil => exact Relation.ReflTransGen.refl
  | cons c cs ih =>
      have hfirst : Move U x₀ hx₀
          (before ++ (c :: cs).map CoverChange.leftEntry ++ after)
          (before ++ CoverChange.rightEntry c ::
            cs.map CoverChange.leftEntry ++ after) := by
        rcases c with ⟨i, j, ω⟩
        simpa [CoverChange.leftEntry, CoverChange.rightEntry,
          List.append_assoc] using
          Move.changeCover before (cs.map CoverChange.leftEntry ++ after) i j ω
      refine (Relation.ReflTransGen.single hfirst).trans ?_
      simpa [List.append_assoc] using
        ih (before := before ++ [CoverChange.rightEntry c])

/-- Reinterpret an inverse connector through an overlap, then cancel it with
the connector on the other side. -/
theorem moves_cancel_connector_pair
    (before after : List (Entry U x₀ hx₀)) (i j : ι)
    (ω : OverlapGroup U x₀ hx₀ i j) :
    Moves
      (before ++ ⟨i, (overlapToLeft U x₀ hx₀ i j ω)⁻¹⟩ ::
        ⟨j, overlapToRight U x₀ hx₀ i j ω⟩ :: after)
      (before ++ ⟨j, 1⟩ :: after) := by
  have hchange : Move U x₀ hx₀
      (before ++ ⟨i, (overlapToLeft U x₀ hx₀ i j ω)⁻¹⟩ ::
        ⟨j, overlapToRight U x₀ hx₀ i j ω⟩ :: after)
      (before ++ ⟨j, (overlapToRight U x₀ hx₀ i j ω)⁻¹⟩ ::
        ⟨j, overlapToRight U x₀ hx₀ i j ω⟩ :: after) := by
    simpa only [map_inv] using Move.changeCover before
      (⟨j, overlapToRight U x₀ hx₀ i j ω⟩ :: after) i j ω⁻¹
  have hcombine : Move U x₀ hx₀
      (before ++ ⟨j, (overlapToRight U x₀ hx₀ i j ω)⁻¹⟩ ::
        ⟨j, overlapToRight U x₀ hx₀ i j ω⟩ :: after)
      (before ++ ⟨j, 1⟩ :: after) := by
    simpa using Move.combine before after j
        (overlapToRight U x₀ hx₀ i j ω)⁻¹
        (overlapToRight U x₀ hx₀ i j ω)
  exact (Relation.ReflTransGen.single hchange).tail hcombine

/-- Cancel an interface connector and absorb the resulting identity into the
following entry. -/
theorem moves_cancel_connector
    (before after : List (Entry U x₀ hx₀)) (i j : ι)
    (b : CoverGroup U x₀ hx₀ j)
    (ω : OverlapGroup U x₀ hx₀ i j) :
    Moves
      (before ++ ⟨i, (overlapToLeft U x₀ hx₀ i j ω)⁻¹⟩ ::
        ⟨j, overlapToRight U x₀ hx₀ i j ω⟩ :: ⟨j, b⟩ :: after)
      (before ++ ⟨j, b⟩ :: after) := by
  have hpair := moves_cancel_connector_pair
    (U := U) (x₀ := x₀) (hx₀ := hx₀)
    before (⟨j, b⟩ :: after) i j ω
  have hone : Move U x₀ hx₀
      (before ++ ⟨j, 1⟩ :: ⟨j, b⟩ :: after)
      (before ++ ⟨j, b⟩ :: after) := by
    simpa using Move.combine before after j 1 b
  exact hpair.tail hone

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
  moves : Moves F.entries G.entries

/-- Compose a finite family of move chains indexed by the adjacent pairs of
states. -/
theorem moves_fin_chain {n : ℕ}
    (state : Fin (n + 1) → List (Entry U x₀ hx₀))
    (step : ∀ k : Fin n, Moves (state k.castSucc) (state k.succ)) :
    Moves (state 0) (state (Fin.last n)) := by
  induction n with
  | zero => exact Relation.ReflTransGen.refl
  | succ n ih =>
      let initial : Fin (n + 1) → List (Entry U x₀ hx₀) :=
        fun k ↦ state k.castSucc
      have hinitial : Moves (initial 0) (initial (Fin.last n)) := by
        apply ih initial
        intro k
        simpa only [initial, Fin.succ_castSucc] using step k.castSucc
      have hlast := step (Fin.last n)
      simpa [initial, Fin.succ_last] using hinitial.trans hlast

/-- Compose alternating band sweeps and interface sweeps. There are `n + 1`
bands and `n` interfaces. -/
theorem moves_alternating {n : ℕ}
    (lower upper : Fin (n + 1) → List (Entry U x₀ hx₀))
    (band : ∀ k, Moves (lower k) (upper k))
    (interface : ∀ k : Fin n, Moves (upper k.castSucc) (lower k.succ)) :
    Moves (lower 0) (upper (Fin.last n)) := by
  have hlower : Moves (lower 0) (lower (Fin.last n)) := by
    apply moves_fin_chain lower
    intro k
    exact (band k.castSucc).trans (interface k)
  exact hlower.trans (band (Fin.last n))

/-- Entry-list form of the complete alternating sweep, with only the two
endpoint factorizations kept as dependent objects. -/
theorem sweep_of_moves_alternating
    {δ : Path x₀ x₀} {n : ℕ}
    (F : Factorization U x₀ hx₀ γ) (K : Factorization U x₀ hx₀ δ)
    (lower upper : Fin (n + 1) → List (Entry U x₀ hx₀))
    (hfirst : lower 0 = F.entries)
    (hlast : upper (Fin.last n) = K.entries)
    (band : ∀ k, Moves (lower k) (upper k))
    (interface : ∀ k : Fin n, Moves (upper k.castSucc) (lower k.succ)) :
    Sweep F K := by
  constructor
  rw [← hfirst, ← hlast]
  exact moves_alternating lower upper band interface

/-- A path and a factorization of that path, packaged so a finite family may
vary its path with the row index. -/
abbrev PackedFactorization :=
  Σ p : Path x₀ x₀, Factorization U x₀ hx₀ p

/-- Package-level form of `moves_alternating`. -/
theorem sweep_alternating {n : ℕ}
    (lower upper : Fin (n + 1) →
      PackedFactorization (U := U) (x₀ := x₀) (hx₀ := hx₀))
    (band : ∀ k, Sweep (lower k).2 (upper k).2)
    (interface : ∀ k : Fin n,
      Sweep (upper k.castSucc).2 (lower k.succ).2) :
    Sweep (lower 0).2 (upper (Fin.last n)).2 := by
  constructor
  exact moves_alternating
    (fun k ↦ (lower k).2.entries)
    (fun k ↦ (upper k).2.entries)
    (fun k ↦ (band k).moves)
    (fun k ↦ (interface k).moves)

/-- Add entry-list identifications at the two ends of an alternating sweep. -/
theorem sweep_of_alternating_of_entries_eq
    {δ : Path x₀ x₀} {n : ℕ}
    (F : Factorization U x₀ hx₀ γ) (K : Factorization U x₀ hx₀ δ)
    (lower upper : Fin (n + 1) →
      PackedFactorization (U := U) (x₀ := x₀) (hx₀ := hx₀))
    (hfirst : (lower 0).2.entries = F.entries)
    (hlast : (upper (Fin.last n)).2.entries = K.entries)
    (band : ∀ k, Sweep (lower k).2 (upper k).2)
    (interface : ∀ k : Fin n,
      Sweep (upper k.castSucc).2 (lower k.succ).2) :
    Sweep F K :=
  sweep_of_moves_alternating F K
    (fun k ↦ (lower k).2.entries)
    (fun k ↦ (upper k).2.entries)
    hfirst hlast
    (fun k ↦ (band k).moves)
    (fun k ↦ (interface k).moves)

private theorem quotient_wordOfEntries_eq_of_moves
    {es es' : List (Entry U x₀ hx₀)}
    (h : Moves es es') :
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
