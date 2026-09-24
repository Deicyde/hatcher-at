# Presentation-complex implementation specification

This is a project-authored formalization specification for the construction in
the proof of Hatcher's Corollary 1.28 (page 52). It is not an independent
mathematical source. Hatcher supplies the construction: choose a presentation,
take a wedge of circles indexed by the generators, and attach one two-cell
along a loop spelling each relator. The details below fix the interfaces needed
to express that construction against the pinned Mathlib APIs.

## Concrete space and basepoint

For `S : Type u`, let `W(S)` be `Hatcher.PointedWedge` of the constant family
of circles, based at `1`. For `rels : Set (FreeGroup S)`, choose for every
`r : rels` a based map from `TopCat.diskBoundary 2` to `W(S)` whose standard
boundary generator maps to the inverse image of `r.1` under
`Hatcher.fundamentalGroupEquivWedgeCircles`. The presentation complex
`P(S, rels)` is the corresponding `IndexedConeAttachment`, based at the image
of the wedge point.

The choice of boundary map may use a representative of a fundamental-group
class. Its public correctness lemma must state both preservation of the
basepoint and the image of the standard boundary generator; downstream nodes
must not depend on the representative chosen internally.

## Fundamental-group calculation

Apply the formalized two-cell attachment theorem to `W(S) → P(S, rels)`.
Transport the normal closure of the attaching loops through
`Hatcher.fundamentalGroupEquivWedgeCircles`; it is exactly
`Subgroup.normalClosure rels`. Quotient transport then gives

```lean
PresentedGroup rels ≃* FundamentalGroup (P(S, rels)) p₀.
```

This step must work for arbitrary, potentially empty or infinite, generator
and relator types.

## Abstract CW structure

Use the natural-number sequence

```text
initial → point → W(S) → P(S, rels) → P(S, rels) → ⋯
```

with one zero-cell at step zero, one one-cell for each generator at step one,
one two-cell for each relator at step two, and empty identity attachments
thereafter. Package this eventually constant sequence as a
`TopCat.CWComplex`. Its cell index is empty in all dimensions at least three,
so every cell has dimension at most two.

This direct construction uses Mathlib's abstract categorical CW API and does
not rely on the unresolved comparison with its classical skeleton API.

## Pinned implementation interfaces

The specification targets Mathlib `v4.31.0` at
`fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`:

- [`HomotopicalAlgebra.AttachCells`](https://github.com/leanprover-community/mathlib4/blob/fabf563a7c95a166b8d7b6efca11c8b4dc9d911f/Mathlib/AlgebraicTopology/RelativeCellComplex/AttachCells.lean)
  records each pushout attachment.
- [`TopCat.CWComplex`](https://github.com/leanprover-community/mathlib4/blob/fabf563a7c95a166b8d7b6efca11c8b4dc9d911f/Mathlib/Topology/CWComplex/Abstract/Basic.lean)
  records the natural-number-indexed cell sequence.
- [`Functor.IsEventuallyConstantFrom`](https://github.com/leanprover-community/mathlib4/blob/fabf563a7c95a166b8d7b6efca11c8b4dc9d911f/Mathlib/CategoryTheory/Limits/Constructions/EventuallyConstant.lean)
  supplies the colimit of the constant tail.
- [`PresentedGroup`](https://github.com/leanprover-community/mathlib4/blob/fabf563a7c95a166b8d7b6efca11c8b4dc9d911f/Mathlib/GroupTheory/PresentedGroup.lean)
  is the quotient of `FreeGroup S` by the normal closure of `rels`.

## Scope boundary

Only the existence of this abstract two-dimensional CW complex and its
fundamental-group equivalence are required. No local-finiteness, regularity,
geometric embedding, or comparison with a classical CW skeleton is asserted.
