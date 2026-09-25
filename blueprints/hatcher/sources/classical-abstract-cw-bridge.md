# Classical-to-abstract CW bridge implementation specification

This is a project-authored formalization specification for the bridge used in
the proof of Hatcher's Proposition 1.26(c), pages 50--51. It is not an
independent mathematical source. Hatcher supplies the facts that a CW complex
is built one skeleton at a time by attaching cells and that its weak topology
controls maps out of the resulting quotient. The details below fix the
interfaces needed to express those facts against the pinned Mathlib APIs.

## Required endpoint

Only a forward, one-stage bridge is required. For a classical CW complex `C`
and `n : ℕ`, package the inclusion

```text
skeletonLT C n → skeletonLT C (n + 1)
```

as `HomotopicalAlgebra.AttachCells` for Mathlib's standard abstract `n`-cell.
The project does not need a reverse conversion or an equivalence between the
full classical and abstract CW-complex structures.

## Comparing the cell shapes

The pinned classical API uses the sup-norm ball and sphere in `Fin n → ℝ`.
The abstract API's `TopCat.RelativeCWComplex.basicCell n` uses an `ULift` of
the Euclidean, L2-norm disk and boundary. A plain linear homeomorphism does not
carry one unit sphere to the other.

Construct a radial gauge-rescaling homeomorphism between the two ambient
finite-dimensional real vector spaces, restrict it to the closed balls and
spheres, then apply the universe lift. The restrictions must commute with the
two boundary inclusions, producing an isomorphism of arrows. The construction
must cover `n = 0` as well as positive dimensions.

## The successor-skeleton quotient

For every classical `n`-cell, restrict its characteristic map to the closed
sup-norm ball and its boundary. The boundary map lands in `skeletonLT C n`,
and the closed-cell map lands in `skeletonLT C (n + 1)`. Assemble these maps
over the cell index into a coproduct square.

The joint map

```text
skeletonLT C n ⊕
  (Σ i : CWComplex.cell C n, closedBall (0 : Fin n → ℝ) 1)
    → skeletonLT C (n + 1)
```

is a quotient map. Surjectivity comes from
`skeletonLT_union_iUnion_closedCell_eq_skeletonLT_succ`. The coinducing
direction uses the classical weak-topology axiom `RelCWComplex.closed`, together
with the inherited CW structure on a skeleton and the closedness of each
compact closed-cell image in the Hausdorff ambient space. Expose the induced
successor-stage descent map and simp lemmas for its restrictions to the old
skeleton and each new cell.

Turn this quotient statement into the `TopCat` pushout for the coproduct
square, then build `AttachCells` for the classical sup-norm cell family.
Finally use `AttachCells.reindexCellTypes` and the cell-arrow isomorphism to
obtain the standard abstract-cell attachment. Also provide the wrapper using
Mathlib's `skeleton C n = skeletonLT C (n + 1)` notation.

Hatcher's proof of Appendix Proposition A.2 contains the analogous quotient
argument and is useful implementation guidance. This roadmap does not add
Proposition A.2 to the selected source slice: the local theorem is scoped only
as infrastructure for the already selected Proposition 1.26(c), while the
Appendix remainder stays deferred.

## Path-connectedness needed by Proposition 1.26(c)

The bridge alone is not sufficient. The already formalized higher-cell
fundamental-group equivalence assumes its source is path-connected at every
stage. Ambient path-connectedness does not automatically synthesize that
instance for a skeleton.

Isolate two additional facts. First, an attachment by cells of dimension
greater than one reflects `Joined` for points in its source; as a corollary,
attaching higher cells to a path-connected source has path-connected target.
Second, prove that the classical 2-skeleton of a path-connected CW complex is
path-connected. Put an ambient path inside a bounded skeleton using
Proposition A.1, then repeatedly apply the reflection theorem through the
successor-stage attachment bridge. This is the component-level argument
implicit in Hatcher's finite-dimensional induction and must not be replaced by
an extra path-connectedness hypothesis on the 2-skeleton. Hatcher Appendix
Exercise 3 states the stronger fact that a CW complex is path-connected exactly
when its 1-skeleton is; it is prior art here, not an expansion of the project's
exercise scope.

## Historical implementation-interface snapshot

The initial specification targeted Mathlib `v4.31.0` at
`fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`. The project now builds against
`v4.34.1`; the immutable links below preserve the interface snapshot used for
the original implementation:

- [`Topology.CWComplex`](https://github.com/leanprover-community/mathlib4/blob/fabf563a7c95a166b8d7b6efca11c8b4dc9d911f/Mathlib/Topology/CWComplex/Classical/Basic.lean)
  provides characteristic maps, skeleta, the successor-stage set identity,
  and the weak-topology closed-set axiom.
- [`Topology.CWComplex.Subcomplex`](https://github.com/leanprover-community/mathlib4/blob/fabf563a7c95a166b8d7b6efca11c8b4dc9d911f/Mathlib/Topology/CWComplex/Classical/Subcomplex.lean)
  supplies the inherited classical CW structure on each skeleton.
- [`TopCat.RelativeCWComplex.basicCell`](https://github.com/leanprover-community/mathlib4/blob/fabf563a7c95a166b8d7b6efca11c8b4dc9d911f/Mathlib/Topology/CWComplex/Abstract/Basic.lean)
  is the standard abstract disk-boundary arrow.
- [`HomotopicalAlgebra.AttachCells`](https://github.com/leanprover-community/mathlib4/blob/fabf563a7c95a166b8d7b6efca11c8b4dc9d911f/Mathlib/AlgebraicTopology/RelativeCellComplex/AttachCells.lean)
  records the required pushout and provides `reindexCellTypes`.

## Upstream prior art

Robert Maxton's open Mathlib PRs
[#29788](https://github.com/leanprover-community/mathlib4/pull/29788),
[#29790](https://github.com/leanprover-community/mathlib4/pull/29790), and
[#29792](https://github.com/leanprover-community/mathlib4/pull/29792) develop
continuous coproduct maps, coherent-cover descent, and colimits of classical
skeleta. An unsubmitted fork commit
[`0fef4116bb`](https://github.com/robertmaxton42/mathlib4/commit/0fef4116bba65c7017f7c3298ab1bc6d48afaded)
contains a forward classical-to-abstract construction. These are useful
implementation prior art only: they are unmerged, absent from the pinned
revision, and the fork changes the classical characteristic domain to the L2
model, so it does not remove the cell-shape comparison above.

## Scope boundary

Do not construct a full classical-to-abstract CW complex, a reverse bridge,
or an equivalence of the two APIs. The deliverables are the successor-stage
attachment, the connectivity interfaces needed to iterate it, and the
finite-stage fundamental-group comparison used by Proposition 1.26(c).
