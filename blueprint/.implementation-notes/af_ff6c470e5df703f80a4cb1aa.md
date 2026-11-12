# Implementation note: Gaps between cell dimensions force zero cellular differentials

## Candidate

`Hatcher.ClassicalCW.cellularDifferentialsZeroOfSparseCells` proves vanishing
for every pair of natural-number indices of the actual cellular complex.
The proof is awaiting compilation and independent review.

## Route

The fixed skeletal cell-basis isomorphism identifies an empty cell dimension
with a zero chain object. An adjacent differential has an empty source or
an empty target by the sparse-cell hypothesis. Every other differential is
zero by the existing downward chain-complex shape theorem. No finiteness,
connectedness, nonemptiness or positive-degree assumption is used.

## Reused declarations

`skeletonRelativeHomology`, `cellularChainComplex_X` and
`cellularChainComplex_d_eq_zero` supply the existing cellular objects and
maps. `IsZero.of_iso`, `IsZero.eq_of_src` and `IsZero.eq_of_tgt` supply the
zero-object transport and map equalities. The two skeletal pair definitions
are definitionally equal, as already compiled in the no-cells proof.

Blueprint searches found no existing theorem with this conclusion. None of
the copied dependencies has a usable shared Autoform index; the pinned
Mathlib sources were inspected directly. No import change is needed.
