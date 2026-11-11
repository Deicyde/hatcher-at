# Implementation note: Gaps between cell dimensions force zero cellular differentials

## Remaining goal

If a classical CW complex has no two occupied cell dimensions that are adjacent, every differential of its actual ordinary integral cellular complex is zero. The outgoing degree-zero map is the existing unaugmented zero map.

## Candidate declaration

`Hatcher.ClassicalCW.sparseCellularDifferentials` is a naming proposal, not a verified declaration.

## Route

For each adjacent source and target degree, at least one cellular group is free on an empty set. The differential is zero through that zero object.

## Existing algebra and cellular APIs

Reuse `Hatcher.ClassicalCW.skeletonRelativeHomology`, `cellularChainComplex`,
`cellularHomologyComparison` and its actual forward map. Mathlib supplies
`ShortComplex.isZero_homology_of_isZero_X₂`, `HomologyData.ofZeros`,
`Submodule.nonempty_basis_of_pid`,
`LinearIndependent.fintype_card_le_finrank`, and
`AddGroup.rank_le_of_surjective`. The PID basis does not alone supply r ≤ k;
prove that bound through the included independent family. The abelian group
rank-monotonicity TODO in `GroupTheory/Rank.lean` is not a theorem.
