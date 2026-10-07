---
article_id: af_db2445f3fea351a02e084322
source_units: [appendix-proposition-a-1]
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: Hatcher.compact_subset_skeleton
---

# Compact subsets lie in a bounded skeleton

Derive the finite-dimensional form of Hatcher's Appendix Proposition A.1:
every compact subset of a classical CW complex is contained in one finite
skeleton.

Apply `Hatcher.compact_subset_finite_subcomplex`, then extract a dimension
bound from `CWComplex.FiniteDimensional.eventually_isEmpty_cell`. Use the
subcomplex cell correspondence to show that its underlying set lies in the
ambient skeleton with that bound.

## Depends on

None beyond pinned Mathlib.

## Proof depends on

- [Compact subsets lie in finite subcomplexes](../compact-subspace-finite-subcomplex.md)

## Sources

- [Hatcher Appendix Proposition A.1 and its §1.2 use](../../../sources/hatcher-1-2.md)
