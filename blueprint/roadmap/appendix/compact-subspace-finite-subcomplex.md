---
article_id: af_7fbee0c3ad37e661e770ab4d
source_units: [appendix-proposition-a-1]
declaration: proposition
origin: cited
statement: formalized
proof: formalized
lean: Hatcher.compact_subset_finite_subcomplex
---

# Compact subsets lie in finite subcomplexes

**Hatcher, Proposition A.1 (page 520).** Every compact subspace of a CW
complex is contained in a finite subcomplex.

Intended artifact: `Hatcher.compact_subset_finite_subcomplex`.

State the result against Mathlib's classical `Topology.CWComplex` API: for a
compact subset `K` of a CW complex, produce a `CWComplex.Subcomplex` containing
`K` whose inherited CW structure satisfies `CWComplex.Finite`. The ambient
space is assumed Hausdorff (`T2Space`), as required by Mathlib's classical
subcomplex and closed-cell API.

Formalized in `Hatcher/Appendix/CompactSubspaceFiniteSubcomplex.lean`. The
proof first shows that a compact subset meets only finitely many open cells,
then closes this finite family under cell frontiers and constructs the
resulting finite subcomplex.

The §1.2 proof that the 2-skeleton determines `π₁` uses this twice: a loop has
image in a finite subcomplex, hence in some finite-dimensional skeleton, and a
nullhomotopy of such a loop has image in another finite subcomplex.

## Depends on

None beyond the chosen Mathlib CW-complex representation.

## Sources

- [Hatcher §1.2 source map and Appendix prerequisite](../../sources/hatcher-1-2.md)
