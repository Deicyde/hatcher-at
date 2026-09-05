---
article_id: af_03778eab6bda848bf3919cc7
source_units: [hatcher-1-3-selected-spine]
declaration: lemma
origin: cited
statement: formalized
proof: formalized
lean: Hatcher.isTopologicalBasis_nullhomotopicOpens
---

# Small nullhomotopy neighborhoods form a basis

For a locally path-connected, semilocally simply-connected space `X`, the
path-connected open subsets `U` whose inclusion into `X` induces the trivial
map on fundamental groups form a basis for the topology.

Intended artifact: `Hatcher.isTopologicalBasis_nullhomotopicOpens`.

The statement must carry the basepoint-independence lemma from the semilocal
definition, since Hatcher uses arbitrary endpoints when defining `U[γ]`.

Formalized in `Hatcher/Covering/NullhomotopicOpenBasis.lean`, using the
basepoint-independent predicate `Hatcher.IsNullhomotopicOpen`.

## Depends on

- [Semilocally simply-connected spaces](semilocally-simply-connected.md)

## Sources

- [Hatcher §1.3, small-open basis on page 64](../../../../sources/hatcher-1-3.md)
