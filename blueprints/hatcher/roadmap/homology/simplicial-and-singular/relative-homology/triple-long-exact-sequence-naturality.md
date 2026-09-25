---
article_id: af_d76311ba89ebf1425b8eed61
source_units: [hatcher-2-1-triple-les]
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hatcher.Relative.tripleConnecting_naturality
---

# The triple long exact sequence is natural

**Hatcher, §2.1 (page 128).** A map of triples induces a morphism between their
long exact homology sequences. The maps on the three relative terms commute
with the inclusion, quotient, and connecting morphisms.

`Hatcher.Relative.tripleSequenceMap` packages the induced morphism between six
consecutive terms. The main theorem
`Hatcher.Relative.tripleConnecting_naturality` proves the substantive square
containing the connecting morphism; the remaining squares follow from
functoriality of relative homology.

## Depends on

- [The long exact sequence of a triple](triple-long-exact-sequence.md)

## Proof depends on

- [A short exact sequence gives an exact homology sequence](short-exact-homology-sequence.md)

## Sources

- [Hatcher §2.1, naturality for triples, page 128](../../../../sources/hatcher-2-1.md)
- [Triple-homology implementation specification](../../../../sources/triple-homology-implementation.md)
