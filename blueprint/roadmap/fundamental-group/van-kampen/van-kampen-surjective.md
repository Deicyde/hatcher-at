---
article_id: af_5040a99f20e27330d5bb75a9
source_units: [hatcher-1-2-selected-spine]
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hatcher.VanKampen.coverMap_surjective
---

# The van Kampen cover map is surjective

**Hatcher, Theorem 1.20, first clause (page 43).** Let `X` be the union of an
arbitrary indexed family of path-connected open sets `U i`, all containing
the basepoint `x₀`. If every pairwise intersection is path-connected, then the
canonical map

`Φ : (∗ i, π₁(U i, x₀)) →* π₁(X, x₀)`

is surjective.

Intended artifact: `Hatcher.VanKampen.coverMap_surjective`.

The proof should reuse the completed Lemma 1.15 node: split a loop into a
finite concatenation of loops lying in cover members, then take the
corresponding finite word in `Monoid.CoprodI`.

Formalized in `Hatcher/VanKampen/CoverMapSurjective.lean`. The proof represents
each factor loop in its cover member and inducts over the finite concatenation,
accounting for the reversed multiplication convention in the fundamental
group.

## Depends on

- [The group presentation associated to an open cover](cover-group-presentation.md)

## Proof depends on

- [A loop splits across an open cover](../basic-constructions/loop-in-open-cover.md)

## Sources

- [Hatcher §1.2, Theorem 1.20 and its use of Lemma 1.15](../../../sources/hatcher-1-2.md)
