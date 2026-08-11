---
declaration: theorem
origin: cited
---

# A loop splits across an open cover

**Hatcher, Lemma 1.15 (page 35).** If `X` is the union of path-connected open
sets `Aα` each containing the basepoint `x₀`, and each intersection `Aα ∩ Aβ`
is path-connected, then every loop in `X` at `x₀` is homotopic to a product of
loops each contained in a single `Aα`.

The proof subdivides the interval by a Lebesgue-number argument so that each
subinterval maps into some `Aα`, then uses path-connectedness of the pairwise
intersections to join each subdivision point back to `x₀` inside the
intersection of the two neighbouring sets.

This is the combinatorial heart of the van Kampen theorem, and §1.2 restates it
in that generality. Formalizing it here means the §1.2 work will likely
generalize rather than reuse this statement verbatim; that trade was accepted
when the slice was scoped, and
[the §1.2 page](../van-kampen/README.md) records it.

Intended artifact: `Hatcher.loop_homotopic_prod_of_isOpenCover` in
`Hatcher/Sphere/LoopInOpenCover.lean`.

## Depends on

No roadmap prerequisites. Rests on Mathlib's path algebra and the Lebesgue
number lemma.

## Sources

- [Hatcher §1.1, Lemma 1.15, page 35](../../../sources/hatcher-1-1.md)
