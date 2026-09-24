---
article_id: af_9da1e6c5697d0bac0b2a1624
---

# Homology

Hatcher's Chapter 2 (pages 97–184). Two selected §2.1 slices are decomposed:
the completed singular-homology functoriality spine and a new reduced- and
relative-homology exact-sequence spine. The rest of the chapter remains mapped
or explicitly deferred.

The fundamental group sees only loops, and it is non-abelian and hard to
compute in high dimensions. Homology replaces it with a sequence of abelian
groups `Hₙ(X)` that are computable by machine and defined in every degree, at
the cost of a longer road to the definition. Chapter 2 builds them twice —
combinatorially from a Δ-complex structure, and functorially from singular
simplices — proves the two agree, and then makes them computable through the
long exact sequences.

[Simplicial and singular homology](simplicial-and-singular/README.md) has a
completed ten-node first slice covering singular chains, `H₀`, the point
calculation, functoriality, and homotopy invariance. A second fifteen-leaf
slice covers reduced and relative homology, Theorem 2.16, the long exact
sequence of a pair and its naturality, Example 2.18, and Proposition 2.19.
The simplicial-pair foundation is gated on upgrading from the current Mathlib
pin to a stable release containing PR #41285. The Δ-complex and excision
branches remain deferred.

[Computations and applications](computations-and-applications/README.md) turns
that machinery into results: the degree of a map `Sⁿ → Sⁿ`, cellular homology
for CW complexes, Mayer–Vietoris, and homology with coefficients. Brouwer in
all dimensions and invariance of domain land here.

[The formal viewpoint](formal-viewpoint/README.md) axiomatizes what was built,
as the Eilenberg–Steenrod axioms, and introduces the categorical language.

The pinned Mathlib defines singular homology, proves homotopy invariance and
`H₀`, and contains the generic algebraic long exact sequence. Relative
simplicial-set homology is available in stable Mathlib `v4.34.1`, after this
repository's `v4.31.0` pin. Singular excision, Mayer–Vietoris, `Hₙ(Sⁿ)`, degree,
and cellular homology remain outside the pinned library. Excision is the main
prerequisite for the rest.

## Sections

- [Simplicial and singular homology](simplicial-and-singular/README.md)
- [Computations and applications](computations-and-applications/README.md)
- [The formal viewpoint](formal-viewpoint/README.md)

## Sources

- [Hatcher, Chapter 2](../../sources/hatcher.md)
