# Homology

Hatcher's Chapter 2 (pages 97–184). The selected §2.1 singular-homology
functoriality spine is decomposed; the rest of the chapter remains mapped or
explicitly deferred.

The fundamental group sees only loops, and it is non-abelian and hard to
compute in high dimensions. Homology replaces it with a sequence of abelian
groups `Hₙ(X)` that are computable by machine and defined in every degree, at
the cost of a longer road to the definition. Chapter 2 builds them twice —
combinatorially from a Δ-complex structure, and functorially from singular
simplices — proves the two agree, and then makes them computable through the
long exact sequences.

[Simplicial and singular homology](simplicial-and-singular/README.md) now has a
ten-node first slice covering singular chains, `H₀`, the point calculation,
functoriality, and homotopy invariance. Eight nodes are exact pinned Mathlib
declarations and the other two are formalized locally. Its Δ-complex,
relative-homology, and excision branches remain deferred.

[Computations and applications](computations-and-applications/README.md) turns
that machinery into results: the degree of a map `Sⁿ → Sⁿ`, cellular homology
for CW complexes, Mayer–Vietoris, and homology with coefficients. Brouwer in
all dimensions and invariance of domain land here.

[The formal viewpoint](formal-viewpoint/README.md) axiomatizes what was built,
as the Eilenberg–Steenrod axioms, and introduces the categorical language.

The pinned Mathlib defines singular homology and proves homotopy invariance and
`H₀`. Relative simplicial-set homology merged after the pin, while singular
excision, Mayer–Vietoris, `Hₙ(Sⁿ)`, degree, and cellular homology remain outside
the pinned library. Excision is the main prerequisite for the rest.

## Sections

- [Simplicial and singular homology](simplicial-and-singular/README.md)
- [Computations and applications](computations-and-applications/README.md)
- [The formal viewpoint](formal-viewpoint/README.md)

## Sources

- [Hatcher, Chapter 2](../../sources/hatcher.md)
