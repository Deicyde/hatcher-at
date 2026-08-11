# Homology

Hatcher's Chapter 2 (pages 97–184). Mapped, not yet decomposed.

The fundamental group sees only loops, and it is non-abelian and hard to
compute in high dimensions. Homology replaces it with a sequence of abelian
groups `Hₙ(X)` that are computable by machine and defined in every degree, at
the cost of a longer road to the definition. Chapter 2 builds them twice —
combinatorially from a Δ-complex structure, and functorially from singular
simplices — proves the two agree, and then makes them computable through the
long exact sequences.

[Simplicial and singular homology](simplicial-and-singular/README.md) gives
both definitions, proves homotopy invariance, establishes excision and the long
exact sequence of a pair, and reconciles the two theories.

[Computations and applications](computations-and-applications/README.md) turns
that machinery into results: the degree of a map `Sⁿ → Sⁿ`, cellular homology
for CW complexes, Mayer–Vietoris, and homology with coefficients. Brouwer in
all dimensions and invariance of domain land here.

[The formal viewpoint](formal-viewpoint/README.md) axiomatizes what was built,
as the Eilenberg–Steenrod axioms, and introduces the categorical language.

Mathlib defines singular homology in
`Mathlib/AlgebraicTopology/SingularHomology/` and proves homotopy invariance
and `H₀`, and states the Eilenberg–Steenrod axioms in
`AlgebraicTopology/EilenbergSteenrod.lean`. Excision, the long exact sequence
of a pair, Mayer–Vietoris for singular homology, `Hₙ(Sⁿ)`, degree, and cellular
homology are all absent. Excision is the hard prerequisite for the rest.

## Sections

- [Simplicial and singular homology](simplicial-and-singular/README.md)
- [Computations and applications](computations-and-applications/README.md)
- [The formal viewpoint](formal-viewpoint/README.md)

## Sources

- [Hatcher, Chapter 2](../../sources/hatcher.md)
