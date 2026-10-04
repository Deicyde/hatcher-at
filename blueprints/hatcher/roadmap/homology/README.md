---
article_id: af_9da1e6c5697d0bac0b2a1624
---

# Homology

Hatcher's Chapter 2 (pages 97–184). Five selected §2.1 slices are complete: the
singular-homology functoriality spine, a fifteen-leaf reduced- and
relative-homology exact-sequence spine, a four-leaf triple-sequence slice, and
a ten-leaf small-chains/excision DAG, together with the fifteen-leaf good-pair
quotient milestone. The six-leaf §2.2 Mayer–Vietoris slice is
also complete. The thirteen-leaf neighborhood-retract, Example 2.46, and
reduced sphere-homology milestone is complete as well, as is its three-leaf
Corollary 2.15 continuation through Brouwer's theorem. The good-pair quotient
milestone formalizes Proposition 2.22, Theorem 2.13, and naturality. The rest
of the chapter remains explicitly deferred.

The fundamental group sees only loops, and it is non-abelian and hard to
compute in high dimensions. Homology replaces it with a sequence of abelian
groups `Hₙ(X)` that are computable by machine and defined in every degree, at
the cost of a longer road to the definition. Chapter 2 builds them twice —
combinatorially from a Δ-complex structure, and functorially from singular
simplices — proves the two agree, and then makes them computable through the
long exact sequences.

[Simplicial and singular homology](simplicial-and-singular/README.md) has a
completed ten-node first slice covering singular chains, `H₀`, the point
calculation, functoriality, and homotopy invariance. A second fifteen-leaf slice
covers reduced and relative homology, Theorem 2.16, the long exact sequence of
a pair and its naturality, Example 2.18, and Proposition 2.19. Its four reduced
homology leaves, generic algebraic exact-sequence leaf, simplicial-pair
foundation, singular-pair functor, relative-homology functor, and pair long
exact sequence with its connecting-map formula and naturality are complete.
The relative homotopy branch through Proposition 2.19, the reduced pair
sequence with its naturality, and the pointed comparison are complete as well.
The completed third slice adds the chain-level short exact sequence of a
triple, its long exact sequence, degree-zero endpoint, and naturality. Mathlib `v4.34.1`
contains PR #41285 but not the open triple PR #41318. The
[small-chains/excision branch](simplicial-and-singular/relative-homology/small-chains-and-excision/README.md)
is decomposed into ten complete leaves; the Δ-complex branch remains deferred.
The completed
[good-pair quotient branch](simplicial-and-singular/relative-homology/good-pair-quotient/README.md)
adds the functorial point quotient and the canonical quotient exact sequence.

[Computations and applications](computations-and-applications/README.md)
contains the six complete ordinary and reduced binary-cover Mayer–Vietoris
leaves, the completed sphere-homology milestone, and the completed Corollary
2.15 continuation. The branch adds conditional neighborhood transport, the
hemisphere recurrence, the full reduced homology calculation, no-retraction,
and Brouwer. Degree, cellular homology, the
later Mayer–Vietoris examples, and homology with coefficients remain deferred.
Invariance of domain belongs to out-of-scope Additional Topic §2.B.

[The formal viewpoint](formal-viewpoint/README.md) axiomatizes what was built,
as the Eilenberg–Steenrod axioms, and introduces the categorical language.

The pinned Mathlib `v4.34.1` defines singular homology, proves homotopy
invariance and `H₀`, contains the generic algebraic long exact sequence, and
contains relative simplicial-set homology from PR #41285. Singular excision,
Mayer–Vietoris, `Hₙ(Sⁿ)`, degree, and cellular homology remain outside the
pinned library. The completed local excision milestone supplies the main input
used by the Mayer–Vietoris branches; sphere homology is formalized locally
rather than claimed as upstream coverage.

## Sections

- [Simplicial and singular homology](simplicial-and-singular/README.md)
- [Computations and applications](computations-and-applications/README.md)
- [The formal viewpoint](formal-viewpoint/README.md)

## Sources

- [Hatcher, Chapter 2](../../sources/hatcher.md)
