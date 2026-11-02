# Triple-homology implementation specification

This is a project-authored implementation specification for the long exact
sequence of a triple in Hatcher §2.1. It is not an independent mathematical
source. The mathematical statements come from the official Hatcher PDF at the
locations recorded in [the section source note](hatcher-2-1.md).

## Scope

For embeddings `B ↪ A ↪ X`, Hatcher constructs the short exact sequence

`0 → C_*(A,B;R) → C_*(X,B;R) → C_*(X,A;R) → 0`

on printed pages 118–119 and its associated long exact homology sequence. On
page 128 he records naturality for maps of triples. This slice covers the
topological triple and its maps, the chain-level short exact sequence, the long
exact sequence including its degree-zero endpoint, and naturality of the
connecting morphism.

The specialization with `B` a point, excision, good-pair quotient comparison,
sphere computations, and the simplicial–singular comparison are not part of
this slice.

## Representation

Bundle a topological triple as composable embeddings `B ↪ A ↪ X`, written in
source order as `(X,A,B)`. It determines the three Mathlib `TopPair` objects
`(A,B)`, `(X,B)`, and `(X,A)`. A morphism of triples consists of compatible maps
on `B`, `A`, and `X`; it induces maps on all three pairs and hence on their
relative chain complexes and homology objects.

This packaging is project-authored: Hatcher uses triples and maps between them
without defining a category of triples. Keep the public Hatcher-facing layer
thin so that a future upstream triple API can replace its implementation.

## Coefficients and indexing

As in the existing relative-homology API, state reusable results for a
coefficient object `R` in an abelian category with the coproducts required by
singular chains. Hatcher's groups are the specialization to
`AddCommGrpCat.of ℤ`.

Mathlib indexes chain complexes by `ℕ`. For adjacent degrees `m + 1 = n`, expose
six consecutive terms

`H_n(A,B) → H_n(X,B) → H_n(X,A) → H_m(A,B) → H_m(X,B) → H_m(X,A)`.

Also expose the degree-zero epimorphism `H_0(X,B) → H_0(X,A)`, since overlapping
six-term windows do not by themselves state exactness at the terminal
degree-zero object.

## Chain-level construction

Apply `Hatcher.Relative.chainComplexFunctor R` to the two canonical maps of
pairs `(A,B) → (X,B) → (X,A)`. Their composite is zero. Prove the resulting
short complex exact using the cokernel tail of
`CategoryTheory.kernelCokernelCompSequence` and transport it through the
existing relative-chain cokernel universal properties. This avoids a second
relative-chain quotient API and avoids classical choices of complementary
bases.

The pinned Mathlib `v4.34.1` contains the generic homology-sequence machinery
`HomologicalComplex.HomologySequence.composableArrows₅`,
`composableArrows₅_exact`, `mapComposableArrows₅`, and `δ_naturality`. Use these
to package the long exact sequence and its naturality after establishing the
chain-level short exact sequence.

## Prior art

Joël Riou's open Mathlib PR
[#41318](https://github.com/leanprover-community/mathlib4/pull/41318) contains a
122-line simplicial-set triple construction and a degreewise splitting proof.
It remains unmerged and paused pending excision, and its branch uses helper APIs
that are not present at this repository's pin. It is implementation prior art,
not a project dependency or a source of `mathlib: true` claims. The local proof
uses the pinned kernel–cokernel sequence instead while retaining compatible
mathematical orientation and naming.
