# Relative-homology implementation specification

This is a project-authored implementation specification for the selected
relative-homology and exact-sequence material in Hatcher §2.1. It is not an
independent mathematical source. The mathematical statements come from the
official Hatcher PDF at the locations recorded in
[the section source note](hatcher-2-1.md).

## Scope

This slice contains Hatcher's augmented-complex definition of reduced homology
(page 110), functoriality of reduced homology (page 113), relative chains and
homology (pages 115–117), Theorem 2.16 and its application to a pair (page 117),
Example 2.18 and Proposition 2.19 (page 118), and naturality of the pair and
reduced-pair long exact sequences (pages 127–128).

Theorem 2.13, Example 2.17, the triple sequence, excision, small chains,
good-pair quotient comparison, sphere applications, invariance of dimension,
and the simplicial–singular comparison remain deferred. This prevents
Theorem 2.13 from being placed before the excision and quotient results used in
its proof.

## Coefficients and indexing

State the reusable API for a coefficient object `R` in an abelian category with
the coproducts needed by singular chains. Hatcher's integral groups are the
specialization to `AddCommGrpCat.of ℤ`.

Mathlib indexes chain complexes by `ℕ`. To represent Hatcher's augmented
complex

```text
⋯ → C₁(X; R) → C₀(X; R) → R → 0,
```

use `ChainComplex.augment`: degree zero is `R`, and degree `n + 1` is the
ordinary singular chain object in degree `n`. Define reduced homology in degree
`n` as homology of this augmented complex in degree `n + 1`. The chain-level
augmentation sends every singular zero-simplex summand to `𝟙 R`; prove its
composite with the degree-one boundary is zero and make the construction
natural in the space.

Do not define reduced homology to be relative homology at a chosen basepoint.
That equivalence is the content of Example 2.18 and must be proved rather than
built into the definition. For a chosen point, record separately the
non-natural splitting `H₀(X; R) ≅ H̃₀(X; R) ⊞ R`; in positive degrees,
the shift of the augmented complex gives `H̃ₙ(X; R) ≅ Hₙ(X; R)`.

## Relative singular homology

Use Mathlib's `TopPair`, where `P.fst` is the ambient space, `P.snd` is the
subspace, and `P.map : P.snd ⟶ P.fst` is an embedding. Apply
`TopCat.toSSet` to both sides to obtain a simplicial-set pair. Preserve this
ordering: `SSetPair.left` is the subobject and `SSetPair.right` is the ambient
object.

At the current Mathlib `v4.34.1` pin,
`Hatcher.Relative.singularPairFunctor : TopPair ⥤ SSetPair` is formalized.
The next implementation node obtains the relative singular chain-complex and
homology functors by composing it with `SSetPair.chainComplexFunctor` and
`SSetPair.homologyFunctor`. These are the quotient chains
`Cₙ(X; R) / Cₙ(A; R)` from pages 115–116. Maps of pairs are handled by
functoriality rather than by a second ad hoc map construction.

## Exactness and naturality

The pinned Mathlib already contains the algebraic long exact sequence for a
short exact sequence of chain complexes:

- `HomologicalComplex.HomologySequence.composableArrows₅_exact`;
- `HomologicalComplex.HomologySequence.δ_naturality`.

Use the short exact sequence from absolute chains of `A`, absolute chains of
`X`, and relative chains of `(X,A)` to expose Hatcher's pair sequence. Its
connecting morphism sends a relative cycle represented by `α` to the homology
class of `∂α`, as on page 117, after specializing to ordinary integral
homology. Naturality covers maps of pairs and the pair and reduced-pair
sequences discussed on pages 127–128; the triple sequence and the quotient
sequence for Theorem 2.13 are not part of this slice.

## Relative homotopy invariance

For a `TopPair.Homotopy f g`, use the compatible absolute singular-chain
homotopies on the ambient and subspace maps. Descend them through the
relative-chain cokernel to a chain homotopy between the relative maps, then
apply `Homotopy.homologyMap_eq`. This proves Proposition 2.19 without treating
the `HomologyPretheory.IsHomotopyInvariant` interface as an implementation.

## The pointed-pair comparison

For a point `x₀ : X`, use the pair `(X,{x₀})`. Combine the reduced pair
sequence with the homology calculation of a point to construct
`Hₙ(X,{x₀};R) ≅ H̃ₙ(X;R)` in every degree. The degree-zero case is
part of the theorem and must not be dropped or inferred from the
positive-degree comparison.

## Dependency status and prior art

The original roadmap audit used Mathlib `v4.31.0` at
`fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`. That historical pin had the
generic homology sequence and `TopPair`, but not `SSetPair` relative homology.

Mathlib PR [#41285](https://github.com/leanprover-community/mathlib4/pull/41285)
was merged as commit
[`dbd0e3c605be1c1ac468d358d0815b9183566a8a`](https://github.com/leanprover-community/mathlib4/commit/dbd0e3c605be1c1ac468d358d0815b9183566a8a)
and is included at the repository's current stable Mathlib `v4.34.1` pin. It
provides `SSetPair`, `SSetPair.chainComplex`, `SSetPair.homologyFunctor`,
`SSetPair.homologyδ`, and `SSetPair.homology_exact₁/₂/₃`. The simplicial-pair
foundation is therefore exact Mathlib coverage, and `singular-pair-functor` is
formalized locally. The relative chain-complex and homology functors are also
formalized locally by composition with this API.

Andrew Yang's PR
[#37659](https://github.com/leanprover-community/mathlib4/pull/37659) is an
older direct relative-singular-homology proposal superseded in design by
`SSetPair`. Joël Riou's
[`excision`](https://github.com/joelriou/excision/tree/8b56cd0c8e5f39a7c2f36418c80b298e469596a6)
repository supplies useful implementation prior art for
`TopPair.toSSetPair`, subdivision, small chains, and excision, but it is an
unreleased work-in-progress and is not a dependency or a source of
`mathlib: true` claims. PR
[#41318](https://github.com/leanprover-community/mathlib4/pull/41318) for the
triple sequence remains open and paused pending excision.

## Readiness status

The Mathlib gate is satisfied: the simplicial-pair foundation is complete at
`v4.34.1`, and the singular-pair and relative-homology functors are formalized
locally. Eight of the fifteen relative-homology leaves are complete, with seven
downstream leaves incomplete; four statements are ready to formalize.
