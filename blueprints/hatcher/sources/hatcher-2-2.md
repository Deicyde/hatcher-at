# Hatcher §2.2, Mayer–Vietoris sequences

Selected material from Hatcher, *Algebraic Topology*, §2.2, printed pages
149–150 (PDF pages 158–159). Statements below are paraphrased; consult the
official PDF for the source text and diagrams.

## Binary interior-cover sequence

Let `A` and `B` be subspaces of `X` whose interiors cover `X`. Hatcher gives
the long exact sequence

`⋯ → H_n(A ∩ B) → H_n(A) ⊕ H_n(B) → H_n(X)`
`→ H_{n-1}(A ∩ B) → ⋯ → H_0(X) → 0`.

The first map is induced by the two inclusions with the sign convention
`Φ(x) = (x, -x)`. The second is the sum of the inclusion-induced maps,
`Ψ(x, y) = x + y`.

## Chain-level construction

On printed pages 149–150, Hatcher writes `C_n(A+B)` for the subgroup of
singular chains in `X` that are sums of chains in `A` and chains in `B`. The
Mayer–Vietoris sequence comes from the degreewise short exact sequence

`0 → C_n(A ∩ B) → C_n(A) ⊕ C_n(B) → C_n(A+B) → 0`,

with the same maps `x ↦ (x,-x)` and `(x,y) ↦ x+y`. Proposition 2.21 identifies
the homology of `C_*(A+B)` with the singular homology of `X` when the
interiors cover.

For a cycle represented after subdivision as `z = x + y`, with `x` supported
in `A` and `y` supported in `B`, the connecting map is represented by
`∂x = -∂y` in `A ∩ B`.

## Reduced sequence

On printed page 150, Hatcher obtains the formally identical reduced
Mayer–Vietoris sequence by augmenting the preceding short exact sequence.
The displayed augmentation square has bottom row

`0 → ℤ → ℤ ⊕ ℤ → ℤ → 0`,

again with maps `x ↦ (x,-x)` and `(x,y) ↦ x+y`.

Hatcher defines reduced homology for nonempty spaces on printed page 110 to
avoid a degree-minus-one group. Accordingly, the terminal local contract
`H̃_0(A ∩ B) → H̃_0(A) ⊕ H̃_0(B) → H̃_0(X) → 0` assumes that `A ∩ B` is
nonempty. The adjacent positive-degree windows need no additional
nonemptiness hypothesis in the project's augmented-chain implementation.

## Selected boundary

This source unit contains only the ordinary and reduced binary-cover
Mayer–Vietoris sequences and their chain-level construction. It excludes the
neighborhood-deformation-retract extension later on printed page 150 and
Examples 2.46–2.48 beginning there, as well as degree, cellular homology, and
homology with general coefficient groups elsewhere in §2.2.

The local formalization may use a general abelian target category and a
coefficient object `R`; Hatcher's displayed groups are the integral
specialization.
