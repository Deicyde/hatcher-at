# Hatcher §2.2, Mayer–Vietoris sequences

Selected material from Hatcher, *Algebraic Topology*, §2.2, printed pages
149–150 (PDF pages 158–159). It comprises the core Mayer–Vietoris sequences,
their neighborhood-deformation-retract extension, and Example 2.46.
Statements below are paraphrased; consult the official PDF for the source text
and diagrams.

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

## Neighborhood-deformation-retract extension

Later on printed page 150, Hatcher considers a decomposition `X = A ∪ B`
where `A` and `B` deformation retract from neighborhoods `U` and `V`, and
`A ∩ B` deformation retracts from `U ∩ V`. The three deformation retractions
give homology isomorphisms from `A`, `B`, and `A ∩ B` to their neighborhood
counterparts. Comparing the long exact homology sequences associated to the
two short exact chain-complex sequences, the five lemma then shows that
`C_*(A+B) → C_*(U+V)` induces an isomorphism on homology.
Transporting the open-cover sequence for `U` and `V` therefore gives
Mayer–Vietoris sequences with the homology of `A`, `B`, and `A ∩ B` and the
actual inclusion-induced maps.

The claim is about the maps induced on homology, not about the underlying
degreewise chain maps being isomorphisms. The selected formal statement takes
the neighborhoods and their deformation-retraction data as hypotheses. It does
not construct Hatcher's `Nε(A)` neighborhoods for CW subcomplexes.

## Example 2.46: sphere recurrence

On printed page 150, for `n > 0`, the northern and southern hemispheres of
`Sⁿ` are contractible and meet in the equatorial `Sⁿ⁻¹`. The reduced
Mayer–Vietoris sequence therefore gives, in positive homological degrees,

`H̃_i(Sⁿ;R) ≅ H̃_{i-1}(Sⁿ⁻¹;R)`.

Together with the direct `S⁰` calculation and the vanishing of reduced zeroth
homology for positive-dimensional spheres, this yields the sphere computation
stated as Corollary 2.14 on printed page 114. The roadmap attributes the
recurrence to Example 2.46 and does not claim to formalize Corollary 2.14's
original good-pair quotient proof.

## Selected boundary

The first selected source unit contains the ordinary and reduced binary-cover
Mayer–Vietoris sequences and their chain-level construction. A second selected
unit contains the conditional neighborhood-deformation-retract extension and
Example 2.46. The general CW-subcomplex neighborhood construction, Examples
2.47–2.48, Mayer–Vietoris naturality as a separate API, relative
Mayer–Vietoris, degree, cellular homology, and homology with general
coefficient groups as a separate source topic remain excluded.

The local formalization may use a general abelian target category and a
coefficient object `R`; Hatcher's displayed groups are the integral
specialization.
