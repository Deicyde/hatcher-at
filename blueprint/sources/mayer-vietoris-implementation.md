# Mayer–Vietoris implementation specification

This is a project-authored implementation specification for the selected
Mayer–Vietoris material in Hatcher §2.2. It is not an independent
mathematical source. The cited statements and signs come from the official
Hatcher PDF at the locations recorded in
[the §2.2 source note](hatcher-2-2.md).

## Mathematical scope

For subsets `A B : Set X` whose interiors cover `X`, construct the ordinary
and reduced Mayer–Vietoris sequences. The ordinary sequence has canonical
maps

`H_n(A ∩ B;R) → H_n(A;R) ⊞ H_n(B;R) → H_n(X;R)`

given by `(i_A*, -i_B*)` and the sum of the two inclusion maps. Its connecting
map sends a small representative `z = x + y` to the class represented by
`∂x = -∂y`. Include exact adjacent-degree windows and the degree-zero
epimorphism onto `H_0(X;R)`.

The reduced sequence has the formally identical maps on reduced homology.
Include its adjacent-degree windows and, when `A ∩ B` is nonempty, its
terminal exact sequence ending in `H̃_0(X;R) → 0`.

## Chain representation

Reuse `Hatcher.Excision.smallSubcomplexOfSet` and
`Hatcher.Excision.smallSubcomplex`. For arbitrary `A` and `B`, write
`C_*^{A+B}(X;R)` for the chain complex of
`smallSubcomplex (Bool.rec A B)`. Construct the short complex

`C_*(A ∩ B;R) → C_*(A;R) ⊞ C_*(B;R) → C_*^{A+B}(X;R)`.

The first chain map is the biproduct lift of the two subspace-inclusion maps,
with a minus sign on the `B` component. The second is the biproduct descent of
the two maps into the small-cover subcomplex. These choices must reduce on
chains to Hatcher's formulas `x ↦ (x,-x)` and `(x,y) ↦ x+y`; do not reverse
the sign convention merely because the resulting exact sequence would be
isomorphic.

Prove short exactness degreewise. A useful splitting sends a small singular
simplex to the `A` summand when it lies in `A`, and otherwise to the `B`
summand. The coefficient-general `Sigma`-basis arguments in
`Hatcher/Excision/Devissage.lean` are implementation precedent, but its
private helpers are not part of the public contract.

## Homology transport

Use `Hatcher.Excision.CoverCondition` as the public cover hypothesis. Expose a
public conversion to `SmallSimplicesCondition` in the new implementation
layer rather than making a second cover predicate. Transport the homology
sequence of the short exact chain complex along
`smallChainInclusionHomotopyEquiv(...).toHomologyIso` for the third term and
along the additive homology functor's binary-biproduct comparison for the
middle term.

Package six consecutive terms with `ComposableArrows`, following the existing
pair and triple sequence APIs. The public sequence must display singular
homology of the actual subspace types and ambient space, rather than exposing
range-subcomplex or small-chain implementation objects.

The connecting-map formula should follow the generic
`ShortComplex.ShortExact.δ_eq` interface, as the pair formula in
`Hatcher/Singular/Relative.lean` does. State it for generalized elements if
that keeps the result coefficient-general.

## Reduced chains

For an arbitrary family, define the augmentation on small chains by restricting
the ordinary singular-chain augmentation. Under `SmallSimplicesCondition`,
extend the small-chain inclusion and its homotopy inverse through
`ChainComplex.augment`, using the identity on the inserted coefficient object
in degree zero. The existing fact that every vertex is small under an interior
cover supplies the degree-zero compatibility.

The augmented Mayer–Vietoris short complex has the ordinary chain sequence in
each successor degree and

`R → R ⊞ R → R`

in degree zero, with maps `(𝟙_R,-𝟙_R)` and codiagonal addition. Prove it short
exact degreewise, then transport its homology sequence to the existing
`Hatcher.Reduced.homologyFunctor`. Require `Nonempty (A ∩ B)` only for the
terminal degree-zero statement, where it kills the suppressed augmented
degree-zero homology.

## Intended public contract

Place the source-facing declarations in `Hatcher.MayerVietoris`; keep the
general augmented small-chain bridge in `Hatcher.Excision`. The fine roadmap
targets these main declarations:

1. `Hatcher.MayerVietoris.chainComplexShortComplex`;
2. `Hatcher.MayerVietoris.chainComplexShortComplex_shortExact`;
3. `Hatcher.MayerVietoris.sequence_exact` and the degree-zero endpoint;
4. `Hatcher.Excision.smallAugmentedChainInclusionHomotopyEquiv`;
5. `Hatcher.MayerVietoris.augmentedChainComplexShortComplex_shortExact`; and
6. `Hatcher.MayerVietoris.reducedSequence_exact` and its terminal endpoint.

Supporting definitions should name the canonical intersection, union, and
connecting maps so later applications can state commutative diagrams without
unfolding a `ComposableArrows` value.

For universes `w`, `v`, and `u`, chain-level definitions use an ambient
category `C : Type u` with `[Category.{v} C]`, `[Preadditive C]`, and
`[HasCoproducts.{w} C]`. Add `[Abelian C]` for short exactness and long exact
homology sequences. Hatcher's integral result is the specialization to the
coefficient object `AddCommGrpCat.of ℤ`.

## Pinned API and prior art

The repository pins Mathlib `v4.34.1` at
`d13f23b723b8a846827a245b89c10fc7d3f11612`. Relevant local and pinned APIs
include:

- `Hatcher.Excision.smallSubcomplexOfSet`, `smallSubcomplexOfSet_inter`, and
  `smallSubcomplex_bool`;
- `Hatcher.Excision.smallChainInclusionHomotopyEquiv`;
- `Hatcher.Excision.CoverCondition`;
- `Hatcher.Reduced.augmentedSingularChainComplexFunctor` and
  `Hatcher.Reduced.homologyFunctor`;
- `HomologicalComplex.shortExact_of_degreewise_shortExact`;
- `HomologicalComplex.HomologySequence.composableArrows₅` and
  `composableArrows₅_exact`; and
- the additive `HomologicalComplex.homologyFunctor` and its
  `Functor.mapBiprod` comparison.

The pinned Mathlib has no singular-homology Mayer–Vietoris theorem. Its files
named `MayerVietoris` concern sheaves and are unrelated. Open Mathlib PR
[#38369](https://github.com/leanprover-community/mathlib4/pull/38369) proposes
an abstract Eilenberg–Steenrod interface but does not supply this singular
chain sequence and is not present at the pin. None of these roadmap leaves is
Mathlib-backed.

The Apache-2.0-licensed
[`TauCetiProject/TauCeti`](https://github.com/TauCetiProject/TauCeti/tree/d357125649fae2df580acf7f4ed8de03a20aacca)
snapshot at commit
[`d357125649fae2df580acf7f4ed8de03a20aacca`](https://github.com/TauCetiProject/TauCeti/commit/d357125649fae2df580acf7f4ed8de03a20aacca)
is direct implementation prior art:

- its generic simplicial-set
  [`MayerVietoris.lean`](https://github.com/TauCetiProject/TauCeti/blob/d357125649fae2df580acf7f4ed8de03a20aacca/TauCeti/AlgebraicTopology/SimplicialSet/Homology/MayerVietoris.lean)
  provides `SSet.shortExact_mayerVietorisShortComplex`, the signed biproduct
  maps, exactness, the degree-zero epimorphism, and connecting-map naturality
  for a pushout square;
- its singular
  [`Basic.lean`](https://github.com/TauCetiProject/TauCeti/blob/d357125649fae2df580acf7f4ed8de03a20aacca/TauCeti/AlgebraicTopology/Singular/MayerVietoris/Basic.lean)
  transports that sequence across a small-chain equivalence, but assumes that
  the two cover members are open; and
- its singular
  [`Reduced.lean`](https://github.com/TauCetiProject/TauCeti/blob/d357125649fae2df580acf7f4ed8de03a20aacca/TauCeti/AlgebraicTopology/Singular/MayerVietoris/Reduced.lean)
  constructs a reduced connecting morphism and acyclic-cover applications,
  not the full augmented reduced sequence selected here.

This project keeps Hatcher's more general hypothesis that the interiors of
arbitrary subsets cover `X`, expressed by the already formalized
`Hatcher.Excision.CoverCondition`. TauCeti is neither a dependency nor pinned
Mathlib coverage; port or adapt its categorical organization only after
checking it against this repository's stable pin and local small-chain APIs.

## Explicit exclusions

This milestone does not include a category of cover morphisms or a separate
naturality theorem, the neighborhood-deformation-retract or CW-subcomplex
extension on printed page 150, Examples 2.46–2.48, sphere homology, degree,
cellular homology, or coefficients as a separate source topic.
