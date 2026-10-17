# Local-degree implementation specification

This is a project-authored implementation specification for the selected
local-degree passage of Hatcher §2.2. It fixes the Lean representation and the
bridging lemmas needed to formalize the source without treating implementation
choices as claims made by Hatcher.

## Boundary and public theorem

The public endpoint is Proposition 2.30 for `n > 0`: if
`f : TopCat.sphere n ⟶ TopCat.sphere n` and the fiber over `y` is finite, then
the global integral degree is the finite sum of the local degrees over that
fiber. Local degree is also exposed for an arbitrary isolated preimage, and a
sphere homeomorphism has local degree `1` or `-1`.

The milestone does not construct maps of prescribed degree, compute circle
power maps, prove suspension invariance, or begin cellular homology.

## General coproducts of topological pairs (completed)

The completed generic API extends the pointed-pair coproduct construction.
For a family `P : ι → TopPair`, its ambient and subspace are the topological
sigma types of `P i`. The pair map applies each `P i` structure map within its
own summand, and every summand has a canonical pair morphism into the sigma
pair.

The shared chain argument gives an isomorphism

`∐ i, C_*(P i; R) ≅ C_*(sigmaPair P; R)`

with the expected component formula. The completed homology comparison gives

`∐ i, H_k(P i; R) ≅ H_k(sigmaPair P; R)`

under the same `AB4OfSize` exact-coproduct hypothesis used by the existing
pointed result. Both comparisons identify the canonical forward map and its
summand components. The pointed declarations remain exact compatibility
specializations of shared implementations and proofs; the empty index and
universe-zero integral specializations are preserved.

## Deleted pairs and disjoint open unions

Write `deletedPair X F` for `(X, X \ F)`. Generalize the completed singleton
open-neighborhood theorem: if `F` is closed and contained in an open set `W`,
the canonical map from the deleted pair inside `W` to `deletedPair X F`
induces an isomorphism on relative homology. The proof is the existing binary
cover excision argument with `{x}` replaced by `F`.

For pairwise disjoint open subsets `U i` of a space, construct the canonical
homeomorphism from `Σ i, U i` to their union. With points `x i ∈ U i`, lift
this to a pair isomorphism between the sigma pair of
`(U i, U i \ {x i})` and the union with the range of the `x i` deleted.
Record component formulas; later proofs must use canonical inclusions rather
than an arbitrary isomorphism between abstract groups.

## Oriented local homology

For `y : Sⁿ`, define the target local fundamental class by composing the
completed ordered reduced sphere class with
`Hatcher.Relative.reducedPairProjection` for
`puncturedPair (Sⁿ) y`. The complement of `y` is contractible by the completed
stereographic theorem, so this class is an isomorphism. This choice transports
the exact orientation already used by `Hatcher.Sphere.degree`.

An isolated-preimage neighborhood for `f`, `x`, and `y` consists of an open
set `U` containing `x`, the equality `f x = y`, and the assertion that no
other point of `U` maps to `y`. It induces a morphism

`(U, U \ {x}) → (Sⁿ, Sⁿ \ {y})`.

Transport the source local fundamental class backward through the
open-neighborhood homology isomorphism, conjugate the induced map by the two
oriented local classes, and evaluate the resulting endomorphism of `ℤ` at
`1`. Prove its fundamental-class equation. For nested isolated neighborhoods,
naturality and the open-neighborhood isomorphisms show equality. Intersecting
two neighborhoods then proves independence, after which the public local
degree may use a classical choice of witness without exposing that choice.

## Finite fibers and the sum formula

Give a finite fiber its subtype index. `Set.Finite.t2_separation` supplies
pairwise disjoint open neighborhoods of all fiber points; pairwise disjointness
ensures that each contains no other fiber point. Their union is an open
neighborhood of the full fiber.

Compose the general sigma-pair homology isomorphism, the disjoint-union pair
isomorphism, and deleted-pair excision to obtain the canonical finite-sum
isomorphism

`∐ x : fiber f y, H_n(U_x, U_x - {x})`
`  ≅ H_n(Sⁿ, Sⁿ - fiber f y)`.

Its component formula must identify every categorical summand injection with
the inclusion of the corresponding local pair. Prove that the reduced sphere
class projected to the finite-puncture pair is the finite sum of the oriented
local classes. The pair map induced by `f` factors on each summand through the
isolated-preimage pair map, so the summand class maps to its local-degree
multiple. Naturality of `reducedPairProjection`, together with the completed
positive-degree comparison between reduced and ordinary homology, identifies
the image of the finite-puncture class with the global-degree multiple of the
target local class. Cancel the latter isomorphism to obtain Proposition 2.30.
The construction includes the empty fiber, so the resulting empty sum
recovers the completed nonsurjective-degree-zero theorem.

## Pinned API and proof-integrity requirements

Reuse the following completed declarations and their naturality laws:

- `Hatcher.Relative.puncturedPair`,
  `localHomologyOpenNeighborhoodMap`, and
  `localHomologyOpenNeighborhoodMap_isIso_of_t1`;
- `Hatcher.Relative.reducedPairProjection` and
  `reducedPairProjection_naturality`;
- `Hatcher.Relative.relativeChainComplexSigmaPairIso` and
  `relativeHomologySigmaPairIso`, with `relativeChainComplexSigmaIso` and
  `relativeHomologySigmaIso` retained as their exact pointed special cases;
- `Hatcher.Excision.coverHomologyMap_isIso` and the deleted-subset form of
  excision;
- `Hatcher.Simplex.doubleSimplexSphereFundamentalClass` and
  `Hatcher.Sphere.integralSphereFundamentalClass`;
- `Hatcher.Sphere.degree`,
  `integralSphereFundamentalClass_map`, and the degree laws; and
- `Set.Finite.t2_separation` from pinned Mathlib.

Every comparison theorem must identify the actual induced morphism and state
its component or naturality equation. An arbitrary existence of an isomorphism
is insufficient for the sum formula. The implementation may not use `sorry`,
`admit`, new axioms, `unsafe`, `partial`, or `native_decide`.

## Fine decomposition

The source unit has twenty formalization leaves: general sigma pairs;
relative chains and homology of those sigma pairs; a disjoint-open-union
homeomorphism; deleted-pair neighborhood excision; the punctured-pair union
isomorphism; the oriented local sphere class; isolated-preimage data; local
degree on a chosen neighborhood; shrinking invariance; well-defined local
degree; the homeomorphism case; finite-fiber neighborhoods; the finite-puncture
pair comparison; its homology coproduct isomorphism; the diagonal projection
matrix; the finite-puncture orientation sum; the finite-fiber pair map on local
classes; its global-degree square; and Proposition 2.30.
