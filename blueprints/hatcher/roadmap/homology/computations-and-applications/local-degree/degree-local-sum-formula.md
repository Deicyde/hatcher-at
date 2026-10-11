---
article_id: af_680f7dd9f0023187b145b0eb
source_units: [hatcher-2-2-local-degree]
declaration: theorem
origin: cited
---

# Degree is the sum of the local degrees

Let `0 < n`, let `f : TopCat.sphere n ⟶ TopCat.sphere n`, and let
`y : TopCat.sphere n`. If `hfinite : (f ⁻¹' {y}).Finite`, install the finite
fiber subtype's `Fintype` from `hfinite`; every fiber point is then an isolated
preimage and the following finite sum is defined.

The main theorem `Hatcher.Sphere.degree_eq_sum_localDegree` is Hatcher's
Proposition 2.30:

`degree n hn f = ∑ x : fiber f y, localDegree n hn f x y (isolated x)`.

Apply the finite-fiber pair map to the orientation-sum equation and rewrite
each summand with `finiteFiberPairMap_localClass`. Naturality of
`reducedPairProjection` and the completed degree class equation identify the
same composite with the global-degree multiple of the target local class.
Cancel the target local orientation isomorphism and evaluate at `1`.
The statement includes the empty fiber; in that case the sum is zero and the
result agrees with the completed nonsurjective-degree theorem.

## Depends on

- [The finite-puncture class is the sum of the local classes](finite-puncture-orientation-sum.md)
- [The finite-fiber pair map acts by the local degrees](finite-fiber-local-map.md)
- [The finite-fiber pair map carries the global degree](global-degree-fiber-square.md)

## Sources

- [Hatcher §2.2, Proposition 2.30, printed page 136](../../../../sources/hatcher-2-2-local-degree.md)
- [Local-degree implementation specification](../../../../sources/local-degree-implementation.md)
