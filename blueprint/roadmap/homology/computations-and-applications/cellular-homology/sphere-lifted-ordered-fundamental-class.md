---
article_id: af_44f4c1e406da249186c75b97
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: Hatcher.Sphere.liftedOrderedSphereFundamentalClass_isIso, Hatcher.Sphere.liftedOrderedSphereFirstSimplex, Hatcher.Sphere.liftedOrderedSphereSecondSimplex, Hatcher.Sphere.liftedOrderedSphereCycle, Hatcher.Sphere.liftedOrderedSphereCycle_eq_difference, Hatcher.Sphere.liftedOrderedSphereCycle_d, Hatcher.Sphere.liftedOrderedSphereFundamentalClass, Hatcher.Sphere.liftedOrderedSphereFundamentalClass_eq_cycle
---

# The ordered sphere generator lifts with its defining cycle

For every universe u and k ≥ 0, put m = k + 1 and keep the lifted integer
coefficient object Rᵤ in the category of abelian groups of universe u.
Construct the two singular m-simplices on the universe-u standard m-sphere
obtained from the actual first and second ordered simplices of the double
simplex: use the fixed double-simplex sphere homeomorphism and then the
canonical space-universe lift.

Their literal first-minus-second difference is an augmented singular cycle.
Construct its reduced-homology class morphism Rᵤ → H̃ₘ(Sᵐ; Rᵤ) and prove that
this morphism is an isomorphism. Record both the exact difference-chain
formula and the equality with the accepted ordered sphere class transported
through the canonical augmented chain isomorphism.

The ordered class determines the orientation. No arbitrary sphere-homology
isomorphism, supplied generator, cycle certificate, or dimension-zero
restriction on the space universe replaces these equations. The result
covers every positive sphere dimension.

## Proof sketch

Apply the canonical augmented sphere-chain lift to the existing ordered
double-simplex sphere cycle. Its computation on each actual singular-simplex
inclusion identifies the transported chain with the stated first-minus-second
difference and preserves the coefficients and signs. Differential
compatibility proves that the difference is a cycle.

Use the naturality of cycle lifts and the homology projection to identify its
class with the transported ordered sphere class. The original ordered class
is a generator, and the constructed chain isomorphism induces a homology
isomorphism, so the resulting fixed class is a generator in universe u.

## Depends on

- [Canonical space-universe lifting preserves augmented sphere chains](sphere-space-universe-chain-lift.md)
- [The double simplex is a sphere](../post-excision-applications/double-simplex-sphere-homeomorphism.md)
- [Reduced singular homology](../../simplicial-and-singular/relative-homology/reduced-singular-homology.md)

## Proof depends on

- [The ordered difference of the two simplices is a cycle](../post-excision-applications/double-simplex-fundamental-cycle.md)

## Sources

- [Hatcher §2.1, ordered sphere cycle in Example 2.23, printed page 125](../../../../sources/hatcher-2-1.md)
- [Hatcher §2.2, cellular homology, printed pages 137–140](../../../../sources/hatcher-2-2-cellular.md#lemma-234)
- [Cellular-homology implementation specification: lifted ordered sphere generator](../../../../sources/cellular-homology-implementation.md#lifted-ordered-sphere-generator)
