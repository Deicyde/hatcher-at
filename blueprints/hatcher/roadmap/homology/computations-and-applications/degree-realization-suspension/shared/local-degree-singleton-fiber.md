---
article_id: af_c91632048e647755bd9a6e50
source_units: [hatcher-2-2-degree-realization-suspension]
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: Hatcher.Sphere.singletonFiberIsolatedPreimage Hatcher.Sphere.localDegree_eq_degree_of_fiber_eq_singleton
---

# A singleton fiber has local degree equal to global degree

For n > 0, let f : Sⁿ → Sⁿ be continuous and assume f⁻¹({y}) = {x}. Derive that x is an isolated preimage of y and prove that its neighborhood-independent local degree is the global degree of f, for every isolation witness.

## Proof sketch

The singleton fiber is finite. Apply Proposition 2.30 and identify its one summand with x; proof independence removes the canonical witness from the equality. No local-homeomorphism hypothesis is used, so the result also applies to suspension poles.

## Depends on

- [sphere degree definition](../../degree/sphere-degree-definition.md)
- [local degree well defined](../../local-degree/local-degree-well-defined.md)

## Proof depends on

- [degree local sum formula](../../local-degree/degree-local-sum-formula.md)

## Sources

- [Hatcher §2.2, printed pages 136–137](../../../../../sources/hatcher-2-2-degree-applications.md#pole-fibers-and-local-degree-realization)
- [Degree-realization and suspension specification](../../../../../sources/degree-applications-implementation.md)
