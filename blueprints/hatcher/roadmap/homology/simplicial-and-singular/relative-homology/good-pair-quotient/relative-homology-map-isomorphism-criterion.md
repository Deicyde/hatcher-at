---
article_id: af_d047fabeff7641326468fef6
source_units: [hatcher-2-1-good-pair-quotient]
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: Hatcher.Relative.homologyMap_isIso_of_components
---

# Componentwise isomorphisms imply a relative isomorphism

Let `f : P ⟶ Q` be a morphism of topological pairs. If its ambient and
subspace maps induce ordinary homology isomorphisms in every degree, prove
that the canonical relative-homology map

`(Hatcher.Relative.homologyFunctor R n).map f`

is an isomorphism for every `n`, including degree zero. The intended main
theorem is `Hatcher.Relative.homologyMap_isIso_of_components` and should use
`HomologicalComplex.HomologySequence.isIso_homologyMap_τ₃` rather than a new
diagram chase.

## Depends on

- [Relative singular chains and homology](../relative-singular-homology.md)

## Proof depends on

- [The long exact sequence of a pair](../pair-long-exact-sequence.md)

## Sources

- [Good-pair quotient implementation specification](../../../../../sources/good-pair-quotient-implementation.md)
