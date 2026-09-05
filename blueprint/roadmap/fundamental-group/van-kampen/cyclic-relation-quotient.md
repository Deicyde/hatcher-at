---
declaration: def
origin: bridged
statement: formalized
proof: formalized
lean: Hatcher.cyclicPresentationQuotientEquiv
---

# The degree-n circle relation gives the cyclic group

For a natural number `n`, quotient `π₁(S¹, 1)` by the normal closure of the
class of the degree-`n` loop. The resulting group is isomorphic to
`Multiplicative (ZMod n)`.

Formalized as `Hatcher.cyclicPresentationQuotientEquiv` in
`Hatcher/VanKampen/CyclicPresentationAlgebra.lean`. The definition
`Hatcher.Circle.degreeLoopClass` names the relator, and the companion
application theorems record that the quotient equivalence is winding number
reduced modulo `n`.

This is the complete algebraic endgame of Hatcher's cyclic presentation
complex calculation. It does not construct the topological adjunction space
or prove that attaching a 2-cell imposes this relation.

## Depends on

- [The fundamental group of the circle](../basic-constructions/fundamental-group-circle.md)

## Sources

- [Hatcher §1.2, Example 1.29, page 52](../../../sources/hatcher-1-2.md)
