---
declaration: def
origin: cited
statement: formalized
proof: formalized
lean: Hatcher.Covering.actionEquivDeck
---

# Orbit quotients are normal and have the expected deck group

**Hatcher, Proposition 1.40(a,b) (page 72).** If a group `G` acts on `Y` by a
covering-space action, the orbit projection

`q : Y → Quotient (MulAction.orbitRel G Y)`

is a normal covering. If `Y` is path-connected, the canonical homomorphism
from `G` to `deck q` is an isomorphism.

The main artifact is `Hatcher.Covering.actionEquivDeck`. The same file should
export the normality theorem without adding connectedness when it is not
needed. Fiber transitivity comes from
`IsQuotientCoveringMap.mulActionFiber_isPretransitive`, transported along
`actionToDeck` to the deck action; surjectivity is part of the
quotient-covering structure. To prove every deck transformation arises from
`G`, match it at one point and apply unique lifting on the path-connected total
space.

Formalized in `Hatcher/Covering/OrbitQuotientDeckGroup.lean`. The file also
exports `Hatcher.Covering.isNormal_orbitQuotient`, whose statement does not
require path-connectedness.

## Depends on

- [Deck transformations and normal covers](deck-transformation-group.md)
- [Covering-space actions give quotient coverings](covering-space-action.md)

## Proof depends on

- [A lift is determined by one point](../unique-lifting.md)

## Sources

- [Hatcher §1.3, Proposition 1.40(a,b)](../../../../sources/hatcher-1-3.md)
