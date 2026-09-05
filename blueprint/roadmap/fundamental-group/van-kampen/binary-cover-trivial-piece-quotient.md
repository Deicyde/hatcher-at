---
declaration: def
origin: bridged
statement: formalized
proof: formalized
lean: Hatcher.VanKampen.binaryCoverLeftQuotientEquivFundamentalGroupOfSubsingleton
---

# A binary cover with a trivial second fundamental group

Let two path-connected open sets cover `X`, and suppose the second member has
trivial fundamental group. Then `π₁(X)` is the quotient of the first member's
fundamental group by the normal closure of the image of the intersection
group.

Formalized as
`Hatcher.VanKampen.binaryCoverLeftQuotientEquivFundamentalGroupOfSubsingleton`
in `Hatcher/VanKampen/CellAttachmentAlgebra.lean`. Its companion formulas show
that the quotient map followed by this equivalence is exactly the homomorphism
induced by inclusion of the first cover member.

The module also proves the underlying group-theoretic result: a binary pushout
whose second factor is subsingleton is the quotient of its first factor by the
normal closure of the amalgamating map's image.

This is the algebraic endgame of the 2-cell attachment calculation. The
point-set attachment cover and the identification of the overlap generators
with the attaching loops remain geometric prerequisites.

## Depends on

None beyond pinned Mathlib.

## Proof depends on

- [Binary van Kampen is a group pushout](binary-van-kampen-pushout.md)

## Sources

- [Hatcher §1.2, proof of Proposition 1.26(a), page 50](../../../sources/hatcher-1-2.md)
