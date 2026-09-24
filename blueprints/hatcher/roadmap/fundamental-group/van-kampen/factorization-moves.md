---
article_id: af_9b54c2e1e18382f244cd1c57
source_units: [hatcher-1-2-selected-spine]
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: Hatcher.VanKampen.factorization_quotient_eq_of_move
---

# Elementary factorization moves preserve the quotient class

Hatcher uses two elementary moves: combine adjacent factors lying in one
cover member, or reinterpret a factor lying in `U i ∩ U j` through the other
inclusion. Prove that each move preserves the image of the factorization word
in the quotient by the overlap-relation subgroup.

Intended artifact: `Hatcher.VanKampen.factorization_quotient_eq_of_move`.

The reflexive-transitive closure is packaged as
`Hatcher.VanKampen.Factorization.Sweep`; the theorem
`Hatcher.VanKampen.factorization_quotient_eq_of_sweep` proves quotient
invariance for an arbitrary finite sweep without requiring intermediate entry
lists to be realized by paths.
The move toolkit is closed under arbitrary list contexts, combines or splits
same-cover blocks in reverse-product order, and performs lists of
overlap-certified cover changes pointwise.

Formalized in `Hatcher/VanKampen/FactorizationMoves.lean`. Elementary moves
act on the geometric-order list of indexed factor classes. Combining adjacent
factors uses the reversed multiplication convention of `FundamentalGroup`,
while changing a cover label is killed by the corresponding overlap relator.

## Depends on

- [Cover factorizations of a loop](cover-factorization.md)
- [The group presentation associated to an open cover](cover-group-presentation.md)

## Sources

- [Hatcher §1.2, elementary factorization moves on page 44](../../../sources/hatcher-1-2.md)
