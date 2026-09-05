---
declaration: def
origin: bridged
statement: formalized
proof: formalized
lean: Hatcher.VanKampen.pushoutEquivFundamentalGroup
---

# Binary van Kampen is a group pushout

Let path-connected open subsets `A` and `B` cover `X`, contain the shared
basepoint `x₀`, and have path-connected intersection. The two inclusion maps
from `π₁(A ∩ B, x₀)` exhibit `π₁(X, x₀)` as the corresponding group pushout,
represented by `Monoid.PushoutI` over a two-element index type.

Intended artifact: `Hatcher.VanKampen.pushoutEquivFundamentalGroup`.

This is the two-set specialization stated immediately after Example 1.22. Its
proof identifies Mathlib's `Monoid.PushoutI` with the free-product quotient in
Theorem 1.20. It is not the representation of the arbitrary-cover theorem,
where each pair of cover members has its own intersection group.

Formalized in `Hatcher/VanKampen/BinaryVanKampen.lean` for a cover indexed by
`Fin 2`. The equivalence is proved to have the canonical pushout map as its
underlying homomorphism.

## Depends on

None beyond pinned Mathlib.

## Proof depends on

- [Van Kampen's quotient isomorphism](van-kampen-quotient.md)

## Sources

- [Hatcher §1.2, binary specialization on page 44](../../../sources/hatcher-1-2.md)
