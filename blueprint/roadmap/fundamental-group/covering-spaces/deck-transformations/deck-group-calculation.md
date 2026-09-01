---
declaration: proposition
origin: cited
---

# The deck group is the normalizer quotient

**Hatcher, Proposition 1.39 (page 71).** Let `C` be a pointed path-connected
cover of a path-connected, locally path-connected space, and let `H` be the
image subgroup in `π₁(X,x₀)`. Then:

- `C.proj` is normal exactly when `H` is a normal subgroup; and
- the deck group is isomorphic to
  `(normalizer H) ⧸ H.subgroupOf (normalizer H)`.

The main artifact is
`Hatcher.BasedConnectedCover.normalizerQuotientEquivDeck`, in the natural
direction produced by the first isomorphism theorem. The same file should
export `isNormal_iff_range_normal` and the normal-cover corollary
`π₁(X,x₀) ⧸ H ≃* deck C.proj`, installing the normality instance only after it
has been proved. It should first derive
`Hatcher.BasedConnectedCover.proj_surjective` from the chosen point and
path-connectedness of the base, rather than treating every Mathlib covering
map as surjective.

Construct the quotient equivalence from `normalizerToDeck` using
`QuotientGroup.quotientKerEquivOfSurjective`. For the first clause, first prove
that deck transformations commute with covering monodromy. Use this to show
that, over a path-connected base, deck transitivity on the chosen fiber is
equivalent to transitivity on every fiber. The normalizer endpoint criterion
then identifies chosen-fiber transitivity with `normalizer H = ⊤`; finish with
`Subgroup.normalizer_eq_top_iff`.

## Depends on

- [Deck transformations and normal covers](deck-transformation-group.md)
- [Pointed connected covering spaces](../based-connected-cover.md)

## Proof depends on

- [The normalizer map is surjective with kernel the covering subgroup](normalizer-to-deck-exactness.md)
- [The fundamental group acts on a covering fiber](../monodromy-action.md)

## Sources

- [Hatcher §1.3, Proposition 1.39](../../../../sources/hatcher-1-3.md)
