---
declaration: def
origin: bridged
statement: formalized
proof: formalized
lean: Hatcher.BasedConnectedCover.normalizerToDeck
---

# The normalizer acts by deck transformations

Let `C` be a pointed connected cover of a path-connected, locally
path-connected base, and let `H` be the image of its induced fundamental-group
map. Construct the homomorphism

`Hatcher.BasedConnectedCover.normalizerToDeck : normalizer H →* deck C.proj`.

For `g : normalizer H`, lift a representative of `g⁻¹` from the chosen point.
The basepoint-change formula identifies the subgroup at its endpoint with `H`,
so the deck-realization theorem supplies the unique deck transformation
carrying the chosen point to that endpoint.

The defining formula must match the project's monodromy convention:

`normalizerToDeck g • e₀ = monodromyPerm (g : π₁(X,x₀))⁻¹ e₀`.

The inverse belongs here, not in `monodromyPerm`. Direct monodromy is
multiplicative for Mathlib's fundamental-group law, while the deck
transformation selected by an endpoint composes in the opposite order unless
the normalizer argument is inverted.

Formalized in `Hatcher/Covering/NormalizerToDeck.lean`. The same file proves
the displayed formula as
`Hatcher.BasedConnectedCover.normalizerToDeck_smul_basepoint` and exports
`deck.smul_monodromy` and `deck.smul_monodromyPerm` for the commutation
calculations used below.

## Depends on

- [Deck transformations and normal covers](deck-transformation-group.md)
- [Pointed connected covering spaces](../based-connected-cover.md)
- [The fundamental group acts on a covering fiber](../monodromy-action.md)

## Proof depends on

- [A deck transformation is determined by one lifted point](deck-realization.md)
- [Changing the lifted basepoint conjugates the image subgroup](../cover-basepoint-conjugacy.md)

## Sources

- [Hatcher §1.3, normalizer construction in Proposition 1.39](../../../../sources/hatcher-1-3.md)
