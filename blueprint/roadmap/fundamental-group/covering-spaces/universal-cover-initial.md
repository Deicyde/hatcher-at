---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hatcher.BasedConnectedCover.existsUnique_map_fromSimplyConnected
---

# A simply-connected cover maps uniquely to every pointed connected cover

Let `U → X` be a pointed simply-connected cover and `E → X` a pointed
path-connected cover, with `X` path-connected and locally path-connected.
There is a unique basepoint-preserving map `U → E` over `X`, and this map is a
covering map. Consequently any two pointed simply-connected covers of `X` are
isomorphic as covering spaces.

Intended artifact: `Hatcher.BasedConnectedCover.existsUnique_map_fromSimplyConnected`;
the same file should provide
`Hatcher.BasedConnectedCover.nonempty_iso_of_simplyConnected`.

This is an initial, not terminal, property in the category whose morphisms are
pointed maps of covers over `X`. Existence is the lifting criterion because the
source fundamental group is trivial. Unique lifting identifies comparison
maps. A supporting local lemma should show that such a map between covers is
itself a covering map.

Formalized in `Hatcher/Covering/UniversalCoverInitial.lean`. The proof first
constructs the unique lift by the fundamental-group lifting criterion. It then
proves the comparison map is a covering by combining path-lifting
surjectivity, cancellation for local homeomorphisms, and compatible
path-connected trivialization neighborhoods. Applying the construction in
both directions gives the pointed covering isomorphism.

## Depends on

- [Pointed connected covering spaces](based-connected-cover.md)

## Proof depends on

- [A map lifts exactly when its fundamental group lands in the covering subgroup](lifting-criterion.md)
- [A lift is determined by one point](unique-lifting.md)
- [Local path-connectedness ascends along a covering](locally-path-connected-total-space.md)

## Sources

- [Hatcher §1.3, universal-cover initiality on page 68](../../../sources/hatcher-1-3.md)
