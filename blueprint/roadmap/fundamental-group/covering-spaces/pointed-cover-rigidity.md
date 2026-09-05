---
article_id: af_748dca8af0bc5f4091a3db8f
source_units: [hatcher-1-3-selected-spine]
declaration: proposition
origin: cited
statement: formalized
proof: formalized
lean: Hatcher.BasedConnectedCover.nonempty_iso_iff_range_eq
---

# Equal image subgroups characterize pointed cover isomorphism

**Hatcher, Proposition 1.37 (page 67).** Let `X` be path-connected and locally
path-connected. Two pointed path-connected covering spaces over `(X,x₀)` are
isomorphic by a basepoint-preserving covering isomorphism if and only if their
induced image subgroups in `π₁(X,x₀)` are equal.

Formalized as `Hatcher.BasedConnectedCover.nonempty_iso_iff_range_eq` in
`Hatcher/Covering/Rigidity.lean`. The same file defines the source-facing image
subgroup `Hatcher.BasedConnectedCover.fundamentalGroupRange`.

For the reverse direction, lift each projection through the other cover using
the lifting criterion. Unique lifting makes the two composites identities.

## Depends on

- [Pointed connected covering spaces](based-connected-cover.md)

## Proof depends on

- [A map lifts exactly when its fundamental group lands in the covering subgroup](lifting-criterion.md)
- [A lift is determined by one point](unique-lifting.md)
- [Local path-connectedness ascends along a covering](locally-path-connected-total-space.md)

## Sources

- [Hatcher §1.3, Proposition 1.37](../../../sources/hatcher-1-3.md)
