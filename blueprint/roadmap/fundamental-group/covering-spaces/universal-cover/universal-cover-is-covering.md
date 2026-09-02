---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hatcher.UniversalCover.isCoveringMap_proj
---

# The endpoint map is a covering

Let `X` be path-connected, locally path-connected, and semilocally
simply-connected. For the path-class space, the endpoint projection

`Hatcher.UniversalCover.proj : UniversalCover X x₀ → X`

is a covering map. For each small open `U`, the sets `U[γ]` partition the
preimage of `U`, and projection restricts to a homeomorphism on every part.

Intended artifact: `Hatcher.UniversalCover.isCoveringMap_proj`.

Hatcher's general definition permits empty fibers, but this endpoint map is
surjective because `X` is path-connected.

Formalized in `Hatcher/Covering/UniversalCoverIsCovering.lean`. The file also
exports continuity and surjectivity of the endpoint map, discreteness of its
fibers, and openness of the basic sheets used in the covering trivializations.

## Depends on

- [The path-class universal-cover space](universal-cover-path-space.md)

## Proof depends on

- [The universal-cover basic sets form a basis](universal-cover-basis.md)

## Sources

- [Hatcher §1.3, endpoint projection on pages 64–65](../../../../sources/hatcher-1-3.md)
