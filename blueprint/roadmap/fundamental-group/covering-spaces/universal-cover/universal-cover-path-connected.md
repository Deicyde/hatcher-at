---
declaration: instance
origin: cited
statement: formalized
proof: formalized
lean: Hatcher.UniversalCover.pathConnectedSpace
---

# The path-class cover is path-connected

Let `X` be path-connected, locally path-connected, and semilocally
simply-connected. The total space `Hatcher.UniversalCover X x₀` is
path-connected. A point represented by `γ` is joined to the constant-path basepoint by the path
`t ↦ [γₜ]`, where `γₜ` follows `γ` up to time `t` and is then stationary.

Intended artifact: `Hatcher.UniversalCover.pathConnectedSpace`.

The same file must first prove continuity of the initial-segment family in the
`U[γ]` basis; the path construction is not merely set-level.

Formalized in `Hatcher/Covering/UniversalCoverPathConnected.lean`. The file
exports the initial-segment family, its continuity theorem, and the resulting
path before installing the path-connected-space instance.

## Depends on

- [The path-class universal-cover space](universal-cover-path-space.md)

## Proof depends on

- [The universal-cover basic sets form a basis](universal-cover-basis.md)

## Sources

- [Hatcher §1.3, path-connectedness proof on page 65](../../../../sources/hatcher-1-3.md)
