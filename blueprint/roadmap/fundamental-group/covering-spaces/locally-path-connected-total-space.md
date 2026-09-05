---
article_id: af_6d85bf7f4fb1bcb124a18cee
source_units: [hatcher-1-3-selected-spine]
declaration: lemma
origin: cited
statement: formalized
proof: formalized
lean: Hatcher.Covering.locPathConnectedSpace_total
---

# Local path-connectedness ascends along a covering

If `p : E → X` is a covering map and `X` is locally path-connected, then `E`
is locally path-connected.

Formalized as `Hatcher.Covering.locPathConnectedSpace_total` in
`Hatcher/Covering/LocalPathConnected.lean`.

Hatcher uses this unnumbered fact before the classification theorem. It is a
small local-homeomorphism argument, but it must be explicit before applying
the lifting criterion with one covering space as the domain of a map to
another.

## Depends on

None beyond pinned Mathlib.

## Sources

- [Hatcher §1.3, local path-connectedness of covering spaces on page 63](../../../sources/hatcher-1-3.md)
