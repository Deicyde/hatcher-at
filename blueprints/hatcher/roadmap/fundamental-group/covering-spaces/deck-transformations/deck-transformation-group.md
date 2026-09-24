---
article_id: af_ebb4b344828f45dcaaa53f6c
source_units: [hatcher-1-3-selected-spine]
declaration: def
origin: cited
statement: formalized
proof: formalized
lean: deck
---

# Deck transformations and normal covers

For a map `p : E → X`, define `deck p` as the subgroup of
self-homeomorphisms of `E` that commute with `p`. This is the main artifact of
the node. The same file should provide the induced action on `E` and on every
fiber, together with `deck.mem_iff`, `deck.comp_eq`, and `deck.proj_smul`.

The pin also predates the supporting `Homeomorph.applyMulAction`,
`Homeomorph.applyFaithfulSMul`, and `Homeomorph.continuousConstSMul`
instances. Backport the small upstream definitions needed by `deck` in the
same compatibility module.

Define `Hatcher.Covering.IsNormal p` to mean that `p` is a covering map, is
surjective, and has a transitive deck action on every fiber. Requiring
surjectivity matters: Mathlib and Hatcher's local definition of a covering map
permit empty fibers, so fiber transitivity alone would call the empty map
normal.

Backport the final lower-camel-case API from post-pin Mathlib PR #40135 so the
local compatibility layer can later be replaced without a naming migration.
That code is not available at the pinned revision and must not receive
`mathlib: true`.

Formalized in `Hatcher/Covering/Deck.lean`. The global `deck` definition and
its basic API match PR #40135. The project extension
`deck.mulActionFiber` restricts the action to each fiber, and
`Hatcher.Covering.IsNormal` records the covering, surjectivity, and fiberwise
transitivity requirements.

## Depends on

None beyond pinned Mathlib.

## Sources

- [Hatcher §1.3, deck transformations and normal covers on pages 70–71](../../../../sources/hatcher-1-3.md)
