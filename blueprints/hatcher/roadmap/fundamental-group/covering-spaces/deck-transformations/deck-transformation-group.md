---
article_id: af_ebb4b344828f45dcaaa53f6c
source_units: [hatcher-1-3-selected-spine]
declaration: def
origin: cited
mathlib: true
mathlib_declaration: deck
mathlib_file: Mathlib/Topology/Covering/Deck.lean
---

# Deck transformations and normal covers

For a map `p : E → X`, Mathlib v4.34.1 defines `deck p` as the subgroup of
self-homeomorphisms of `E` that commute with `p`. The upstream file also
provides the induced action on `E`, together with `deck.mem_iff`,
`deck.comp_eq`, and `deck.proj_smul`.

The supporting `Homeomorph.applyMulAction`,
`Homeomorph.applyFaithfulSMul`, and `Homeomorph.continuousConstSMul`
instances are likewise present in the current pin.

Define `Hatcher.Covering.IsNormal p` to mean that `p` is a covering map, is
surjective, and has a transitive deck action on every fiber. Requiring
surjectivity matters: Mathlib and Hatcher's local definition of a covering map
permit empty fibers, so fiber transitivity alone would call the empty map
normal.

Mathlib PR [#40135](https://github.com/leanprover-community/mathlib4/pull/40135)
is the historical provenance for this API, which is now included in the
v4.34.1 pin. `Hatcher/Covering/Deck.lean` retains only the project extensions:
`deck.mulActionFiber` restricts the action to each fiber, and
`Hatcher.Covering.IsNormal` records the covering, surjectivity, and fiberwise
transitivity requirements used downstream.

## Depends on

None beyond Mathlib v4.34.1.

## Sources

- [Hatcher §1.3, deck transformations and normal covers on pages 70–71](../../../../sources/hatcher-1-3.md)
