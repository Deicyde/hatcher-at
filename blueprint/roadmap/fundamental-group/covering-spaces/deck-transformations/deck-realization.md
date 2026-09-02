---
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: Hatcher.BasedConnectedCover.existsUnique_deck_apply_basepoint_iff_range_eq
---

# A deck transformation is determined by one lifted point

Let `C` be a pointed path-connected cover of a path-connected, locally
path-connected space `(X,x₀)`, and let `e₁` lie over `x₀`. There is exactly one
deck transformation carrying the chosen point `e₀` to `e₁` if and only if the
image subgroups obtained by basing the cover at `e₀` and `e₁` are equal.

Formalized as
`Hatcher.BasedConnectedCover.existsUnique_deck_apply_basepoint_iff_range_eq`
in `Hatcher/Covering/DeckRealization.lean`. The supporting theorem
`deck.ext_of_eq_at` supplies uniqueness from agreement at one point.

Existence is Proposition 1.37 applied to the same cover with two choices of
lifted basepoint. Uniqueness follows because two deck transformations that
agree at one point are equal on the connected total space. Export this
extensionality statement as `deck.ext_of_eq_at` before proving the main
equivalence.

## Depends on

- [Deck transformations and normal covers](deck-transformation-group.md)
- [Pointed connected covering spaces](../based-connected-cover.md)

## Proof depends on

- [Equal image subgroups characterize pointed cover isomorphism](../pointed-cover-rigidity.md)
- [A lift is determined by one point](../unique-lifting.md)

## Sources

- [Hatcher §1.3, proof of Proposition 1.39 on page 71](../../../../sources/hatcher-1-3.md)
