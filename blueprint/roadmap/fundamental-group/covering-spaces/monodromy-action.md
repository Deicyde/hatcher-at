---
declaration: def
origin: bridged
---

# The fundamental group acts on a covering fiber

For a pointed covering `p : (E,e₀) → (X,x₀)`, package endpoint transport as a
homomorphism

`π₁(X,x₀) →* Equiv.Perm (p ⁻¹' {x₀})`.

Intended artifact: `IsCoveringMap.monodromyPerm`, backported with the exact
post-pin API.

Use Mathlib's `IsCoveringMap.monodromy` transport directly. Its
`FundamentalGroup` multiplication is already opposite categorical path
composition, so `monodromy_trans_apply` makes direct endpoint transport a
homomorphism to `Equiv.Perm`. Inverting transport here would reverse products
and would not define the claimed homomorphism.

The construction should expose its action on a represented loop and prove that
the chosen lift closes exactly when the action fixes `e₀`.

Merged Mathlib PR #33108 contains the exact post-pin implementation, with
`coe_monodromyPerm` definitionally equal to `IsCoveringMap.monodromy`. It is
prior art, not `mathlib: true` for this project.

## Depends on

None beyond pinned Mathlib.

## Sources

- [Hatcher §1.3, action on a fiber on pages 68–69](../../../sources/hatcher-1-3.md)
