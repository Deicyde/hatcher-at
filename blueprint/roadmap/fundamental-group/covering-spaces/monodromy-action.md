---
declaration: def
origin: bridged
---

# The fundamental group acts on a covering fiber

For a pointed covering `p : (E,e₀) → (X,x₀)`, package endpoint transport as a
homomorphism

`π₁(X,x₀) →* Equiv.Perm (p ⁻¹' {x₀})`.

Intended artifact: `Hatcher.Covering.monodromyPerm`.

Use the inverse of Mathlib's `IsCoveringMap.monodromy` transport so the
homomorphism agrees with Hatcher's left-to-right path-composition convention.
The construction should expose its action on a represented loop and prove that
the chosen lift closes exactly when the action fixes `e₀`.

Merged Mathlib PR #33108 contains a post-pin implementation. It is prior art,
not `mathlib: true` for this project.

## Depends on

None beyond pinned Mathlib.

## Sources

- [Hatcher §1.3, action on a fiber on pages 68–69](../../../sources/hatcher-1-3.md)
