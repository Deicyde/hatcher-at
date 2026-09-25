---
article_id: af_01f1d32e23e7d1c05553c471
source_units: [hatcher-1-3-selected-spine]
declaration: def
origin: bridged
mathlib: true
mathlib_declaration: IsCoveringMap.monodromyPerm
mathlib_file: Mathlib/Topology/Homotopy/Lifting.lean
---

# The fundamental group acts on a covering fiber

For a covering `p : E → X` and basepoint `x₀ : X`, package endpoint transport
on the fiber over `x₀` as a homomorphism

`π₁(X,x₀) →* Equiv.Perm (p ⁻¹' {x₀})`.

This is `IsCoveringMap.monodromyPerm` in Mathlib v4.34.1.

Use Mathlib's `IsCoveringMap.monodromy` transport directly. Its
`FundamentalGroup` multiplication is already opposite categorical path
composition, so `monodromy_trans_apply` makes direct endpoint transport a
homomorphism to `Equiv.Perm`. Inverting transport here would reverse products
and would not define the claimed homomorphism.

The upstream definition `IsCoveringMap.fundamentalGroupMulAction` exposes the
action, and `IsCoveringMap.coe_monodromyPerm` identifies it pointwise with
endpoint transport. `Hatcher/Covering/Monodromy.lean` retains the
project-specific fixed-point characterization used by the next node.

Mathlib PR [#33108](https://github.com/leanprover-community/mathlib4/pull/33108)
is the historical provenance for the implementation, including the pointwise
identification with `IsCoveringMap.monodromy`; that API is now included in the
v4.34.1 pin.

## Depends on

None beyond Mathlib v4.34.1.

## Sources

- [Hatcher §1.3, action on a fiber on pages 68–69](../../../sources/hatcher-1-3.md)
