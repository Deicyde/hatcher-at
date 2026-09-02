---
declaration: def
origin: bridged
statement: formalized
proof: formalized
lean: IsCoveringMap.monodromyPerm
---

# The fundamental group acts on a covering fiber

For a covering `p : E → X` and basepoint `x₀ : X`, package endpoint transport
on the fiber over `x₀` as a homomorphism

`π₁(X,x₀) →* Equiv.Perm (p ⁻¹' {x₀})`.

Formalized as `IsCoveringMap.monodromyPerm` in
`Hatcher/Covering/Monodromy.lean`, backported with the exact post-pin API.

Use Mathlib's `IsCoveringMap.monodromy` transport directly. Its
`FundamentalGroup` multiplication is already opposite categorical path
composition, so `monodromy_trans_apply` makes direct endpoint transport a
homomorphism to `Equiv.Perm`. Inverting transport here would reverse products
and would not define the claimed homomorphism.

The supporting definition `IsCoveringMap.fundamentalGroupMulAction` exposes the
action, and `IsCoveringMap.coe_monodromyPerm` identifies it pointwise with
endpoint transport. The chosen lift's fixed-point criterion belongs to the
next node.

Merged Mathlib PR #33108 contains the exact post-pin implementation, with
`coe_monodromyPerm` definitionally equal to `IsCoveringMap.monodromy`. It is
prior art, not `mathlib: true` for this project.

## Depends on

None beyond pinned Mathlib.

## Sources

- [Hatcher §1.3, action on a fiber on pages 68–69](../../../sources/hatcher-1-3.md)
