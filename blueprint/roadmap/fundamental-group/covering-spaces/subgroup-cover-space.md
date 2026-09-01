---
declaration: def
origin: cited
---

# The covering space associated to a subgroup

Let `X` be path-connected, locally path-connected, and semilocally
simply-connected, and fix `H ≤ π₁(X,x₀)`. On the path-class universal cover,
identify two points represented by paths `γ` and `γ'` when they have the same
endpoint and the loop class of `γ.trans γ'.symm` lies in `H`. Define
`SubgroupCover H` as the quotient, with its endpoint projection and the class
of the constant path as basepoint.

The main artifact is `Hatcher.SubgroupCover H`; supporting artifacts should be
`Hatcher.SubgroupCover.proj` and `Hatcher.SubgroupCover.basepoint`.

The equivalence relation and quotient topology must be stated directly. Do not
silently assume a deck-transformation action, which is part of the later
deferred material in Hatcher.

## Depends on

- [The path-class universal-cover space](universal-cover/universal-cover-path-space.md)

## Sources

- [Hatcher §1.3, construction in the proof of Proposition 1.36](../../../sources/hatcher-1-3.md)
