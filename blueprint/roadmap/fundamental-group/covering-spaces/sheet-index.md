---
declaration: proposition
origin: cited
---

# Sheets are cosets of the induced subgroup

**Hatcher, Proposition 1.32 (page 61).** For a pointed covering with
path-connected base and total spaces, let `H` be the image subgroup in
`π₁(X,x₀)`. The fiber over the basepoint is equivalent to Hatcher's right-coset
type `H \ π₁(X,x₀)`, represented in Lean by
`Quotient (QuotientGroup.rightRel H)`. Consequently the fiber and this coset
type have equal cardinality.

The main artifact is `Hatcher.Covering.fiberEquivRightCosets`; the same file
should derive `Hatcher.Covering.mk_fiber_eq_mk_rightCosets`. Since the local
monodromy homomorphism uses inverse endpoint transport, send the class of `g`
to `g⁻¹ • e₀`; this is the inversion bridge to Hatcher's forward-lift map
`H g ↦ endpoint(lift g)`.

Do not state the general result only with `Subgroup.index : ℕ`: Mathlib assigns
zero to an infinite index, while Hatcher's number of sheets is cardinal-valued.
The finite-sheeted natural-number corollary can be added after the equivalence.

## Depends on

None beyond pinned Mathlib.

## Proof depends on

- [The fundamental group acts on a covering fiber](monodromy-action.md)
- [The induced subgroup consists of loops with closed lifts](closed-lift-image.md)

## Sources

- [Hatcher §1.3, Proposition 1.32](../../../sources/hatcher-1-3.md)
