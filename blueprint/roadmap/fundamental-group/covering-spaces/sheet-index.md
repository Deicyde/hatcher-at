---
article_id: af_19db673677b8848bafffc26a
source_units: [hatcher-1-3-selected-spine]
declaration: def
origin: cited
statement: formalized
proof: formalized
lean: Hatcher.Covering.fiberEquivQuotientRange
---

# Sheets are cosets of the induced subgroup

**Hatcher, Proposition 1.32 (page 61).** For a pointed covering with
path-connected base and total spaces, let `H` be the image subgroup in
`π₁(X,x₀)`. The fiber over the basepoint is equivalent to Hatcher's right-coset
type `H \ π₁(X,x₀)`. Because Mathlib's fundamental-group multiplication is
opposite Hatcher's first-then path concatenation, this is represented in Lean
by the ordinary quotient `π₁(X,x₀) ⧸ H`, using `QuotientGroup.leftRel`.
Consequently the fiber and this quotient have equal cardinality.

Formalized as `Hatcher.Covering.fiberEquivQuotientRange` in
`Hatcher/Covering/SheetIndex.lean`, with the cardinal-valued corollary
`Hatcher.Covering.mk_fiber_eq_mk_quotientRange`. The proof makes the direct
monodromy action transitive using path-connectedness of the total space, then
applies orbit-stabilizer and the closed-lift characterization of the
stabilizer.

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
