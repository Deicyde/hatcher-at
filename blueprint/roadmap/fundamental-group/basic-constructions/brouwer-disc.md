---
article_id: af_dc4c0168f0ede11ba75a2f9a
source_units: [hatcher-1-1-basic-constructions]
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hatcher.Disc.exists_fixed_point
---

# Brouwer's fixed point theorem for the disc

**Hatcher, Theorem 1.9 (pages 31–32).** Every continuous `h : D² → D²` has a
fixed point.

If `h(x) ≠ x` for every `x`, define `r(x)` to be the point where the ray from
`h(x)` through `x` meets `S¹`. This is continuous, and it fixes `S¹`
pointwise, so it is a retraction of `D²` onto `S¹`. No such retraction exists,
so `h` has a fixed point.

The formalization work is almost entirely in the construction of `r` and its
continuity: the ray-intersection point is given by an explicit formula whose
denominator is nonzero exactly because `h(x) ≠ x`. The topological content is
already discharged by the [no-retraction](no-retraction-disc.md) node.

Brouwer's fixed point theorem is not in the pinned Mathlib in any dimension.
The general case comes from homology in
[Chapter 2](../../homology/computations-and-applications/README.md); this node
is only the two-dimensional case Hatcher proves from `π₁`.

Formalized in `Hatcher/Disc/Brouwer.lean` as
`Hatcher.Disc.exists_fixed_point`.

## Depends on

- [The circle is not a retract of the disc](no-retraction-disc.md)

## Sources

- [Hatcher §1.1, Theorem 1.9, pages 31–32](../../../sources/hatcher-1-1.md)
