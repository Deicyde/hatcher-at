---
article_id: af_6c62c4e9a3ce19ebaaa1a93d
source_units: [hatcher-1-2-selected-spine]
declaration: def
origin: bridged
statement: formalized
lean: Hatcher.diskBoundaryTwoHomeomorphCircle
---

# The boundary of the two-disk is the circle

Construct a basepoint-preserving homeomorphism from Mathlib's
`TopCat.diskBoundary 2` to `_root_.Circle`, using the standard linear
identification of two-dimensional Euclidean space with the complex plane. The
distinguished boundary point is the `ULift` of the unit vector `(1, 0)`, and
the homeomorphism must send it to `1 : Circle`.

Intended artifact: `Hatcher.diskBoundaryTwoHomeomorphCircle`. The module should
also expose the loop on `TopCat.diskBoundary 2` obtained by transporting
Hatcher's standard once-around loop, so an attaching map has a canonical
fundamental-group element with the orientation used by the existing winding
number calculation.

## Depends on

- [The fundamental group of the circle](../../basic-constructions/fundamental-group-circle.md)

## Sources

- [Hatcher §1.2, attaching circles in Proposition 1.26(a)](../../../../sources/hatcher-1-2.md)
