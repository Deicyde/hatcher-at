---
declaration: def
origin: bridged
statement: formalized
proof: formalized
lean: Hatcher.VanKampen.ConeAttachment.diskHomeomorph
---

# The cone on a disk boundary is the disk

The single-cone quotient attached to Mathlib's exact `TopCat.diskBoundary n`
by the identity map is homeomorphic to `TopCat.disk n`.

Formalized as `Hatcher.VanKampen.ConeAttachment.diskHomeomorph`. The proof
uses the radial map: retained boundary points have radius one, the cone apex
maps to the origin, and a cylinder point `(x,t)` maps to `t • x`. Its kernel is
exactly the cone-attachment relation.

The companion theorem
`Hatcher.VanKampen.ConeAttachment.diskHomeomorph_base_eq_diskBoundaryInclusion`
shows that the homeomorphism carries the retained boundary to Mathlib's
`TopCat.diskBoundaryInclusion n`. Thus this is a comparison with the same
boundary and disk objects used by `TopCat.RelativeCWComplex.basicCell`, not a
homeomorphic substitute with an unrecorded change of model.

## Depends on

- [A single cone attachment has a two-set open cover](single-cone-open-cover.md)

## Sources

- [Hatcher §1.2, disk attachments in Proposition 1.26](../../../../sources/hatcher-1-2.md)
- [Mathlib's standard disk and boundary](https://github.com/leanprover-community/mathlib4/blob/fabf563a7c95a166b8d7b6efca11c8b4dc9d911f/Mathlib/Topology/Category/TopCat/Sphere.lean)
