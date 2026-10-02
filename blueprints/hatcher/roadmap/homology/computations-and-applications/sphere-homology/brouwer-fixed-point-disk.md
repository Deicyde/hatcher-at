---
article_id: af_ab8bb311f815ae4ee1f81367
source_units: [hatcher-2-1-corollary-2-15]
declaration: theorem
origin: cited
---

# Brouwer's fixed-point theorem for disks

For every `n : ℕ` and every morphism

`f : TopCat.disk.{0} (n + 1) ⟶ TopCat.disk.{0} (n + 1)`,

there is a point `x` with `f x = x`.

The intended main result is `Hatcher.Disc.exists_fixed_point_disk`. If `f`
had no fixed point, the boundary-ray construction would give a retraction of
the disk onto its boundary, contradicting the homological no-retraction
theorem.

## Depends on

None.

## Proof depends on

- [The boundary sphere is not a retract of the disk](disk-boundary-no-retraction.md)
- [A fixed-point-free disk map produces a boundary retraction](fixed-point-free-disk-map-retraction.md)

## Sources

- [Hatcher §2.1, Corollary 2.15, pages 114–115](../../../../sources/hatcher-2-1.md)
- [Hatcher §1.1, proof of Theorem 1.9, pages 31–32](../../../../sources/hatcher-1-1.md)
- [Corollary 2.15 implementation specification](../../../../sources/corollary-2-15-implementation.md)
