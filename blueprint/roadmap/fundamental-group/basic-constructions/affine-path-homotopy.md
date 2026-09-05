---
declaration: def
origin: cited
statement: formalized
proof: formalized
lean: Hatcher.affinePathHomotopy
---

# Straight-line homotopy between paths

**Hatcher, Example 1.1 (page 25).** Two paths in `ℝⁿ` with the same endpoints
are homotopic relative to those endpoints by the straight-line homotopy
`(1 - t) • p(s) + t • q(s)`.

The local definition `Hatcher.affinePathHomotopy` proves the more general
statement for paths in any real topological vector space. Its endpoint
conditions are part of `Path.Homotopy`, so the result is relative to the two
endpoints exactly as Hatcher requires.

## Depends on

None beyond pinned Mathlib.

## Sources

- [Hatcher §1.1, Example 1.1, page 25](../../../sources/hatcher-1-1.md)
