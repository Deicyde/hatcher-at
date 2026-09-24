---
article_id: af_6423c35a3510db89ce80b6a0
source_units: [hatcher-2-1-relative-homology-les]
declaration: theorem
origin: cited
---

# The pair long exact sequence is natural

**Hatcher, §2.1 (page 127).** A map of topological pairs induces a morphism
between their long exact homology sequences. In particular it commutes with
the inclusion maps, the maps induced by the relative-chain quotients, and the
connecting homomorphisms.

The main artifact should be `Hatcher.Relative.pairConnecting_naturality`.
Naturality of the ordinary and relative homology functors supplies the first
two squares; the substantive compatibility is the square containing the
connecting morphism.

## Depends on

- [The long exact sequence of a pair](pair-long-exact-sequence.md)
- [Relative singular chains and homology](relative-singular-homology.md)

## Proof depends on

- [A short exact sequence gives an exact homology sequence](short-exact-homology-sequence.md)

## Sources

- [Hatcher §2.1, naturality of the pair sequence, page 127](../../../../sources/hatcher-2-1.md)
- [Relative-homology implementation specification](../../../../sources/relative-homology-implementation.md)
