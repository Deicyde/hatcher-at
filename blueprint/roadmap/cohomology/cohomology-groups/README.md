---
not_ready: true
---

# Cohomology groups

Hatcher §3.1 (pages 190–205). Mapped, not yet decomposed.

Applying `Hom(−, G)` to a chain complex does not commute with taking homology,
and the universal coefficient theorem measures the failure exactly: a split
short exact sequence relating `Hⁿ(C; G)` to `Hom(Hₙ(C), G)` with an
`Ext¹(H_{n−1}(C), G)` correction. With that in hand the section defines
singular cohomology of spaces and reruns Chapter 2's tools — relative groups,
long exact sequences, excision, Mayer–Vietoris — in the dual setting.

Mathlib has the homological algebra this needs, including `Ext` and the
machinery of derived functors in `CategoryTheory/Abelian/`. It has no singular
cochain complex. Given Mathlib's `SingularHomology` chain complex, defining
cochains and deriving the universal coefficient theorem is the natural entry
point to the chapter.

## Sources

- [Hatcher §3.1](../../../sources/hatcher.md)
