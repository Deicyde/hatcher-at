---
article_id: af_024ce3f1092989d73a73aac7
not_ready: true
---

# The formal viewpoint

Hatcher §2.3 (pages 160–165). Mapped, not yet decomposed.

The section steps back and asks what was actually used. The answer is the
Eilenberg–Steenrod axioms: a homology theory is a sequence of functors with
natural long exact sequences, excision, additivity, and a dimension axiom, and
these determine singular homology on CW pairs. It then introduces categories
and functors properly, having used them informally throughout.

This is the section closest to being upstream already.
`Mathlib/AlgebraicTopology/EilenbergSteenrod.lean` states the axioms, and
Mathlib's category theory library is far more developed than anything Hatcher
needs. The work here is connecting Mathlib's axiom interface to the singular
theory once excision exists, and proving the uniqueness statement.

## Sources

- [Hatcher §2.3](../../../sources/hatcher.md)
