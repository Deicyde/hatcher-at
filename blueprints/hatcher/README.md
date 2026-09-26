# Algebraic Topology (Hatcher)

A Lean 4 formalization of results from Allen Hatcher's *Algebraic Topology*
(Cambridge University Press, 2002), built on Mathlib. The book's text is not
redistributed here; source notes cite it by chapter and section.

Every chapter and numbered section of the book is mapped. All 152 formalizable
leaves in the selected scope are complete: 134 are formalized locally and 18
are pinned Mathlib declarations. These comprise all 133 nodes
in the previously completed §1.1, §1.2, §1.3, §2.1 functoriality, and Appendix
A.1 slices, plus all fifteen nodes in the §2.1 reduced- and relative-homology
branch. Its four-node reduced-homology branch and generic
exact-sequence theorem are complete, and Mathlib now supplies the
simplicial-pair foundation. The singular-pair and relative-homology functors
and the pair long exact sequence, including its connecting-map formula and
naturality, are also complete. The relative homotopy branch through Proposition
2.19, the reduced pair sequence with its naturality, and the pointed comparison
are complete, finishing that selected §2.1 slice. The four additional leaves
for the long exact sequence of a triple and its naturality are also complete.
The coverage contract maps small chains and excision as a bounded future unit
and explicitly defers the other remaining main-line source areas; mapping is
not a claim of formalization progress.

- [Roadmap](roadmap/README.md) — the book: chapters, statements, and their
  dependencies.
- [Coverage](coverage/README.md) — what counts as done, and what is out of
  scope.

<!-- Reference material goes in sources/. It is vault material rather than a
     chapter, so the site does not publish it: a statement's "## Sources" list
     links to the file in the repository instead. -->
