# Algebraic Topology (Hatcher)

A Lean 4 formalization of results from Allen Hatcher's *Algebraic Topology*
(Cambridge University Press, 2002), built on Mathlib. The book's text is not
redistributed here; source notes cite it by chapter and section.

Every chapter and numbered section of the book is mapped. The selected scope
contains 148 formalizable leaves, of which 138 are complete: 123 local
declarations and 15 pinned Mathlib declarations. These comprise all 133 nodes
in the previously completed §1.1, §1.2, §1.3, §2.1 functoriality, and Appendix
A.1 slices, plus five nodes in a fifteen-leaf §2.1 reduced- and
relative-homology branch. Its four-node reduced-homology branch and generic
exact-sequence theorem are complete; the remaining ten nodes are blocked by
the simplicial-pair foundation's Mathlib pin-update gate. The coverage contract
explicitly defers the remaining main-line source areas; decomposition alone is
not a claim of formalization progress.

- [Roadmap](roadmap/README.md) — the book: chapters, statements, and their
  dependencies.
- [Coverage](coverage/README.md) — what counts as done, and what is out of
  scope.

<!-- Reference material goes in sources/. It is vault material rather than a
     chapter, so the site does not publish it: a statement's "## Sources" list
     links to the file in the repository instead. -->
