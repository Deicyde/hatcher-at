# Algebraic Topology (Hatcher)

A Lean 4 formalization of results from Allen Hatcher's *Algebraic Topology*
(Cambridge University Press, 2002), built on Mathlib. The book's text is not
redistributed here; source notes cite it by chapter and section.

Every chapter and numbered section of the book is mapped. The selected scope
contains 148 formalizable leaves, of which 146 are complete: 128 local
declarations and 18 pinned Mathlib declarations. These comprise all 133 nodes
in the previously completed §1.1, §1.2, §1.3, §2.1 functoriality, and Appendix
A.1 slices, plus thirteen nodes in a fifteen-leaf §2.1 reduced- and
relative-homology branch. Its four-node reduced-homology branch and generic
exact-sequence theorem are complete, and Mathlib now supplies the
simplicial-pair foundation. The singular-pair and relative-homology functors
and the pair long exact sequence, including its connecting-map formula and
naturality, are also complete. The relative homotopy branch through Proposition
2.19 and the reduced pair sequence are complete. Two downstream nodes remain:
the pointed comparison and reduced-pair-sequence naturality, both ready to
state.
The coverage contract explicitly defers the remaining main-line source areas;
decomposition alone is not a claim of formalization progress.

- [Roadmap](roadmap/README.md) — the book: chapters, statements, and their
  dependencies.
- [Coverage](coverage/README.md) — what counts as done, and what is out of
  scope.

<!-- Reference material goes in sources/. It is vault material rather than a
     chapter, so the site does not publish it: a statement's "## Sources" list
     links to the file in the repository instead. -->
