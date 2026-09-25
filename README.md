# Algebraic Topology (Hatcher)

A Lean 4 formalization of results from Allen Hatcher's *Algebraic Topology*,
built on Mathlib. The book's text is not redistributed here.

The whole book's numbered sections are mapped in the roadmap and coverage
contract. The selected scope contains 152 formalizable leaves, of which 148 are
complete: 130 local declarations and 18 pinned Mathlib declarations. This
comprises all 133 nodes in the previously completed slices—twenty-two nodes in
[§1.1](blueprints/hatcher/roadmap/fundamental-group/basic-constructions/README.md),
the selected 67-node §1.2 spine, the selected 32-node §1.3 classification and
deck spine through Proposition 1.40, the selected ten-node §2.1 functoriality
spine, and two Appendix A.1 prerequisites—plus all fifteen nodes in the §2.1
reduced- and relative-homology slice. Its four-node reduced-homology
branch, generic exact-sequence theorem, simplicial-pair foundation, and
singular-pair and relative-homology functors are complete, as are the pair long
exact sequence, its connecting-map formula, and pair-sequence naturality. The
relative homotopy branch through Proposition 2.19, the reduced pair sequence
with its naturality, and the pointed comparison are also complete. Four
additional leaves decompose the long exact sequence of a triple and its
naturality for implementation.
Thirteen other source units are explicitly deferred; lettered additional
topics and exercises remain out of scope.

[Browse the published formalization blueprint](https://deicyde.github.io/hatcher-at/)
or [inspect its Markdown source](blueprints/hatcher/README.md).

Developed with [AutoformBot](https://github.com/facebookresearch/autoform-bot).
