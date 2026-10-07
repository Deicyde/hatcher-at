## README.md

### Small chains, good-pair quotients, and post-excision applications

Relative homology for simplicial-set pairs merged in Mathlib PR
[#41285](https://github.com/leanprover-community/mathlib4/pull/41285) and is
present at the repository's `v4.34.1` pin. The simplicial-pair foundation is
therefore complete, and
[the singular-pair functor](relative-homology/singular-pair-functor.md) and
[relative singular homology](relative-homology/relative-singular-homology.md)
are now formalized. The
[pair long exact sequence](relative-homology/pair-long-exact-sequence.md),
including its connecting-map formula, is also formalized. Pair-sequence
naturality is now formalized. The compatible relative chain homotopy and its
induced homology-map equality complete the relative homotopy branch and
Proposition 2.19. The reduced pair sequence, its naturality, and the pointed
comparison are now formalized. All four local triple-sequence leaves are now
formalized. The excision target is now decomposed locally; Riou's independent
implementation remains active upstream prior art. The completed good-pair
milestone uses a functorial TopCat pushout model for `X/A`; no exact endpoint is
present in pinned Mathlib.
