# Sources

The project formalizes results from a single reference.

- [Hatcher, *Algebraic Topology*](hatcher.md) — edition, citation scheme, and
  the chapter/section map the roadmap mirrors.
- [Hatcher §1.1, Basic Constructions](hatcher-1-1.md) — the labelled results
  behind the completed selected slice.
- [Hatcher §1.2, Van Kampen's Theorem](hatcher-1-2.md) — the source map,
  selected spine, prior art, and representation decisions for the van Kampen
  slice.
- [Hatcher §1.3, Covering Spaces](hatcher-1-3.md) — lifting, universal-cover,
  and classification targets with pinned and post-pin Mathlib prior art.
- [Hatcher §2.1, Simplicial and Singular Homology](hatcher-2-1.md) records the
  selected functoriality, relative-homology, excision, and sphere-homology
  foundations, deferred results, and current Mathlib boundary.
- [Hatcher §2.2, Computations and Applications](hatcher-2-2.md) records the
  selected ordinary and reduced Mayer–Vietoris sequences, their conditional
  neighborhood extension, Example 2.46, the selected degree milestone, and
  the explicitly deferred remainder.
- [Hatcher §2.2, Degree foundations](hatcher-2-2-degree.md) records the degree
  definition and properties (a)–(g), Theorem 2.28, and Proposition 2.29.
- [Hatcher Appendix Proposition A.5](hatcher-appendix-a5.md) records the
  regular-neighborhood deformation retraction and intersection identity used
  by CW-subcomplex excision.
- [Relative-homology implementation specification](relative-homology-implementation.md)
  fixes the project representation, dependency gate, and prior-art boundary
  for the second §2.1 slice.
- [Triple-homology implementation specification](triple-homology-implementation.md)
  fixes the representation, exact-sequence boundary, and upstream prior-art
  policy for the selected triple slice.
- [Singular excision implementation specification](excision-implementation.md)
  fixes the scope, representation, upstream boundary, and decomposition choices
  for the decomposed small-chains/excision unit.
- [Mayer–Vietoris implementation specification](mayer-vietoris-implementation.md)
  fixes the binary-cover chain models, exact-sequence boundary, and reuse of
  the completed excision and reduced-homology APIs.
- [Sphere-homology implementation specification](sphere-homology-implementation.md)
  fixes the neighborhood data, canonical sphere model, coefficient policy,
  recurrence, and base-case boundary for the selected sphere calculation.
- [Corollary 2.15 implementation specification](corollary-2-15-implementation.md)
  fixes the disk model, integral homology obstruction, boundary-ray bridge,
  and exclusions for no-retraction and Brouwer.
- [Good-pair quotient implementation specification](good-pair-quotient-implementation.md)
  fixes the point-quotient model and the source-facing comparison, exact
  sequence, and naturality results.
- [Post-excision applications implementation specification](post-excision-applications-implementation.md)
  fixes the mapping-cone, explicit-cycle, CW-excision, wedge-additivity, and
  local-homology architecture through Theorem 2.26.
- [Degree-foundations implementation specification](degree-theory-implementation.md)
  fixes the ordered orientation, degree API, reflection calculation, tangent
  fields, and free-action boundary through Proposition 2.29.
- [CW-subcomplex neighborhood implementation specification](cw-subcomplex-neighborhood-implementation.md)
  fixes the selected Appendix A.5 regular-neighborhood construction.

<!-- AUTHORING NOTES — these comments are not published.

     The book itself is NOT in this repository. `/sources/` is gitignored: the
     text is copyrighted and this repository is public. Cite by chapter,
     section, numbered result, and page. Do not paste passages in.
-->
