# Hatcher §1.3, Covering Spaces

Numbered results in [Hatcher](hatcher.md) §1.3, pages 56–82. Printed page
numbers are used below; the PDF page is the printed page plus nine.

Statements are paraphrased. Read the actual text in the official PDF.

## Lifting properties (56–62)

Hatcher permits empty fibers in the definition of a covering map, so a
covering map is not required to be surjective. The fiber cardinal is locally
constant on the base, and hence constant when the base is connected.

| Result | Page | Paraphrase |
| --- | --- | --- |
| **Proposition 1.30** | 60 | A homotopy into the base has a unique lift after its time-zero map is lifted. Path lifting is the specialization to a one-point parameter space. |
| **Proposition 1.31** | 61 | A covering map induces an injection on fundamental groups, and its image consists exactly of loop classes whose lifts from the chosen point are loops. |
| **Proposition 1.32** | 61 | For path-connected base and total spaces, the cardinality of a fiber equals the index of the induced subgroup in the base fundamental group. |
| **Proposition 1.33** | 61–62 | A based map from a path-connected, locally path-connected space lifts through a covering exactly when its induced fundamental-group image lies in the covering subgroup. |
| **Proposition 1.34** | 62 | Two lifts from a connected space that agree at one point agree everywhere. |

## Construction and classification (63–70)

Hatcher defines a space to be semilocally simply-connected when every point
has a neighborhood whose inclusion induces the trivial map on fundamental
groups. Under local path-connectedness, the path-connected open neighborhoods
with this property form a basis.

The universal cover is constructed from endpoint-preserving homotopy classes
of paths starting at a fixed basepoint. Basic neighborhoods `U[γ]` extend a
representative path inside one of the small open sets above. The endpoint map
is a covering, and the path-shortening construction proves that its total
space is path-connected and simply-connected.

| Result | Page | Paraphrase |
| --- | --- | --- |
| Example 1.35 | 65–66 | For `m,n ≥ 2`, the complex `Xₘ,ₙ` has a contractible universal cover homeomorphic to `Tₘ,ₙ × ℝ`. |
| **Proposition 1.36** | 66–67 | If `X` is path-connected, locally path-connected, and semilocally simply-connected, every subgroup of `π₁(X,x₀)` is the image subgroup of a pointed covering of `X`. |
| **Proposition 1.37** | 67 | If `X` is path-connected and locally path-connected, two pointed path-connected covers are pointed-isomorphic exactly when their image subgroups are equal. |
| **Theorem 1.38** | 67–68 | If `X` is path-connected, locally path-connected, and semilocally simply-connected, pointed connected covers correspond to subgroups of `π₁(X,x₀)`; after forgetting basepoints, connected covers correspond to conjugacy classes. |

Immediately after Theorem 1.38, Hatcher observes that a simply-connected
cover maps over `X` to every other path-connected cover and is unique up to
covering isomorphism. In the category of pointed covers over `X`, this is an
initial property. Pages 68–70 then classify possibly disconnected covers by
permutation actions on a fiber.

## Deck transformations and examples (70–78)

| Result | Page | Paraphrase |
| --- | --- | --- |
| **Proposition 1.39** | 71 | For a path-connected cover over a path-connected, locally path-connected base, the cover is normal exactly when its image subgroup is normal, and its deck group is the normalizer quotient `N(H)/H`. |
| **Proposition 1.40** | 72 | Hatcher's local-disjoint-translates condition produces a normal quotient cover; for connected `Y` the acting group is the deck group, and under local path-connectedness it is the corresponding fundamental-group quotient. |
| Example 1.41 | 73–74 | Cyclic rotations give finite-sheeted covers between closed orientable surfaces. |
| Example 1.42 | 74 | Grid actions recover the torus and Klein-bottle groups. |
| Example 1.43 | 74–76 | The antipodal action gives `π₁(ℝPⁿ) ≅ ℤ/2ℤ` for `n ≥ 2`, followed by examples and restrictions for free finite-group actions on spheres. |
| Example 1.44 | 76 | The group `Gₘ,ₙ = ⟨a,b | a^m = b^n⟩` acts on the universal cover `Tₘ,ₙ × ℝ`; the later rank computation is Exercise 33, not part of the example. |
| Examples 1.45–1.48 | 77–78 | Cayley-complex models are described for a free group, `ℤ²`, `ℤ/nℤ`, and `ℤ/2ℤ * ℤ/2ℤ`. |

Exercises 1–33 on pages 79–82 and the Additional Topic §1.A beginning on
page 83 are outside this project's source targets.

## Selected slice

The selected classification spine contains Propositions 1.30–1.34, the
path-class construction of a universal cover, Propositions 1.36–1.37,
Theorem 1.38, and the universal cover's initial property. Proposition 1.32 remains a side
branch because it tests the monodromy action and infinite-cardinality behavior.

Example 1.35, the permutation classification on pages 68–70, Propositions
1.39–1.40 and Examples 1.41–1.48 are deferred. They require
specific geometric models, a general reconstruction from permutation actions,
or a deck-transformation API beyond the first classification milestone.

## Prior art in the pinned Mathlib

Checked against Mathlib `v4.31.0` at
`fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`.

Available ingredients:

- `IsCoveringMap` in `Mathlib/Topology/Covering/Basic.lean` uses the same
  convention as Hatcher and permits empty fibers.
- `IsCoveringMap.liftHomotopy`, `liftHomotopy_lifts`,
  `liftHomotopy_zero`, and `eq_liftHomotopy_iff'` in
  `Mathlib/Topology/Homotopy/Lifting.lean` contain Proposition 1.30.
- `IsCoveringMap.injective_path_homotopic_map` is the first clause of
  Proposition 1.31 in a stronger fundamental-groupoid form.
- `IsCoveringMap.monodromy`, `monodromy_trans_apply`,
  `monodromyFunctor`, and `monodromy_bijective` supply transport on fibers.
- `IsCoveringMap.existsUnique_continuousMap_lifts_of_range_le` contains the
  hard direction and uniqueness in Proposition 1.33. Only the converse and
  source-facing `↔` wrapper are missing.
- `IsCoveringMap.eq_of_comp_eq` is Proposition 1.34, with
  `PreconnectedSpace` plus a specified point in place of connectedness.
- `MulAction.orbitEquivQuotientStabilizer` and the subgroup-index API supply
  the algebra for Proposition 1.32. The primary theorem should be an
  equivalence of the fiber with a coset type, since `Subgroup.index : ℕ`
  records an infinite index as zero.
- `IsQuotientCoveringMap` and
  `Topology.IsQuotientMap.isCoveringMapOn_of_smul_disjoint` in
  `Mathlib/Topology/Covering/Quotient.lean` provide later quotient-action
  infrastructure. Mathlib's `ProperlyDiscontinuousSMul` is stronger than
  Hatcher's condition `(*)` and is not an exact replacement.

The pinned revision has no semilocally simply-connected API, universal-cover
construction, arbitrary-subgroup cover, covering-isomorphism bundle,
classification theorem, or deck-transformation group.

## Active upstream work

- [Mathlib PR #33108](https://github.com/leanprover-community/mathlib4/pull/33108)
  merged four days after the pin. It packages the based fundamental-group
  action on a fiber and related quotient-cover results. It is useful prior art
  but is not available to this build.
- [Mathlib PR #38292](https://github.com/leanprover-community/mathlib4/pull/38292)
  is an open, CI-green universal-cover development at head `54865ee`. It adds
  semilocal simple connectivity, based paths, tube neighborhoods, the
  path-class universal cover, and its fundamental-group action. Reviewers have
  requested that the large change be split. This roadmap uses it as design
  prior art while retaining Hatcher's direct `U[γ]` topology.
- [Mathlib PR #40135](https://github.com/leanprover-community/mathlib4/pull/40135)
  merged after the pin and adds a deck-transformation subgroup. It belongs to
  the deferred Proposition 1.39 milestone.

None of this post-pin work receives `mathlib: true`.

## Decisions taken

- **Covering convention.** Keep Mathlib and Hatcher's convention that a
  general covering map may have empty fibers. The selected classification
  nodes use pointed connected covers, so their fibers are nonempty.
- **Source-facing wrappers.** Use thin local wrappers for Propositions 1.30,
  1.31, and 1.33 where the pinned library contains the hard theorem but not the
  exact conjunction or equivalence stated by Hatcher. Proposition 1.34 is an
  exact pinned declaration.
- **Monodromy orientation.** Define the based action using inverse endpoint
  transport so multiplication agrees with Hatcher's left-to-right path
  convention. State Proposition 1.32 first as a fiber-to-coset equivalence and
  derive cardinal equality from it.
- **Universal cover.** Use Hatcher's direct `U[γ]` basis topology from pages
  63–65. PR #38292 remains implementation prior art for based paths and
  universal-cover proofs, but its compact-open quotient topology is not mixed
  into the source-facing definition without an equivalence theorem.
- **Cover bundles.** Use a small project-local record for a pointed connected
  cover and its basepoint-preserving isomorphisms rather than a full category
  of objects over `X`. Fix the total-space universe explicitly. Packaging the
  resulting isomorphism classes as a literal set-level bijection remains a
  not-ready node until the quotient and universe boundary is fixed.
- **Deferred material.** Do not treat monodromy alone as the permutation
  classification, and do not state the deck group as `π₁(X)/H` without the
  normality hypothesis.
