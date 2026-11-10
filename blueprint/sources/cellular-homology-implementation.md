# Cellular-homology implementation specification

This is a project-authored specification for the
[Hatcher source passage](hatcher-2-2-cellular.md), not a literary source.
It fixes the models and completeness conditions of the 17-leaf milestone.

## Actual skeleta and cells

Use the pinned classical CW complex and its actual cell indices. Write
Sₚ = skeletonLT X p, so S₀ is empty and Sₙ₊₁ is Xⁿ. The relative pair Pₙ is
(Sₙ₊₁,Sₙ) with the actual subspace inclusion. Standard disk and sphere models
must be transported through the completed cell-arrow and cone-quotient
homeomorphisms, keeping their characteristic-map equations.

The wedge of cell spheres has the weak quotient topology and may have an
arbitrary index set. Finite one-point compactification results do not replace
this geometry. The free-group coordinates are finite-support integer
functions on the actual cells, with standard basis vectors mapped to the
characteristic-map fundamental classes using the fixed cell orientation.

## Empty and zero-degree cases

The existing good-pair interface requires a nonempty subspace. For n = 0,
compute (X⁰,∅) directly from ordinary relative chains. If a positive skeleton’s
predecessor is empty, the nonempty boundary of a positive cell rules out every
such cell, so its successor is empty as well. These cases are part of the
final results, not caller exclusions. Degree zero uses ordinary homology and
no augmentation.

## Coefficients and universes

The endpoints are ordinary integral homology of every classical CW complex.
Use the correctly universe-sized abelian-group category and a lift of the
integer coefficient object when needed. Existing sphere generators and some
convenience wrappers are universe zero; their actual lifted chain-generator
transport must be proved before the general-universe result is completed.
Do not impose finiteness or a smaller cell-index universe to avoid that proof.
No arbitrary-coefficient theorem is claimed by this selected milestone.

## Sphere space-universe lift

The two sphere generator bridges provide model support for the same
Lemma 2.34 calculation. They add no later book passage. With the lifted
integer coefficient object in the universe-u abelian-group category held
fixed, the [canonical augmented sphere-chain lift](../roadmap/homology/computations-and-applications/cellular-homology/sphere-space-universe-chain-lift.md)
changes the space model from universe zero to universe u. It uses the actual
coordinate homeomorphism and actual singular-simplex equivalences, maps each
coefficient-copy inclusion to that lifted simplex, and is the identity in
augmentation degree zero. The maps and their compatibility are constructed;
no given chain isomorphism or smaller index universe is allowed.

## Lifted ordered sphere generator

The [lifted ordered sphere generator](../roadmap/homology/computations-and-applications/cellular-homology/sphere-lifted-ordered-fundamental-class.md)
retains the first-minus-second cycle from the accepted double-simplex sphere
model of Example 2.23 on printed page 125. Its coefficient category is already
generic. For each positive sphere dimension, transport that actual cycle
through the canonical augmented chain lift, prove the literal difference and
homology-class equations, and prove its class morphism is an isomorphism.
This fixed orientation then passes through the actual disk/cone quotient and
cell characteristic maps in the positive skeletal relative-homology result.
Neither an arbitrary sphere isomorphism nor a supplied generator replaces it.

## Infinite-dimensional passage

Use actual singular chains, their finite support in continuous standard
simplices, and the completed compact-subset bounded-skeleton theorem. A finite
family of chains has a common skeleton bound at least any requested bound.
Injectivity of inclusion on simplices and free chain groups reflects cycle
and boundary equations. This unit does not introduce a general filtered
colimit or spectral sequence.

Prove finite-stage homology stability before lifting cycles or bounding
chains to prove the actual skeleton-to-space inclusion result. No supplied
vanishing, basis, homology-stability or comparison certificate is permitted.

## Cellular complex and canonical comparison

Define Cₙ = Hₙ(Pₙ), with dₙ₊₁ equal to the actual pair connecting map followed
by relative projection jₙ. Pair exactness proves square zero.

The comparison’s forward map is fixed by the equation: the identification
Hₙ(Xⁿ) ≅ cyclesₙ(C), induced by jₙ, followed by the cellular homology quotient
and the cellular/singular isomorphism, equals the actual inclusion-induced
map Hₙ(Xⁿ) → Hₙ(X). Construct that identification and prove the equation;
neither is a caller premise. Include n = 0 and empty complexes.

Filtration-map functoriality and cellular approximation are follow-on scope.
Theorem 2.35’s leaf contains only the canonical comparison and its equation.

## Reuse and verification boundary

Reuse the completed good-pair comparison, weak pointed-wedge homology,
classical successor quotient, regular neighborhood, sphere orientation,
compact-subset theorem and pair exact sequence. Pinned Mathlib supplies the
chain-complex shape, concrete cycles/quotients and finite-support algebra.
None is evidence that the new cellular endpoints are already formalized.

All new leaves begin unproved. Formalize requires exact compilation, axiom and
unused-argument checks, full evidence and independent review before recording
progress. If a genuine prerequisite proves larger than its planned unit,
Roadmap must split it with source binding and independent DAG review first.
