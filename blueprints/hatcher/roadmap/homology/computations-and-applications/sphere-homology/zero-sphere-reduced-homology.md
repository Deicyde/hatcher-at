---
article_id: af_7721073fdde0911573d95b14
source_units: [hatcher-2-1-sphere-homology]
declaration: theorem
origin: cited
---

# Reduced homology of the zero-sphere

Let `C` be an abelian category with `HasCoproducts.{w} C`, and let `R : C`.
The main theorem
`Hatcher.Sphere.reducedHomology_sphere_zero R` has the completion criterion

`Nonempty (H̃_0(TopCat.sphere 0;R) ≅ R) ∧`
`  ∀ i, i ≠ 0 → IsZero (H̃_i(TopCat.sphere 0;R))`.

Use the two path components of `S⁰` to identify ordinary zeroth homology with
`R ⊞ R`, including the explicit comparison
`∐ (_ : ULift Bool), R ≅ R ⊞ R`. Prove that defined reduced zeroth homology
is the kernel of the induced ordinary-`H₀` augmentation, identify that map with
the codiagonal, and compute its kernel as the antidiagonal copy of `R`. Do not
use cancellation of biproduct summands in an arbitrary abelian category.
Positive-degree vanishing follows from the totally-disconnected calculation
and the reduced/ordinary comparison.

## Depends on

- [Reduced singular homology](../../simplicial-and-singular/relative-homology/reduced-singular-homology.md)

## Proof depends on

- [The zero-sphere is a two-point space](zero-sphere-two-point-homeomorphism.md)
- [Zeroth homology is free on path components](../../simplicial-and-singular/zeroth-homology-components.md)
- [Zeroth homology splits at a basepoint](../../simplicial-and-singular/relative-homology/pointed-zeroth-homology-splitting.md)
- [Higher homology vanishes for totally disconnected spaces](../../simplicial-and-singular/totally-disconnected-higher-homology.md)
- [Reduced and ordinary homology agree in positive degrees](../../simplicial-and-singular/relative-homology/reduced-positive-degree-comparison.md)

## Sources

- [Hatcher §2.1, Propositions 2.7–2.8 and Corollary 2.14, pages 109–114](../../../../sources/hatcher-2-1.md)
- [Sphere-homology implementation specification](../../../../sources/sphere-homology-implementation.md)
