---
article_id: af_647c3193fb9509bf31577ca0
source_units: [hatcher-2-1-small-chains-excision]
declaration: theorem
origin: cited
---

# Deleted-subset excision induces homology isomorphisms

**Hatcher, Theorem 2.20 (page 119), deleted-subset form.** Let
`Z ⊆ A ⊆ X` and suppose `closure Z ⊆ interior A`. For every degree `n`, the
canonical inclusion of pairs induces an isomorphism

`H_n(X ∖ Z, A ∖ Z;R) → H_n(X,A;R)`.

State the result for `{C : Type u}`, `[Category.{v} C]`, `[Preadditive C]`,
`[HasCoproducts.{w} C]`, `[CategoryWithHomology C]`, and `R : C`.

The intended main declaration
`Hatcher.Excision.deletedSubsetHomologyMap_isIso` is an `IsIso` instance for
the exact morphism obtained from `Hatcher.Relative.homologyFunctor R n`.
Construct the source pair from the two subtypes of `X` and use their canonical
inclusions into the target pair.

The proof specializes binary-cover excision to `B = Zᶜ`. It must record the
ambient identities `A ∩ Zᶜ = A ∖ Z` and
`interior (Zᶜ) = (closure Z)ᶜ`; these turn the closure hypothesis into the
required interior-cover condition. The theorem is about subset pairs, not the
stronger arbitrary-embedding criterion found in implementation prior art.

## Depends on

- [Relative singular chains and homology](../relative-singular-homology.md)

## Proof depends on

- [Binary-cover excision induces homology isomorphisms](binary-cover-excision-homology-isomorphism.md)

## Sources

- [Hatcher §2.1, Theorem 2.20, page 119](../../../../../sources/hatcher-2-1.md)
- [Singular excision implementation specification](../../../../../sources/excision-implementation.md)
