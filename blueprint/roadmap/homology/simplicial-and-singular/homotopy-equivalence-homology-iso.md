---
declaration: def
origin: cited
---

# A homotopy equivalence induces homology isomorphisms

**Hatcher, Corollary 2.11 (page 111).** For topological spaces `X` and `Y`, a
homotopy equivalence `e : X ≃ₕ Y`, a coefficient object `R : C`, and a degree
`n`, define an isomorphism between their degree-`n` singular homology objects.
Here `C` has a category structure, coproducts, a preadditive structure, and
homology.

The intended noncomputable definition is
`Hatcher.Singular.homologyIsoOfHomotopyEquiv`. Its source is
`ContinuousMap.HomotopyEquiv`; its target is an `Iso` from
`((singularHomologyFunctor C n).obj R).obj (TopCat.of X)` to the corresponding
object for `Y`; and its forward morphism is induced by `e.toFun`.

Construct the inverse from `e.invFun`, then use functoriality and homotopy
invariance for the two inverse laws. Mathlib's generic
`HomotopyEquiv.toHomologyIso` is additional chain-complex-level prior art, but
there is no pinned topological theorem with this interface.

## Depends on

- [Singular homology](singular-homology.md)

## Proof depends on

- [A chain map induces a map on homology](chain-map-homology.md)
- [Homotopic maps induce the same singular-homology map](singular-homology-homotopy-invariance.md)

## Sources

- [Hatcher §2.1, Corollary 2.11](../../../sources/hatcher-2-1.md)
