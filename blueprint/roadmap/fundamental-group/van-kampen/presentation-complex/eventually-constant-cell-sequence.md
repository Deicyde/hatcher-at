---
article_id: af_a3d30c4dc82968256f79aee5
source_units: [hatcher-1-2-selected-spine]
declaration: def
origin: bridged
statement: formalized
proof: formalized
lean: Hatcher.VanKampen.CellAttachment.cwComplexOfEventuallyConstantSequence
---

# Eventually constant cell sequences form abstract CW complexes

Package a natural-number sequence of standard cell attachments as a
`TopCat.CWComplex` whenever its initial stage is initial and its tail is
eventually constant.

Intended main artifact:

```lean
noncomputable def Hatcher.VanKampen.CellAttachment.cwComplexOfEventuallyConstantSequence
    (X : ℕ → TopCat.{u}) (step : ∀ n, X n ⟶ X (n + 1))
    (hX₀ : CategoryTheory.Limits.IsInitial (X 0)) (N : ℕ)
    (hconst : (CategoryTheory.Functor.ofSequence step).IsEventuallyConstantFrom N)
    (cells : ∀ n, HomotopicalAlgebra.AttachCells.{u}
      (TopCat.RelativeCWComplex.basicCell.{u} n) (step n)) :
    TopCat.CWComplex (X N)
```

Also expose a helper deriving eventual constancy from isomorphism instances
on all steps after `N`, and a theorem saying that if each tail attachment has
empty cell index then every cell in the resulting CW structure has dimension
strictly less than `N`. The construction uses the eventual-constant cocone and
its colimit proof; it does not postulate a finite-sequence CW constructor.

## Depends on

None beyond pinned Mathlib.

## Sources

- [Hatcher §1.2, proof of Corollary 1.28](../../../../sources/hatcher-1-2.md)
- [Presentation-complex implementation specification](../../../../sources/presentation-complex-implementation.md)
