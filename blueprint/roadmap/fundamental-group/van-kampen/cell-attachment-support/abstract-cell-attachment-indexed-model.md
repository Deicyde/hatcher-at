---
article_id: af_44c18946ee5a142c153be548
source_units: [hatcher-1-2-selected-spine]
declaration: def
origin: bridged
statement: formalized
lean: Hatcher.VanKampen.CellAttachment.modelIso
---

# Every abstract cell attachment has an indexed cone model

Let `c : HomotopicalAlgebra.AttachCells.{u}
(TopCat.RelativeCWComplex.basicCell n) f`. Define the attaching map of its cell
`i : c.ι` by following the `i`-th boundary coproduct injection with `c.g₁`.
Construct an isomorphism from the target of `f` to the explicit indexed cone
attachment of these maps.

Intended main artifact: `Hatcher.VanKampen.CellAttachment.modelIso`.
The module must also prove that this isomorphism commutes with the base map and
with every cell inclusion:

```lean
@[reassoc] theorem f_modelIso_hom :
  f ≫ (modelIso c).hom = IndexedConeAttachment.baseHom (attachingMap c)

@[reassoc] theorem cell_modelIso_hom (i : c.ι) :
  c.cell i ≫ (modelIso c).hom = modelDiskHom c i
```

These equations preserve the maps needed later to identify the two-cell
relations, rather than recording only an unpointed homeomorphism of targets.

## Depends on

- [An indexed cone attachment is a standard cell attachment](indexed-basic-cell-attachment.md)

## Sources

- [Hatcher §1.2, cell attachments in Proposition 1.26](../../../../sources/hatcher-1-2.md)
- [Mathlib's `AttachCells` pushout interface](https://github.com/leanprover-community/mathlib4/blob/fabf563a7c95a166b8d7b6efca11c8b4dc9d911f/Mathlib/AlgebraicTopology/RelativeCellComplex/AttachCells.lean)
