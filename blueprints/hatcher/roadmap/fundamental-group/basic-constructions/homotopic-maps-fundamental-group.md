---
article_id: af_28bc6aa1a0e500efc3633ca9
source_units: [hatcher-1-1-basic-constructions]
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hatcher.fundamentalGroupMap_eq_basepointChange_comp
---

# Homotopic maps differ by basepoint change

**Hatcher, Lemma 1.19 (page 37).** Let `H` be a homotopy from `f : X → Y`
to `g : X → Y`, and let `h(t) = H(t, x)` be the path traced by a basepoint
`x`. Then the induced maps satisfy `f_* = β_h ∘ g_*`, where `β_h` changes
basepoint from `g(x)` back to `f(x)`.

Formalized as `Hatcher.fundamentalGroupMap_eq_basepointChange_comp` in
`Hatcher/VanKampen/WedgeFundamentalGroup.lean`. The proof specializes
Mathlib's natural isomorphism between the fundamental-groupoid functors of
homotopic maps. The inverse path equivalence in the statement is intentional:
Mathlib's path equivalence follows `h` from `f(x)` to `g(x)`, while Hatcher's
`β_h` goes in the opposite direction.

## Depends on

None beyond pinned Mathlib.

## Sources

- [Hatcher §1.1, Lemma 1.19, page 37](../../../sources/hatcher-1-1.md)
