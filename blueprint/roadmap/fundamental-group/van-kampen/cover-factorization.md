---
declaration: structure
origin: bridged
statement: formalized
proof: formalized
lean: Hatcher.VanKampen.Factorization
---

# Cover factorizations of a loop

Package Hatcher's factorization of a based loop as finite data: a finite
sequence of cover indices, based loops whose ranges lie in the corresponding
sets, and a path homotopy from their concatenation to the original loop. Its
evaluation is the associated word in the indexed free product.

The main artifact is `Hatcher.VanKampen.Factorization`. Keeping the
factorization data explicit makes the elementary moves and the homotopy-grid
argument reviewable without hiding them behind choice functions.

Formalized in `Hatcher/VanKampen/CoverFactorization.lean`. Each factor is a
loop in the relevant cover-member subtype, so its support condition is encoded
in its type. `Hatcher.VanKampen.Factorization.word` evaluates the finite list
of factors in the indexed free product.

## Depends on

- [The group presentation associated to an open cover](cover-group-presentation.md)

## Sources

- [Hatcher §1.2, factorization terminology on pages 44–45](../../../sources/hatcher-1-2.md)
