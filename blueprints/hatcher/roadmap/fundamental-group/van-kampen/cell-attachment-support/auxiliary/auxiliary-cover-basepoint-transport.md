---
article_id: af_0edc868d44849128f8728457
source_units: [hatcher-1-2-selected-spine]
declaration: def
origin: bridged
statement: formalized
lean: Hatcher.VanKampen.AuxiliaryCellAttachment.basepointPath
---

# The auxiliary cover basepoint transports to the original basepoint

Let `z₀` be the common basepoint chosen on the spine of Hatcher's auxiliary
cover. Construct the canonical path in the base-side member from `z₀` to the
image of `x₀`, and prove that the base-side retraction sends its endpoint to
`x₀` and its path class to the corresponding basepoint-change isomorphism.

Intended main artifact:
`Hatcher.VanKampen.AuxiliaryCellAttachment.basepointPath`. The same module must
expose the endpoint, retraction, and induced fundamental-group equations needed
to compare the binary-cover calculation at `z₀` with
`FundamentalGroup X x₀`. This records Hatcher's path `h` explicitly rather than
requiring the two basepoints to be definitionally equal.

## Depends on

- [Hatcher's binary cover of the strip enlargement](auxiliary-cell-attachment-open-cover.md)
- [The base-side auxiliary cover retracts onto the original space](auxiliary-base-cover-retract.md)

## Sources

- [Hatcher §1.2, basepoint path `h` on page 50](../../../../../sources/hatcher-1-2.md)
