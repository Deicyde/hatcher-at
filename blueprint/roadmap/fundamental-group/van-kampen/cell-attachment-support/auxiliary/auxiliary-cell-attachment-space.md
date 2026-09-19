---
article_id: af_43db7201dc624aac2ff260ed
source_units: [hatcher-1-2-selected-spine]
declaration: def
origin: bridged
statement: formalized
lean: Hatcher.VanKampen.AuxiliaryCellAttachment
---

# The strip-enlarged cell-attachment space

For attaching maps `f j : S j → X`, chosen boundary points `s₀ j`, a common
basepoint `x₀ : X`, and paths `γ j : Path x₀ (f j (s₀ j))`, construct
Hatcher's auxiliary space `Z`.

Intended artifact: `Hatcher.VanKampen.AuxiliaryCellAttachment`. Give `Z` as an
explicit quotient containing the indexed cone attachment, a common interval
spine, and one square `I × I` per cell. Glue each square's bottom edge along
`γ j`, its left edge to the common spine, and its right edge to a fixed
truncated radial segment in the `j`-th cone; leave the top edge free. Expose
continuous maps for the attachment, base, spine, and strips, together with the
four boundary equations. The radial segment must avoid the cone apex so that
the apex can serve as Hatcher's removed point in the later cover.

## Depends on

- [An indexed family of cones has a two-set open cover](../indexed-cone-open-cover.md)

## Sources

- [Hatcher §1.2, construction of `Z` on page 50](../../../../../sources/hatcher-1-2.md)
