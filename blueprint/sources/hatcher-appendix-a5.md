# Hatcher Appendix Proposition A.5

Selected material from Hatcher, *Algebraic Topology*, Appendix, printed pages
522–523 (PDF pages 531–532). Statements below are paraphrased; consult the
official PDF for the construction and diagrams.

## Regular neighborhoods

Hatcher defines `Nε(A)` for a subcomplex `A` of a CW complex by induction over
the skeleta. In each cell outside `A`, the new neighborhood is a radial product
collar of the portion already constructed on the cell boundary. The parameters
`εα` are chosen positive cell by cell; Proposition A.5 adds the upper bound
`εα < 1`.

## Proposition A.5

If every `εα < 1`, the open neighborhood `Nε(A)` deformation retracts onto
`A`. On a cell outside `A`, the retraction slides the collar outward along
radial segments, compatibly with the deformation already defined on the cell
boundary.

Immediately after the proposition, Hatcher records the exact identity

`Nε(A) ∩ Nε(B) = Nε(A ∩ B)`

for subcomplexes `A` and `B` when the same cellwise parameters are used. This
gives the compatible open neighborhoods needed to extend van Kampen and
Mayer–Vietoris/excision arguments from open covers to covers by subcomplexes.

## Selected boundary

The roadmap selects one fixed-radius instance of the construction, its strong
deformation retraction, and the intersection identity. The later compactly
generated-space and product results in the Appendix remain deferred.
