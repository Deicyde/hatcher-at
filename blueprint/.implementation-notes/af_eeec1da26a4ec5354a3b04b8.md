# Implementation note: The standard sphere has its minimal classical cell structure

## Remaining goal

For every n > 0, construct the finite classical CW structure on the actual standard Sⁿ with one zero-cell at its fixed point and one n-cell. Its characteristic map is the actual disk-boundary collapse; preserve its interior and boundary equations.

## Candidate declaration

`Hatcher.ClassicalCW.sphereClassicalCw` is a naming proposal, not a verified declaration.

## Route

Use the completed disk-boundary quotient sphere identification and the quotient complement homeomorphism. Transport the classical disk charts and apply the finite classical constructor.

## Classical cell model obligation

Use `CWComplex.mkFinite` and `finite_mkFinite` with actual partial
characteristic maps, disjoint interiors, boundary containment and cover.
The accepted comparison needs `Topology.CWComplex C`; an abstract
`TopCat.CWComplex` is insufficient. The classical sup-norm product cells
concatenate directly, including zero-dimensional factors.

`Hatcher.ClassicalCW.classicalCellArrowIso (n : ℕ)` is already the public
dimension-only classical/Euclidean cell-arrow comparison. Its disk and
boundary maps are available through the Arrow isomorphism components. Use
those maps directly and prove any genuinely needed interior convenience
equation. This is reuse of existing mathematics, without an orientation assertion.
