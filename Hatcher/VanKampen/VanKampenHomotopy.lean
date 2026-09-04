import Hatcher.VanKampen.FinalBandSweep
import Hatcher.VanKampen.InterfaceCoarsening

noncomputable section

open Set

namespace Hatcher.VanKampen.StaggeredCoverGrid

universe u v

variable {ι : Type u} {X : Type v} [TopologicalSpace X]
  {U : ι → Set X} {x₀ : X} {hx₀ : ∀ i, x₀ ∈ U i}
  {γ δ : Path x₀ x₀}

/-- The final interface coarsening followed by the final cellular band sweep. -/
theorem finalBandMoves
    (F : Factorization U x₀ hx₀ γ) (K : Factorization U x₀ hx₀ δ)
    (h : γ.Homotopic δ)
    (G : StaggeredCoverGrid U (F.boundaryHomotopy K h)
      F.boundaryCover K.boundaryCover)
    (hone : ∀ i, IsPathConnected (U i))
    (htwo : ∀ i j, IsPathConnected (U i ∩ U j))
    (hthree : ∀ i j k, IsPathConnected (U i ∩ U j ∩ U k)) :
    Factorization.Moves
      (G.chainLowerEntries F K h hone htwo hthree G.finalBand)
      (G.chainUpperEntries F K h hone htwo hthree G.finalBand) := by
  have hrefine := G.moves_upperInterfaceEntries_to_lowerCoarseEntries
    hx₀ hone htwo hthree G.finalInterface
  have hband := G.finalBandCoarseMoves hx₀
    (G.finalBandLowerConnectors hx₀ hone htwo hthree)
    (G.lastBandUpperConnectors F K h)
  have htotal := hrefine.trans hband
  have hlower :
      G.chainLowerEntries F K h hone htwo hthree G.finalBand =
        (G.upperInterfaceFactorization hx₀ hone htwo hthree
          G.finalInterface).entries := by
    rw [← G.finalInterface_succ]
    unfold chainLowerEntries
    rw [Fin.cases_succ]
  have hupper :
      G.chainUpperEntries F K h hone htwo hthree G.finalBand =
        ((G.lastBandUpperConnectors F K h).toFactorization
          (hx₀ := hx₀)).entries := by
    unfold chainUpperEntries finalBand
    rw [Fin.lastCases_last]
  rw [hlower, hupper]
  exact htotal

end Hatcher.VanKampen.StaggeredCoverGrid
