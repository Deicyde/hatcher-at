import Hatcher.VanKampen.FinalBandSweep
import Hatcher.VanKampen.InterfaceCoarsening
import Hatcher.VanKampen.NonfinalBandSweep

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

namespace Hatcher.VanKampen

local instance homotopyQuotientRelationNormal
    {ι : Type u} {X : Type v} [TopologicalSpace X]
    {U : ι → Set X} {x₀ : X} {hx₀ : ∀ i, x₀ ∈ U i} :
    (relationSubgroup U x₀ hx₀).Normal := by
  unfold relationSubgroup
  infer_instance

/-- Homotopic cover factorizations are connected by a finite sequence of
elementary factorization moves. -/
theorem factorization_sweep_of_homotopic
    {ι : Type u} {X : Type v} [TopologicalSpace X]
    {U : ι → Set X} {x₀ : X} {hx₀ : ∀ i, x₀ ∈ U i}
    {γ δ : Path x₀ x₀}
    (hU : ∀ i, IsOpen (U i)) (hcover : univ ⊆ ⋃ i, U i)
    (hone : ∀ i, IsPathConnected (U i))
    (htwo : ∀ i j, IsPathConnected (U i ∩ U j))
    (hthree : ∀ i j k, IsPathConnected (U i ∩ U j ∩ U k))
    (F : Factorization U x₀ hx₀ γ) (K : Factorization U x₀ hx₀ δ)
    (h : γ.Homotopic δ) :
    Factorization.Sweep F K := by
  obtain ⟨G⟩ := F.exists_staggeredCoverGrid K h hU hcover
  exact G.sweep_of_nonfinal_and_last_band_moves F K h hone htwo hthree
    (G.nonfinalBandMoves F K h hone htwo hthree)
    (G.finalBandMoves F K h hone htwo hthree)

/-- Homotopic cover factorizations determine the same class modulo the
overlap-relation subgroup. -/
theorem factorization_quotient_eq_of_homotopic
    {ι : Type u} {X : Type v} [TopologicalSpace X]
    {U : ι → Set X} {x₀ : X} {hx₀ : ∀ i, x₀ ∈ U i}
    {γ δ : Path x₀ x₀}
    (hU : ∀ i, IsOpen (U i)) (hcover : univ ⊆ ⋃ i, U i)
    (hone : ∀ i, IsPathConnected (U i))
    (htwo : ∀ i j, IsPathConnected (U i ∩ U j))
    (hthree : ∀ i j k, IsPathConnected (U i ∩ U j ∩ U k))
    (F : Factorization U x₀ hx₀ γ) (K : Factorization U x₀ hx₀ δ)
    (h : γ.Homotopic δ) :
    QuotientGroup.mk' (relationSubgroup U x₀ hx₀) F.word =
      QuotientGroup.mk' (relationSubgroup U x₀ hx₀) K.word :=
  factorization_quotient_eq_of_sweep F K <|
    factorization_sweep_of_homotopic hU hcover hone htwo hthree F K h

end Hatcher.VanKampen
