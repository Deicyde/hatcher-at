import Hatcher.VanKampen.HomotopySweep
import Hatcher.VanKampen.InterfaceCoarsening

noncomputable section

open Set

namespace Hatcher.VanKampen.StaggeredCoverGrid

universe u v

variable {ι : Type u} {X : Type v} [TopologicalSpace X]
  {U : ι → Set X} {x₀ : X} {hx₀ : ∀ i, x₀ ∈ U i}
  {p q γ δ : Path x₀ x₀}
  {H : p.Homotopy q} {bottom : BoundaryCover U p}
  {top : BoundaryCover U q}

private abbrev BoundaryPackage (U : ι → Set X) (x₀ : X) :=
  Σ r : Path x₀ x₀, BoundaryCover U r

private theorem boundaryCover_heq_of_path_eq_toLabeled_eq
    {r s : Path x₀ x₀} (B : BoundaryCover U r) (C : BoundaryCover U s)
    (hpath : r = s) (hlabeled : B.toLabeled = C.toLabeled) : HEq B C := by
  subst s
  apply heq_of_eq
  cases B with
  | mk subdivision label mapsTo =>
      cases C with
      | mk subdivision' label' mapsTo' =>
          simp only [BoundaryCover.toLabeled] at hlabeled
          cases hlabeled
          rfl

private def castBoundaryConnectors
    {P Q : BoundaryPackage U x₀} (h : P = Q)
    (C : BoundaryConnectors P.2) : BoundaryConnectors Q.2 := h ▸ C

private theorem castBoundaryConnectors_entries
    {P Q : BoundaryPackage U x₀} (h : P = Q)
    (C : BoundaryConnectors P.2) :
    ((castBoundaryConnectors h C).toFactorization
      (hx₀ := hx₀)).entries =
      (C.toFactorization (hx₀ := hx₀)).entries := by
  subst Q
  rfl

theorem interfacePath_castSucc_eq_bandLowerPath_succ
    (G : StaggeredCoverGrid U H bottom top)
    (r : Fin (G.extraRows + 1)) :
    G.interfacePath r.castSucc = G.bandLowerPath r.succ := by
  unfold interfacePath bandLowerPath
  congr 1

private theorem lowerCoarsePackage_eq_nextBandLowerPackage
    (G : StaggeredCoverGrid U H bottom top)
    (r : Fin (G.extraRows + 1)) :
    (⟨G.interfacePath r.castSucc, G.lowerCoarseBoundary r.castSucc⟩ :
        BoundaryPackage U x₀) =
      ⟨G.bandLowerPath r.succ, G.bandLowerBoundary r.succ⟩ := by
  apply Sigma.ext (G.interfacePath_castSucc_eq_bandLowerPath_succ r)
  apply boundaryCover_heq_of_path_eq_toLabeled_eq
    (G.lowerCoarseBoundary r.castSucc) (G.bandLowerBoundary r.succ)
    (G.interfacePath_castSucc_eq_bandLowerPath_succ r)
  change G.horizontal r.castSucc.succ = G.horizontal r.succ.castSucc
  rw [Fin.succ_castSucc]

def nextBandLowerConnectors
    (G : StaggeredCoverGrid U H bottom top)
    (hone : ∀ i, IsPathConnected (U i))
    (htwo : ∀ i j, IsPathConnected (U i ∩ U j))
    (hthree : ∀ i j k, IsPathConnected (U i ∩ U j ∩ U k))
    (r : Fin (G.extraRows + 1)) :
    BoundaryConnectors (G.bandLowerBoundary r.succ) :=
  castBoundaryConnectors
    (G.lowerCoarsePackage_eq_nextBandLowerPackage r)
    (G.lowerCoarseConnectors hx₀ hone htwo hthree r.castSucc)

theorem nextBandLowerConnectors_entries
    (G : StaggeredCoverGrid U H bottom top)
    (hone : ∀ i, IsPathConnected (U i))
    (htwo : ∀ i j, IsPathConnected (U i ∩ U j))
    (hthree : ∀ i j k, IsPathConnected (U i ∩ U j ∩ U k))
    (r : Fin (G.extraRows + 1)) :
    ((G.nextBandLowerConnectors (hx₀ := hx₀) hone htwo hthree r).toFactorization
      (hx₀ := hx₀)).entries =
      ((G.lowerCoarseConnectors hx₀ hone htwo hthree r.castSucc).toFactorization
        (hx₀ := hx₀)).entries := by
  exact castBoundaryConnectors_entries
    (G.lowerCoarsePackage_eq_nextBandLowerPackage r)
    (G.lowerCoarseConnectors hx₀ hone htwo hthree r.castSucc)

theorem firstBandMoves
    (F : Factorization U x₀ hx₀ γ) (K : Factorization U x₀ hx₀ δ)
    (h : γ.Homotopic δ)
    (G : StaggeredCoverGrid U (F.boundaryHomotopy K h)
      F.boundaryCover K.boundaryCover)
    (hone : ∀ i, IsPathConnected (U i))
    (htwo : ∀ i j, IsPathConnected (U i ∩ U j))
    (hthree : ∀ i j k, IsPathConnected (U i ∩ U j ∩ U k)) :
    Factorization.Moves
      (G.chainLowerEntries F K h hone htwo hthree
        (0 : Fin (G.extraRows + 2)).castSucc)
      (G.chainUpperEntries F K h hone htwo hthree
        (0 : Fin (G.extraRows + 2)).castSucc) := by
  have hband := G.bandMoves hx₀ 0
    (G.firstBandLowerConnectors F K h)
    (G.upperCoarseConnectors hx₀ hone htwo hthree 0)
  have hrefine :=
    (G.upperCoarseToLowerInterfaceSweep hx₀ hone htwo hthree 0).moves
  have htotal := hband.trans hrefine
  unfold chainLowerEntries chainUpperEntries
  rw [Fin.lastCases_castSucc]
  have hzero :
      ((0 : Fin (G.extraRows + 2)).castSucc :
        Fin (G.extraRows + 3)) = 0 := by
    apply Fin.ext
    rfl
  rw [hzero, Fin.cases_zero]
  exact htotal

theorem internalBandMoves
    (G : StaggeredCoverGrid U H bottom top)
    (hone : ∀ i, IsPathConnected (U i))
    (htwo : ∀ i j, IsPathConnected (U i ∩ U j))
    (hthree : ∀ i j k, IsPathConnected (U i ∩ U j ∩ U k))
    (r : Fin (G.extraRows + 1)) :
    Factorization.Moves
      (G.upperInterfaceFactorization
        hx₀ hone htwo hthree r.castSucc).entries
      (G.lowerInterfaceFactorization
        hx₀ hone htwo hthree r.succ).entries := by
  have hright :=
    (G.upperInterfaceToLowerCoarseSweep
      hx₀ hone htwo hthree r.castSucc).moves
  rw [← G.nextBandLowerConnectors_entries hone htwo hthree r] at hright
  have hband := G.bandMoves hx₀ r.succ
    (G.nextBandLowerConnectors (hx₀ := hx₀) hone htwo hthree r)
    (G.upperCoarseConnectors hx₀ hone htwo hthree r.succ)
  have hleft :=
    (G.upperCoarseToLowerInterfaceSweep
      hx₀ hone htwo hthree r.succ).moves
  exact hright.trans (hband.trans hleft)

theorem nonfinalBandMoves
    (F : Factorization U x₀ hx₀ γ) (K : Factorization U x₀ hx₀ δ)
    (h : γ.Homotopic δ)
    (G : StaggeredCoverGrid U (F.boundaryHomotopy K h)
      F.boundaryCover K.boundaryCover)
    (hone : ∀ i, IsPathConnected (U i))
    (htwo : ∀ i j, IsPathConnected (U i ∩ U j))
    (hthree : ∀ i j k, IsPathConnected (U i ∩ U j ∩ U k))
    (r : Fin (G.extraRows + 2)) :
    Factorization.Moves
      (G.chainLowerEntries F K h hone htwo hthree r.castSucc)
      (G.chainUpperEntries F K h hone htwo hthree r.castSucc) := by
  exact Fin.cases
    (G.firstBandMoves F K h hone htwo hthree)
    (fun k ↦ by
      unfold chainLowerEntries chainUpperEntries
      rw [Fin.lastCases_castSucc]
      have hindex :
          (k.succ.castSucc : Fin (G.extraRows + 3)) =
            k.castSucc.succ := by
        apply Fin.ext
        rfl
      rw [hindex, Fin.cases_succ]
      exact G.internalBandMoves hone htwo hthree k)
    r

end Hatcher.VanKampen.StaggeredCoverGrid
