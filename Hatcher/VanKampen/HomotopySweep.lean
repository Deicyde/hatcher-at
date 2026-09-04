import Hatcher.VanKampen.BandGeometry

noncomputable section

open Set
open scoped unitInterval

namespace Hatcher.VanKampen

universe u v

namespace StaggeredCoverGrid

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

private theorem castBoundaryConnectors_toFactorization_entries
    {P Q : BoundaryPackage U x₀} (h : P = Q)
    (C : BoundaryConnectors P.2) :
    ((castBoundaryConnectors h C).toFactorization (hx₀ := hx₀)).entries =
      (C.toFactorization (hx₀ := hx₀)).entries := by
  subst Q
  rfl

@[simp]
theorem bandLowerPath_zero (G : StaggeredCoverGrid U H bottom top) :
    G.bandLowerPath 0 = p := by
  unfold bandLowerPath
  rw [show (0 : Fin (G.extraRows + 2)).castSucc.castSucc = 0 by rfl,
    G.level_zero, H.eval_zero]

private theorem firstBandLowerPackage_eq
    (F : Factorization U x₀ hx₀ γ) (K : Factorization U x₀ hx₀ δ)
    (h : γ.Homotopic δ)
    (G : StaggeredCoverGrid U (F.boundaryHomotopy K h)
      F.boundaryCover K.boundaryCover) :
    (⟨G.bandLowerPath 0, G.bandLowerBoundary 0⟩ : BoundaryPackage U x₀) =
      ⟨F.concatenatedPath, F.boundaryCover⟩ := by
  apply Sigma.ext G.bandLowerPath_zero
  apply boundaryCover_heq_of_path_eq_toLabeled_eq
    (G.bandLowerBoundary 0) F.boundaryCover G.bandLowerPath_zero
  change G.horizontal 0 = F.boundaryCover.toLabeled
  exact G.bottom_eq

/-- The canonical connectors of the original factorization, transported to
the lower boundary of the first grid band. -/
def firstBandLowerConnectors
    (F : Factorization U x₀ hx₀ γ) (K : Factorization U x₀ hx₀ δ)
    (h : γ.Homotopic δ)
    (G : StaggeredCoverGrid U (F.boundaryHomotopy K h)
      F.boundaryCover K.boundaryCover) :
    BoundaryConnectors (G.bandLowerBoundary 0) :=
  castBoundaryConnectors (firstBandLowerPackage_eq F K h G).symm
    F.canonicalBoundaryConnectors

/-- The lower boundary factorization of the first grid band has the original
factorization's entry list. -/
theorem firstBandLowerConnectors_entries
    (F : Factorization U x₀ hx₀ γ) (K : Factorization U x₀ hx₀ δ)
    (h : γ.Homotopic δ)
    (G : StaggeredCoverGrid U (F.boundaryHomotopy K h)
      F.boundaryCover K.boundaryCover) :
    ((G.firstBandLowerConnectors F K h).toFactorization
      (hx₀ := hx₀)).entries = F.entries := by
  rw [firstBandLowerConnectors,
    castBoundaryConnectors_toFactorization_entries]
  exact F.canonicalBoundaryFactorization_entries

/-- The path along the upper edge of the final grid band. -/
def lastBandUpperPath (G : StaggeredCoverGrid U H bottom top) : Path x₀ x₀ :=
  H.eval (G.level (Fin.last (G.extraRows + 3)))

@[simp]
theorem lastBandUpperPath_eq_top (G : StaggeredCoverGrid U H bottom top) :
    G.lastBandUpperPath = q := by
  unfold lastBandUpperPath
  rw [G.level_one, H.eval_one]

/-- The upper boundary of the final grid band, with the labels of its cells. -/
def lastBandUpperBoundary (G : StaggeredCoverGrid U H bottom top) :
    BoundaryCover U G.lastBandUpperPath where
  subdivision := (G.horizontal (Fin.last (G.extraRows + 2))).subdivision
  label := (G.horizontal (Fin.last (G.extraRows + 2))).label
  mapsTo k x hx := by
    apply G.subordinate (Fin.last (G.extraRows + 2)) k
    exact ⟨⟨(G.level_strictMono Fin.castSucc_lt_succ).le, le_rfl⟩, hx⟩

private theorem lastBandUpperPackage_eq
    (F : Factorization U x₀ hx₀ γ) (K : Factorization U x₀ hx₀ δ)
    (h : γ.Homotopic δ)
    (G : StaggeredCoverGrid U (F.boundaryHomotopy K h)
      F.boundaryCover K.boundaryCover) :
    (⟨G.lastBandUpperPath, G.lastBandUpperBoundary⟩ : BoundaryPackage U x₀) =
      ⟨K.concatenatedPath, K.boundaryCover⟩ := by
  apply Sigma.ext G.lastBandUpperPath_eq_top
  apply boundaryCover_heq_of_path_eq_toLabeled_eq
    G.lastBandUpperBoundary K.boundaryCover G.lastBandUpperPath_eq_top
  change G.horizontal (Fin.last (G.extraRows + 2)) =
    K.boundaryCover.toLabeled
  exact G.top_eq

/-- The canonical connectors of the final factorization, transported to the
upper boundary of the last grid band. -/
def lastBandUpperConnectors
    (F : Factorization U x₀ hx₀ γ) (K : Factorization U x₀ hx₀ δ)
    (h : γ.Homotopic δ)
    (G : StaggeredCoverGrid U (F.boundaryHomotopy K h)
      F.boundaryCover K.boundaryCover) :
    BoundaryConnectors G.lastBandUpperBoundary :=
  castBoundaryConnectors (lastBandUpperPackage_eq F K h G).symm
    K.canonicalBoundaryConnectors

/-- The upper boundary factorization of the last grid band has the final
factorization's entry list. -/
theorem lastBandUpperConnectors_entries
    (F : Factorization U x₀ hx₀ γ) (K : Factorization U x₀ hx₀ δ)
    (h : γ.Homotopic δ)
    (G : StaggeredCoverGrid U (F.boundaryHomotopy K h)
      F.boundaryCover K.boundaryCover) :
    ((G.lastBandUpperConnectors F K h).toFactorization
      (hx₀ := hx₀)).entries = K.entries := by
  rw [lastBandUpperConnectors,
    castBoundaryConnectors_toFactorization_entries]
  exact K.canonicalBoundaryFactorization_entries

/-- Entry lists at the lower edges of all grid bands. The first is the
original factorization; every later one is the upper labeling of the
preceding interface. -/
def chainLowerEntries
    (F : Factorization U x₀ hx₀ γ) (K : Factorization U x₀ hx₀ δ)
    (h : γ.Homotopic δ)
    (G : StaggeredCoverGrid U (F.boundaryHomotopy K h)
      F.boundaryCover K.boundaryCover)
    (hone : ∀ i, IsPathConnected (U i))
    (htwo : ∀ i j, IsPathConnected (U i ∩ U j))
    (hthree : ∀ i j k, IsPathConnected (U i ∩ U j ∩ U k))
    (r : Fin (G.extraRows + 3)) : List (Factorization.Entry U x₀ hx₀) :=
  Fin.cases
    ((G.firstBandLowerConnectors F K h).toFactorization
      (hx₀ := hx₀)).entries
    (fun k ↦
      (G.upperInterfaceFactorization hx₀ hone htwo hthree k).entries)
    r

/-- Entry lists at the upper edges of all grid bands. Every non-final one is
the lower labeling of its following interface; the final one is the target
factorization. -/
def chainUpperEntries
    (F : Factorization U x₀ hx₀ γ) (K : Factorization U x₀ hx₀ δ)
    (h : γ.Homotopic δ)
    (G : StaggeredCoverGrid U (F.boundaryHomotopy K h)
      F.boundaryCover K.boundaryCover)
    (hone : ∀ i, IsPathConnected (U i))
    (htwo : ∀ i j, IsPathConnected (U i ∩ U j))
    (hthree : ∀ i j k, IsPathConnected (U i ∩ U j ∩ U k))
    (r : Fin (G.extraRows + 3)) : List (Factorization.Entry U x₀ hx₀) :=
  Fin.lastCases
    ((G.lastBandUpperConnectors F K h).toFactorization
      (hx₀ := hx₀)).entries
    (fun k ↦
      (G.lowerInterfaceFactorization hx₀ hone htwo hthree k).entries)
    r

@[simp]
theorem chainLowerEntries_zero
    (F : Factorization U x₀ hx₀ γ) (K : Factorization U x₀ hx₀ δ)
    (h : γ.Homotopic δ)
    (G : StaggeredCoverGrid U (F.boundaryHomotopy K h)
      F.boundaryCover K.boundaryCover)
    (hone : ∀ i, IsPathConnected (U i))
    (htwo : ∀ i j, IsPathConnected (U i ∩ U j))
    (hthree : ∀ i j k, IsPathConnected (U i ∩ U j ∩ U k)) :
    G.chainLowerEntries F K h hone htwo hthree 0 = F.entries := by
  unfold chainLowerEntries
  rw [Fin.cases_zero]
  exact G.firstBandLowerConnectors_entries F K h

@[simp]
theorem chainUpperEntries_last
    (F : Factorization U x₀ hx₀ γ) (K : Factorization U x₀ hx₀ δ)
    (h : γ.Homotopic δ)
    (G : StaggeredCoverGrid U (F.boundaryHomotopy K h)
      F.boundaryCover K.boundaryCover)
    (hone : ∀ i, IsPathConnected (U i))
    (htwo : ∀ i j, IsPathConnected (U i ∩ U j))
    (hthree : ∀ i j k, IsPathConnected (U i ∩ U j ∩ U k)) :
    G.chainUpperEntries F K h hone htwo hthree
      (Fin.last (G.extraRows + 2)) = K.entries := by
  unfold chainUpperEntries
  rw [Fin.lastCases_last]
  exact G.lastBandUpperConnectors_entries F K h

/-- The adjacent entry lists at every internal boundary are related by the
already-constructed interface sweep. -/
theorem chainInterfaceMoves
    (F : Factorization U x₀ hx₀ γ) (K : Factorization U x₀ hx₀ δ)
    (h : γ.Homotopic δ)
    (G : StaggeredCoverGrid U (F.boundaryHomotopy K h)
      F.boundaryCover K.boundaryCover)
    (hone : ∀ i, IsPathConnected (U i))
    (htwo : ∀ i j, IsPathConnected (U i ∩ U j))
    (hthree : ∀ i j k, IsPathConnected (U i ∩ U j ∩ U k))
    (r : Fin (G.extraRows + 2)) :
    Factorization.Moves
      (G.chainUpperEntries F K h hone htwo hthree r.castSucc)
      (G.chainLowerEntries F K h hone htwo hthree r.succ) := by
  unfold chainUpperEntries chainLowerEntries
  rw [Fin.lastCases_castSucc, Fin.cases_succ]
  exact (G.interfaceSweep hx₀ hone htwo hthree r).moves

/-- Once every geometric band supplies its move chain, the endpoint
factorizations are connected by one finite sweep. -/
theorem sweep_of_band_moves
    (F : Factorization U x₀ hx₀ γ) (K : Factorization U x₀ hx₀ δ)
    (h : γ.Homotopic δ)
    (G : StaggeredCoverGrid U (F.boundaryHomotopy K h)
      F.boundaryCover K.boundaryCover)
    (hone : ∀ i, IsPathConnected (U i))
    (htwo : ∀ i j, IsPathConnected (U i ∩ U j))
    (hthree : ∀ i j k, IsPathConnected (U i ∩ U j ∩ U k))
    (band : ∀ r : Fin (G.extraRows + 3),
      Factorization.Moves
        (G.chainLowerEntries F K h hone htwo hthree r)
        (G.chainUpperEntries F K h hone htwo hthree r)) :
    Factorization.Sweep F K := by
  apply Factorization.sweep_of_moves_alternating F K
    (G.chainLowerEntries F K h hone htwo hthree)
    (G.chainUpperEntries F K h hone htwo hthree)
  · exact G.chainLowerEntries_zero F K h hone htwo hthree
  · exact G.chainUpperEntries_last F K h hone htwo hthree
  · exact band
  · exact G.chainInterfaceMoves F K h hone htwo hthree

/-- It suffices to prove all non-final band moves uniformly and the final
band move separately. -/
theorem sweep_of_nonfinal_and_last_band_moves
    (F : Factorization U x₀ hx₀ γ) (K : Factorization U x₀ hx₀ δ)
    (h : γ.Homotopic δ)
    (G : StaggeredCoverGrid U (F.boundaryHomotopy K h)
      F.boundaryCover K.boundaryCover)
    (hone : ∀ i, IsPathConnected (U i))
    (htwo : ∀ i j, IsPathConnected (U i ∩ U j))
    (hthree : ∀ i j k, IsPathConnected (U i ∩ U j ∩ U k))
    (band : ∀ r : Fin (G.extraRows + 2),
      Factorization.Moves
        (G.chainLowerEntries F K h hone htwo hthree r.castSucc)
        (G.chainUpperEntries F K h hone htwo hthree r.castSucc))
    (lastBand : Factorization.Moves
      (G.chainLowerEntries F K h hone htwo hthree
        (Fin.last (G.extraRows + 2)))
      (G.chainUpperEntries F K h hone htwo hthree
        (Fin.last (G.extraRows + 2)))) :
    Factorization.Sweep F K := by
  apply G.sweep_of_band_moves F K h hone htwo hthree
  intro r
  exact Fin.lastCases lastBand band r

end StaggeredCoverGrid

end Hatcher.VanKampen
