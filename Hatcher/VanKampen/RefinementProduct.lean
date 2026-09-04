import Hatcher.VanKampen.BoundaryFactorization

noncomputable section

open scoped unitInterval

namespace Hatcher.VanKampen

universe u

local infixr:80 " ≫ₚ " => Path.trans

private theorem reverseProd_fromPath_eq_concat {X : Type u}
    [TopologicalSpace X] {x₀ : X} (n : ℕ) (f : Fin n → Path x₀ x₀) :
    (List.ofFn fun k ↦ FundamentalGroup.fromPath (.mk (f k))).reverse.prod =
      FundamentalGroup.fromPath
        (.mk (Path.concat (fun _ : Fin (n + 1) ↦ x₀) f)) := by
  induction n with
  | zero =>
      rw [Path.concat_zero, Path.Homotopic.Quotient.mk_refl]
      rfl
  | succ n ih =>
      rw [List.ofFn_succ_last, List.reverse_append, List.reverse_singleton,
        List.prod_append, List.prod_singleton, Path.concat_succ]
      calc
        FundamentalGroup.fromPath (.mk (f (Fin.last n))) *
            (List.ofFn fun i ↦
              FundamentalGroup.fromPath (.mk (f i.castSucc))).reverse.prod =
            FundamentalGroup.fromPath (.mk (f (Fin.last n))) *
              FundamentalGroup.fromPath
                (.mk (Path.concat (fun _ : Fin (n + 1) ↦ x₀)
                  (fun k ↦ f k.castSucc))) :=
          congrArg
            (fun z ↦ FundamentalGroup.fromPath (.mk (f (Fin.last n))) * z)
            (ih (fun k ↦ f k.castSucc))
        _ = FundamentalGroup.fromPath
            (.mk ((Path.concat ((fun _ : Fin (n + 2) ↦ x₀) ∘ Fin.castSucc)
              (fun k ↦ f k.castSucc)).trans (f (Fin.last n)))) := by
          rw [Path.Homotopic.Quotient.mk_trans]
          rfl

/-- Closing a chain of composable edges by compatible basepoint connectors
telescopes to the closure of the whole edge chain. -/
theorem reverseProd_closedEdges_eq {Y : Type u} [TopologicalSpace Y]
    {base : Y} {n : ℕ} (vertex : Fin (n + 1) → Y)
    (edge : ∀ k : Fin n, Path (vertex k.castSucc) (vertex k.succ))
    (connector : ∀ j : Fin (n + 1), Path base (vertex j)) :
    (List.ofFn fun k ↦ FundamentalGroup.fromPath
      (.mk (connector k.castSucc ≫ₚ edge k ≫ₚ
        (connector k.succ).symm))).reverse.prod =
      FundamentalGroup.fromPath
        (.mk (connector 0 ≫ₚ Path.concat vertex edge ≫ₚ
          (connector (Fin.last n)).symm)) := by
  rw [reverseProd_fromPath_eq_concat]
  exact congrArg FundamentalGroup.fromPath <|
    Path.Homotopic.Quotient.eq.mpr <|
      Hatcher.concat_trans_trans_symm vertex
        (fun _ : Fin (n + 1) ↦ base) edge connector

/-- Variant of `reverseProd_closedEdges_eq` with the concatenated edge chain
replaced by any homotopic path with the same endpoints. -/
theorem reverseProd_closedEdges_eq_of_homotopic {Y : Type u}
    [TopologicalSpace Y] {base : Y} {n : ℕ}
    (vertex : Fin (n + 1) → Y)
    (edge : ∀ k : Fin n, Path (vertex k.castSucc) (vertex k.succ))
    (connector : ∀ j : Fin (n + 1), Path base (vertex j))
    (whole : Path (vertex 0) (vertex (Fin.last n)))
    (hwhole : (Path.concat vertex edge).Homotopic whole) :
    (List.ofFn fun k ↦ FundamentalGroup.fromPath
      (.mk (connector k.castSucc ≫ₚ edge k ≫ₚ
        (connector k.succ).symm))).reverse.prod =
      FundamentalGroup.fromPath
        (.mk (connector 0 ≫ₚ whole ≫ₚ
          (connector (Fin.last n)).symm)) := by
  rw [reverseProd_closedEdges_eq vertex edge connector]
  exact congrArg FundamentalGroup.fromPath <|
    Path.Homotopic.Quotient.eq.mpr <|
      Path.Homotopic.hcomp
        (Path.Homotopic.refl _)
        (Path.Homotopic.hcomp hwhole (Path.Homotopic.refl _))

end Hatcher.VanKampen
