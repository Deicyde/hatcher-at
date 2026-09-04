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

/-- The coordinate of a point inside a nondegenerate unit-interval segment. -/
def intervalCoordinate (a b x : I) (hab : a < b) (hx : x ∈ Set.Icc a b) : I :=
  ⟨((x : ℝ) - a) / ((b : ℝ) - a), by
    have hd : 0 < (b : ℝ) - a := sub_pos.mpr hab
    have hax : (a : ℝ) ≤ x := hx.1
    have hxb : (x : ℝ) ≤ b := hx.2
    constructor
    · exact div_nonneg (sub_nonneg.mpr hax) hd.le
    · exact (div_le_one hd).2 (sub_le_sub_right hxb (a : ℝ))⟩

@[simp]
theorem convexComb_intervalCoordinate (a b x : I) (hab : a < b)
    (hx : x ∈ Set.Icc a b) :
    Set.Icc.convexComb a b (intervalCoordinate a b x hab hx) = x := by
  apply Subtype.ext
  simp only [Set.Icc.coe_convexComb, intervalCoordinate]
  have hd : (b : ℝ) - a ≠ 0 := ne_of_gt (sub_pos.mpr hab)
  field_simp
  ring

/-- Restricting a subpath to coordinates corresponding to ambient points
recovers the direct subpath between those points. -/
theorem subpath_subpath_intervalCoordinate {X : Type*} [TopologicalSpace X]
    {a₀ a₁ : X} (p : Path a₀ a₁) (a b x y : I) (hab : a < b)
    (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc a b) :
    (p.subpath a b).subpath
        (intervalCoordinate a b x hab hx)
        (intervalCoordinate a b y hab hy) =
      (p.subpath x y).cast
        (congrArg p (convexComb_intervalCoordinate a b x hab hx))
        (congrArg p (convexComb_intervalCoordinate a b y hab hy)) := by
  ext t
  change p (Set.Icc.convexComb a b
      (Set.Icc.convexComb (intervalCoordinate a b x hab hx)
        (intervalCoordinate a b y hab hy) t)) =
    p (Set.Icc.convexComb x y t)
  congr 1
  apply Subtype.ext
  simp only [Set.Icc.coe_convexComb, intervalCoordinate]
  have hd : (b : ℝ) - a ≠ 0 := ne_of_gt (sub_pos.mpr hab)
  field_simp
  ring

end Hatcher.VanKampen
