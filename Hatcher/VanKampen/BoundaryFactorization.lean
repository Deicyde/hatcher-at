import Hatcher.Sphere.LoopInOpenCover
import Hatcher.VanKampen.FactorizationMoves
import Hatcher.VanKampen.HomotopyCoverDecomposition

noncomputable section

open Fin Set
open scoped unitInterval

namespace Hatcher.VanKampen

universe u v

local infixr:80 " ≫ₚ " => Path.trans

/-- A path restricted to a subtype containing its range. -/
private def pathIn {X : Type v} [TopologicalSpace X]
    (S : Set X) {a b : X} (q : Path a b)
    (ha : a ∈ S) (hb : b ∈ S) (hq : Set.range q ⊆ S) :
    Path (⟨a, ha⟩ : S) ⟨b, hb⟩ where
  toFun t := ⟨q t, hq (Set.mem_range_self t)⟩
  continuous_toFun := q.continuous.subtype_mk _
  source' := Subtype.ext q.source
  target' := Subtype.ext q.target

@[simp]
private theorem pathIn_map {X : Type v} [TopologicalSpace X]
    (S : Set X) {a b : X} (q : Path a b)
    (ha : a ∈ S) (hb : b ∈ S) (hq : Set.range q ⊆ S) :
    (pathIn S q ha hb hq).map continuous_subtype_val = q := by
  ext t
  rfl

/-- Connector paths from the basepoint to every subdivision vertex. Each
connector lies in every boundary cell incident to that vertex. -/
structure BoundaryConnectors {X : Type v} [TopologicalSpace X]
    {U : ι → Set X} {x₀ : X} {p : Path x₀ x₀}
    (B : BoundaryCover U p) where
  path : ∀ j, Path x₀ (p (B.subdivision.point j))
  left_eq : path 0 = (Path.refl x₀).cast rfl
    ((congrArg p B.subdivision.left).trans p.source)
  right_eq : path (Fin.last B.subdivision.cells) =
    (Path.refl x₀).cast rfl
      ((congrArg p B.subdivision.right).trans p.target)
  range_left : ∀ k, Set.range (path k.castSucc) ⊆ U (B.label k)
  range_right : ∀ k, Set.range (path k.succ) ⊆ U (B.label k)

namespace BoundaryCover

variable {ι : Type u} {X : Type v} [TopologicalSpace X] {U : ι → Set X}
  {x₀ : X} {hx₀ : ∀ i, x₀ ∈ U i} {p : Path x₀ x₀}

private theorem left_endpoint_mem (B : BoundaryCover U p)
    (k : Fin B.subdivision.cells) :
    p (B.subdivision.point k.castSucc) ∈ U (B.label k) :=
  B.mapsTo k ⟨le_rfl, (B.subdivision.strictMono Fin.castSucc_lt_succ).le⟩

private theorem right_endpoint_mem (B : BoundaryCover U p)
    (k : Fin B.subdivision.cells) :
    p (B.subdivision.point k.succ) ∈ U (B.label k) :=
  B.mapsTo k ⟨(B.subdivision.strictMono Fin.castSucc_lt_succ).le, le_rfl⟩

/-- The boundary path segment of one cell, restricted to its label. -/
def cellPathIn (B : BoundaryCover U p) (k : Fin B.subdivision.cells) :
    Path
      (⟨p (B.subdivision.point k.castSucc), B.left_endpoint_mem k⟩ : U (B.label k))
      ⟨p (B.subdivision.point k.succ), B.right_endpoint_mem k⟩ := by
  apply pathIn (U (B.label k))
    (p.subpath (B.subdivision.point k.castSucc) (B.subdivision.point k.succ))
  rw [Path.range_subpath_of_le]
  · rintro _ ⟨t, ht, rfl⟩
    exact B.mapsTo k ht
  · exact (B.subdivision.strictMono Fin.castSucc_lt_succ).le

end BoundaryCover

namespace BoundaryConnectors

variable {ι : Type u} {X : Type v} [TopologicalSpace X] {U : ι → Set X}
  {x₀ : X} {hx₀ : ∀ i, x₀ ∈ U i} {p : Path x₀ x₀}
  {B : BoundaryCover U p}

/-- The left connector of a cell, restricted to that cell's cover member. -/
def leftPathIn (C : BoundaryConnectors B) (k : Fin B.subdivision.cells) :
    Path (⟨x₀, hx₀ (B.label k)⟩ : U (B.label k))
      ⟨p (B.subdivision.point k.castSucc), B.left_endpoint_mem k⟩ :=
  pathIn (U (B.label k)) (C.path k.castSucc) (hx₀ (B.label k))
    (B.left_endpoint_mem k) (C.range_left k)

/-- The right connector of a cell, restricted to that cell's cover member. -/
def rightPathIn (C : BoundaryConnectors B) (k : Fin B.subdivision.cells) :
    Path (⟨x₀, hx₀ (B.label k)⟩ : U (B.label k))
      ⟨p (B.subdivision.point k.succ), B.right_endpoint_mem k⟩ :=
  pathIn (U (B.label k)) (C.path k.succ) (hx₀ (B.label k))
    (B.right_endpoint_mem k) (C.range_right k)

/-- The based loop contributed by one boundary cell. -/
def factor (C : BoundaryConnectors B) (k : Fin B.subdivision.cells) :
    Path (⟨x₀, hx₀ (B.label k)⟩ : U (B.label k))
      ⟨x₀, hx₀ (B.label k)⟩ :=
  C.leftPathIn k ≫ₚ B.cellPathIn k ≫ₚ (C.rightPathIn k).symm

@[simp]
theorem factor_map (C : BoundaryConnectors B)
    (k : Fin B.subdivision.cells) :
    (C.factor (hx₀ := hx₀) k).map
        (continuous_subtype_val : Continuous (fun z : U (B.label k) => (z : X))) =
      C.path k.castSucc ≫ₚ
        p.subpath (B.subdivision.point k.castSucc)
          (B.subdivision.point k.succ) ≫ₚ
        (C.path k.succ).symm := by
  ext t
  simp [factor, leftPathIn, rightPathIn, BoundaryCover.cellPathIn,
    pathIn, Path.trans_apply]

private theorem concat_loops_cast {n m : ℕ} {x : X} (h : n = m)
    (f : Fin m → Path x x) :
    Path.concat (fun _ : Fin (n + 1) ↦ x) (fun k ↦ f (Fin.cast h k)) =
      Path.concat (fun _ : Fin (m + 1) ↦ x) f := by
  subst m
  rfl

/-- The ambient concatenation of the boundary-cell factors recovers the
original based loop. -/
theorem concat_factor_map_homotopic (C : BoundaryConnectors B) :
    (Path.concat (fun _ : Fin (B.subdivision.cells + 1) ↦ x₀) fun k ↦
      (C.factor (hx₀ := hx₀) k).map
        (continuous_subtype_val :
          Continuous (fun z : U (B.label k) => (z : X)))).Homotopic p := by
  have hcancel := Hatcher.concat_trans_trans_symm
    (fun j ↦ p (B.subdivision.point j))
    (fun _ : Fin (B.subdivision.cells + 1) ↦ x₀)
    (fun k ↦ p.subpath (B.subdivision.point k.castSucc)
      (B.subdivision.point k.succ)) C.path
  have hpaths : (fun k : Fin B.subdivision.cells ↦
      (C.factor (hx₀ := hx₀) k).map
        (continuous_subtype_val :
          Continuous (fun z : U (B.label k) => (z : X)))) =
      (fun k ↦ C.path k.castSucc ≫ₚ
        p.subpath (B.subdivision.point k.castSucc)
          (B.subdivision.point k.succ) ≫ₚ
        (C.path k.succ).symm) := by
    funext k
    exact C.factor_map k
  rw [hpaths]
  apply hcancel.trans
  rw [C.left_eq, C.right_eq, ← Path.cast_symm, Path.refl_symm]
  refine Hatcher.cast_trans_trans_homotopic_of_homotopic_cast
    (Path.Homotopic.trans
      (Path.Homotopic.concat_subpath p B.subdivision.point) ?_)
  rw! (castMode := .all)
    [B.subdivision.left, B.subdivision.right, Path.subpath_zero_one]
  rfl

/-- The factorization carried by a labeled boundary and a compatible family
of connector paths. -/
noncomputable def toFactorization (C : BoundaryConnectors B) :
    Factorization U x₀ hx₀ p := by
  let n := B.subdivision.cells - 1
  have hn : n + 1 = B.subdivision.cells :=
    Nat.sub_add_cancel B.subdivision.cells_pos
  refine
    { n := n
      index := fun k ↦ B.label (Fin.cast hn k)
      factor := fun k ↦ C.factor (hx₀ := hx₀) (Fin.cast hn k)
      homotopic := ?_ }
  let f : Fin B.subdivision.cells → Path x₀ x₀ := fun k ↦
    (C.factor (hx₀ := hx₀) k).map
      (continuous_subtype_val : Continuous (fun z : U (B.label k) => (z : X)))
  change (Path.concat (fun _ : Fin (n + 2) ↦ x₀)
    (fun k ↦ f (Fin.cast hn k))).Homotopic p
  rw [concat_loops_cast hn f]
  exact C.concat_factor_map_homotopic (hx₀ := hx₀)

end BoundaryConnectors

end Hatcher.VanKampen
