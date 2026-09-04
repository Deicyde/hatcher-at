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

theorem toFactorization_entries (C : BoundaryConnectors B) :
    (C.toFactorization (hx₀ := hx₀)).entries =
      List.ofFn fun k : Fin B.subdivision.cells ↦
        ⟨B.label k,
          (Path.Homotopic.Quotient.mk (C.factor (hx₀ := hx₀) k) :
            CoverGroup U x₀ hx₀ (B.label k))⟩ := by
  let n := B.subdivision.cells - 1
  have hn : n + 1 = B.subdivision.cells :=
    Nat.sub_add_cancel B.subdivision.cells_pos
  unfold toFactorization Factorization.entries
  change List.ofFn (fun k : Fin (n + 1) ↦
      (⟨B.label (Fin.cast hn k),
        (Path.Homotopic.Quotient.mk
          (C.factor (hx₀ := hx₀) (Fin.cast hn k)) :
            CoverGroup U x₀ hx₀ (B.label (Fin.cast hn k)))⟩ :
        Factorization.Entry U x₀ hx₀)) = _
  rw [List.ofFn_congr hn]
  congr 1

end BoundaryConnectors

/-- Every canonical cut point of a concatenation of based loops is sent to
the common basepoint. -/
theorem concat_apply_concatSubdivisionPoint {X : Type*} [TopologicalSpace X]
    (x₀ : X) (n : ℕ) (f : Fin (n + 1) → Path x₀ x₀)
    (k : Fin (n + 2)) :
    Path.concat (fun _ : Fin (n + 2) ↦ x₀) f
        (concatSubdivisionPoint n k) = x₀ := by
  induction n with
  | zero =>
      refine Fin.cases ?_ (fun j ↦ ?_) k
      · rw [concatSubdivisionPoint_zero]
        exact Path.source _
      · have hj : j = 0 := Subsingleton.elim _ _
        subst j
        rw [show (0 : Fin 1).succ = Fin.last 1 by rfl,
          concatSubdivisionPoint_last]
        exact Path.target _
  | succ n ih =>
      rw [Path.concat_succ]
      refine Fin.lastCases ?_ (fun j ↦ ?_) k
      · simp
      · rw [concatSubdivisionPoint_succ_cast]
        change ((Path.concat (fun _ : Fin (n + 2) ↦ x₀)
          (fun q ↦ f q.castSucc)).trans (f (Fin.last (n + 1))))
            (unitHalf (concatSubdivisionPoint n j)) = x₀
        rw [Path.trans_apply]
        have hhalf : ((unitHalf (concatSubdivisionPoint n j) : I) : ℝ) ≤ 1 / 2 := by
          dsimp only [unitHalf]
          linarith [(concatSubdivisionPoint n j).property.2]
        rw [dif_pos hhalf]
        have harg :
            (⟨2 * ((unitHalf (concatSubdivisionPoint n j) : I) : ℝ), by
                exact (unitInterval.mul_pos_mem_iff zero_lt_two).2
                  ⟨(unitHalf (concatSubdivisionPoint n j)).property.1, hhalf⟩⟩ : I) =
              concatSubdivisionPoint n j := by
          apply Subtype.ext
          simp only [unitHalf]
          ring
        rw [harg]
        exact ih (fun q ↦ f q.castSucc) j

/-- The piece of a finite concatenation lying over one canonical cell,
recast as a based loop. -/
def concatCellPath {X : Type*} [TopologicalSpace X]
    (x₀ : X) (n : ℕ) (f : Fin (n + 1) → Path x₀ x₀)
    (k : Fin (n + 1)) : Path x₀ x₀ :=
  let p := Path.concat (fun _ : Fin (n + 2) ↦ x₀) f
  (p.subpath (concatSubdivisionPoint n k.castSucc)
      (concatSubdivisionPoint n k.succ)).cast
    (concat_apply_concatSubdivisionPoint x₀ n f k.castSucc).symm
    (concat_apply_concatSubdivisionPoint x₀ n f k.succ).symm

private def unitMid : I := ⟨(1 : ℝ) / 2, by norm_num⟩

private theorem trans_apply_unitMid {X : Type*} [TopologicalSpace X]
    {x₀ : X} (p q : Path x₀ x₀) : (p.trans q) unitMid = x₀ := by
  rw [Path.trans_apply]
  simp [unitMid]

private theorem unitHalf_convexComb (a b t : I) :
    Icc.convexComb (unitHalf a) (unitHalf b) t =
      unitHalf (Icc.convexComb a b t) := by
  apply Subtype.ext
  simp only [Icc.coe_convexComb, unitHalf]
  ring

private theorem trans_apply_unitHalf {X : Type*} [TopologicalSpace X]
    {x₀ : X} (p q : Path x₀ x₀) (t : I) :
    (p.trans q) (unitHalf t) = p t := by
  rw [Path.trans_apply]
  have hhalf : ((unitHalf t : I) : ℝ) ≤ 1 / 2 := by
    dsimp only [unitHalf]
    linarith [t.property.2]
  rw [dif_pos hhalf]
  congr 1
  apply Subtype.ext
  simp only [unitHalf]
  ring

private def transSecondHalf {X : Type*} [TopologicalSpace X]
    {x₀ : X} (p q : Path x₀ x₀) : Path x₀ x₀ :=
  ((p.trans q).subpath unitMid 1).cast
    (trans_apply_unitMid p q).symm (Path.target _).symm

private theorem transSecondHalf_eq {X : Type*} [TopologicalSpace X]
    {x₀ : X} (p q : Path x₀ x₀) : transSecondHalf p q = q := by
  ext t
  change (p.trans q) (Icc.convexComb unitMid 1 t) = q t
  rw [Path.trans_apply]
  by_cases ht : (t : ℝ) = 0
  · have ht0 : t = 0 := Subtype.ext ht
    subst t
    simp [unitMid]
  · have hnot : ¬((1 - (t : ℝ)) * (1 / 2) + (t : ℝ) * 1 ≤ 1 / 2) := by
      intro h
      have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1 (Ne.symm ht)
      linarith
    have hnot' : ¬((Icc.convexComb unitMid 1 t : I) : ℝ) ≤ 1 / 2 := by
      simpa [unitMid] using hnot
    rw [dif_neg hnot']
    congr 1
    apply Subtype.ext
    dsimp [unitMid]
    ring

theorem concatCellPath_last {X : Type*} [TopologicalSpace X]
    (x₀ : X) (n : ℕ) (f : Fin (n + 2) → Path x₀ x₀) :
    concatCellPath x₀ (n + 1) f (Fin.last (n + 1)) =
      f (Fin.last (n + 1)) := by
  ext t
  change Path.concat (fun _ : Fin (n + 3) ↦ x₀) f
    (Icc.convexComb
      (concatSubdivisionPoint (n + 1) (Fin.last (n + 1)).castSucc)
      (concatSubdivisionPoint (n + 1) (Fin.last (n + 1)).succ) t) = _
  rw [concatSubdivisionPoint_succ_cast, concatSubdivisionPoint_last,
    unitHalf_one]
  rw [show (Fin.last (n + 1)).succ = Fin.last (n + 2) by rfl,
    concatSubdivisionPoint_last]
  rw [Path.concat_succ]
  let p : Path x₀ x₀ :=
    Path.concat ((fun _ : Fin (n + 3) ↦ x₀) ∘ Fin.castSucc)
      (fun q ↦ f q.castSucc)
  let q : Path x₀ x₀ := f (Fin.last (n + 1))
  change (p.trans q) (Icc.convexComb unitMid 1 t) = q t
  have ht := congrArg (fun z : Path x₀ x₀ ↦ z t)
    (transSecondHalf_eq p q)
  change (p.trans q) (Icc.convexComb unitMid 1 t) = q t at ht
  exact ht

theorem concatCellPath_castSucc {X : Type*} [TopologicalSpace X]
    (x₀ : X) (n : ℕ) (f : Fin (n + 2) → Path x₀ x₀)
    (j : Fin (n + 1)) :
    concatCellPath x₀ (n + 1) f j.castSucc =
      concatCellPath x₀ n (fun q ↦ f q.castSucc) j := by
  ext t
  change Path.concat (fun _ : Fin (n + 3) ↦ x₀) f
    (Icc.convexComb
      (concatSubdivisionPoint (n + 1) j.castSucc.castSucc)
      (concatSubdivisionPoint (n + 1) j.castSucc.succ) t) =
    Path.concat (fun _ : Fin (n + 2) ↦ x₀) (fun q ↦ f q.castSucc)
      (Icc.convexComb (concatSubdivisionPoint n j.castSucc)
        (concatSubdivisionPoint n j.succ) t)
  rw [show j.castSucc.succ = j.succ.castSucc by rfl]
  rw [concatSubdivisionPoint_succ_cast,
    concatSubdivisionPoint_succ_cast, unitHalf_convexComb]
  rw [Path.concat_succ]
  let p : Path x₀ x₀ :=
    Path.concat ((fun _ : Fin (n + 3) ↦ x₀) ∘ Fin.castSucc)
      (fun q ↦ f q.castSucc)
  let z : I := Icc.convexComb (concatSubdivisionPoint n j.castSucc)
    (concatSubdivisionPoint n j.succ) t
  change (p.trans (f (Fin.last (n + 1)))) (unitHalf z) = p z
  exact trans_apply_unitHalf p (f (Fin.last (n + 1))) z

theorem concatCellPath_homotopic {X : Type*} [TopologicalSpace X]
    (x₀ : X) (n : ℕ) (f : Fin (n + 1) → Path x₀ x₀)
    (k : Fin (n + 1)) : (concatCellPath x₀ n f k).Homotopic (f k) := by
  induction n with
  | zero =>
      have hk : k = 0 := Fin.eq_zero k
      subst k
      have heq : concatCellPath x₀ 0 f 0 = (Path.refl x₀).trans (f 0) := by
        ext t
        change Path.concat (fun _ : Fin 2 ↦ x₀) f
          (Icc.convexComb
            (concatSubdivisionPoint 0 (0 : Fin 1).castSucc)
            (concatSubdivisionPoint 0 (0 : Fin 1).succ) t) = _
        rw [show (0 : Fin 1).castSucc = (0 : Fin 2) by rfl,
          concatSubdivisionPoint_zero]
        rw [show (0 : Fin 1).succ = Fin.last 1 by rfl,
          concatSubdivisionPoint_last, Icc.convexComb_zero_one]
        simp [Path.concat_succ]
      rw [heq]
      exact Path.Homotopic.refl_trans (f 0)
  | succ n ih =>
      refine Fin.lastCases ?_ (fun j ↦ ?_) k
      · rw [concatCellPath_last]
      · rw [concatCellPath_castSucc]
        exact ih (fun q ↦ f q.castSucc) j

theorem concatCellPath_eq_of_ne_zero {X : Type*} [TopologicalSpace X]
    (x₀ : X) (n : ℕ) (f : Fin (n + 1) → Path x₀ x₀)
    (k : Fin (n + 1)) (hk : k ≠ 0) : concatCellPath x₀ n f k = f k := by
  induction n with
  | zero => exact (hk (Fin.eq_zero k)).elim
  | succ n ih =>
      by_cases hlast : k = Fin.last (n + 1)
      · subst k
        exact concatCellPath_last x₀ n f
      · let j : Fin (n + 1) := k.castPred hlast
        have hjk : j.castSucc = k := Fin.castSucc_castPred k hlast
        have hj : j ≠ 0 := by
          intro hj0
          apply hk
          rw [← hjk, hj0]
          rfl
        rw [← hjk, concatCellPath_castSucc]
        exact ih (fun q ↦ f q.castSucc) j hj

theorem concatCellPath_zero {X : Type*} [TopologicalSpace X]
    (x₀ : X) (n : ℕ) (f : Fin (n + 1) → Path x₀ x₀) :
    concatCellPath x₀ n f 0 = (Path.refl x₀).trans (f 0) := by
  induction n with
  | zero =>
      ext t
      change Path.concat (fun _ : Fin 2 ↦ x₀) f
        (Icc.convexComb
          (concatSubdivisionPoint 0 (0 : Fin 1).castSucc)
          (concatSubdivisionPoint 0 (0 : Fin 1).succ) t) = _
      rw [show (0 : Fin 1).castSucc = (0 : Fin 2) by rfl,
        concatSubdivisionPoint_zero]
      rw [show (0 : Fin 1).succ = Fin.last 1 by rfl,
        concatSubdivisionPoint_last, Icc.convexComb_zero_one]
      simp [Path.concat_succ]
  | succ n ih =>
      rw [show (0 : Fin (n + 2)) = (0 : Fin (n + 1)).castSucc by rfl]
      rw [concatCellPath_castSucc]
      exact ih (fun q ↦ f q.castSucc)

namespace Factorization

variable {iota : Type u} {X : Type v} [TopologicalSpace X]
  {U : iota → Set X} {x₀ : X} {hx₀ : ∀ i, x₀ ∈ U i}
  {γ : Path x₀ x₀}

/-- A canonical cell restriction stays inside its factor's assigned cover
member. -/
theorem concatCellPath_mem (F : Factorization U x₀ hx₀ γ)
    (k : Fin (F.n + 1)) (t : I) :
    concatCellPath x₀ F.n F.ambientFactor k t ∈ U (F.index k) := by
  apply F.concatenatedPath_cell_subset k
  change Icc.convexComb
    (concatSubdivisionPoint F.n k.castSucc)
    (concatSubdivisionPoint F.n k.succ) t ∈
      Icc (concatSubdivisionPoint F.n k.castSucc)
        (concatSubdivisionPoint F.n k.succ)
  have hab : concatSubdivisionPoint F.n k.castSucc ≤
      concatSubdivisionPoint F.n k.succ :=
    (concatSubdivisionPoint_strictMono F.n Fin.castSucc_lt_succ).le
  have hab' : ((concatSubdivisionPoint F.n k.castSucc : I) : ℝ) ≤
      concatSubdivisionPoint F.n k.succ := hab
  constructor <;>
    change (_ : ℝ) ≤ _ <;>
    simp only [Icc.coe_convexComb] <;>
    nlinarith [t.property.1, t.property.2, hab']

/-- The restriction of the ambient concatenation to one canonical factor
cell, lifted back to that factor's cover member. -/
def canonicalCellFactor (F : Factorization U x₀ hx₀ γ)
    (k : Fin (F.n + 1)) :
    Path (⟨x₀, hx₀ (F.index k)⟩ : U (F.index k))
      ⟨x₀, hx₀ (F.index k)⟩ where
  toFun t := ⟨concatCellPath x₀ F.n F.ambientFactor k t,
    concatCellPath_mem F k t⟩
  continuous_toFun :=
    Continuous.subtype_mk (concatCellPath x₀ F.n F.ambientFactor k).continuous
      (concatCellPath_mem F k)
  source' := by
    apply Subtype.ext
    exact Path.source _
  target' := by
    apply Subtype.ext
    exact Path.target _

/-- Canonical cell restriction does not change the factor's based homotopy
class inside its cover member. -/
theorem canonicalCellFactor_homotopic (F : Factorization U x₀ hx₀ γ)
    (k : Fin (F.n + 1)) : (F.canonicalCellFactor k).Homotopic (F.factor k) := by
  by_cases hk : k = 0
  · subst k
    have heq : F.canonicalCellFactor 0 =
        (Path.refl (⟨x₀, hx₀ (F.index 0)⟩ : U (F.index 0))).trans
          (F.factor 0) := by
      ext t
      change concatCellPath x₀ F.n F.ambientFactor 0 t = _
      rw [concatCellPath_zero]
      rw [Path.trans_apply, Path.trans_apply]
      split_ifs <;> rfl
    rw [heq]
    exact Path.Homotopic.refl_trans (F.factor 0)
  · have heq : F.canonicalCellFactor k = F.factor k := by
      ext t
      change concatCellPath x₀ F.n F.ambientFactor k t = _
      rw [concatCellPath_eq_of_ne_zero x₀ F.n F.ambientFactor k hk]
      rfl
    rw [heq]

@[simp]
theorem mk_canonicalCellFactor (F : Factorization U x₀ hx₀ γ)
    (k : Fin (F.n + 1)) :
    (Path.Homotopic.Quotient.mk (F.canonicalCellFactor k) :
      CoverGroup U x₀ hx₀ (F.index k)) =
      Path.Homotopic.Quotient.mk (F.factor k) :=
  Path.Homotopic.Quotient.eq.mpr (F.canonicalCellFactor_homotopic k)

/-- The canonical cell restrictions recover the original entry list. -/
theorem canonical_entries_eq (F : Factorization U x₀ hx₀ γ) :
    (List.ofFn fun k ↦
      ⟨F.index k,
        (Path.Homotopic.Quotient.mk (F.canonicalCellFactor k) :
          CoverGroup U x₀ hx₀ (F.index k))⟩) = F.entries := by
  simp [entries]

theorem concatenatedPath_concatSubdivisionPoint
    (F : Factorization U x₀ hx₀ γ) (j : Fin (F.n + 2)) :
    F.concatenatedPath (concatSubdivisionPoint F.n j) = x₀ :=
  concat_apply_concatSubdivisionPoint x₀ F.n F.ambientFactor j

/-- The canonical boundary of a factorization uses constant connector paths,
because every subdivision vertex maps to the common basepoint. -/
def canonicalBoundaryConnectors (F : Factorization U x₀ hx₀ γ) :
    BoundaryConnectors F.boundaryCover where
  path j := (Path.refl x₀).cast rfl
    (F.concatenatedPath_concatSubdivisionPoint j)
  left_eq := rfl
  right_eq := rfl
  range_left k := by
    rw [Path.cast_coe, Path.refl_range, singleton_subset_iff]
    exact hx₀ (F.index k)
  range_right k := by
    rw [Path.cast_coe, Path.refl_range, singleton_subset_iff]
    exact hx₀ (F.index k)

private theorem canonicalBoundaryConnectors_leftPathIn_eq
    (F : Factorization U x₀ hx₀ γ) (k : Fin (F.n + 1)) :
    (F.canonicalBoundaryConnectors.leftPathIn (hx₀ := hx₀) k) =
      (Path.refl (⟨x₀, hx₀ (F.index k)⟩ : U (F.index k))).cast rfl
        (Subtype.ext (F.concatenatedPath_concatSubdivisionPoint k.castSucc)) := by
  ext t
  rfl

private theorem canonicalBoundaryConnectors_rightPathIn_symm_eq
    (F : Factorization U x₀ hx₀ γ) (k : Fin (F.n + 1)) :
    (F.canonicalBoundaryConnectors.rightPathIn (hx₀ := hx₀) k).symm =
      (Path.refl (⟨x₀, hx₀ (F.index k)⟩ : U (F.index k))).cast
        (Subtype.ext (F.concatenatedPath_concatSubdivisionPoint k.succ)) rfl := by
  ext t
  rfl

private theorem boundaryCover_cellPathIn_homotopic_canonicalCellFactor_cast
    (F : Factorization U x₀ hx₀ γ) (k : Fin (F.n + 1)) :
    (F.boundaryCover.cellPathIn k).Homotopic
      ((F.canonicalCellFactor k).cast
        (Subtype.ext (F.concatenatedPath_concatSubdivisionPoint k.castSucc))
        (Subtype.ext (F.concatenatedPath_concatSubdivisionPoint k.succ))) := by
  apply Path.Homotopic.refl

theorem canonicalBoundaryFactor_homotopic
    (F : Factorization U x₀ hx₀ γ) (k : Fin (F.n + 1)) :
    (F.canonicalBoundaryConnectors.factor (hx₀ := hx₀) k).Homotopic
      (F.canonicalCellFactor k) := by
  unfold BoundaryConnectors.factor
  change ((F.canonicalBoundaryConnectors.leftPathIn (hx₀ := hx₀) k).trans
    ((F.boundaryCover.cellPathIn k).trans
      (F.canonicalBoundaryConnectors.rightPathIn (hx₀ := hx₀) k).symm)).Homotopic
        (F.canonicalCellFactor k)
  rw [F.canonicalBoundaryConnectors_leftPathIn_eq k,
    F.canonicalBoundaryConnectors_rightPathIn_symm_eq k]
  exact Hatcher.cast_trans_trans_homotopic_of_homotopic_cast
    (F.boundaryCover_cellPathIn_homotopic_canonicalCellFactor_cast k)

@[simp]
theorem mk_canonicalBoundaryFactor
    (F : Factorization U x₀ hx₀ γ) (k : Fin (F.n + 1)) :
    (Path.Homotopic.Quotient.mk
      (F.canonicalBoundaryConnectors.factor (hx₀ := hx₀) k) :
        CoverGroup U x₀ hx₀ (F.index k)) =
      Path.Homotopic.Quotient.mk (F.factor k) := by
  exact (Path.Homotopic.Quotient.eq.mpr
    (F.canonicalBoundaryFactor_homotopic k)).trans
      (F.mk_canonicalCellFactor k)

/-- Converting the canonical labeled boundary back to a factorization
recovers the original entry list. -/
theorem canonicalBoundaryFactorization_entries
    (F : Factorization U x₀ hx₀ γ) :
    (F.canonicalBoundaryConnectors.toFactorization (hx₀ := hx₀)).entries =
      F.entries := by
  change (List.ofFn fun k : Fin (F.n + 1) ↦
    ⟨F.index k,
      (Path.Homotopic.Quotient.mk
        (F.canonicalBoundaryConnectors.factor (hx₀ := hx₀) k) :
          CoverGroup U x₀ hx₀ (F.index k))⟩) = F.entries
  unfold entries
  rw [List.ofFn_inj]
  funext k
  apply Sigma.ext
  · rfl
  · rw [F.mk_canonicalBoundaryFactor k]

end Factorization

end Hatcher.VanKampen
