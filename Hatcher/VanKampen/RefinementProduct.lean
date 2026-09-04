import Hatcher.VanKampen.InterfaceFactorization

noncomputable section

open Set
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

private theorem convexComb_mem_Icc {a b : I} (hab : a ≤ b) (t : I) :
    Icc.convexComb a b t ∈ Icc a b := by
  constructor <;>
    change (_ : ℝ) ≤ _ <;>
    simp only [Icc.coe_convexComb] <;>
    nlinarith [t.property.1, t.property.2,
      show (a : ℝ) ≤ b from hab]

/-- A connector-closed segment, lifted to a set containing the segment and
both connectors. -/
def basedSegmentLoopInSet {X : Type u} [TopologicalSpace X]
    {x₀ : X} (S : Set X) (hx₀ : x₀ ∈ S) (p : Path x₀ x₀)
    (a b : I) (hab : a ≤ b) (ca : Path x₀ (p a)) (cb : Path x₀ (p b))
    (hca : ∀ t, ca t ∈ S) (hcb : ∀ t, cb t ∈ S)
    (hp : MapsTo p (Icc a b) S) :
    Path (⟨x₀, hx₀⟩ : S) ⟨x₀, hx₀⟩ :=
  pathInSet (basedSegmentLoop p a b ca cb) S hx₀ hx₀ <|
    fun t ↦ basedSegmentLoop_mem p a b hab ca cb S hca hcb hp t

private theorem pathInSet_subpath_val {X : Type u} [TopologicalSpace X]
    {a b : X} (p : Path a b) (S : Set X) (ha : a ∈ S) (hb : b ∈ S)
    (hp : ∀ t, p t ∈ S) (x y t : I) :
    ((((pathInSet p S ha hb hp).subpath x y) t : S) : X) =
      (p.subpath x y) t := rfl

private theorem pathInSet_cast_val {X : Type u} [TopologicalSpace X]
    {a b : X} (p : Path a b) (S : Set X) (ha : a ∈ S) (hb : b ∈ S)
    (hp : ∀ t, p t ∈ S) {a' b' : S}
    (h₀ : a' = ⟨a, ha⟩) (h₁ : b' = ⟨b, hb⟩) (t : I) :
    ((((pathInSet p S ha hb hp).cast h₀ h₁) t : S) : X) = p t := by
  rw [show ⇑((pathInSet p S ha hb hp).cast h₀ h₁) =
      ⇑(pathInSet p S ha hb hp) from Path.cast_coe _ _ _]
  rfl

private theorem pathInSet_val {X : Type u} [TopologicalSpace X]
    {a b : X} (p : Path a b) (S : Set X) (ha : a ∈ S) (hb : b ∈ S)
    (hp : ∀ t, p t ∈ S) (t : I) :
    ((pathInSet p S ha hb hp t : S) : X) = p t := rfl

private theorem closeEdgeInSet_eq {X : Type u} [TopologicalSpace X]
    {x₀ x y : X} (S : Set X) (hx₀ : x₀ ∈ S) (a b : S)
    (ca : Path x₀ x) (e : Path x y) (cb : Path x₀ y)
    (caS : Path (⟨x₀, hx₀⟩ : S) a) (eS : Path a b)
    (cbS : Path (⟨x₀, hx₀⟩ : S) b)
    (hca : ∀ t, ((caS t : S) : X) = ca t)
    (he : ∀ t, ((eS t : S) : X) = e t)
    (hcb : ∀ t, ((cbS t : S) : X) = cb t)
    (hloop : ∀ t, (ca.trans (e.trans cb.symm)) t ∈ S) :
    caS.trans (eS.trans cbS.symm) =
      pathInSet (ca.trans (e.trans cb.symm)) S hx₀ hx₀ hloop := by
  apply Path.ext
  funext t
  apply Subtype.ext
  rw [pathInSet_val]
  rw [Path.trans_apply caS (eS.trans cbS.symm),
    Path.trans_apply ca (e.trans cb.symm)]
  by_cases h : (t : ℝ) ≤ 1 / 2
  · simp only [dif_pos h]
    exact hca _
  · simp only [dif_neg h]
    rw [Path.trans_apply eS cbS.symm, Path.trans_apply e cb.symm]
    by_cases h' : (2 * (t : ℝ) - 1) ≤ 1 / 2
    · simp only [dif_pos h']
      exact he _
    · simp only [dif_neg h']
      rw [Path.symm_apply, Path.symm_apply]
      exact hcb _

set_option maxHeartbeats 800000 in
/-- Subdividing a segment inside one set does not change its connector-closed
fundamental-group class. -/
theorem reverseProd_basedSegmentLoopInSet_eq {X : Type u} [TopologicalSpace X]
    {x₀ : X} (S : Set X) (hx₀ : x₀ ∈ S) (p : Path x₀ x₀)
    (a b : I) (hab : a < b) (hp : MapsTo p (Icc a b) S)
    (n : ℕ) (point : Fin (n + 1) → I) (hpoint : ∀ j, point j ∈ Icc a b)
    (hmono : StrictMono point)
    (connector : ∀ j, Path x₀ (p (point j)))
    (hconnector : ∀ j t, connector j t ∈ S) :
    (List.ofFn fun k ↦ FundamentalGroup.fromPath (.mk <|
      basedSegmentLoopInSet S hx₀ p
        (point k.castSucc) (point k.succ) (hmono Fin.castSucc_lt_succ).le
        (connector k.castSucc) (connector k.succ)
        (hconnector k.castSucc) (hconnector k.succ)
        (fun _ hx ↦ hp ⟨(hpoint k.castSucc).1.trans hx.1,
          hx.2.trans (hpoint k.succ).2⟩))).reverse.prod =
      FundamentalGroup.fromPath (.mk <|
        basedSegmentLoopInSet S hx₀ p (point 0) (point (Fin.last n))
          (hmono.monotone (Fin.zero_le _))
          (connector 0) (connector (Fin.last n))
          (hconnector 0) (hconnector (Fin.last n))
          (fun _ hx ↦ hp ⟨(hpoint 0).1.trans hx.1,
            hx.2.trans (hpoint (Fin.last n)).2⟩)) := by
  let segmentRange : Set.range (p.subpath a b) ⊆ S := by
    rw [Path.range_subpath_of_le p a b hab.le]
    exact image_subset_iff.mpr hp
  let segment : Path
      (⟨p a, hp ⟨le_rfl, hab.le⟩⟩ : S)
      ⟨p b, hp ⟨hab.le, le_rfl⟩⟩ :=
    pathInSet (p.subpath a b) S
      (hp ⟨le_rfl, hab.le⟩) (hp ⟨hab.le, le_rfl⟩)
      (fun t ↦ segmentRange ⟨t, rfl⟩)
  let coord : Fin (n + 1) → I := fun j ↦
    intervalCoordinate a b (point j) hab (hpoint j)
  let vertex : Fin (n + 1) → S := fun j ↦ segment (coord j)
  have vertex_eq (j : Fin (n + 1)) :
      vertex j = (⟨p (point j), hp (hpoint j)⟩ : S) := by
    apply Subtype.ext
    change p (Icc.convexComb a b (coord j)) = p (point j)
    rw [show coord j = intervalCoordinate a b (point j) hab (hpoint j) by rfl,
      convexComb_intervalCoordinate]
  let edge : ∀ k : Fin n, Path (vertex k.castSucc) (vertex k.succ) :=
    fun k ↦ segment.subpath (coord k.castSucc) (coord k.succ)
  let connectorIn : ∀ j : Fin (n + 1),
      Path (⟨x₀, hx₀⟩ : S) (vertex j) := fun j ↦
    (pathInSet (connector j) S hx₀ (hp (hpoint j))
      (hconnector j)).cast rfl (vertex_eq j)
  have edge_eq (k : Fin n) : edge k =
      (pathInSet (p.subpath (point k.castSucc) (point k.succ)) S
        (hp (hpoint k.castSucc)) (hp (hpoint k.succ))
        (by
          intro t
          apply hp
          have hk : point k.castSucc ≤ point k.succ :=
            (hmono (show k.castSucc < k.succ from Fin.castSucc_lt_succ)).le
          have hx := convexComb_mem_Icc hk t
          exact ⟨(hpoint k.castSucc).1.trans hx.1,
            hx.2.trans (hpoint k.succ).2⟩)).cast
        (vertex_eq k.castSucc) (vertex_eq k.succ) := by
    apply Path.ext
    funext t
    apply Subtype.ext
    simp only [edge, segment, coord]
    rw [pathInSet_subpath_val, pathInSet_cast_val]
    exact congrArg (fun z ↦ z t) (subpath_subpath_intervalCoordinate p a b
      (point k.castSucc) (point k.succ) hab
      (hpoint k.castSucc) (hpoint k.succ))
  have fineLoop_eq (k : Fin n) :
      connectorIn k.castSucc ≫ₚ edge k ≫ₚ (connectorIn k.succ).symm =
        basedSegmentLoopInSet S hx₀ p
          (point k.castSucc) (point k.succ) (hmono Fin.castSucc_lt_succ).le
          (connector k.castSucc) (connector k.succ)
          (hconnector k.castSucc) (hconnector k.succ)
          (fun x hx ↦ hp ⟨(hpoint k.castSucc).1.trans hx.1,
            hx.2.trans (hpoint k.succ).2⟩) := by
    rw [edge_eq]
    apply closeEdgeInSet_eq S hx₀
      (vertex k.castSucc) (vertex k.succ)
      (connector k.castSucc)
      (p.subpath (point k.castSucc) (point k.succ))
      (connector k.succ)
    · intro t
      exact pathInSet_cast_val _ _ _ _ _ _ _ _
    · intro t
      exact pathInSet_cast_val _ _ _ _ _ _ _ _
    · intro t
      exact pathInSet_cast_val _ _ _ _ _ _ _ _
  let whole : Path (vertex 0) (vertex (Fin.last n)) :=
    segment.subpath (coord 0) (coord (Fin.last n))
  have whole_eq : whole =
      (pathInSet (p.subpath (point 0) (point (Fin.last n))) S
        (hp (hpoint 0)) (hp (hpoint (Fin.last n)))
        (by
          intro t
          apply hp
          have hk : point 0 ≤ point (Fin.last n) :=
            hmono.monotone (Fin.zero_le _)
          have hx := convexComb_mem_Icc hk t
          exact ⟨(hpoint 0).1.trans hx.1,
            hx.2.trans (hpoint (Fin.last n)).2⟩)).cast
        (vertex_eq 0) (vertex_eq (Fin.last n)) := by
    apply Path.ext
    funext t
    apply Subtype.ext
    simp only [whole, segment, coord]
    rw [pathInSet_subpath_val, pathInSet_cast_val]
    exact congrArg (fun z ↦ z t) (subpath_subpath_intervalCoordinate p a b
      (point 0) (point (Fin.last n)) hab
      (hpoint 0) (hpoint (Fin.last n)))
  have coarseLoop_eq :
      connectorIn 0 ≫ₚ whole ≫ₚ (connectorIn (Fin.last n)).symm =
        basedSegmentLoopInSet S hx₀ p (point 0) (point (Fin.last n))
          (hmono.monotone (Fin.zero_le _))
          (connector 0) (connector (Fin.last n))
          (hconnector 0) (hconnector (Fin.last n))
          (fun x hx ↦ hp ⟨(hpoint 0).1.trans hx.1,
            hx.2.trans (hpoint (Fin.last n)).2⟩) := by
    rw [whole_eq]
    apply closeEdgeInSet_eq S hx₀
      (vertex 0) (vertex (Fin.last n))
      (connector 0)
      (p.subpath (point 0) (point (Fin.last n)))
      (connector (Fin.last n))
    · intro t
      exact pathInSet_cast_val _ _ _ _ _ _ _ _
    · intro t
      exact pathInSet_cast_val _ _ _ _ _ _ _ _
    · intro t
      exact pathInSet_cast_val _ _ _ _ _ _ _ _
  have hprod := reverseProd_closedEdges_eq_of_homotopic
    vertex edge connectorIn whole
    (Path.Homotopic.concat_subpath segment coord)
  simp_rw [fineLoop_eq] at hprod
  rw [coarseLoop_eq] at hprod
  exact hprod

end Hatcher.VanKampen
