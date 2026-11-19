import Hatcher.Appendix.SuccessorSkeletonQuotient
import Mathlib.AlgebraicTopology.RelativeCellComplex.AttachCells

/-!
# Classical skeleton inclusions as cell attachments

This file packages each successor step in a classical CW complex as an
`AttachCells` square. The classical sup-norm cells are first used directly,
then transported to Mathlib's standard abstract cells.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Metric Set
open scoped TopCat

namespace Hatcher.ClassicalCW

universe u

open Topology

variable {X : Type u} [TopologicalSpace X] [T2Space X]
variable (C : Set X) {D : Set X} [RelCWComplex C D]

private noncomputable def skeletonLTStepCellMap
    (n : ℕ)
    (c : PushoutCocone (skeletonLTStepAttachingMap C n)
      (skeletonLTStepBoundaryInclusion C n))
    (i : RelCWComplex.cell C n) :
    C(↑(closedBall (0 : Fin n → ℝ) 1), c.pt) where
  toFun x := c.inr ⟨i, ULift.up x⟩
  continuous_toFun := c.inr.hom.continuous.comp
    (continuous_sigmaMk.comp continuous_uliftUp)

private theorem skeletonLTStep_isPushout (n : ℕ) :
    IsPushout (skeletonLTStepAttachingMap C n)
      (skeletonLTStepBoundaryInclusion C n)
      (skeletonLTInclusion C n)
      (skeletonLTStepCharacteristicMap C n) := by
  have comm := (skeletonLTStep_square C n).symm
  have hboundary
      (c : PushoutCocone (skeletonLTStepAttachingMap C n)
        (skeletonLTStepBoundaryInclusion C n)) :
      ∀ (i : RelCWComplex.cell C n)
        (x : ↑(sphere (0 : Fin n → ℝ) 1)),
        c.inl.hom (skeletonLTStepBoundaryMap C n i x) =
          skeletonLTStepCellMap C n c i ⟨x, sphere_subset_closedBall x.2⟩ := by
    intro i x
    exact ConcreteCategory.congr_hom c.condition ⟨i, ULift.up x⟩
  let d (c : PushoutCocone (skeletonLTStepAttachingMap C n)
      (skeletonLTStepBoundaryInclusion C n)) :
      TopCat.of ↑(RelCWComplex.skeletonLT C (n + 1) : Set X) ⟶ c.pt :=
    TopCat.ofHom (skeletonLTStepDesc C n c.inl.hom
      (skeletonLTStepCellMap C n c) (hboundary c))
  refine { w := comm, isColimit' := ⟨?_⟩ }
  refine PushoutCocone.IsColimit.mk comm d ?_ ?_ ?_
  · intro c
    ext x
    exact skeletonLTStepDesc_old_apply C n c.inl.hom
      (skeletonLTStepCellMap C n c) (hboundary c) x
  · intro c
    ext p
    rcases p with ⟨i, x⟩
    exact skeletonLTStepDesc_cell_apply C n c.inl.hom
      (skeletonLTStepCellMap C n c) (hboundary c) i x.down
  · intro c m hmOld hmCells
    ext y
    obtain ⟨z, rfl⟩ := surjective_skeletonLTStepJointMap C n y
    rcases z with x | ⟨i, x⟩
    · change m (skeletonLTStepOldMap C n x) =
        d c (skeletonLTStepOldMap C n x)
      calc
        _ = c.inl x := ConcreteCategory.congr_hom hmOld x
        _ = _ := (skeletonLTStepDesc_old_apply C n c.inl.hom
          (skeletonLTStepCellMap C n c) (hboundary c) x).symm
    · change m (skeletonLTStepClosedCellMap C n i x) =
        d c (skeletonLTStepClosedCellMap C n i x)
      calc
        _ = c.inr ⟨i, ULift.up x⟩ :=
          ConcreteCategory.congr_hom hmCells ⟨i, ULift.up x⟩
        _ = _ := (skeletonLTStepDesc_cell_apply C n c.inl.hom
          (skeletonLTStepCellMap C n c) (hboundary c) i x).symm

private noncomputable def skeletonLTInclusion_attachClassicalCells (n : ℕ) :
    HomotopicalAlgebra.AttachCells.{u}
      (fun _ : Unit ↦ classicalDiskBoundaryInclusion.{u} n)
      (skeletonLTInclusion C n) where
  ι := RelCWComplex.cell C n
  π := fun _ ↦ ()
  cofan₁ := skeletonLTStepBoundaryCofan C n
  cofan₂ := skeletonLTStepClosedCellCofan C n
  isColimit₁ := TopCat.sigmaCofanIsColimit _
  isColimit₂ := TopCat.sigmaCofanIsColimit _
  m := skeletonLTStepBoundaryInclusion C n
  hm i := by
    ext x
    rfl
  g₁ := skeletonLTStepAttachingMap C n
  g₂ := skeletonLTStepCharacteristicMap C n
  isPushout := skeletonLTStep_isPushout C n

/-- The inclusion into the next strict classical skeleton is an attachment by
standard abstract cells. -/
noncomputable def skeletonLTInclusion_attachCells (n : ℕ) :
    HomotopicalAlgebra.AttachCells.{u}
      (TopCat.RelativeCWComplex.basicCell.{u} n)
      (skeletonLTInclusion C n) :=
  (skeletonLTInclusion_attachClassicalCells C n).reindexCellTypes
    (TopCat.RelativeCWComplex.basicCell.{u} n) (fun _ ↦ ())
    (fun _ ↦ classicalCellArrowIso n)

/-- Inclusion of one standard classical skeleton into its successor. -/
noncomputable def skeletonInclusion (n : ℕ) :
    TopCat.of ↑(RelCWComplex.skeleton C n : Set X) ⟶
      TopCat.of ↑(RelCWComplex.skeleton C (n + 1) : Set X) :=
  skeletonLTInclusion C (n + 1)

/-- The inclusion into the next classical skeleton is an attachment by cells
of the next dimension. -/
noncomputable def skeletonInclusion_attachCells (n : ℕ) :
    HomotopicalAlgebra.AttachCells.{u}
      (TopCat.RelativeCWComplex.basicCell.{u} (n + 1))
      (skeletonInclusion C n) :=
  skeletonLTInclusion_attachCells C (n + 1)

end Hatcher.ClassicalCW

namespace Hatcher.ClassicalCW

open Metric Set _root_.Topology

universe u v w

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  (C : Set X) [CWComplex C] (D : Set Y) [CWComplex D]

/-- A product cell is a pair of actual factor cells whose dimensions sum to `n`. -/
abbrev ClassicalProductCell (n : ℕ) :=
  {i : (Σ p, RelCWComplex.cell C p) × (Σ q, RelCWComplex.cell D q) // i.1.1 + i.2.1 = n}

/-- Concatenate the two sup-norm coordinate spaces in the given product cell. -/
def classicalProductCellAxes {n : ℕ} (i : ClassicalProductCell C D n) :
    ((Fin i.val.1.1 → ℝ) × (Fin i.val.2.1 → ℝ)) ≃ᵢ (Fin n → ℝ) :=
  Fin.appendIsometryOfEq (α := ℝ) i.property

private theorem appendProductAxes_zero {p q n : ℕ} (h : p + q = n) :
    Fin.appendIsometryOfEq (α := ℝ) h 0 = 0 := by
  subst n
  funext j
  change Fin.append (0 : Fin p → ℝ) (0 : Fin q → ℝ) ((finCongr rfl).symm j) = 0
  have hj : (finCongr rfl).symm j = j := by ext <;> rfl
  rw [hj]
  refine Fin.addCases (motive := fun k ↦
    Fin.append (0 : Fin p → ℝ) (0 : Fin q → ℝ) k = 0) ?_ ?_ j
  · intro k
    simp
  · intro k
    simp

private theorem classicalProductCellDist_zero {n : ℕ} (i : ClassicalProductCell C D n)
    (x : Fin n → ℝ) : dist ((classicalProductCellAxes C D i).symm x) 0 = dist x 0 := by
  let e := classicalProductCellAxes C D i
  have h : e 0 = 0 := appendProductAxes_zero i.property
  simpa only [IsometryEquiv.apply_symm_apply, h] using (e.dist_eq (e.symm x) 0).symm

private theorem classicalProductCell_mem_ball {n : ℕ} (i : ClassicalProductCell C D n)
    (x : Fin n → ℝ) :
    x ∈ ball 0 1 ↔ ((classicalProductCellAxes C D i).symm x).1 ∈ ball 0 1 ∧
      ((classicalProductCellAxes C D i).symm x).2 ∈ ball 0 1 := by
  let z := (classicalProductCellAxes C D i).symm x
  calc
    x ∈ ball 0 1 ↔ z ∈ ball 0 1 := by
      simp only [mem_ball, z, classicalProductCellDist_zero C D i]
    _ ↔ z.1 ∈ ball 0 1 ∧ z.2 ∈ ball 0 1 := by
      change z ∈ ball (0, 0) 1 ↔ _
      rw [← Metric.ball_prod_same] <;> rfl

private theorem classicalProductCell_mem_closedBall {n : ℕ} (i : ClassicalProductCell C D n)
    (x : Fin n → ℝ) :
    x ∈ closedBall 0 1 ↔ ((classicalProductCellAxes C D i).symm x).1 ∈ closedBall 0 1 ∧
      ((classicalProductCellAxes C D i).symm x).2 ∈ closedBall 0 1 := by
  let z := (classicalProductCellAxes C D i).symm x
  calc
    x ∈ closedBall 0 1 ↔ z ∈ closedBall 0 1 := by
      simp only [mem_closedBall, z, classicalProductCellDist_zero C D i]
    _ ↔ z.1 ∈ closedBall 0 1 ∧ z.2 ∈ closedBall 0 1 := by
      change z ∈ closedBall (0, 0) 1 ↔ _
      rw [← Metric.closedBall_prod_same] <;> rfl

private theorem classicalProductCell_mem_frontier {n : ℕ} (i : ClassicalProductCell C D n)
    {x : Fin n → ℝ} (hx : x ∈ sphere 0 1) :
    ((classicalProductCellAxes C D i).symm x).1 ∈ sphere 0 1 ∨
      ((classicalProductCellAxes C D i).symm x).2 ∈ sphere 0 1 := by
  let z := (classicalProductCellAxes C D i).symm x
  have hclosed := (classicalProductCell_mem_closedBall C D i x).1 (sphere_subset_closedBall hx)
  have hnot : ¬ (z.1 ∈ ball 0 1 ∧ z.2 ∈ ball 0 1) := fun h ↦
    (ne_of_lt (mem_ball.mp ((classicalProductCell_mem_ball C D i x).2 h))) (mem_sphere.mp hx)
  by_cases hl : z.1 ∈ ball 0 1
  · right
    exact mem_sphere.mpr (le_antisymm (mem_closedBall.mp hclosed.2)
      (le_of_not_gt (fun hr ↦ hnot ⟨hl, mem_ball.mpr hr⟩)))
  · left
    exact mem_sphere.mpr (le_antisymm (mem_closedBall.mp hclosed.1)
      (le_of_not_gt (fun h ↦ hl (mem_ball.mpr h))))

private def classicalProductCellMap (n : ℕ) (i : ClassicalProductCell C D n) :
    PartialEquiv (Fin n → ℝ) (X × Y) :=
  (classicalProductCellAxes C D i).symm.toEquiv.transPartialEquiv
    ((RelCWComplex.map (C := C) i.val.1.1 i.val.1.2).prod
      (RelCWComplex.map (C := D) i.val.2.1 i.val.2.2))

private theorem classicalProductCellSource (n : ℕ) (i : ClassicalProductCell C D n) :
    (classicalProductCellMap C D n i).source = ball 0 1 := by
  ext x
  let a := RelCWComplex.map (C := C) i.val.1.1 i.val.1.2
  let b := RelCWComplex.map (C := D) i.val.2.1 i.val.2.2
  change (classicalProductCellAxes C D i).symm x ∈ a.source ×ˢ b.source ↔ _
  simp only [a, b, RelCWComplex.source_eq]
  exact (classicalProductCell_mem_ball C D i x).symm

private theorem classicalProductCellContinuous (n : ℕ) (i : ClassicalProductCell C D n) :
    ContinuousOn (classicalProductCellMap C D n i) (closedBall 0 1) := by
  let e := (classicalProductCellAxes C D i).symm
  let a := RelCWComplex.map (C := C) i.val.1.1 i.val.1.2
  let b := RelCWComplex.map (C := D) i.val.2.1 i.val.2.2
  have ha : ContinuousOn (fun x ↦ a (e x).1) (closedBall 0 1) :=
    (RelCWComplex.continuousOn (C := C) i.val.1.1 i.val.1.2).comp
      (continuous_fst.comp e.continuous).continuousOn
      (fun x hx ↦ ((classicalProductCell_mem_closedBall C D i x).1 hx).1)
  have hb : ContinuousOn (fun x ↦ b (e x).2) (closedBall 0 1) :=
    (RelCWComplex.continuousOn (C := D) i.val.2.1 i.val.2.2).comp
      (continuous_snd.comp e.continuous).continuousOn
      (fun x hx ↦ ((classicalProductCell_mem_closedBall C D i x).1 hx).2)
  exact ha.prodMk hb

private theorem classicalProductCellInverseContinuous (n : ℕ) (i : ClassicalProductCell C D n) :
    ContinuousOn (classicalProductCellMap C D n i).symm (classicalProductCellMap C D n i).target := by
  let e := classicalProductCellAxes C D i
  let a := RelCWComplex.map (C := C) i.val.1.1 i.val.1.2
  let b := RelCWComplex.map (C := D) i.val.2.1 i.val.2.2
  change ContinuousOn (fun z : X × Y ↦ e (a.symm z.1, b.symm z.2)) (a.target ×ˢ b.target)
  have ha : ContinuousOn (fun z : X × Y ↦ a.symm z.1) (a.target ×ˢ b.target) :=
    (RelCWComplex.continuousOn_symm (C := C) i.val.1.1 i.val.1.2).comp
      continuous_fst.continuousOn (fun _ hz ↦ hz.1)
  have hb : ContinuousOn (fun z : X × Y ↦ b.symm z.2) (a.target ×ˢ b.target) :=
    (RelCWComplex.continuousOn_symm (C := D) i.val.2.1 i.val.2.2).comp
      continuous_snd.continuousOn (fun _ hz ↦ hz.2)
  exact e.continuous.comp_continuousOn (ha.prodMk hb)

private theorem classicalProductCell_image {n : ℕ} (i : ClassicalProductCell C D n)
    {S : Set (Fin n → ℝ)} {U : Set (Fin i.val.1.1 → ℝ)} {V : Set (Fin i.val.2.1 → ℝ)}
    (h : ∀ x, x ∈ S ↔ ((classicalProductCellAxes C D i).symm x).1 ∈ U ∧
      ((classicalProductCellAxes C D i).symm x).2 ∈ V) :
    classicalProductCellMap C D n i '' S =
      (RelCWComplex.map (C := C) i.val.1.1 i.val.1.2 '' U) ×ˢ
        (RelCWComplex.map (C := D) i.val.2.1 i.val.2.2 '' V) := by
  let e := classicalProductCellAxes C D i
  let a := RelCWComplex.map (C := C) i.val.1.1 i.val.1.2
  let b := RelCWComplex.map (C := D) i.val.2.1 i.val.2.2
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hh := (h x).mp hx
    exact ⟨⟨_, hh.1, rfl⟩, ⟨_, hh.2, rfl⟩⟩
  · rintro ⟨⟨x, hx, hx'⟩, ⟨y, hy, hy'⟩⟩
    refine ⟨e (x, y), (h _).mpr ?_, ?_⟩
    · change (e.symm (e (x, y))).1 ∈ U ∧ (e.symm (e (x, y))).2 ∈ V
      rw [e.symm_apply_apply]
      exact ⟨hx, hy⟩
    · change (a (e.symm (e (x, y))).1, b (e.symm (e (x, y))).2) = z
      rw [e.symm_apply_apply]
      exact Prod.ext hx' hy'

private theorem classicalProductCell_openImage {n : ℕ} (i : ClassicalProductCell C D n) :
    classicalProductCellMap C D n i '' ball 0 1 =
      RelCWComplex.openCell (C := C) i.val.1.1 i.val.1.2 ×ˢ
        RelCWComplex.openCell (C := D) i.val.2.1 i.val.2.2 :=
  classicalProductCell_image C D i (classicalProductCell_mem_ball C D i)

private theorem classicalProductCell_closedImage {n : ℕ} (i : ClassicalProductCell C D n) :
    classicalProductCellMap C D n i '' closedBall 0 1 =
      RelCWComplex.closedCell (C := C) i.val.1.1 i.val.1.2 ×ˢ
        RelCWComplex.closedCell (C := D) i.val.2.1 i.val.2.2 :=
  classicalProductCell_image C D i (classicalProductCell_mem_closedBall C D i)

private theorem classicalProductCellsDisjoint :
    (univ : Set (Σ n, ClassicalProductCell C D n)).PairwiseDisjoint
      (fun i ↦ classicalProductCellMap C D i.1 i.2 '' ball 0 1) := by
  intro i _ j _ hij
  rw [classicalProductCell_openImage C D i.2, classicalProductCell_openImage C D j.2,
    Set.disjoint_left]
  intro z hz hw
  have hc : i.2.val.1 = j.2.val.1 := RelCWComplex.eq_of_not_disjoint_openCell (C := C)
    (fun h ↦ Set.disjoint_left.mp h hz.1 hw.1)
  have hd : i.2.val.2 = j.2.val.2 := RelCWComplex.eq_of_not_disjoint_openCell (C := D)
    (fun h ↦ Set.disjoint_left.mp h hz.2 hw.2)
  let e := Equiv.sigmaFiberEquiv
    (fun a : (Σ p, RelCWComplex.cell C p) × (Σ q, RelCWComplex.cell D q) ↦ a.1.1 + a.2.1)
  exact hij (e.injective (Prod.ext hc hd))

private theorem classicalCellBoundaryInLower {T : Type w} [TopologicalSpace T]
    (A : Set T) [CWComplex A] {p : ℕ} (i : RelCWComplex.cell A p)
    {x : Fin p → ℝ} (hx : x ∈ sphere 0 1) :
    ∃ m < p, ∃ j : RelCWComplex.cell A m,
      RelCWComplex.map (C := A) p i x ∈ RelCWComplex.closedCell (C := A) m j := by
  obtain ⟨I, hI⟩ := CWComplex.mapsTo (C := A) p i
  obtain ⟨m, hm⟩ := Set.mem_iUnion.mp (hI hx)
  obtain ⟨hlt, hm⟩ := Set.mem_iUnion.mp hm
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hm
  obtain ⟨_, hj⟩ := Set.mem_iUnion.mp hj
  exact ⟨m, hlt, j, hj⟩

private theorem classicalProductCell_mem_lower {n p q : ℕ} {z : X × Y}
    {i : RelCWComplex.cell C p} {j : RelCWComplex.cell D q} (hpq : p + q < n)
    (hC : z.1 ∈ RelCWComplex.closedCell (C := C) p i)
    (hD : z.2 ∈ RelCWComplex.closedCell (C := D) q j) :
    z ∈ ⋃ (m < n) (k : ClassicalProductCell C D m), classicalProductCellMap C D m k '' closedBall 0 1 := by
  let k : ClassicalProductCell C D (p + q) := ⟨(⟨p, i⟩, ⟨q, j⟩), rfl⟩
  refine Set.mem_iUnion.mpr ⟨p + q, Set.mem_iUnion.mpr ⟨hpq, Set.mem_iUnion.mpr ⟨k, ?_⟩⟩⟩
  rw [classicalProductCell_closedImage]
  exact ⟨hC, hD⟩

private theorem classicalProductCellBoundary (n : ℕ) (i : ClassicalProductCell C D n) :
    MapsTo (classicalProductCellMap C D n i) (sphere 0 1)
      (⋃ (m < n) (j : ClassicalProductCell C D m), classicalProductCellMap C D m j '' closedBall 0 1) := by
  intro x hx
  let z := (classicalProductCellAxes C D i).symm x
  have hi := i.property
  have hclosed := (classicalProductCell_mem_closedBall C D i x).1 (sphere_subset_closedBall hx)
  have hC : (classicalProductCellMap C D n i x).1 ∈
      RelCWComplex.closedCell (C := C) i.val.1.1 i.val.1.2 := ⟨z.1, hclosed.1, rfl⟩
  have hD : (classicalProductCellMap C D n i x).2 ∈
      RelCWComplex.closedCell (C := D) i.val.2.1 i.val.2.2 := ⟨z.2, hclosed.2, rfl⟩
  rcases classicalProductCell_mem_frontier C D i hx with h | h
  · obtain ⟨m, hm, j, hj⟩ := classicalCellBoundaryInLower C i.val.1.2 h
    exact classicalProductCell_mem_lower C D (show m + i.val.2.1 < n by omega) hj hD
  · obtain ⟨m, hm, j, hj⟩ := classicalCellBoundaryInLower D i.val.2.2 h
    exact classicalProductCell_mem_lower C D (show i.val.1.1 + m < n by omega) hC hj

private theorem classicalProductCellsCover :
    (⋃ (n : ℕ) (i : ClassicalProductCell C D n), classicalProductCellMap C D n i '' closedBall 0 1) =
      C ×ˢ D := by
  apply Set.Subset.antisymm
  · intro z hz
    obtain ⟨n, hz⟩ := Set.mem_iUnion.mp hz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
    rw [classicalProductCell_closedImage] at hi
    exact ⟨RelCWComplex.closedCell_subset_complex (C := C) _ _ hi.1,
      RelCWComplex.closedCell_subset_complex (C := D) _ _ hi.2⟩
  · intro z hz
    have hC : z.1 ∈ ⋃ (p : ℕ) (i : RelCWComplex.cell C p), RelCWComplex.closedCell (C := C) p i := by
      rw [CWComplex.union]
      exact hz.1
    have hD : z.2 ∈ ⋃ (q : ℕ) (j : RelCWComplex.cell D q), RelCWComplex.closedCell (C := D) q j := by
      rw [CWComplex.union]
      exact hz.2
    obtain ⟨p, hp⟩ := Set.mem_iUnion.mp hC
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hp
    obtain ⟨q, hq⟩ := Set.mem_iUnion.mp hD
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hq
    let k : ClassicalProductCell C D (p + q) := ⟨(⟨p, i⟩, ⟨q, j⟩), rfl⟩
    refine Set.mem_iUnion.mpr ⟨p + q, Set.mem_iUnion.mpr ⟨k, ?_⟩⟩
    rw [classicalProductCell_closedImage]
    exact ⟨hi, hj⟩

variable [CWComplex.Finite C] [CWComplex.Finite D]

private theorem classicalProductCellEventuallyEmpty :
    ∀ᶠ n in Filter.atTop, IsEmpty (ClassicalProductCell C D n) := by
  obtain ⟨p, hp⟩ := Filter.eventually_atTop.mp
    (CWComplex.FiniteDimensional.eventually_isEmpty_cell (C := C))
  obtain ⟨q, hq⟩ := Filter.eventually_atTop.mp
    (CWComplex.FiniteDimensional.eventually_isEmpty_cell (C := D))
  refine Filter.eventually_atTop.mpr ⟨p + q, fun n hn ↦ ⟨fun i ↦ ?_⟩⟩
  have hi := i.property
  by_cases h : p ≤ i.val.1.1
  · exact (hp _ h).false i.val.1.2
  · exact (hq _ (show q ≤ i.val.2.1 by omega)).false i.val.2.2

private theorem classicalProductCellFinite (n : ℕ) : Finite (ClassicalProductCell C D n) := by
  letI : Finite (Σ p, RelCWComplex.cell C p) := RelCWComplex.finite_cells_of_finite (C := C)
  letI : Finite (Σ q, RelCWComplex.cell D q) := RelCWComplex.finite_cells_of_finite (C := D)
  infer_instance

/-- **Hatcher, Chapter 0, Products.** The actual topological product of two
finite classical CW complexes has their product cell structure. -/
@[instance_reducible]
def finiteClassicalCwProduct : CWComplex (C ×ˢ D) :=
  CWComplex.mkFinite _ (ClassicalProductCell C D) (classicalProductCellMap C D)
    (classicalProductCellEventuallyEmpty C D) (classicalProductCellFinite C D)
    (classicalProductCellSource C D) (classicalProductCellContinuous C D)
    (classicalProductCellInverseContinuous C D) (classicalProductCellsDisjoint C D)
    (classicalProductCellBoundary C D) (classicalProductCellsCover C D)

/-- The product is finite with the specified cell structure. -/
theorem finiteClassicalCwProduct_finite :
    letI := finiteClassicalCwProduct C D
    CWComplex.Finite (C ×ˢ D) :=
  CWComplex.finite_mkFinite _ (ClassicalProductCell C D) (classicalProductCellMap C D)
    (classicalProductCellEventuallyEmpty C D) (classicalProductCellFinite C D)
    (classicalProductCellSource C D) (classicalProductCellContinuous C D)
    (classicalProductCellInverseContinuous C D) (classicalProductCellsDisjoint C D)
    (classicalProductCellBoundary C D) (classicalProductCellsCover C D)

/-- The degree `n` cells of this structure are exactly the pairs of total degree `n`. -/
def finiteClassicalCwProduct_cells (n : ℕ) :
    letI := finiteClassicalCwProduct C D
    RelCWComplex.cell (C ×ˢ D) n ≃ ClassicalProductCell C D n := Equiv.refl _

/-- The actual product characteristic map is the pair of factor maps after
splitting the classical coordinates. This holds in particular on the closed disk. -/
theorem finiteClassicalCwProduct_characteristic {n : ℕ} (i : ClassicalProductCell C D n)
    (x : Fin n → ℝ) :
    letI := finiteClassicalCwProduct C D
    RelCWComplex.map (C := C ×ˢ D) n ((finiteClassicalCwProduct_cells C D n).symm i) x =
      (RelCWComplex.map (C := C) i.val.1.1 i.val.1.2 ((classicalProductCellAxes C D i).symm x).1,
        RelCWComplex.map (C := D) i.val.2.1 i.val.2.2 ((classicalProductCellAxes C D i).symm x).2) := rfl

/-- The actual open product cell is the product of the two open cells. -/
theorem finiteClassicalCwProduct_openCell {n : ℕ} (i : ClassicalProductCell C D n) :
    letI := finiteClassicalCwProduct C D
    RelCWComplex.openCell (C := C ×ˢ D) n ((finiteClassicalCwProduct_cells C D n).symm i) =
      RelCWComplex.openCell (C := C) i.val.1.1 i.val.1.2 ×ˢ
        RelCWComplex.openCell (C := D) i.val.2.1 i.val.2.2 := classicalProductCell_openImage C D i

/-- The actual closed product cell is the product of the factor closed cells. -/
theorem finiteClassicalCwProduct_closedCell {n : ℕ} (i : ClassicalProductCell C D n) :
    letI := finiteClassicalCwProduct C D
    RelCWComplex.closedCell (C := C ×ˢ D) n ((finiteClassicalCwProduct_cells C D n).symm i) =
      RelCWComplex.closedCell (C := C) i.val.1.1 i.val.1.2 ×ˢ
        RelCWComplex.closedCell (C := D) i.val.2.1 i.val.2.2 := classicalProductCell_closedImage C D i

end Hatcher.ClassicalCW
