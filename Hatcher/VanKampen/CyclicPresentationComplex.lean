import Hatcher.VanKampen.CellAttachmentTwo
import Hatcher.VanKampen.CyclicPresentationAlgebra
import Hatcher.VanKampen.IndexedConeAttachment

/-!
# The cyclic presentation complex

This file constructs Hatcher's presentation complex for
`\langle a \mid a^n \rangle` as one two-cell attached to the circle by the
degree-`n` map, and computes its fundamental group.
-/

noncomputable section

open CategoryTheory FundamentalGroupoid HomotopicalAlgebra Set Topology
open scoped ContinuousMap TopCat

namespace Hatcher

/-- The attaching map for the cyclic presentation complex. -/
noncomputable def cyclicPresentationAttachingMap (n : ℕ) (_ : Unit) :
    ((TopCat.diskBoundary 2 : TopCat) : Type) → _root_.Circle :=
  fun z ↦ Circle.degreeMap n (diskBoundaryTwoHomeomorphCircle z)

theorem continuous_cyclicPresentationAttachingMap (n : ℕ) (i : Unit) :
    Continuous (cyclicPresentationAttachingMap n i) :=
  (Circle.degreeMap n).continuous.comp diskBoundaryTwoHomeomorphCircle.continuous

@[simp]
theorem cyclicPresentationAttachingMap_basepoint (n : ℕ) (i : Unit) :
    cyclicPresentationAttachingMap n i diskBoundaryTwoBasepoint =
      (1 : _root_.Circle) := by
  simp [cyclicPresentationAttachingMap]

/-- The space obtained by attaching one two-cell to the circle by the
degree-`n` map. -/
abbrev cyclicPresentationComplex (n : ℕ) : Type :=
  VanKampen.IndexedConeAttachment (cyclicPresentationAttachingMap n)

/-- The image of `1 : Circle` in the cyclic presentation complex. -/
def cyclicPresentationBasepoint (n : ℕ) : cyclicPresentationComplex n :=
  VanKampen.IndexedConeAttachment.base
    (cyclicPresentationAttachingMap n) 1

/-- The inclusion of the circle into the cyclic presentation complex. -/
def cyclicPresentationBaseHom (n : ℕ) :
    TopCat.of _root_.Circle ⟶ TopCat.of (cyclicPresentationComplex n) :=
  VanKampen.IndexedConeAttachment.baseHom
    (cyclicPresentationAttachingMap n)

/-- The cyclic presentation complex is a single standard two-cell attachment. -/
def cyclicPresentationAttachCells (n : ℕ) :
    AttachCells (TopCat.RelativeCWComplex.basicCell 2)
      (cyclicPresentationBaseHom n) :=
  VanKampen.IndexedConeAttachment.attachCells_basicCell 2
    (cyclicPresentationAttachingMap n)
    (continuous_cyclicPresentationAttachingMap n)

@[simp]
theorem cyclicPresentationAttachCells_attachingFamily (n : ℕ)
    (i : (cyclicPresentationAttachCells n).ι) :
    VanKampen.CellAttachmentCover.attachingFamily
        (cyclicPresentationAttachCells n) i =
      cyclicPresentationAttachingMap n i := by
  rfl

/-- The attaching map is based at the circle basepoint. -/
def cyclicPresentationBasepointPath (n : ℕ) :
    ∀ i : (cyclicPresentationAttachCells n).ι,
      Path (1 : _root_.Circle)
        (VanKampen.CellAttachmentCover.attachingFamily
          (cyclicPresentationAttachCells n) i diskBoundaryTwoBasepoint) :=
  fun i ↦ (Path.refl (1 : _root_.Circle)).cast rfl
    (cyclicPresentationAttachingMap_basepoint n i)

private theorem fundamentalGroup_basechange_refl_cast_map_eq_mapOfEq
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (F : C(A, B)) (a : A) (b : B) (h : F a = b)
    (g : FundamentalGroup A a) :
    (FundamentalGroup.fundamentalGroupMulEquivOfPath
        ((Path.refl b).cast rfl h)).symm
          (FundamentalGroup.map F a g) =
      FundamentalGroup.mapOfEq F h g := by
  subst b
  rfl

private theorem fundamentalGroup_mapOfEq_comp_apply
    {A B C : Type*} [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalSpace C] (F : C(A, B)) (G : C(B, C))
    (a : A) (b : B) (c : C) (hF : F a = b) (hG : G b = c)
    (g : FundamentalGroup A a) :
    FundamentalGroup.mapOfEq (G.comp F)
        ((congrArg G hF).trans hG) g =
      FundamentalGroup.mapOfEq G hG
        (FundamentalGroup.mapOfEq F hF g) := by
  subst b
  subst c
  induction g using Path.Homotopic.Quotient.ind with
  | mk p =>
      rw [FundamentalGroup.mapOfEq_apply,
        FundamentalGroup.mapOfEq_apply,
        FundamentalGroup.mapOfEq_apply]
      apply congrArg FundamentalGroup.fromPath
      apply congrArg Path.Homotopic.Quotient.mk
      apply Path.ext
      rfl

private noncomputable def diskBoundaryTwoContinuousMap :
    C(VanKampen.AuxiliaryCellAttachment.BoundaryTwo, _root_.Circle) :=
  ⟨diskBoundaryTwoHomeomorphCircle,
    diskBoundaryTwoHomeomorphCircle.continuous⟩

private theorem diskBoundaryTwoContinuousMap_generator :
    FundamentalGroup.mapOfEq diskBoundaryTwoContinuousMap
        diskBoundaryTwoHomeomorphCircle_basepoint
        VanKampen.AuxiliaryCellAttachment.diskBoundaryTwoGenerator =
      Circle.degreeLoopClass 1 := by
  unfold VanKampen.AuxiliaryCellAttachment.diskBoundaryTwoGenerator
    Circle.degreeLoopClass
  rw [FundamentalGroup.mapOfEq_apply]
  exact congrArg FundamentalGroup.fromPath
    (congrArg Path.Homotopic.Quotient.mk
      diskBoundaryTwoHomeomorphCircle_map_loop)

private noncomputable def cyclicPresentationAttachingContinuousMap
    (n : ℕ) (i : Unit) :
    C(VanKampen.AuxiliaryCellAttachment.BoundaryTwo, _root_.Circle) :=
  ⟨cyclicPresentationAttachingMap n i,
    continuous_cyclicPresentationAttachingMap n i⟩

private theorem cyclicPresentationAttachingContinuousMap_generator
    (n : ℕ) (i : Unit) :
    FundamentalGroup.mapOfEq
        (cyclicPresentationAttachingContinuousMap n i)
        (cyclicPresentationAttachingMap_basepoint n i)
        VanKampen.AuxiliaryCellAttachment.diskBoundaryTwoGenerator =
      Circle.degreeLoopClass n := by
  calc
    _ = FundamentalGroup.mapOfEq (Circle.degreeMap n)
          (Circle.degreeMap_one n)
          (FundamentalGroup.mapOfEq diskBoundaryTwoContinuousMap
            diskBoundaryTwoHomeomorphCircle_basepoint
            VanKampen.AuxiliaryCellAttachment.diskBoundaryTwoGenerator) := by
        exact fundamentalGroup_mapOfEq_comp_apply
          diskBoundaryTwoContinuousMap (Circle.degreeMap n)
          diskBoundaryTwoBasepoint 1 1
          diskBoundaryTwoHomeomorphCircle_basepoint.{0}
          (Circle.degreeMap_one n)
          VanKampen.AuxiliaryCellAttachment.diskBoundaryTwoGenerator
    _ = Circle.degreeLoopClass n := by
      rw [diskBoundaryTwoContinuousMap_generator,
        Circle.mapOfEq_degreeMap_degreeLoopClass_one]

@[simp]
theorem cyclicPresentation_twoCellAttachingLoop (n : ℕ)
    (i : (cyclicPresentationAttachCells n).ι) :
    VanKampen.twoCellAttachingLoop
        (cyclicPresentationAttachCells n) 1
        (cyclicPresentationBasepointPath n) i =
      Circle.degreeLoopClass n := by
  calc
    _ = FundamentalGroup.mapOfEq
        (cyclicPresentationAttachingContinuousMap n i)
        (cyclicPresentationAttachingMap_basepoint n i)
        VanKampen.AuxiliaryCellAttachment.diskBoundaryTwoGenerator := by
      unfold VanKampen.twoCellAttachingLoop cyclicPresentationBasepointPath
      apply fundamentalGroup_basechange_refl_cast_map_eq_mapOfEq
    _ = Circle.degreeLoopClass n :=
      cyclicPresentationAttachingContinuousMap_generator n i

@[simp]
theorem cyclicPresentation_twoCellAttachingNormalSubgroup (n : ℕ) :
    VanKampen.twoCellAttachingNormalSubgroup
        (cyclicPresentationAttachCells n) 1
        (cyclicPresentationBasepointPath n) =
      Subgroup.normalClosure ({Circle.degreeLoopClass n} : Set _) := by
  unfold VanKampen.twoCellAttachingNormalSubgroup
  apply congrArg Subgroup.normalClosure
  ext g
  constructor
  · rintro ⟨i, rfl⟩
    rw [cyclicPresentation_twoCellAttachingLoop]
    exact Set.mem_singleton (Circle.degreeLoopClass n)
  · intro hg
    rw [Set.mem_singleton_iff] at hg
    subst g
    exact ⟨(), cyclicPresentation_twoCellAttachingLoop n ()⟩

/-- **Hatcher, Example 1.29 (page 52), group calculation.** For positive `n`,
the fundamental group of the space obtained by attaching one two-cell to the
circle along the degree-`n` map is the cyclic group of order `n`. The
construction also makes sense for `n = 0`, where the target is `ZMod 0 ≃+ ℤ`. -/
noncomputable def fundamentalGroupEquiv_cyclicPresentationComplex (n : ℕ) :
    FundamentalGroup (cyclicPresentationComplex n)
        (cyclicPresentationBasepoint n) ≃*
      Multiplicative (ZMod n) := by
  letI : (VanKampen.twoCellAttachingNormalSubgroup
      (cyclicPresentationAttachCells n) 1
      (cyclicPresentationBasepointPath n)).Normal :=
    VanKampen.twoCellAttachingNormalSubgroup_normal
      (cyclicPresentationAttachCells n) 1
      (cyclicPresentationBasepointPath n)
  refine
    (fundamentalGroup_quotient_of_attachTwoCells
      (cyclicPresentationAttachCells n) 1
      (cyclicPresentationBasepointPath n)).symm.trans ?_
  exact (QuotientGroup.quotientMulEquivOfEq
      (cyclicPresentation_twoCellAttachingNormalSubgroup n)).trans
    (cyclicPresentationQuotientEquiv n)

/-- Under the cyclic-presentation equivalence, inclusion of a circle loop is
winding number reduced modulo `n`. -/
@[simp]
theorem fundamentalGroupEquiv_cyclicPresentationComplex_map (n : ℕ)
    (g : FundamentalGroup _root_.Circle 1) :
    fundamentalGroupEquiv_cyclicPresentationComplex n
        (FundamentalGroup.map (cyclicPresentationBaseHom n).hom 1 g) =
      Multiplicative.ofAdd ((Circle.windingNumberFun g : ℤ) : ZMod n) := by
  letI : (VanKampen.twoCellAttachingNormalSubgroup
      (cyclicPresentationAttachCells n) 1
      (cyclicPresentationBasepointPath n)).Normal :=
    VanKampen.twoCellAttachingNormalSubgroup_normal
      (cyclicPresentationAttachCells n) 1
      (cyclicPresentationBasepointPath n)
  change
    cyclicPresentationQuotientEquiv n
      (QuotientGroup.quotientMulEquivOfEq
        (cyclicPresentation_twoCellAttachingNormalSubgroup n)
        ((fundamentalGroup_quotient_of_attachTwoCells
          (cyclicPresentationAttachCells n) 1
          (cyclicPresentationBasepointPath n)).symm
          (FundamentalGroup.map (cyclicPresentationBaseHom n).hom 1 g))) = _
  rw [← fundamentalGroup_quotient_of_attachTwoCells_mk]
  rw [MulEquiv.symm_apply_apply]
  change cyclicPresentationQuotientEquiv n
      (QuotientGroup.mk'
        (Subgroup.normalClosure ({Circle.degreeLoopClass n} : Set _)) g) = _
  exact cyclicPresentationQuotientEquiv_mk n g

end Hatcher
