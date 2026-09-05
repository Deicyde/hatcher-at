import Hatcher.VanKampen.VanKampenKernel
import Hatcher.VanKampen.WellPointedWedgeNeckContraction
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

noncomputable section

open CategoryTheory Set
open scoped ContinuousMap

namespace Hatcher

universe u v w

/-- The homomorphism between indexed free products induced componentwise. -/
def coprodIMap {ι : Type u} {G : ι → Type v} {H : ι → Type w}
    [∀ i, Group (G i)] [∀ i, Group (H i)]
    (f : ∀ i, G i →* H i) :
    Monoid.CoprodI G →* Monoid.CoprodI H :=
  Monoid.CoprodI.lift fun i =>
    (Monoid.CoprodI.of : H i →* Monoid.CoprodI H).comp (f i)

@[simp]
theorem coprodIMap_of {ι : Type u} {G : ι → Type v} {H : ι → Type w}
    [∀ i, Group (G i)] [∀ i, Group (H i)]
    (f : ∀ i, G i →* H i) (i : ι) (g : G i) :
    coprodIMap f (Monoid.CoprodI.of g) = Monoid.CoprodI.of (f i g) := by
  simp [coprodIMap]

/-- An indexed free product over an empty index type has one element. -/
@[reducible]
def coprodIUniqueOfIsEmpty {ι : Type u} [IsEmpty ι]
    (G : ι → Type v) [∀ i, Group (G i)] :
    Unique (Monoid.CoprodI G) where
  default := 1
  uniq g := by
    refine Monoid.CoprodI.induction_on
      (motive := fun g => g = 1) g rfl ?_ ?_
    · intro i
      exact isEmptyElim i
    · intro x y hx hy
      simp [hx, hy]

/-- Componentwise group equivalences induce an equivalence of indexed free
products. -/
def coprodIEquiv {ι : Type u} {G : ι → Type v} {H : ι → Type w}
    [∀ i, Group (G i)] [∀ i, Group (H i)]
    (e : ∀ i, G i ≃* H i) :
    Monoid.CoprodI G ≃* Monoid.CoprodI H where
  toFun := coprodIMap fun i => (e i).toMonoidHom
  invFun := coprodIMap fun i => (e i).symm.toMonoidHom
  left_inv g := by
    have hcomp :
        (coprodIMap fun i => (e i).symm.toMonoidHom).comp
            (coprodIMap fun i => (e i).toMonoidHom) =
          MonoidHom.id (Monoid.CoprodI G) := by
      apply Monoid.CoprodI.ext_hom
      intro i
      ext x
      simp
    exact DFunLike.congr_fun hcomp g
  right_inv h := by
    have hcomp :
        (coprodIMap fun i => (e i).toMonoidHom).comp
            (coprodIMap fun i => (e i).symm.toMonoidHom) =
          MonoidHom.id (Monoid.CoprodI H) := by
      apply Monoid.CoprodI.ext_hom
      intro i
      ext x
      simp
    exact DFunLike.congr_fun hcomp h
  map_mul' g h := map_mul (coprodIMap fun i => (e i).toMonoidHom) g h

/-- A group is canonically equivalent to its quotient by a subgroup proved
equal to bottom. -/
def quotientEquivOfEqBot {G : Type u} [Group G]
    (N : Subgroup G) [N.Normal] (hN : N = ⊥) :
    G ≃* G ⧸ N :=
  ((QuotientGroup.quotientMulEquivOfEq hN).trans
    QuotientGroup.quotientBot).symm

@[simp]
theorem quotientEquivOfEqBot_apply {G : Type u} [Group G]
    (N : Subgroup G) [N.Normal] (hN : N = ⊥) (g : G) :
    quotientEquivOfEqBot N hN g = QuotientGroup.mk' N g := by
  subst N
  rfl

/-- A homotopy equivalence induces an equivalence of fundamental groups at
corresponding basepoints. -/
def fundamentalGroupMulEquivOfHomotopyEquiv
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₕ Y) (x : X) :
    FundamentalGroup X x ≃* FundamentalGroup Y (e.toFun x) :=
  (FundamentalGroupoidFunctor.equivOfHomotopyEquiv e).fullyFaithfulFunctor.mulEquivEnd
    (FundamentalGroupoid.mk x)

@[simp]
theorem fundamentalGroupMulEquivOfHomotopyEquiv_apply
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₕ Y) (x : X) (g : FundamentalGroup X x) :
    fundamentalGroupMulEquivOfHomotopyEquiv e x g =
      FundamentalGroup.map e.toFun x g :=
  rfl

/-- A basepoint-preserving homotopy equivalence induces an equivalence at a
specified target basepoint. -/
def fundamentalGroupMulEquivOfHomotopyEquivOfEq
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₕ Y) (x : X) (y : Y) (hxy : e.toFun x = y) :
    FundamentalGroup X x ≃* FundamentalGroup Y y := by
  subst y
  exact fundamentalGroupMulEquivOfHomotopyEquiv e x

@[simp]
theorem fundamentalGroupMulEquivOfHomotopyEquivOfEq_apply
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₕ Y) (x : X) (y : Y) (hxy : e.toFun x = y)
    (g : FundamentalGroup X x) :
    fundamentalGroupMulEquivOfHomotopyEquivOfEq e x y hxy g =
      FundamentalGroup.mapOfEq e.toFun hxy g := by
  subst y
  change (FundamentalGroup.map e.toFun x) g =
    (FundamentalGroup.mapOfEq e.toFun rfl) g
  symm
  change (CategoryTheory.Iso.refl _).conj
    ((FundamentalGroup.map e.toFun x) g) = _
  rw [CategoryTheory.Iso.refl_conj]

namespace StrongDeformationRetract

variable {A : Type u} {Y : Type v} [TopologicalSpace A] [TopologicalSpace Y]
variable {inclusion : C(A, Y)}

/-- A strong deformation retract induces an equivalence on fundamental
groups whose forward map is induced by the inclusion. -/
def fundamentalGroupMulEquiv
    (h : StrongDeformationRetract inclusion) (a : A) :
    FundamentalGroup A a ≃* FundamentalGroup Y (inclusion a) :=
  fundamentalGroupMulEquivOfHomotopyEquiv h.toHomotopyEquiv.symm a

/-- A strong deformation retract with an identified image basepoint induces
an equivalence at that specified basepoint. -/
def fundamentalGroupMulEquivOfEq
    (h : StrongDeformationRetract inclusion) (a : A) (y : Y)
    (hay : inclusion a = y) :
    FundamentalGroup A a ≃* FundamentalGroup Y y :=
  fundamentalGroupMulEquivOfHomotopyEquivOfEq
    h.toHomotopyEquiv.symm a y hay

@[simp]
theorem fundamentalGroupMulEquivOfEq_apply
    (h : StrongDeformationRetract inclusion) (a : A) (y : Y)
    (hay : inclusion a = y) (g : FundamentalGroup A a) :
    h.fundamentalGroupMulEquivOfEq a y hay g =
      FundamentalGroup.mapOfEq inclusion hay g :=
  fundamentalGroupMulEquivOfHomotopyEquivOfEq_apply
    h.toHomotopyEquiv.symm a y hay g

end StrongDeformationRetract

namespace VanKampen

variable {ι : Type u} {Z : Type v} [TopologicalSpace Z]

/-- If every off-diagonal overlap has trivial fundamental group, all van
Kampen overlap relations are trivial. -/
theorem relationSubgroup_eq_bot_of_overlap_subsingleton
    (U : ι → Set Z) (z₀ : Z) (hz₀ : ∀ i, z₀ ∈ U i)
    (htrivial : ∀ i j, i ≠ j →
      Subsingleton (OverlapGroup U z₀ hz₀ i j)) :
    relationSubgroup U z₀ hz₀ = ⊥ := by
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    rintro r ⟨i, j, ω, rfl⟩
    change overlapRelation U z₀ hz₀ i j ω = 1
    by_cases hij : i = j
    · subst j
      simp [overlapRelation, overlapToLeft, overlapToRight]
    · letI := htrivial i j hij
      rw [Subsingleton.elim ω 1]
      simp [overlapRelation]
  · exact bot_le

/-- Van Kampen reduces to the unquotiented cover free product when every
overlap relation is trivial. -/
noncomputable def freeProductEquivFundamentalGroupOfRelationsTrivial
    (U : ι → Set Z) (z₀ : Z)
    (hUopen : ∀ i, IsOpen (U i))
    (hUcover : Set.univ ⊆ ⋃ i, U i)
    (hone : ∀ i, IsPathConnected (U i))
    (htwo : ∀ i j, IsPathConnected (U i ∩ U j))
    (hthree : ∀ i j k, IsPathConnected (U i ∩ U j ∩ U k))
    (hz₀ : ∀ i, z₀ ∈ U i)
    (hrelations : relationSubgroup U z₀ hz₀ = ⊥) :
    CoverFreeProduct U z₀ hz₀ ≃* FundamentalGroup Z z₀ :=
  (quotientEquivOfEqBot (relationSubgroup U z₀ hz₀) hrelations).trans
    (quotientEquivFundamentalGroup U z₀ hUopen hUcover hone htwo hthree hz₀)

@[simp]
theorem freeProductEquivFundamentalGroupOfRelationsTrivial_apply
    (U : ι → Set Z) (z₀ : Z)
    (hUopen : ∀ i, IsOpen (U i))
    (hUcover : Set.univ ⊆ ⋃ i, U i)
    (hone : ∀ i, IsPathConnected (U i))
    (htwo : ∀ i j, IsPathConnected (U i ∩ U j))
    (hthree : ∀ i j k, IsPathConnected (U i ∩ U j ∩ U k))
    (hz₀ : ∀ i, z₀ ∈ U i)
    (hrelations : relationSubgroup U z₀ hz₀ = ⊥)
    (w : CoverFreeProduct U z₀ hz₀) :
    freeProductEquivFundamentalGroupOfRelationsTrivial U z₀ hUopen
        hUcover hone htwo hthree hz₀ hrelations w =
      coverMap U z₀ hz₀ w := by
  rfl

end VanKampen

namespace PointedWedge

variable {ι : Type u} {X : ι → Type v} [∀ i, TopologicalSpace (X i)]
variable (x₀ : ∀ i, X i)

/-- The empty-family wedge theorem, where both groups are trivial. -/
noncomputable def fundamentalGroupEquivPointedWedgeOfIsEmpty
    [IsEmpty ι] :
    Monoid.CoprodI (fun i => FundamentalGroup (X i) (x₀ i)) ≃*
      FundamentalGroup (Hatcher.PointedWedge X x₀) (basepoint x₀) := by
  letI := coprodIUniqueOfIsEmpty
    (fun i => FundamentalGroup (X i) (x₀ i))
  letI : Unique
      (FundamentalGroup (Hatcher.PointedWedge X x₀) (basepoint x₀)) := {
    default := 1
    uniq g := Subsingleton.elim g 1 }
  exact MulEquiv.ofUnique

/-- Contractibility of the common neck kills every relation in the standard
wedge-cover presentation. -/
theorem relationSubgroup_vanKampenCover_eq_bot
    (hwell : ∀ i, WellPointedAt (x₀ i))
    [ContractibleSpace (vanKampenNeck x₀ hwell)] :
    VanKampen.relationSubgroup (vanKampenCover x₀ hwell)
      (basepoint x₀) (basepoint_mem_vanKampenCover x₀ hwell) = ⊥ := by
  apply VanKampen.relationSubgroup_eq_bot_of_overlap_subsingleton
  intro i j hij
  haveI : ContractibleSpace
      (vanKampenCover x₀ hwell i ∩ vanKampenCover x₀ hwell j :
        Set (Hatcher.PointedWedge X x₀)) := by
    rw [vanKampenCover_inter_eq_vanKampenNeck x₀ hwell hij]
    infer_instance
  infer_instance

/-- Algebraic endgame for the wedge theorem, parameterized only by the
member deformation retracts and neck contractibility supplied by the cover
construction. -/
noncomputable def fundamentalGroupEquivPointedWedgeOfRetracts
    [Nonempty ι] [∀ i, PathConnectedSpace (X i)]
    (hwell : ∀ i, WellPointedAt (x₀ i))
    (hmember : ∀ i,
      StrongDeformationRetract (vanKampenCoverInclusion x₀ hwell i)) :
    Monoid.CoprodI (fun i => FundamentalGroup (X i) (x₀ i)) ≃*
      FundamentalGroup (Hatcher.PointedWedge X x₀) (basepoint x₀) := by
  letI : ContractibleSpace (vanKampenNeck x₀ hwell) :=
    contractibleSpace_vanKampenNeck x₀ hwell
  let U := vanKampenCover x₀ hwell
  let hx₀ := basepoint_mem_vanKampenCover x₀ hwell
  have hone : ∀ i, IsPathConnected (U i) := by
    intro i
    rw [isPathConnected_iff_pathConnectedSpace]
    exact (hmember i).pathConnectedSpace
  have hneck : IsPathConnected (vanKampenNeck x₀ hwell) := by
    rw [isPathConnected_iff_pathConnectedSpace]
    infer_instance
  have htwo : ∀ i j, IsPathConnected (U i ∩ U j) := by
    intro i j
    by_cases hij : i = j
    · subst j
      simpa using hone i
    · rw [vanKampenCover_inter_eq_vanKampenNeck x₀ hwell hij]
      exact hneck
  have hthree : ∀ i j k, IsPathConnected (U i ∩ U j ∩ U k) := by
    intro i j k
    by_cases hij : i = j
    · subst j
      simpa using htwo i k
    · rw [vanKampenCover_inter_eq_vanKampenNeck x₀ hwell hij]
      rw [inter_eq_left.mpr (vanKampenNeck_subset x₀ hwell k)]
      exact hneck
  let memberEquiv : ∀ i,
      FundamentalGroup (X i) (x₀ i) ≃*
        VanKampen.CoverGroup U (basepoint x₀) hx₀ i := fun i =>
    (hmember i).fundamentalGroupMulEquivOfEq (x₀ i)
      (⟨basepoint x₀, hx₀ i⟩ : U i)
      (vanKampenCoverInclusion_basepoint x₀ hwell i)
  exact (coprodIEquiv memberEquiv).trans
    (VanKampen.freeProductEquivFundamentalGroupOfRelationsTrivial
      U (basepoint x₀) (isOpen_vanKampenCover x₀ hwell)
      (univ_subset_iUnion_vanKampenCover x₀ hwell) hone htwo hthree hx₀
      (relationSubgroup_vanKampenCover_eq_bot x₀ hwell))

@[simp]
theorem fundamentalGroupEquivPointedWedgeOfRetracts_of
    [Nonempty ι] [∀ i, PathConnectedSpace (X i)]
    (hwell : ∀ i, WellPointedAt (x₀ i))
    (hmember : ∀ i,
      StrongDeformationRetract (vanKampenCoverInclusion x₀ hwell i))
    (i : ι) (g : FundamentalGroup (X i) (x₀ i)) :
    fundamentalGroupEquivPointedWedgeOfRetracts x₀ hwell hmember
        (Monoid.CoprodI.of g) =
      FundamentalGroup.mapOfEq
        (⟨inclusion x₀ i, continuous_inclusion x₀ i⟩ :
          C(X i, Hatcher.PointedWedge X x₀))
        (inclusion_basepoint x₀ i) g := by
  simp [fundamentalGroupEquivPointedWedgeOfRetracts,
    VanKampen.coverMap, coprodIEquiv]
  induction g using Path.Homotopic.Quotient.ind with
  | mk p =>
      rw [FundamentalGroup.mapOfEq_apply,
        FundamentalGroup.mapOfEq_apply]
      rfl

end PointedWedge

end Hatcher
