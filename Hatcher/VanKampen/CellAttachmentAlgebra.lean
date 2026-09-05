import Hatcher.VanKampen.BinaryVanKampen
import Hatcher.VanKampen.WedgeFundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

noncomputable section

open Set

namespace Hatcher.VanKampen

universe u v w

private abbrev pushoutLeftRelationSubgroup
    {G : Fin 2 → Type u} {H : Type v}
    [∀ i, Group (G i)] [Group H]
    (φ : ∀ i, H →* G i) : Subgroup (G 0) :=
  Subgroup.normalClosure ((φ 0).range : Set (G 0))

private def quotientToPushoutIOfRightSubsingleton
    {G : Fin 2 → Type u} {H : Type v}
    [∀ i, Group (G i)] [Group H] [Subsingleton (G 1)]
    (φ : ∀ i, H →* G i) :
    G 0 ⧸ pushoutLeftRelationSubgroup φ →* Monoid.PushoutI φ :=
  QuotientGroup.lift (pushoutLeftRelationSubgroup φ)
    (Monoid.PushoutI.of 0)
    (Subgroup.normalClosure_le_normal fun g hg ↦ by
      obtain ⟨h, rfl⟩ := hg
      apply MonoidHom.mem_ker.mpr
      rw [Monoid.PushoutI.of_apply_eq_base φ 0 h]
      rw [← Monoid.PushoutI.of_apply_eq_base φ 1 h]
      rw [show φ 1 h = 1 from Subsingleton.elim _ _]
      exact map_one _)

private def pushoutIToQuotientOfRightSubsingleton
    {G : Fin 2 → Type u} {H : Type v}
    [∀ i, Group (G i)] [Group H] [Subsingleton (G 1)]
    (φ : ∀ i, H →* G i) :
    Monoid.PushoutI φ →* G 0 ⧸ pushoutLeftRelationSubgroup φ := by
  let f : ∀ i, G i →* G 0 ⧸ pushoutLeftRelationSubgroup φ :=
    Fin.cases (QuotientGroup.mk' (pushoutLeftRelationSubgroup φ)) fun _ ↦ 1
  let k : H →* G 0 ⧸ pushoutLeftRelationSubgroup φ := 1
  have hf : ∀ i, (f i).comp (φ i) = k := by
    intro i
    fin_cases i
    · apply MonoidHom.ext
      intro h
      exact (QuotientGroup.eq_one_iff _).mpr
        (Subgroup.subset_normalClosure ⟨h, rfl⟩)
    · rfl
  exact Monoid.PushoutI.lift f k hf

private theorem quotientToPushoutI_comp_pushoutIToQuotient
    {G : Fin 2 → Type u} {H : Type v}
    [∀ i, Group (G i)] [Group H] [Subsingleton (G 1)]
    (φ : ∀ i, H →* G i) :
    (quotientToPushoutIOfRightSubsingleton φ).comp
        (pushoutIToQuotientOfRightSubsingleton φ) =
      MonoidHom.id (Monoid.PushoutI φ) := by
  apply Monoid.PushoutI.hom_ext_nonempty
  intro i
  apply MonoidHom.ext
  intro g
  fin_cases i
  · rfl
  · change G 1 at g
    rw [show g = 1 from Subsingleton.elim _ _]
    simp

private theorem pushoutIToQuotient_comp_quotientToPushoutI
    {G : Fin 2 → Type u} {H : Type v}
    [∀ i, Group (G i)] [Group H] [Subsingleton (G 1)]
    (φ : ∀ i, H →* G i) :
    (pushoutIToQuotientOfRightSubsingleton φ).comp
        (quotientToPushoutIOfRightSubsingleton φ) =
      MonoidHom.id (G 0 ⧸ pushoutLeftRelationSubgroup φ) := by
  apply QuotientGroup.monoidHom_ext
  apply MonoidHom.ext
  intro g
  rfl

/-- A binary group pushout with subsingleton right factor is the quotient of
the left factor by the normal closure of the amalgamating map's image. -/
def quotientEquivPushoutIOfRightSubsingleton
    {G : Fin 2 → Type u} {H : Type v}
    [∀ i, Group (G i)] [Group H] [Subsingleton (G 1)]
    (φ : ∀ i, H →* G i) :
    G 0 ⧸ Subgroup.normalClosure ((φ 0).range : Set (G 0)) ≃*
      Monoid.PushoutI φ :=
  MonoidHom.toMulEquiv
    (quotientToPushoutIOfRightSubsingleton φ)
    (pushoutIToQuotientOfRightSubsingleton φ)
    (pushoutIToQuotient_comp_quotientToPushoutI φ)
    (quotientToPushoutI_comp_pushoutIToQuotient φ)

@[simp]
theorem quotientEquivPushoutIOfRightSubsingleton_mk
    {G : Fin 2 → Type u} {H : Type v}
    [∀ i, Group (G i)] [Group H] [Subsingleton (G 1)]
    (φ : ∀ i, H →* G i) (g : G 0) :
    quotientEquivPushoutIOfRightSubsingleton φ
        (QuotientGroup.mk'
          (Subgroup.normalClosure ((φ 0).range : Set (G 0))) g) =
      Monoid.PushoutI.of 0 g := by
  rfl

/-- If the second member of a binary cover has trivial fundamental group, the
ambient fundamental group is the quotient of the first member's fundamental
group by the normal closure of the overlap image. -/
noncomputable def binaryCoverLeftQuotientEquivFundamentalGroupOfSubsingleton
    {X : Type w} [TopologicalSpace X]
    (U : Fin 2 → Set X) (x₀ : X)
    (hUopen : ∀ i, IsOpen (U i))
    (hUcover : Set.univ ⊆ ⋃ i, U i)
    (hone : ∀ i, IsPathConnected (U i))
    (hinter : IsPathConnected (U 0 ∩ U 1))
    (hx₀ : ∀ i, x₀ ∈ U i)
    [Subsingleton (CoverGroup U x₀ hx₀ 1)] :
    CoverGroup U x₀ hx₀ 0 ⧸
        Subgroup.normalClosure
          ((overlapToLeft U x₀ hx₀ 0 1).range : Set _) ≃*
      FundamentalGroup X x₀ :=
  (quotientEquivPushoutIOfRightSubsingleton
    (binaryOverlapMaps U x₀ hx₀)).trans
      (pushoutEquivFundamentalGroup
        U x₀ hUopen hUcover hone hinter hx₀)

@[simp]
theorem binaryCoverLeftQuotientEquivFundamentalGroupOfSubsingleton_mk
    {X : Type w} [TopologicalSpace X]
    (U : Fin 2 → Set X) (x₀ : X)
    (hUopen : ∀ i, IsOpen (U i))
    (hUcover : Set.univ ⊆ ⋃ i, U i)
    (hone : ∀ i, IsPathConnected (U i))
    (hinter : IsPathConnected (U 0 ∩ U 1))
    (hx₀ : ∀ i, x₀ ∈ U i)
    [Subsingleton (CoverGroup U x₀ hx₀ 1)]
    (g : CoverGroup U x₀ hx₀ 0) :
    binaryCoverLeftQuotientEquivFundamentalGroupOfSubsingleton
        U x₀ hUopen hUcover hone hinter hx₀
        (QuotientGroup.mk' _ g) =
      binaryCoverInclusion U x₀ hx₀ 0 g := by
  change pushoutEquivFundamentalGroup
      U x₀ hUopen hUcover hone hinter hx₀
      (quotientEquivPushoutIOfRightSubsingleton
        (binaryOverlapMaps U x₀ hx₀) (QuotientGroup.mk' _ g)) = _
  rw [quotientEquivPushoutIOfRightSubsingleton_mk]
  exact pushoutEquivFundamentalGroup_of
    U x₀ hUopen hUcover hone hinter hx₀ 0 g

theorem binaryCoverLeftQuotientEquivFundamentalGroupOfSubsingleton_comp_mk
    {X : Type w} [TopologicalSpace X]
    (U : Fin 2 → Set X) (x₀ : X)
    (hUopen : ∀ i, IsOpen (U i))
    (hUcover : Set.univ ⊆ ⋃ i, U i)
    (hone : ∀ i, IsPathConnected (U i))
    (hinter : IsPathConnected (U 0 ∩ U 1))
    (hx₀ : ∀ i, x₀ ∈ U i)
    [Subsingleton (CoverGroup U x₀ hx₀ 1)] :
    (binaryCoverLeftQuotientEquivFundamentalGroupOfSubsingleton
      U x₀ hUopen hUcover hone hinter hx₀).toMonoidHom.comp
        (QuotientGroup.mk' _) =
      binaryCoverInclusion U x₀ hx₀ 0 := by
  apply MonoidHom.ext
  intro g
  exact binaryCoverLeftQuotientEquivFundamentalGroupOfSubsingleton_mk
    U x₀ hUopen hUcover hone hinter hx₀ g

/-- A binary group pushout with trivial amalgamating group and trivial second
factor is equivalent to its first factor. -/
def pushoutIEquivLeftOfSubsingleton
    {G : Fin 2 → Type u} {H : Type v}
    [∀ i, Group (G i)] [Group H]
    [Subsingleton H] [Subsingleton (G 1)]
    (φ : ∀ i, H →* G i) :
    Monoid.PushoutI φ ≃* G 0 := by
  let f : ∀ i, G i →* G 0 := Fin.cases (MonoidHom.id (G 0)) fun _ => 1
  let k : H →* G 0 := 1
  have hf : ∀ i, (f i).comp (φ i) = k := by
    intro i
    apply MonoidHom.ext
    intro h
    rw [Subsingleton.elim h 1]
    simp [f, k]
  let toLeft : Monoid.PushoutI φ →* G 0 :=
    Monoid.PushoutI.lift f k hf
  exact
    { toFun := toLeft
      invFun := Monoid.PushoutI.of 0
      left_inv := by
        intro p
        induction p using Monoid.PushoutI.induction_on with
        | of i g =>
            induction i using Fin.cases with
            | zero =>
                rw [Monoid.PushoutI.lift_of]
                rfl
            | succ i =>
                have hi : i = 0 := Fin.eq_zero i
                subst i
                rw [show g = 1 from
                  @Subsingleton.elim (G 1) _ g 1]
                have hto : (Monoid.PushoutI.lift f k hf)
                    (Monoid.PushoutI.of 1 (1 : G 1)) = 1 := by
                  rw [Monoid.PushoutI.lift_of]
                  rfl
                change (Monoid.PushoutI.of 0)
                    ((Monoid.PushoutI.lift f k hf)
                      (Monoid.PushoutI.of 1 (1 : G 1))) =
                  Monoid.PushoutI.of 1 (1 : G 1)
                rw [hto]
                simp
        | base h =>
            rw [Subsingleton.elim h 1]
            simp
        | mul a b ha hb => simp [map_mul, ha, hb]
      right_inv := by
        intro g
        simp [toLeft, f]
      map_mul' := map_mul toLeft }

/-- Binary van Kampen reduces to the first cover member when the intersection
and second cover member have trivial fundamental groups. -/
noncomputable def binaryCoverLeftEquivFundamentalGroupOfSubsingleton
    {X : Type w} [TopologicalSpace X]
    (U : Fin 2 → Set X) (x₀ : X)
    (hUopen : ∀ i, IsOpen (U i))
    (hUcover : Set.univ ⊆ ⋃ i, U i)
    (hone : ∀ i, IsPathConnected (U i))
    (hinter : IsPathConnected (U 0 ∩ U 1))
    (hx₀ : ∀ i, x₀ ∈ U i)
    [Subsingleton (OverlapGroup U x₀ hx₀ 0 1)]
    [Subsingleton (CoverGroup U x₀ hx₀ 1)] :
    CoverGroup U x₀ hx₀ 0 ≃* FundamentalGroup X x₀ :=
  (pushoutIEquivLeftOfSubsingleton
    (binaryOverlapMaps U x₀ hx₀)).symm.trans
      (pushoutEquivFundamentalGroup U x₀ hUopen hUcover hone hinter hx₀)

@[simp]
theorem binaryCoverLeftEquivFundamentalGroupOfSubsingleton_apply
    {X : Type w} [TopologicalSpace X]
    (U : Fin 2 → Set X) (x₀ : X)
    (hUopen : ∀ i, IsOpen (U i))
    (hUcover : Set.univ ⊆ ⋃ i, U i)
    (hone : ∀ i, IsPathConnected (U i))
    (hinter : IsPathConnected (U 0 ∩ U 1))
    (hx₀ : ∀ i, x₀ ∈ U i)
    [Subsingleton (OverlapGroup U x₀ hx₀ 0 1)]
    [Subsingleton (CoverGroup U x₀ hx₀ 1)]
    (g : CoverGroup U x₀ hx₀ 0) :
    binaryCoverLeftEquivFundamentalGroupOfSubsingleton
        U x₀ hUopen hUcover hone hinter hx₀ g =
      binaryCoverInclusion U x₀ hx₀ 0 g := by
  simp [binaryCoverLeftEquivFundamentalGroupOfSubsingleton,
    pushoutIEquivLeftOfSubsingleton, pushoutEquivFundamentalGroup_of]

/-- If the second member of a binary cover is contractible and the overlap is
simply connected, inclusion of the first member induces an equivalence on
fundamental groups. -/
noncomputable def binaryCoverLeftEquivFundamentalGroupOfSimplyConnected
    {X : Type w} [TopologicalSpace X]
    (U : Fin 2 → Set X) (x₀ : X)
    (hUopen : ∀ i, IsOpen (U i))
    (hUcover : Set.univ ⊆ ⋃ i, U i)
    (hone : ∀ i, IsPathConnected (U i))
    (hinter : IsPathConnected (U 0 ∩ U 1))
    (hx₀ : ∀ i, x₀ ∈ U i)
    [ContractibleSpace (U 1)]
    [SimplyConnectedSpace (U 0 ∩ U 1 : Set X)] :
    CoverGroup U x₀ hx₀ 0 ≃* FundamentalGroup X x₀ := by
  exact binaryCoverLeftEquivFundamentalGroupOfSubsingleton
    U x₀ hUopen hUcover hone hinter hx₀

/-- Exact geometric interface needed for the higher-cell argument after an
auxiliary binary cover has been constructed. -/
noncomputable def fundamentalGroupEquivOfBinaryCoverRetraction
    {A : Type u} {Y : Type w}
    [TopologicalSpace A] [TopologicalSpace Y]
    (inclusion : C(A, Y)) (a₀ : A)
    (U : Fin 2 → Set Y) (y₀ : Y)
    (hUopen : ∀ i, IsOpen (U i))
    (hUcover : Set.univ ⊆ ⋃ i, U i)
    (hone : ∀ i, IsPathConnected (U i))
    (hinter : IsPathConnected (U 0 ∩ U 1))
    (hy₀ : ∀ i, y₀ ∈ U i)
    (hinclusion : ∀ a, inclusion a ∈ U 0)
    (hbase : inclusion a₀ = y₀)
    (hretract : StrongDeformationRetract
      (⟨fun a => ⟨inclusion a, hinclusion a⟩,
        inclusion.continuous.subtype_mk _⟩ : C(A, U 0)))
    [ContractibleSpace (U 1)]
    [SimplyConnectedSpace (U 0 ∩ U 1 : Set Y)] :
    FundamentalGroup A a₀ ≃* FundamentalGroup Y y₀ :=
  (hretract.fundamentalGroupMulEquivOfEq a₀
    (⟨y₀, hy₀ 0⟩ : U 0) (by
      apply Subtype.ext
      exact hbase)).trans
    (binaryCoverLeftEquivFundamentalGroupOfSimplyConnected
      U y₀ hUopen hUcover hone hinter hy₀)

end Hatcher.VanKampen
