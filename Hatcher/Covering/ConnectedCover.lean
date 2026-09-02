import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.Covering.Basic

namespace Hatcher

universe u v w z

/-- A pointed path-connected covering of `(X, x₀)` whose total space lives in
the explicit universe `u`. -/
structure BasedConnectedCover (X : Type v) [TopologicalSpace X] (x₀ : X) where
  E : Type u
  topology : TopologicalSpace E
  proj : E → X
  isCoveringMap : IsCoveringMap proj
  basepoint : E
  proj_basepoint : proj basepoint = x₀
  pathConnectedSpace : PathConnectedSpace E

attribute [instance] BasedConnectedCover.topology BasedConnectedCover.pathConnectedSpace

/-- A path-connected covering of `X` whose total space lives in the explicit
universe `u`. -/
structure ConnectedCover (X : Type v) [TopologicalSpace X] where
  E : Type u
  topology : TopologicalSpace E
  proj : E → X
  isCoveringMap : IsCoveringMap proj
  pathConnectedSpace : PathConnectedSpace E

attribute [instance] ConnectedCover.topology ConnectedCover.pathConnectedSpace

namespace BasedConnectedCover

variable {X : Type v} [TopologicalSpace X] {x₀ : X}

/-- Forget the chosen point of a pointed connected cover. -/
def toConnectedCover (C : BasedConnectedCover.{u, v} X x₀) : ConnectedCover.{u, v} X where
  E := C.E
  topology := C.topology
  proj := C.proj
  isCoveringMap := C.isCoveringMap
  pathConnectedSpace := C.pathConnectedSpace

/-- A basepoint-preserving isomorphism of pointed covers. -/
@[ext]
structure Iso (C : BasedConnectedCover.{u, v} X x₀)
    (D : BasedConnectedCover.{w, v} X x₀) where
  toHomeomorph : C.E ≃ₜ D.E
  proj_comp : D.proj ∘ toHomeomorph = C.proj
  map_basepoint : toHomeomorph C.basepoint = D.basepoint

namespace Iso

variable {C : BasedConnectedCover.{u, v} X x₀}
  {D : BasedConnectedCover.{w, v} X x₀}
  {F : BasedConnectedCover.{z, v} X x₀}

instance : CoeFun (C.Iso D) fun _ ↦ C.E → D.E := ⟨fun e ↦ e.toHomeomorph⟩

@[simp]
theorem coe_toHomeomorph (e : C.Iso D) : ⇑e.toHomeomorph = e := rfl

@[simp]
theorem proj_apply (e : C.Iso D) (x : C.E) : D.proj (e x) = C.proj x :=
  congrFun e.proj_comp x

/-- The identity pointed-cover isomorphism. -/
def refl (C : BasedConnectedCover.{u, v} X x₀) : C.Iso C where
  toHomeomorph := Homeomorph.refl C.E
  proj_comp := rfl
  map_basepoint := rfl

/-- The inverse pointed-cover isomorphism. -/
def symm (e : C.Iso D) : D.Iso C where
  toHomeomorph := e.toHomeomorph.symm
  proj_comp := by
    ext x
    simpa using (e.proj_apply (e.toHomeomorph.symm x)).symm
  map_basepoint := by
    apply e.toHomeomorph.injective
    simpa using e.map_basepoint.symm

/-- Composition of pointed-cover isomorphisms. -/
def trans (e : C.Iso D) (f : D.Iso F) : C.Iso F where
  toHomeomorph := e.toHomeomorph.trans f.toHomeomorph
  proj_comp := by
    ext x
    exact (f.proj_apply (e x)).trans (e.proj_apply x)
  map_basepoint := by
    simp only [Homeomorph.trans_apply, e.map_basepoint, f.map_basepoint]

end Iso

/-- Two pointed connected covers are isomorphic over the base. -/
def Isomorphic (C : BasedConnectedCover.{u, v} X x₀)
    (D : BasedConnectedCover.{w, v} X x₀) : Prop :=
  Nonempty (C.Iso D)

@[instance_reducible]
def isomorphicSetoid : Setoid (BasedConnectedCover.{u, v} X x₀) where
  r := Isomorphic
  iseqv := {
    refl := fun C ↦ ⟨Iso.refl C⟩
    symm := fun ⟨e⟩ ↦ ⟨e.symm⟩
    trans := fun ⟨e⟩ ⟨f⟩ ↦ ⟨e.trans f⟩ }

end BasedConnectedCover

namespace ConnectedCover

variable {X : Type v} [TopologicalSpace X]

/-- An isomorphism of connected covers over the same base. -/
@[ext]
structure Iso (C : ConnectedCover.{u, v} X) (D : ConnectedCover.{w, v} X) where
  toHomeomorph : C.E ≃ₜ D.E
  proj_comp : D.proj ∘ toHomeomorph = C.proj

namespace Iso

variable {C : ConnectedCover.{u, v} X} {D : ConnectedCover.{w, v} X}
  {F : ConnectedCover.{z, v} X}

instance : CoeFun (C.Iso D) fun _ ↦ C.E → D.E := ⟨fun e ↦ e.toHomeomorph⟩

@[simp]
theorem coe_toHomeomorph (e : C.Iso D) : ⇑e.toHomeomorph = e := rfl

@[simp]
theorem proj_apply (e : C.Iso D) (x : C.E) : D.proj (e x) = C.proj x :=
  congrFun e.proj_comp x

/-- The identity connected-cover isomorphism. -/
def refl (C : ConnectedCover.{u, v} X) : C.Iso C where
  toHomeomorph := Homeomorph.refl C.E
  proj_comp := rfl

/-- The inverse connected-cover isomorphism. -/
def symm (e : C.Iso D) : D.Iso C where
  toHomeomorph := e.toHomeomorph.symm
  proj_comp := by
    ext x
    simpa using (e.proj_apply (e.toHomeomorph.symm x)).symm

/-- Composition of connected-cover isomorphisms. -/
def trans (e : C.Iso D) (f : D.Iso F) : C.Iso F where
  toHomeomorph := e.toHomeomorph.trans f.toHomeomorph
  proj_comp := by
    ext x
    exact (f.proj_apply (e x)).trans (e.proj_apply x)

end Iso

/-- Two connected covers are isomorphic over the base. -/
def Isomorphic (C : ConnectedCover.{u, v} X) (D : ConnectedCover.{w, v} X) : Prop :=
  Nonempty (C.Iso D)

@[instance_reducible]
def isomorphicSetoid : Setoid (ConnectedCover.{u, v} X) where
  r := Isomorphic
  iseqv := {
    refl := fun C ↦ ⟨Iso.refl C⟩
    symm := fun ⟨e⟩ ↦ ⟨e.symm⟩
    trans := fun ⟨e⟩ ⟨f⟩ ↦ ⟨e.trans f⟩ }

end ConnectedCover

end Hatcher
