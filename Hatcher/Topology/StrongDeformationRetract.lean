/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in `LICENSES/Apache-2.0.txt`.
Authors: Jack McCarthy
-/

import Mathlib.Topology.Homotopy.Contractible

/-!
# Strong deformation retracts

This file packages a strong deformation retract by its inclusion into the
ambient space and records its elementary homotopy-theoretic consequences.
-/

noncomputable section

open Set Topology
open scoped unitInterval

namespace Hatcher

universe u v

/-- A strong deformation retract presented by its inclusion into the ambient
space. -/
structure StrongDeformationRetract
    {A : Type u} {Y : Type v} [TopologicalSpace A] [TopologicalSpace Y]
    (inclusion : C(A, Y)) where
  retract : C(Y, A)
  retract_inclusion : retract.comp inclusion = ContinuousMap.id A
  deformation :
    (ContinuousMap.id Y).HomotopyRel (inclusion.comp retract) (Set.range inclusion)

namespace StrongDeformationRetract

variable {A : Type u} {Y : Type v} [TopologicalSpace A] [TopologicalSpace Y]
  {inclusion : C(A, Y)}

/-- A strong deformation retract supplies the corresponding homotopy
equivalence. -/
def toHomotopyEquiv (h : StrongDeformationRetract inclusion) :
    ContinuousMap.HomotopyEquiv Y A where
  toFun := h.retract
  invFun := inclusion
  left_inv := ⟨h.deformation.toHomotopy.symm⟩
  right_inv := by
    rw [h.retract_inclusion]

/-- A strong deformation retract onto a contractible space is contractible. -/
theorem contractibleSpace [ContractibleSpace A]
    (h : StrongDeformationRetract inclusion) : ContractibleSpace Y :=
  h.toHomotopyEquiv.contractibleSpace

/-- A strong deformation retract onto a path-connected space is
path-connected. -/
theorem pathConnectedSpace [PathConnectedSpace A]
    (h : StrongDeformationRetract inclusion) : PathConnectedSpace Y where
  nonempty := by
    obtain ⟨a⟩ := (PathConnectedSpace.nonempty : Nonempty A)
    exact ⟨inclusion a⟩
  joined y z := by
    have hy : Joined y (inclusion (h.retract y)) :=
      ⟨h.deformation.toHomotopy.evalAt y⟩
    have hz : Joined z (inclusion (h.retract z)) :=
      ⟨h.deformation.toHomotopy.evalAt z⟩
    have ha : Joined (h.retract y) (h.retract z) :=
      PathConnectedSpace.joined _ _
    have hi : Joined (inclusion (h.retract y)) (inclusion (h.retract z)) :=
      ⟨ha.somePath.map inclusion.continuous⟩
    exact hy.trans (hi.trans hz.symm)

/-- A contraction fixing its center is a strong deformation retract onto that
point, represented by `Unit`. -/
def ofPointedContraction (y₀ : Y)
    (H : (ContinuousMap.id Y).HomotopyRel
      (ContinuousMap.const Y y₀) {y₀}) :
    StrongDeformationRetract (ContinuousMap.const Unit y₀) where
  retract := ContinuousMap.const Y ()
  retract_inclusion := by
    ext
  deformation := by
    change (ContinuousMap.id Y).HomotopyRel (ContinuousMap.const Y y₀)
      (Set.range fun _ : Unit ↦ y₀)
    rw [Set.range_const]
    exact H

/-- A pointed contraction supplies contractibility. -/
theorem contractibleSpace_of_pointedContraction (y₀ : Y)
    (H : (ContinuousMap.id Y).HomotopyRel
      (ContinuousMap.const Y y₀) {y₀}) :
    ContractibleSpace Y :=
  (ofPointedContraction y₀ H).contractibleSpace

end StrongDeformationRetract

end Hatcher
