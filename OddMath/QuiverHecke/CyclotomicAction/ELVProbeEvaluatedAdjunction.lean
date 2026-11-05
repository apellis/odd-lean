/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeEvaluatedDotUnit
import OddMath.QuiverHecke.CyclotomicAction.ELVContentAppendDot
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightSuperAdjunction

/-! # The prescribed right adjunction on evaluated old probes

For SwappedActionAssembly F1–F2 and BE (1.10), restrict the actual balanced
unit and counit to the scalar-evaluated full categories. Their evenness
and both triangles are inherited. The whole dot unit retains the existing
native old-content induction dot, with no change of sign or adjunction.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ) (ν : List I) (i : I)
local notation "J" => oldContentAppend D Sc (probeCutoff D m) ν i
local notation "E" => probeEvaluatedInduction D Sc m ν i
local notation "F" => probeEvaluatedRestriction D Sc m ν i

/-- The same chosen balanced unit, on the full evaluated subcategory. -/
def probeEvaluatedUnit : 𝟭 (ProbeEvaluatedModules D Sc m ν) ⟶ E ⋙ F where
  app N := ⟨(adjunction J).unit.app N.obj⟩
  naturality := by
    intro A B f
    exact InducedCategory.hom_ext ((adjunction J).unit.naturality f.hom)

/-- The same chosen multiplication counit, with every module map retained. -/
def probeEvaluatedCounit : F ⋙ E ⟶ 𝟭 (ProbeEvaluatedModules D Sc m (i :: ν)) where
  app N := ⟨(adjunction J).counit.app N.obj⟩
  naturality := by
    intro A B f
    exact InducedCategory.hom_ext ((adjunction J).counit.naturality f.hom)

/-- Restrict the actual right adjunction; both triangle identities are inherited. -/
def probeEvaluatedAdjunction : E ⊣ F where
  unit := probeEvaluatedUnit D Sc m ν i
  counit := probeEvaluatedCounit D Sc m ν i
  left_triangle_components N := InducedCategory.hom_ext ((adjunction J).left_triangle_components N.obj)
  right_triangle_components N := InducedCategory.hom_ext ((adjunction J).right_triangle_components N.obj)

theorem probeEvaluatedAdjunction_unit_mem (N : ProbeEvaluatedModules D Sc m ν) :
    (probeEvaluatedAdjunction D Sc m ν i).unit.app N ∈ parity (R := k) _ _ 0 :=
  adjunctionUnit_mem J N.obj

theorem probeEvaluatedAdjunction_counit_mem (N : ProbeEvaluatedModules D Sc m (i :: ν)) :
    (probeEvaluatedAdjunction D Sc m ν i).counit.app N ∈ parity (R := k) _ _ 0 :=
  adjunctionCounit_mem J N.obj

/-- The actual evaluated module category in the target of the swapped factors. -/
abbrev probeEvaluatedTarget (ν : List I) : PiSCat.{u,u,u+1} k :=
  letI := probeEvaluatedPiSupercategory D Sc m ν
  PiSCat.of k (ProbeEvaluatedModules D Sc m ν)

abbrev probeEvaluatedE : probeEvaluatedTarget D Sc m ν ⟶ probeEvaluatedTarget D Sc m (i :: ν) := ⟨E⟩
abbrev probeEvaluatedF : probeEvaluatedTarget D Sc m (i :: ν) ⟶ probeEvaluatedTarget D Sc m ν := ⟨F⟩

/-- The right adjunction uses precisely the restricted native unit and counit. -/
def probeEvaluatedRightAdjunction :
    SKM.SuperAdjunction (k := k) (probeEvaluatedE D Sc m ν i) (probeEvaluatedF D Sc m ν i) :=
  ordinaryEvenSuperAdjunction (probeEvaluatedE D Sc m ν i) (probeEvaluatedF D Sc m ν i)
    (probeEvaluatedAdjunction D Sc m ν i) (probeEvaluatedAdjunction_unit_mem D Sc m ν i)
    (probeEvaluatedAdjunction_counit_mem D Sc m ν i)

end OddMath.QuiverHecke
