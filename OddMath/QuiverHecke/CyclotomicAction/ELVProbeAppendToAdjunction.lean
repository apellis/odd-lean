/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeCanonicalContent
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeEvaluatedAdjunction
import OddMath.QuiverHecke.CyclotomicAction.ELVContentAppendDot
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightSuperAdjunction

/-! # The prescribed adjunction for stored OLD probe contents

SwappedActionAssembly F1–F2 and BE (1.10): the full evaluated append
and restriction functors retain their specified target permutation. The
right unit, counit, evenness and triangles are the actual balanced ones.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ) (ν : List I) (i : I) (μ : List I) (h : (i :: ν).Perm μ)
local notation "J" => oldContentAppendTo D Sc (probeCutoff D m) ν i μ h
local notation "E" => probeEvaluatedAppendTo D Sc m ν i μ h
local notation "F" => probeEvaluatedRestrictTo D Sc m ν i μ h

/-- The same chosen balanced unit, on the full evaluated subcategory. -/
def probeAppendToUnit : 𝟭 (ProbeEvaluatedModules D Sc m ν) ⟶ E ⋙ F where
  app N := ⟨(adjunction J).unit.app N.obj⟩
  naturality := by
    intro A B f
    exact InducedCategory.hom_ext ((adjunction J).unit.naturality f.hom)

/-- The same chosen multiplication counit, with every module map retained. -/
def probeAppendToCounit : F ⋙ E ⟶ 𝟭 (ProbeEvaluatedModules D Sc m μ) where
  app N := ⟨(adjunction J).counit.app N.obj⟩
  naturality := by
    intro A B f
    exact InducedCategory.hom_ext ((adjunction J).counit.naturality f.hom)

/-- Restrict the actual right adjunction; both triangle identities are inherited. -/
def probeAppendToAdjunction : E ⊣ F where
  unit := probeAppendToUnit D Sc m ν i μ h
  counit := probeAppendToCounit D Sc m ν i μ h
  left_triangle_components N := InducedCategory.hom_ext ((adjunction J).left_triangle_components N.obj)
  right_triangle_components N := InducedCategory.hom_ext ((adjunction J).right_triangle_components N.obj)

theorem probeAppendToAdjunction_unit_mem (N : ProbeEvaluatedModules D Sc m ν) :
    (probeAppendToAdjunction D Sc m ν i μ h).unit.app N ∈ parity (R := k) _ _ 0 :=
  adjunctionUnit_mem J N.obj

theorem probeAppendToAdjunction_counit_mem (N : ProbeEvaluatedModules D Sc m μ) :
    (probeAppendToAdjunction D Sc m ν i μ h).counit.app N ∈ parity (R := k) _ _ 0 :=
  adjunctionCounit_mem J N.obj

abbrev probeAppendToE : probeEvaluatedTarget D Sc m ν ⟶ probeEvaluatedTarget D Sc m μ := ⟨E⟩
abbrev probeAppendToF : probeEvaluatedTarget D Sc m μ ⟶ probeEvaluatedTarget D Sc m ν := ⟨F⟩

/-- The right adjunction uses precisely the restricted native unit and counit. -/
def probeAppendToRightAdjunction :
    SKM.SuperAdjunction (k := k) (probeAppendToE D Sc m ν i μ h) (probeAppendToF D Sc m ν i μ h) :=
  ordinaryEvenSuperAdjunction (probeAppendToE D Sc m ν i μ h) (probeAppendToF D Sc m ν i μ h)
    (probeAppendToAdjunction D Sc m ν i μ h) (probeAppendToAdjunction_unit_mem D Sc m ν i μ h)
    (probeAppendToAdjunction_counit_mem D Sc m ν i μ h)

end OddMath.QuiverHecke
