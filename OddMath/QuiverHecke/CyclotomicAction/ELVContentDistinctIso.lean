/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVContentDistinctMate
import OddMath.QuiverHecke.CyclotomicAction.ELVRectangularMateIso

/-! # The distinct mate isomorphism on untruncated old-content modules

Brundan–Ellis (1.12): apply the proved chosen-chart comparison and old
PBW inverse to the prescribed content cup-crossing-cap. The resulting
module inverse and input-natural inverse have crossing parity p(i)p(j).
No additional pointwise invertibility hypothesis is imposed here.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (ν : List I) (i j : I)
local notation "J" => oldContentAppend D Sc cutoff ν j
local notation "K" => oldContentAppend D Sc cutoff ν i
local notation "L" => oldContentAppend D Sc cutoff (j :: ν) i
local notation "M" => oldContentDistinctUpperAppend D Sc cutoff ν i j

/-- The prescribed positive content mate is an isomorphism of old-content modules. -/
def oldContentDistinctMateModuleIso (hij : i ≠ j)
    (N : Superfunctor k (OldContentCategory D Sc cutoff (j :: ν)) (SVec k)) :
    BalancedInduction.induced K ((BalancedInduction.restriction J).obj N) ≅
      (BalancedInduction.restriction M).obj (BalancedInduction.induced L N) :=
  BalancedInduction.rectangularMateModuleIso J K L M
    (oldContentDistinctCross_supernatural D Sc cutoff ν i j) N
    (fun t => oldContentDistinctMateLinear_bijective D Sc cutoff ν i j hij N t)

@[simp] theorem oldContentDistinctMateModuleIso_hom (hij : i ≠ j)
    (N : Superfunctor k (OldContentCategory D Sc cutoff (j :: ν)) (SVec k)) :
    (oldContentDistinctMateModuleIso D Sc cutoff ν i j hij N).hom =
      oldContentDistinctMateComponent D Sc cutoff ν i j N :=
  BalancedInduction.rectangularMateModuleIso_hom J K L M
    (oldContentDistinctCross_supernatural D Sc cutoff ν i j) N _

/-- The inverse has the same full crossing parity on all coefficient arrows. -/
theorem oldContentDistinctMateModuleIso_inv_mem (hij : i ≠ j)
    (N : Superfunctor k (OldContentCategory D Sc cutoff (j :: ν)) (SVec k)) :
    (oldContentDistinctMateModuleIso D Sc cutoff ν i j hij N).inv ∈
      parity (R := k) _ _ (D.parity i * D.parity j) :=
  BalancedInduction.rectangularMateModuleIso_inv_mem J K L M
    (oldContentDistinctCross_supernatural D Sc cutoff ν i j) N _

/-- The chosen content mate is invertible naturally in arbitrary input-module maps. -/
def oldContentDistinctMateFunctorIso (hij : i ≠ j) :
    BalancedInduction.rectangularMateSourceFunctor (k := k) J K ≅
      BalancedInduction.rectangularMateTargetFunctor (k := k) L M :=
  BalancedInduction.rectangularMateFunctorIso J K L M
    (oldContentDistinctCross_supernatural D Sc cutoff ν i j)
    (fun N t => oldContentDistinctMateLinear_bijective D Sc cutoff ν i j hij N t)

@[simp] theorem oldContentDistinctMateFunctorIso_hom (hij : i ≠ j) :
    (oldContentDistinctMateFunctorIso D Sc cutoff ν i j hij).hom =
      BalancedInduction.rectangularMateHom J K L M
        (oldContentDistinctCross_supernatural D Sc cutoff ν i j) :=
  BalancedInduction.rectangularMateFunctorIso_hom J K L M
    (oldContentDistinctCross_supernatural D Sc cutoff ν i j) _

/-- Every total input component is the independently prescribed content mate. -/
@[simp] theorem oldContentDistinctMateFunctorIso_hom_total (hij : i ≠ j)
    (N : Superfunctor k (OldContentCategory D Sc cutoff (j :: ν)) (SVec k)) :
    (oldContentDistinctMateFunctorIso D Sc cutoff ν i j hij).hom.total N =
      oldContentDistinctMateComponent D Sc cutoff ν i j N := by
  rw [oldContentDistinctMateFunctorIso_hom]
  exact BalancedInduction.rectangularMateHom_total J K L M
    (oldContentDistinctCross_supernatural D Sc cutoff ν i j) N

/-- The input-natural inverse retains the crossing parity, including distinct odd colours. -/
theorem oldContentDistinctMateFunctorIso_inv_mem (hij : i ≠ j) :
    (oldContentDistinctMateFunctorIso D Sc cutoff ν i j hij).inv ∈
      parity (R := k) _ _ (D.parity i * D.parity j) :=
  BalancedInduction.rectangularMateFunctorIso_inv_mem J K L M
    (oldContentDistinctCross_supernatural D Sc cutoff ν i j) _

end OddMath.QuiverHecke.ELVOld
