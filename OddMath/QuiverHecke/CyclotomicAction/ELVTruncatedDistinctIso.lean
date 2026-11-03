/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVTruncatedDistinctMate
import OddMath.QuiverHecke.CyclotomicAction.ELVMixedRectangularMate

/-! # Homogeneous distinct mate inverses after truncation

Brundan–Ellis (1.12): the prescribed positive crossing mate is an
isomorphism on arbitrary truncated modules. The coend PBW inverse
supplies bijectivity, and homogeneous cancellation gives both the
module inverse and its naturality in arbitrary input-module maps.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ) (i j : I)
local notation "A" => truncatedAppend D Sc cutoff N [i]
local notation "B" => truncatedAppend D Sc cutoff N [j]
local notation "hα" => truncatedDistinctCross_supernatural D Sc cutoff N i j

/-- Pointwise decoder bijectivity holds for the prescribed native rectangular map. -/
theorem truncatedDistinctRectangularMate_bijective (hij : i ≠ j)
    (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))
    (w : TruncatedCategory D Sc cutoff N) :
    Function.Bijective (BalancedInduction.orderedRectangularMateLinear B A A B hα M w) :=
  (BalancedInduction.orderedRectangularMateLinear_bijective_iff A B hα M w).mpr
    (truncatedDistinctMate_bijective D Sc cutoff N i j M hij w)

/-- The prescribed mate has a homogeneous inverse on every truncated module. -/
def truncatedDistinctModuleIso (hij : i ≠ j)
    (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k)) :
    BalancedInduction.induced A ((BalancedInduction.restriction B).obj M) ≅
      (BalancedInduction.restriction B).obj (BalancedInduction.induced A M) :=
  BalancedInduction.rectangularMateModuleIso B A A B hα M
    (truncatedDistinctRectangularMate_bijective D Sc cutoff N i j hij M)

@[simp] theorem truncatedDistinctModuleIso_hom (hij : i ≠ j)
    (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k)) :
    (truncatedDistinctModuleIso D Sc cutoff N i j hij M).hom =
      BalancedInduction.orderedRectangularMateComponent B A A B hα M :=
  BalancedInduction.rectangularMateModuleIso_hom B A A B hα M
    (truncatedDistinctRectangularMate_bijective D Sc cutoff N i j hij M)

/-- Both even and odd distinct crossings retain their parity under inversion. -/
theorem truncatedDistinctModuleIso_inv_mem (hij : i ≠ j)
    (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k)) :
    (truncatedDistinctModuleIso D Sc cutoff N i j hij M).inv ∈
      parity (R := k) _ _ (D.parity i * D.parity j) :=
  BalancedInduction.rectangularMateModuleIso_inv_mem B A A B hα M
    (truncatedDistinctRectangularMate_bijective D Sc cutoff N i j hij M)

/-- The inverse is natural in arbitrary input-module morphisms. -/
def truncatedDistinctFunctorIso (hij : i ≠ j) :
    BalancedInduction.rectangularMateSourceFunctor (k := k) B A ≅
      BalancedInduction.rectangularMateTargetFunctor (k := k) A B :=
  BalancedInduction.rectangularMateFunctorIso B A A B hα
    (truncatedDistinctRectangularMate_bijective D Sc cutoff N i j hij)

@[simp] theorem truncatedDistinctFunctorIso_hom (hij : i ≠ j) :
    (truncatedDistinctFunctorIso D Sc cutoff N i j hij).hom =
      BalancedInduction.rectangularMateHom B A A B hα :=
  BalancedInduction.rectangularMateFunctorIso_hom B A A B hα
    (truncatedDistinctRectangularMate_bijective D Sc cutoff N i j hij)

/-- Each total component remains the prescribed cup-crossing-cap. -/
@[simp] theorem truncatedDistinctFunctorIso_hom_total (hij : i ≠ j)
    (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k)) :
    (truncatedDistinctFunctorIso D Sc cutoff N i j hij).hom.total M =
      BalancedInduction.orderedRectangularMateComponent B A A B hα M := by
  rw [truncatedDistinctFunctorIso_hom, BalancedInduction.rectangularMateHom_total]

theorem truncatedDistinctFunctorIso_inv_mem (hij : i ≠ j) :
    (truncatedDistinctFunctorIso D Sc cutoff N i j hij).inv ∈
      parity (R := k) _ _ (D.parity i * D.parity j) :=
  BalancedInduction.rectangularMateFunctorIso_inv_mem B A A B hα
    (truncatedDistinctRectangularMate_bijective D Sc cutoff N i j hij)

end OddMath.QuiverHecke.ELVOld
