import OddMath.QuiverHecke.CyclotomicAction.ELVContentMatrixCharts
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionGridMatrixFamilies
import OddMath.QuiverHecke.CyclotomicAction.ELVParityMatrixCoordinates
import OddMath.QuiverHecke.CyclotomicAction.ELVFiniteMatrixComponents

/-! # Chosen content coordinates for finite unit and cap families

Brundan--Ellis (1.13)--(1.14), DeformedMatrixComparison (4), (5):
the canonical parity coordinates conjugate the selected E/F and value
linear equivalences. These are genuine whole finite-family equivalences,
independently of any inverse-matrix or chart-evenness premise.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open CyclotomicCrossingTensor BalancedInduction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (ν : List I) (i : I)
local notation "J₀" => oldContentAppend D Sc cutoff ν i
local notation "J₁" => oldContentAppend D Sc cutoff (i :: ν) i
local notation "Q₁" => oldContentInclusion D Sc cutoff (i :: ν)
local notation "J" => append D Sc cutoff i
local instance contentGridCoordinatesPi : PiSupercategory k
    (Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k)) := supermodulePiSupercategory
local instance oldGridCoordinatesPi : PiSupercategory k
    (Superfunctor k (OldCategory D Sc cutoff) (SVec k)) := supermodulePiSupercategory
variable (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))
  (m : ℕ) (t : OldContentCategory D Sc cutoff (i :: ν))
local notation "M" => induced Q₁ N

/-- Every unit-family coordinate uses its selected plain chart and the
existing canonical source and target parity coordinates. -/
def oldContentUnitSlotEquiv (a : Option (Fin m)) :
    (gridUnitMatrixFamily J₀ (D.parity i) N m a).obj t ≃ₗ[k]
      (unitMatrixFamily D Sc cutoff i M m a).obj t.obj := by
  cases a with
  | none =>
    dsimp only [gridUnitMatrixFamily, unitMatrixFamily]
    exact shiftedModuleValueLinearEquiv
      (induced J₀ ((restriction J₀).obj N)) (induced J ((restriction J).obj M))
      t t.obj (oldContentEFLinearEquiv D Sc cutoff ν i N t) (D.parity i)
  | some r =>
    dsimp only [gridUnitMatrixFamily, unitMatrixFamily]
    exact shiftedModuleValueLinearEquiv N M t t.obj
      (oldContentValueLinearEquiv D Sc cutoff ν i N t) (r.val • D.parity i)

/-- Every cap-family coordinate retains its selected F/E or value chart. -/
def oldContentCapSlotEquiv (a : Option (Fin m)) :
    (gridCapMatrixFamily J₁ (D.parity i) N m a).obj t ≃ₗ[k]
      (capMatrixFamily D Sc cutoff i M m a).obj t.obj := by
  cases a with
  | none =>
    dsimp only [gridCapMatrixFamily, capMatrixFamily]
    exact shiftedModuleValueLinearEquiv
      ((restriction J₁).obj (induced J₁ N)) ((restriction J).obj (induced J M))
      t t.obj (oldContentFELinearEquiv D Sc cutoff ν i N t) (D.parity i)
  | some r =>
    dsimp only [gridCapMatrixFamily, capMatrixFamily]
    exact shiftedModuleValueLinearEquiv N M t t.obj
      (oldContentValueLinearEquiv D Sc cutoff ν i N t) (r.val • D.parity i)

/-- The whole finite unit source comparison is a genuine coordinate product. -/
def oldContentUnitFamilyEquiv :
    gridUnitMatrixSourceSpace J₀ (D.parity i) N m t ≃ₗ[k]
      unitMatrixSourceSpace D Sc cutoff i M m t.obj :=
  LinearEquiv.piCongrRight (oldContentUnitSlotEquiv D Sc cutoff ν i N m t)

/-- The whole finite cap target comparison is a genuine coordinate product. -/
def oldContentCapFamilyEquiv :
    gridCapMatrixTargetSpace J₁ (D.parity i) N m t ≃ₗ[k]
      capMatrixTargetSpace D Sc cutoff i M m t.obj :=
  LinearEquiv.piCongrRight (oldContentCapSlotEquiv D Sc cutoff ν i N m t)

end OddMath.QuiverHecke.ELVOld
