/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVContentAbsentUnitInverse
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionGridMatrixNaturality
import OddMath.SKM.AugmentedInverseNaturality

/-! # Input-natural unit inversion at absent content

BE (1.14): the constructed pointwise absent-content inverse bundles on
all input-module maps. Inverse signed naturality is derived from the given
ordinary unit/dot fields, without an inverse-naturality assumption.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open BalancedInduction CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (β : Multiset I) (i : I)
local notation "γ" => β + ([i] : Multiset I)
local notation "hK" => contentBlockCanonicalSum β [i]
local notation "K" => contentAppendTo D Sc cutoff N β [i] γ hK
local notation "hDot" => contentBlockMatrixDot_supernatural D Sc cutoff N β i
local notation "CM" => ContentModules D Sc cutoff N β
local notation "FE" => (Superfunctor.mk (induction K ⋙ restriction K) : Superfunctor k CM CM)
local notation "Zero" => (Superfunctor.mk (elvZeroFunctor D Sc cutoff N β) : Superfunctor k CM CM)
local notation "Id" => (Superfunctor.mk (𝟭 CM) : Superfunctor k CM CM)

/-- The absent-sector principal field is the specified zero input-natural map. -/
theorem contentAbsentPrincipal_supernatural :
    IsSupernatural k (D.parity i) (F := (Zero).toFunctor) (G := (FE).toFunctor)
      (fun _ => 0) where
  mem _ := Submodule.zero_mem _
  naturality _ := by simp

/-- The given absent-content unit columns admit a whole augmented inverse
on the full input-module supercategory, including odd module morphisms. -/
theorem contentAbsentUnitFamily_nonempty (hi : i ∉ β) :
    Nonempty (SKM.SuperSumInvFrom (k := k)
      (Superfunctor.homMk (F := Zero) (G := FE)
        (contentAbsentPrincipal_supernatural D Sc cutoff N β i).toSuperNatTrans)
      (fun n => Superfunctor.homMk (F := Id) (G := FE)
        (gridUnitDotColumn_supernatural K hDot n).toSuperNatTrans)
      (D.parity i) (fun n => n • D.parity i) (contentUnitCount D cutoff i β)) := by
  exact ⟨SKM.SuperSumInvFrom.ofSupernaturalComponents (F := FE) (G := Zero) (H := Id)
    (fun M => Classical.choice (contentAbsentUnitInverse_nonempty D Sc cutoff N β i hi M))
    (contentAbsentPrincipal_supernatural D Sc cutoff N β i)
    (fun n => gridUnitDotColumn_supernatural K hDot n)⟩

end OddMath.QuiverHecke.ELVOld
