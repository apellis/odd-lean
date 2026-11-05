/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVContentPrincipalSquare
import OddMath.QuiverHecke.CyclotomicAction.ELVNormalizedGridMate
import OddMath.QuiverHecke.CyclotomicAction.ELVContentCapRowSquare
import OddMath.QuiverHecke.CyclotomicAction.ELVContentUnitColumnSquare
import OddMath.QuiverHecke.CyclotomicAction.ELVContentWeightedCapInverse
import OddMath.SKM.RouquierHomPostInverse

/-! # Prescribed content inverses with a lower predecessor

BE (1.13)–(1.14): the given global weighted inverse transports through
the selected full-content source, target and value isomorphisms. Both
orientations retain the literal negative-crossing grid mate and every
ordinary unit/dot column or cap/dot row.
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
local notation "δ" => γ + ([i] : Multiset I)
local notation "hJ" => contentBlockCanonicalSum β [i]
local notation "hK" => contentBlockCanonicalSum γ [i]
local notation "J" => contentAppendTo D Sc cutoff N β [i] γ hJ
local notation "K" => contentAppendTo D Sc cutoff N γ [i] δ hK
local notation "Q₀" => contentInclusion D Sc cutoff N β
local notation "Q₁" => contentInclusion D Sc cutoff N γ
local notation "Q₂" => contentInclusion D Sc cutoff N δ
local notation "T" => truncatedAppend D Sc cutoff N [i]
local notation "sqJ" => contentAppendTo_inclusion D Sc cutoff N β [i] γ hJ
local notation "sqK" => contentAppendTo_inclusion D Sc cutoff N γ [i] δ hK
local notation "hCross" => contentBlockMatrixCross_supernatural D Sc cutoff N β i
local notation "hDotJ" => contentBlockMatrixDot_supernatural D Sc cutoff N β i
local notation "hDotK" => contentBlockMatrixDot_supernatural D Sc cutoff N γ i
variable (M : ContentModules D Sc cutoff N (β + ([i] : Multiset I)))
local notation "P" => induced Q₁ M
local notation "FE" => Functor.obj (restriction T) (induced T P)
local notation "Target" => fullSquareTargetRetargetIso K Q₂ Q₁ T sqK M FE FE
  (contentAppendToRestrictionSquare D Sc cutoff N γ [i] δ hK (induced T P)) (Iso.refl FE)
local notation "Source" => fullSquareSourceIso J Q₁ Q₀ T sqJ
  (Functor.obj (restriction J) M) (Functor.obj (restriction T) P)
  (contentAppendToRestrictionExtensionIso D Sc cutoff N β i γ hJ M)
local notation "Value" => contentExtensionUnitIso D Sc cutoff N γ M

/-- The prescribed unit inverse on a supported content block is constructed
from the given weighted unit matrix, with no inverse premise. -/
theorem contentSupportedLocalInverseFrom_nonempty
    (hh : 0 ≤ contentCrossingHeight D cutoff i γ) :
    Nonempty (SKM.SuperSumInvFrom (k := k) (orderedGridMateComponent J K hCross M)
      (unitDotColumn K hDotK M) (D.parity i) (fun n => n • D.parity i)
      (contentUnitCount D cutoff i γ)) := by
  let B := weightedContentLocalInverseFrom D Sc cutoff N i P γ hh
  let a := Target
  let b := Source
  let c := Value
  have H := B.mapCoordinates (𝟭 (ContentModules D Sc cutoff N γ)) a b c
    (contentUnitTargetIso_hom_mem D Sc cutoff N γ i M)
    (contentMatrixSourceIso_hom_mem D Sc cutoff N β i M)
    (contentUnitValueIso_hom_mem D Sc cutoff N γ M)
  have hf : b.hom ≫ (𝟭 (ContentModules D Sc cutoff N γ)).map
      ((restriction Q₁).map (weightedMatrixMate D Sc cutoff N i P)) ≫ a.inv =
      orderedGridMateComponent J K hCross M := by
    have hs := contentPrincipalMate_square D Sc cutoff N β i M
    rw [← weightedMatrixMate_eq_ordered D Sc cutoff N i P] at hs
    have he := congrArg (fun f => f ≫ a.inv) hs
    dsimp only [a, b, c] at he ⊢
    simpa only [Functor.id_map, Category.assoc, Iso.hom_inv_id, Category.comp_id] using he.symm
  have hg (n : ℕ) : c.hom ≫ (𝟭 (ContentModules D Sc cutoff N γ)).map
      ((restriction Q₁).map (unitDotColumn T (truncatedDot_supernatural D Sc cutoff N i) P n)) ≫ a.inv =
      unitDotColumn K hDotK M n := by
    have hs := contentUnitDotColumn_square D Sc cutoff N γ i M n
    have he := congrArg (fun f => f ≫ a.inv) hs
    dsimp only [a, b, c] at he ⊢
    simpa only [Functor.id_map, Category.assoc, Iso.hom_inv_id, Category.comp_id] using he.symm
  exact ⟨by simpa only [hf, hg] using H⟩

/-- The prescribed cap inverse on a supported block retains the same chosen
principal field and all ordinary dotted rows. -/
theorem contentSupportedLocalInverseTo_nonempty
    (hh : contentCrossingHeight D cutoff i γ ≤ 0) :
    Nonempty (SKM.SuperSumInvTo (k := k) (orderedGridMateComponent J K hCross M)
      (capDotRow J hDotJ M) (D.parity i) (fun n => n • D.parity i)
      (contentCapCount D cutoff i γ)) := by
  let B := weightedContentLocalInverseTo D Sc cutoff N i P γ hh
  let a := Source
  let b := Target
  let c := Value
  have H := B.mapCoordinates (𝟭 (ContentModules D Sc cutoff N γ)) a b c
    (contentMatrixSourceIso_hom_mem D Sc cutoff N β i M)
    (contentUnitTargetIso_hom_mem D Sc cutoff N γ i M)
    (contentUnitValueIso_hom_mem D Sc cutoff N γ M)
  have hf : a.hom ≫ (𝟭 (ContentModules D Sc cutoff N γ)).map
      ((restriction Q₁).map (weightedMatrixMate D Sc cutoff N i P)) ≫ b.inv =
      orderedGridMateComponent J K hCross M := by
    have hs := contentPrincipalMate_square D Sc cutoff N β i M
    rw [← weightedMatrixMate_eq_ordered D Sc cutoff N i P] at hs
    have he := congrArg (fun f => f ≫ b.inv) hs
    dsimp only [a, b, c] at he ⊢
    simpa only [Functor.id_map, Category.assoc, Iso.hom_inv_id, Category.comp_id] using he.symm
  have hg (n : ℕ) : a.hom ≫ (𝟭 (ContentModules D Sc cutoff N γ)).map
      ((restriction Q₁).map (capDotRow T (truncatedDot_supernatural D Sc cutoff N i) P n)) ≫ c.inv =
      capDotRow J hDotJ M n := by
    have hs := contentMatrixCapDotRow_square D Sc cutoff N β i M n
    have he := congrArg (fun f => f ≫ c.inv) hs
    dsimp only [a, b, c] at he ⊢
    simpa only [Functor.id_map, Category.assoc, Iso.hom_inv_id, Category.comp_id] using he.symm
  exact ⟨by simpa only [hf, hg] using H⟩

private theorem supportedSingletonDot_mem (i : I) :
    dotE D Sc [i] 0 ∈ parity (R := k) _ _ (D.parity i) := by
  simpa only [pow_one, one_nsmul] using firstDot_pow_parity D Sc i [] 1

section Targets
variable (γ' δ' : Multiset I) (hγ' : β + ([i] : Multiset I) = γ')
  (hδ' : γ' + ([i] : Multiset I) = δ')
local notation "J'" => contentAppendTo D Sc cutoff N β [i] γ' hγ'
local notation "K'" => contentAppendTo D Sc cutoff N γ' [i] δ' hδ'
local notation "hCross'" => contentTargetsGridCross_supernatural D Sc cutoff N β γ' δ' i hγ' hδ'
local notation "hDotJ'" => contentAppendTo_supernatural D Sc cutoff N hγ' hγ' (supportedSingletonDot_mem D Sc i)
local notation "hDotK'" => contentAppendTo_supernatural D Sc cutoff N hδ' hδ' (supportedSingletonDot_mem D Sc i)

/-- The constructed unit inverse retains the stored successor contents used
by the weight induction functors. -/
theorem contentTargetsLocalInverseFrom_nonempty (M' : ContentModules D Sc cutoff N γ')
    (hh : 0 ≤ contentCrossingHeight D cutoff i γ') :
    Nonempty (SKM.SuperSumInvFrom (k := k) (orderedGridMateComponent J' K' hCross' M')
      (unitDotColumn K' hDotK' M') (D.parity i) (fun n => n • D.parity i)
      (contentUnitCount D cutoff i γ')) := by
  subst δ'
  subst γ'
  exact contentSupportedLocalInverseFrom_nonempty D Sc cutoff N β i M' hh

/-- The constructed cap inverse keeps the same two stored append targets. -/
theorem contentTargetsLocalInverseTo_nonempty (M' : ContentModules D Sc cutoff N γ')
    (hh : contentCrossingHeight D cutoff i γ' ≤ 0) :
    Nonempty (SKM.SuperSumInvTo (k := k) (orderedGridMateComponent J' K' hCross' M')
      (capDotRow J' hDotJ' M') (D.parity i) (fun n => n • D.parity i)
      (contentCapCount D cutoff i γ')) := by
  subst δ'
  subst γ'
  exact contentSupportedLocalInverseTo_nonempty D Sc cutoff N β i M' hh
end Targets

end OddMath.QuiverHecke.ELVOld
