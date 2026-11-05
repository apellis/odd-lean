/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVContentUnitColumnSquare
import OddMath.QuiverHecke.CyclotomicAction.ELVContentWeightedLocalInverse
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightMatrixBoundary
import OddMath.SKM.RouquierHomPostInverse

/-! # Unit inversion on content with no lower predecessor

BE (1.14): the zero principal source and the ordinary upper unit columns
retain the constructed weighted inverse. The following F/E object is
kept and is not declared zero from the absence of the moving colour.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open BalancedInduction CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (β : Multiset I) (i : I) (hi : i ∉ β)
local notation "γ" => β + ([i] : Multiset I)
local notation "hK" => contentBlockCanonicalSum β [i]
local notation "K" => contentAppendTo D Sc cutoff N β [i] γ hK
local notation "Q" => contentInclusion D Sc cutoff N β
local notation "U" => contentInclusion D Sc cutoff N γ
local notation "T" => truncatedAppend D Sc cutoff N [i]
local notation "sq" => contentAppendTo_inclusion D Sc cutoff N β [i] γ hK
local notation "hDot" => contentBlockMatrixDot_supernatural D Sc cutoff N β i
variable (M : ContentModules D Sc cutoff N β)
local notation "P" => induced (contentInclusion D Sc cutoff N β) M
local notation "FE" => Functor.obj (restriction (truncatedAppend D Sc cutoff N [i]))
  (induced (truncatedAppend D Sc cutoff N [i]) (induced (contentInclusion D Sc cutoff N β) M))
local notation "Target" => fullSquareTargetRetargetIso K U Q T sq M FE FE
  (contentAppendToRestrictionSquare D Sc cutoff N β [i] γ hK (induced T P)) (Iso.refl FE)
local notation "Value" => contentExtensionUnitIso D Sc cutoff N β M

include hi in
/-- The prescribed unit columns on an absent-colour content have all local
inverse identities, with their zero principal source and exact finite count. -/
theorem contentAbsentUnitInverse_nonempty :
    Nonempty (SKM.SuperSumInvFrom (k := k)
      (0 : elvZeroModule D Sc cutoff N β ⟶ (restriction K).obj (induced K M))
      (unitDotColumn K hDot M) (D.parity i) (fun n => n • D.parity i)
      (contentUnitCount D cutoff i β)) := by
  refine ⟨?_⟩
  have hh := contentCrossingHeight_nonneg_of_not_mem D cutoff β.toList i
    (by simpa only [Multiset.mem_toList] using hi)
  rw [Multiset.coe_toList] at hh
  let J := weightedContentLocalInverseFrom D Sc cutoff N i P β hh
  let a := Target
  let c := Value
  have h0 := elvZeroModule_isZero D Sc cutoff N β
  have hGlobal := truncatedIndRes_restriction_isZero D Sc cutoff N i β hi P
  let b := h0.iso hGlobal
  have hb : b.hom ∈ parity (R := k) _ _ 0 := by
    rw [h0.eq_of_src b.hom 0]
    exact Submodule.zero_mem _
  have H := J.mapCoordinates (𝟭 (ContentModules D Sc cutoff N β)) a b c
    (contentUnitTargetIso_hom_mem D Sc cutoff N β i M) hb
    (contentUnitValueIso_hom_mem D Sc cutoff N β M)
  have hf : b.hom ≫ (𝟭 (ContentModules D Sc cutoff N β)).map
      ((restriction Q).map (weightedMatrixMate D Sc cutoff N i P)) ≫ a.inv =
      (0 : elvZeroModule D Sc cutoff N β ⟶ (restriction K).obj (induced K M)) :=
    h0.eq_of_src _ _
  have hg (n : ℕ) : c.hom ≫ (𝟭 (ContentModules D Sc cutoff N β)).map
      ((restriction Q).map (unitDotColumn T (truncatedDot_supernatural D Sc cutoff N i) P n)) ≫ a.inv =
      unitDotColumn K hDot M n := by
    have hu := contentUnitDotColumn_square D Sc cutoff N β i M n
    change unitDotColumn K hDot M n ≫ a.hom =
      c.hom ≫ (restriction Q).map (unitDotColumn T (truncatedDot_supernatural D Sc cutoff N i) P n) at hu
    have he := congrArg (fun f => f ≫ a.inv) hu
    simpa only [Functor.id_map, Category.assoc, Iso.hom_inv_id, Category.comp_id] using he.symm
  simpa only [hf, hg] using H

end OddMath.QuiverHecke.ELVOld
