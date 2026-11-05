/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVFullInductionSquareParity
import OddMath.QuiverHecke.CyclotomicAction.ELVContentBlockMatrixRows
import OddMath.Algebra.FiniteSupermoduleFunctor

/-! # Whole unit-column square at every content

BE (1.14): the selected full upper append chart and content extension
unit identify the literal ordinary unit/dot module columns. No lower
predecessor or lower append is required.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open BalancedInduction
universe u
private theorem total_comp_apply
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {M N P : Superfunctor k C (SVec k)} (f : M ⟶ N) (g : N ⟶ P) (w : C) (b : M.obj w) :
    (f ≫ g).total w b = g.total w (f.total w b) := by
  rw [Superfunctor.comp_total]
  rfl

private theorem restricted_total_apply
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (Q : C ⥤ A) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q]
    {M N : Superfunctor k A (SVec k)} (f : M ⟶ N) (w : C) (b : M.obj (Q.obj w)) :
    ((restriction Q).map f).total w b = f.total (Q.obj w) b := rfl

private theorem identity_total_apply
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    (M : Superfunctor k C (SVec k)) (w : C) (b : M.obj w) :
    (𝟙 M : M ⟶ M).total w b = b := by
  have h := SuperNatTrans.id_total (R := k) M.toFunctor w
  exact congrArg (fun f => f b) h

private theorem fullyFaithfulUnit_total_apply
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (Q : C ⥤ A) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q] [Q.Full] [Q.Faithful]
    (M : Superfunctor k C (SVec k)) (w : C) (b : M.obj w) :
    (fullyFaithfulUnitIso Q M).hom.total w b = unit Q M.toFunctor w b := by
  rw [fullyFaithfulUnitIso_hom]
  simp only [adjunctionUnit, Superfunctor.homMk, SuperNatTrans.total,
    unitTransform_app, ite_true, one_ne_zero, ite_false, add_zero]
  rfl

private theorem restrictionLinear_total_apply
    {k C A B E : Type u} [CommRing k]
    [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
    [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
    [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    (U : A ⥤ E) [U.Additive] [U.Linear k] [IsSuperfunctor k U] [U.Full] [U.Faithful]
    (Q : C ⥤ B) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q]
    (T : B ⥤ E) [T.Additive] [T.Linear k] [IsSuperfunctor k T]
    (h : J ⋙ U = Q ⋙ T) (M : Superfunctor k C (SVec k)) (w : A)
    (b : Obj J M.toFunctor w) :
    fullSquareRestrictionLinear J U Q T h M w b =
      (fullSquareRestrictionIso J U Q T h M).hom.total w b := rfl

private theorem targetLinear_self
    {k C A B E : Type u} [CommRing k]
    [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
    [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
    [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    (U : A ⥤ E) [U.Additive] [U.Linear k] [IsSuperfunctor k U] [U.Full] [U.Faithful]
    (Q : C ⥤ B) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q]
    (T : B ⥤ E) [T.Additive] [T.Linear k] [IsSuperfunctor k T]
    (h : J ⋙ U = Q ⋙ T) (M : Superfunctor k C (SVec k)) (w : A) :
    fullSquareTargetLinear J U Q T h M w (U.obj w) rfl =
      fullSquareRestrictionLinear J U Q T h M w := by
  rw [fullSquareTargetLinear, eqToHom_refl, postcompose_id, LinearMap.id_comp]

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (β : Multiset I) (i : I)
local notation "γ" => β + ([i] : Multiset I)
local notation "hK" => contentBlockCanonicalSum β [i]
local notation "K" => contentAppendTo D Sc cutoff N β [i] γ hK
local notation "Q" => contentInclusion D Sc cutoff N β
local notation "U" => contentInclusion D Sc cutoff N γ
local notation "T" => truncatedAppend D Sc cutoff N [i]
local notation "sq" => contentAppendTo_inclusion D Sc cutoff N β [i] γ hK
local notation "hDot" => contentBlockMatrixDot_supernatural D Sc cutoff N β i
local notation "hGlobalDot" => truncatedDot_supernatural D Sc cutoff N i
variable (M : ContentModules D Sc cutoff N β)
local notation "P" => induced (contentInclusion D Sc cutoff N β) M
local notation "FE" => Functor.obj (restriction (truncatedAppend D Sc cutoff N [i]))
  (induced (truncatedAppend D Sc cutoff N [i]) (induced (contentInclusion D Sc cutoff N β) M))
local notation "Target" => fullSquareTargetRetargetIso K U Q T sq M FE FE
  (contentAppendToRestrictionSquare D Sc cutoff N β [i] γ hK (induced T P)) (Iso.refl FE)
local notation "Value" => contentExtensionUnitIso D Sc cutoff N β M

/-- The selected upper full-inclusion chart is even at every output content. -/
theorem contentUnitTargetIso_hom_mem : (Target).hom ∈ parity (R := k) _ _ 0 := by
  exact fullSquareTargetRetargetIso_hom_mem K U Q T sq M FE FE
    (contentAppendToRestrictionSquare D Sc cutoff N β [i] γ hK (induced T P)) (Iso.refl FE)
    (id_mem _) (id_mem _)

/-- The selected content extension unit is even, including absent-colour contents. -/
theorem contentUnitValueIso_hom_mem : (Value).hom ∈ parity (R := k) _ _ 0 := by
  rw [contentExtensionUnitIso, fullyFaithfulUnitIso_hom]
  exact adjunctionUnit_mem Q M

private theorem restrictionSquare_total_apply
    (w : ContentCategory D Sc cutoff N β)
    (b : ((restriction K).obj ((restriction U).obj (induced T P))).obj w) :
    (contentAppendToRestrictionSquare D Sc cutoff N β [i] γ hK (induced T P)).hom.total w b = b := by
  let A₀ := (restriction K).obj ((restriction U).obj (induced T P))
  change (𝟙 A₀ : A₀ ⟶ A₀).total w b = b
  exact identity_total_apply (k := k) _ w b

/-- The literal given unit/dot columns commute with the selected whole module
charts for every content, including the absent-predecessor boundary. -/
theorem contentUnitDotColumn_square (n : ℕ) :
    unitDotColumn K hDot M n ≫ (Target).hom =
      (Value).hom ≫ (restriction Q).map (unitDotColumn T hGlobalDot P n) := by
  apply OddMath.FiniteSupermodule.hom_ext_total (k := k)
  intro w
  apply SVec.hom_ext
  intro b
  have hLeft := total_comp_apply (k := k) (unitDotColumn K hDot M n) (Target).hom w b
  have hRight := total_comp_apply (k := k) (Value).hom
    ((restriction Q).map (unitDotColumn T hGlobalDot P n)) w b
  have hV := fullyFaithfulUnit_total_apply Q M w b
  change (Value).hom.total w b = _ at hV
  have hRestricted := restricted_total_apply Q (unitDotColumn T hGlobalDot P n) w
    ((Value).hom.total w b)
  have hValue := congrArg (fun z => (unitDotColumn T hGlobalDot P n).total w.obj z) hV
  have hRightValue := hRight.trans (hRestricted.trans hValue)
  have hC := fullSquareTargetRetargetIso_total_apply K U Q T sq M FE FE
    (contentAppendToRestrictionSquare D Sc cutoff N β [i] γ hK (induced T P)) (Iso.refl FE)
    w ((unitDotColumn K hDot M n).total w b)
  simp only [Iso.refl_hom, identity_total_apply, restrictionSquare_total_apply] at hC
  have hRaw := contentBlockUnitDotColumn_square D Sc cutoff N β i M w n b
  have hE := congrArg (fun f => f ((unitDotColumn K hDot M n).total w b))
    (targetLinear_self K U Q T sq M ((K).obj w))
  have hL := restrictionLinear_total_apply K U Q T sq M ((K).obj w)
    ((unitDotColumn K hDot M n).total w b)
  set_option backward.dsimp.instances true in
    dsimp only [induction] at hLeft hRightValue hC hL hE hRaw ⊢
  have hER := hE.symm.trans hRaw
  have hCL := hC.trans hL.symm
  have hJoined := hCL.trans hER
  exact hLeft.trans (hJoined.trans hRightValue.symm)

end OddMath.QuiverHecke.ELVOld
