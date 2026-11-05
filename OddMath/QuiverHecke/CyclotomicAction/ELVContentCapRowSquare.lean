/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVFullInductionSquareParity
import OddMath.QuiverHecke.CyclotomicAction.ELVContentBlockCapPowers
import OddMath.Algebra.FiniteSupermoduleFunctor

/-! # Whole dotted cap-row squares on content

BE (1.13)–(1.14): the selected lower E/F and value full-inclusion
charts compare every prescribed ordinary dotted cap row as whole module
morphisms, on all vectors and arrows.
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

private theorem sourcePostcompose_total_apply
    {k C A B E : Type u} [CommRing k]
    [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
    [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
    [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    (U : A ⥤ E) [U.Additive] [U.Linear k] [IsSuperfunctor k U] [U.Full] [U.Faithful]
    (Q : C ⥤ B) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q]
    (T : B ⥤ E) [T.Additive] [T.Linear k] [IsSuperfunctor k T]
    (h : J ⋙ U = Q ⋙ T) (R : Superfunctor k C (SVec k)) (S : Superfunctor k B (SVec k))
    (e : induced Q R ≅ S) (V : Superfunctor k E (SVec k)) (g : induced T S ⟶ V)
    (w : A) (x : (induced J R).obj w) :
    ((fullSquareSourceIso J U Q T h R S e).hom ≫ (restriction U).map g).total w x =
      g.total (U.obj w) (fullSquareSourceLinear J U Q T h R S e w x) := by
  rw [total_comp_apply, restricted_total_apply]
  rfl

private theorem sourcePostcomposeOrdinary_total_apply
    {k C A B E : Type u} [CommRing k]
    [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
    [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
    [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    (U : A ⥤ E) [U.Additive] [U.Linear k] [IsSuperfunctor k U] [U.Full] [U.Faithful]
    (Q : C ⥤ B) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q]
    (T : B ⥤ E) [T.Additive] [T.Linear k] [IsSuperfunctor k T]
    (h : J ⋙ U = Q ⋙ T) (R : Superfunctor k C (SVec k))
    (L : B ⥤ B) [L.Additive] [L.Linear k] [IsSuperfunctor k L]
    (G : Superfunctor k B (SVec k)) (e : induced Q R ≅ (restriction L).obj G)
    (he : e.hom ∈ parity (R := k) _ _ 0)
    (V : Superfunctor k E (SVec k)) (g : induced T ((restriction L).obj G) ⟶ V)
    (w : A) (x : (induced J R).obj w) :
    ((fullSquareSourceIso J U Q T h R ((restriction L).obj G) e).hom ≫
      (restriction U).map g).total w x =
      g.total (U.obj w) (fullSquareOrdinarySourceLinear J U Q T h R L G e w x) := by
  have h0 := sourcePostcompose_total_apply J U Q T h R ((restriction L).obj G) e V g w x
  have h1 := congrArg (fun f => g.total (U.obj w) (f x))
    (fullSquareOrdinarySourceLinear_eq_source J U Q T h R L G e he w)
  exact h0.trans h1.symm

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (β : Multiset I) (i : I)
local notation "γ" => β + ([i] : Multiset I)
local notation "hJ" => contentBlockCanonicalSum β [i]
local notation "J" => contentAppendTo D Sc cutoff N β [i] γ hJ
local notation "Q₀" => contentInclusion D Sc cutoff N β
local notation "Q₁" => contentInclusion D Sc cutoff N γ
local notation "T" => truncatedAppend D Sc cutoff N [i]
local notation "sqJ" => contentAppendTo_inclusion D Sc cutoff N β [i] γ hJ
local notation "hDot" => contentBlockMatrixDot_supernatural D Sc cutoff N β i
local notation "hGlobalDot" => truncatedDot_supernatural D Sc cutoff N i
variable (M : ContentModules D Sc cutoff N (β + ([i] : Multiset I)))
local notation "P" => induced Q₁ M
local notation "Source" => fullSquareSourceIso J Q₁ Q₀ T sqJ
  (Functor.obj (restriction J) M) (Functor.obj (restriction T) P)
  (contentAppendToRestrictionExtensionIso D Sc cutoff N β i γ hJ M)
local notation "Value" => contentExtensionUnitIso D Sc cutoff N γ M

/-- The selected lower E/F chart is even on all input module values. -/
theorem contentMatrixSourceIso_hom_mem : (Source).hom ∈ parity (R := k) _ _ 0 :=
  fullSquareSourceIso_hom_mem J Q₁ Q₀ T sqJ ((restriction J).obj M) ((restriction T).obj P)
    (contentAppendToRestrictionExtensionIso D Sc cutoff N β i γ hJ M)
    (contentBlockRestrictionExtension_even D Sc cutoff N β i M)

/-- Every literal dotted cap row commutes with the same whole E/F and value charts. -/
theorem contentMatrixCapDotRow_square (n : ℕ) :
    capDotRow J hDot M n ≫ (Value).hom =
      (Source).hom ≫ (restriction Q₁).map (capDotRow T hGlobalDot P n) := by
  apply OddMath.FiniteSupermodule.hom_ext_total (k := k)
  intro w
  apply SVec.hom_ext
  intro b
  have hLeft := total_comp_apply (k := k) (capDotRow J hDot M n) (Value).hom w b
  have hV := fullyFaithfulUnit_total_apply Q₁ M w ((capDotRow J hDot M n).total w b)
  change (Value).hom.total w ((capDotRow J hDot M n).total w b) = _ at hV
  have hLeftValue := hLeft.trans hV
  have hRightValue := sourcePostcomposeOrdinary_total_apply J Q₁ Q₀ T sqJ ((restriction J).obj M)
    T P (contentAppendToRestrictionExtensionIso D Sc cutoff N β i γ hJ M)
    (contentBlockRestrictionExtension_even D Sc cutoff N β i M)
    P (capDotRow T hGlobalDot P n) w b
  have hRaw := contentBlockCapDotRow_square D Sc cutoff N β i M w n b
  exact hLeftValue.trans (hRaw.trans hRightValue.symm)

end OddMath.QuiverHecke.ELVOld
