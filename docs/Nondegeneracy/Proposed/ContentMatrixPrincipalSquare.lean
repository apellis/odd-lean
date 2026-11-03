/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVFullInductionSquareParity
import OddMath.QuiverHecke.CyclotomicAction.ELVContentBlockCapPowers
import OddMath.Algebra.FiniteSupermoduleFunctor

/-! # Whole principal and cap-row squares on content

BE (1.13)–(1.14): the selected lower E/F and upper F/E full-inclusion
charts compare the prescribed crossing mate and every ordinary dotted cap
row as whole module morphisms.
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

private theorem gridMateSquare_apply
    {k C A B E : Type u} [CommRing k]
    [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
    [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
    [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    (K : A ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
    (T : E ⥤ E) [T.Additive] [T.Linear k] [IsSuperfunctor k T]
    {p q : ZMod 2} {α : ∀ s, (J ⋙ K).obj s ⟶ (J ⋙ K).obj s}
    {χ : ∀ s, (T ⋙ T).obj s ⟶ (T ⋙ T).obj s}
    (hα : IsSupernatural k p α) (hχ : IsSupernatural k q χ)
    (M : Superfunctor k A (SVec k)) (P : Superfunctor k E (SVec k)) (w : A) (v : E)
    (c : Obj K M.toFunctor (K.obj w) → Obj T P.toFunctor (T.obj v))
    (d : Obj J ((restriction J).obj M).toFunctor w →
      Obj T ((restriction T).obj P).toFunctor v)
    (h : ∀ x, c (orderedGridMateLinear J K hα M w x) = orderedMateLinear T hχ P v (d x))
    (x : (induced J ((restriction J).obj M)).obj w) :
    c ((orderedGridMateComponent J K hα M).total w x) =
      (orderedMateComponent T hχ P).total v (d x) :=
  h x

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
local notation "hGlobalCross" => truncatedEqualCross_supernatural D Sc cutoff N i
local notation "hDot" => contentBlockMatrixDot_supernatural D Sc cutoff N β i
local notation "hGlobalDot" => truncatedDot_supernatural D Sc cutoff N i
variable (M : ContentModules D Sc cutoff N (β + ([i] : Multiset I)))
local notation "P" => induced Q₁ M
local notation "FE" => Functor.obj (restriction T) (induced T P)
local notation "Target" => fullSquareTargetRetargetIso K Q₂ Q₁ T sqK M FE FE
  (contentAppendToRestrictionSquare D Sc cutoff N γ [i] δ hK (induced T P)) (Iso.refl FE)
local notation "Source" => fullSquareSourceIso J Q₁ Q₀ T sqJ
  (Functor.obj (restriction J) M) (Functor.obj (restriction T) P)
  (contentAppendToRestrictionExtensionIso D Sc cutoff N β i γ hJ M)
local notation "Value" => contentExtensionUnitIso D Sc cutoff N γ M

private theorem restrictionSquare_total_apply
    (w : ContentCategory D Sc cutoff N (β + ([i] : Multiset I)))
    (b : ((restriction K).obj ((restriction Q₂).obj (induced T P))).obj w) :
    (contentAppendToRestrictionSquare D Sc cutoff N γ [i] δ hK (induced T P)).hom.total w b = b := by
  let A₀ := (restriction K).obj ((restriction Q₂).obj (induced T P))
  change (𝟙 A₀ : A₀ ⟶ A₀).total w b = b
  exact identity_total_apply (k := k) _ w b

/-- The chosen whole module charts intertwine the prescribed negative-crossing mate. -/
theorem contentMatrixMate_square :
    orderedGridMateComponent J K hCross M ≫ (Target).hom =
      (Source).hom ≫ (restriction Q₁).map (orderedMateComponent T hGlobalCross P) := by
  apply OddMath.FiniteSupermodule.hom_ext_total (k := k)
  intro w
  apply SVec.hom_ext
  intro b
  have hLeft := total_comp_apply (k := k) (orderedGridMateComponent J K hCross M) (Target).hom w b
  have hRightValue := sourcePostcomposeOrdinary_total_apply J Q₁ Q₀ T sqJ ((restriction J).obj M)
    T P (contentAppendToRestrictionExtensionIso D Sc cutoff N β i γ hJ M)
    (contentBlockRestrictionExtension_even D Sc cutoff N β i M)
    ((restriction T).obj (induced T P)) (orderedMateComponent T hGlobalCross P) w b
  have hC := fullSquareTargetRetargetIso_total_apply K Q₂ Q₁ T sqK M FE FE
    (contentAppendToRestrictionSquare D Sc cutoff N γ [i] δ hK (induced T P)) (Iso.refl FE)
    w ((orderedGridMateComponent J K hCross M).total w b)
  simp only [Iso.refl_hom, identity_total_apply, restrictionSquare_total_apply] at hC
  have hRawFamily := fun x => LinearMap.congr_fun (contentBlockMatrixMate_square D Sc cutoff N β i M w) x
  have hRaw := gridMateSquare_apply J K T hCross hGlobalCross M P w w.obj _ _ hRawFamily b
  have hE := congrArg (fun f => f ((orderedGridMateComponent J K hCross M).total w b))
    (targetLinear_self K Q₂ Q₁ T sqK M ((K).obj w))
  have hL := restrictionLinear_total_apply K Q₂ Q₁ T sqK M ((K).obj w)
    ((orderedGridMateComponent J K hCross M).total w b)
  have hER := hE.symm.trans hRaw
  have hCL := hC.trans hL.symm
  have hJoined := hCL.trans hER
  exact hLeft.trans (hJoined.trans hRightValue.symm)

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
