/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVFullInductionSquareParity
import OddMath.QuiverHecke.CyclotomicAction.ELVContentBlockCapPowers
import OddMath.Algebra.FiniteSupermoduleFunctor

/-! # Whole principal matrix square on content

BE (1.13)–(1.14): the selected lower E/F and upper F/E full-inclusion
charts compare the prescribed crossing mate as a whole module morphism.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open BalancedInduction
universe u
private def rawValue {k V W : Type u} [CommRing k]
    [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]
    (f : V →ₗ[k] W) (x : V) : W := f x

private theorem module_map_id_apply
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    (G : Superfunctor k C (SVec k)) (w : C) (b : G.obj w) : G.map (𝟙 w) b = b := by
  exact congrArg (fun f : G.obj w ⟶ G.obj w => f b) (G.toFunctor.map_id w)

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

private theorem targetLinear_total_apply
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
    (z : E) (hz : U.obj w = z) (x : Obj J M.toFunctor w) :
    rawValue (fullSquareTargetLinear J U Q T h M w z hz) x =
      postcompose T (induced Q M).toFunctor (eqToHom hz)
        ((fullSquareRestrictionIso J U Q T h M).hom.total w x) := rfl

private theorem induced_map_apply
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (T : C ⥤ A) [T.Additive] [T.Linear k] [IsSuperfunctor k T]
    (M : Superfunctor k C (SVec k)) {w z : A} (f : w ⟶ z) (x : (induced T M).obj w) :
    (induced T M).map f x = postcompose T M.toFunctor f x := rfl

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

private theorem gridMate_congr
    {k C A B : Type u} [CommRing k]
    [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
    [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    (K : A ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
    {p : ZMod 2} {α β : ∀ s, (J ⋙ K).obj s ⟶ (J ⋙ K).obj s}
    (hα : IsSupernatural k p α) (hβ : IsSupernatural k p β) (e : α = β)
    (M : Superfunctor k A (SVec k)) :
    orderedGridMateComponent J K hα M = orderedGridMateComponent J K hβ M := by
  cases e
  rfl

private theorem module_total_congr
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {F G : Superfunctor k C (SVec k)} {f g : F ⟶ G} (e : f = g) (w : C) :
    f.total w = g.total w := congrArg (fun f : F ⟶ G => f.total w) e

private theorem componentSquare_apply
    {k C A B E : Type u} [CommRing k]
    [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
    [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
    [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    (K : A ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
    (Q : A ⥤ E) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q]
    (T : E ⥤ E) [T.Additive] [T.Linear k] [IsSuperfunctor k T]
    {q : ZMod 2}
    {χ : ∀ s, (T ⋙ T).obj s ⟶ (T ⋙ T).obj s}
    (hχ : IsSupernatural k q χ)
    (M : Superfunctor k A (SVec k)) (R : Superfunctor k C (SVec k))
    (G : Superfunctor k E (SVec k))
    (f : induced J R ⟶ (restriction K).obj (induced K M)) (w : A)
    (c : Obj K M.toFunctor (K.obj w) →ₗ[k] Obj T G.toFunctor (T.obj (Q.obj w)))
    (d : Obj J R.toFunctor w →ₗ[k]
      Obj T ((restriction T).obj G).toFunctor (Q.obj w))
    (h : c ∘ₗ f.total w = orderedMateLinear T hχ G (Q.obj w) ∘ₗ d)
    (x : (induced J R).obj w) :
    @Eq (((restriction Q).obj ((restriction T).obj (induced T G))).obj w)
      (rawValue c (f.total w x))
      (orderedMateLinear T hχ G (Q.obj w) (d x)) :=
  LinearMap.congr_fun h x

private theorem principalSquare_of_raw
    {k C A B E : Type u} [CommRing k]
    [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
    [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
    [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    (K : A ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
    (Q₀ : C ⥤ E) [Q₀.Additive] [Q₀.Linear k] [IsSuperfunctor k Q₀]
    (Q₁ : A ⥤ E) [Q₁.Additive] [Q₁.Linear k] [IsSuperfunctor k Q₁] [Q₁.Full] [Q₁.Faithful]
    (Q₂ : B ⥤ E) [Q₂.Additive] [Q₂.Linear k] [IsSuperfunctor k Q₂] [Q₂.Full] [Q₂.Faithful]
    (T : E ⥤ E) [T.Additive] [T.Linear k] [IsSuperfunctor k T]
    (sqJ : J ⋙ Q₁ = Q₀ ⋙ T) (sqK : K ⋙ Q₂ = Q₁ ⋙ T)
    {q : ZMod 2} {χ : ∀ s, (T ⋙ T).obj s ⟶ (T ⋙ T).obj s}
    (hχ : IsSupernatural k q χ)
    (M : Superfunctor k A (SVec k)) (R : Superfunctor k C (SVec k))
    (f : induced J R ⟶ (restriction K).obj (induced K M))
    (e : induced Q₀ R ≅ (restriction T).obj (induced Q₁ M))
    (he : e.hom ∈ parity (R := k) _ _ 0)
    (a : (restriction K).obj ((restriction Q₂).obj (induced T (induced Q₁ M))) ≅
      (restriction Q₁).obj ((restriction T).obj (induced T (induced Q₁ M))))
    (ha : ∀ w b, a.hom.total w b =
      (induced T (induced Q₁ M)).map (eqToHom (congrArg (fun F => F.obj w) sqK)) b)
    (hraw : ∀ w,
      fullSquareTargetLinear K Q₂ Q₁ T sqK M (K.obj w) (T.obj (Q₁.obj w))
        (congrArg (fun F => F.obj w) sqK) ∘ₗ f.total w =
      orderedMateLinear T hχ (induced Q₁ M) (Q₁.obj w) ∘ₗ
        fullSquareOrdinarySourceLinear J Q₁ Q₀ T sqJ R T (induced Q₁ M) e w) :
    f ≫
        (fullSquareTargetRetargetIso K Q₂ Q₁ T sqK M
          ((restriction T).obj (induced T (induced Q₁ M)))
          ((restriction T).obj (induced T (induced Q₁ M))) a (Iso.refl _)).hom =
      (fullSquareSourceIso J Q₁ Q₀ T sqJ R
        ((restriction T).obj (induced Q₁ M)) e).hom ≫
        (restriction Q₁).map (orderedMateComponent T hχ (induced Q₁ M)) := by
  apply OddMath.FiniteSupermodule.hom_ext_total (k := k)
  intro w
  apply SVec.hom_ext
  intro b
  rw [total_comp_apply]
  have hRight := sourcePostcompose_total_apply J Q₁ Q₀ T sqJ R
    ((restriction T).obj (induced Q₁ M)) e
    ((restriction T).obj (induced T (induced Q₁ M)))
    (orderedMateComponent T hχ (induced Q₁ M)) w b
  have hC := fullSquareTargetRetargetIso_total_apply K Q₂ Q₁ T sqK M
    ((restriction T).obj (induced T (induced Q₁ M)))
    ((restriction T).obj (induced T (induced Q₁ M))) a (Iso.refl _) w
    ((f).total w b)
  simp only [Iso.refl_hom, identity_total_apply, ha, induced_map_apply] at hC
  have hL := targetLinear_total_apply K Q₂ Q₁ T sqK M (K.obj w) (T.obj (Q₁.obj w))
    (congrArg (fun F => F.obj w) sqK) ((f).total w b)
  have hNative := hraw w
  rw [fullSquareOrdinarySourceLinear_eq_source J Q₁ Q₀ T sqJ R T (induced Q₁ M) e he w] at hNative
  have hRaw := componentSquare_apply J K Q₁ T hχ M R (induced Q₁ M) f w _ _ hNative b
  have hCL := hC.trans hL.symm
  have hJoined := hCL.trans hRaw
  have hFinal := hJoined.trans hRight.symm
  exact hFinal

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
local notation "hGiven" => contentBlockMatrixCross_supernatural D Sc cutoff N β i
local notation "hGlobalCross" => truncatedEqualCross_supernatural D Sc cutoff N i
local notation "hDot" => contentBlockMatrixDot_supernatural D Sc cutoff N β i
local notation "hGlobalDot" => truncatedDot_supernatural D Sc cutoff N i
private theorem restrictionSquare_map_apply
    (G : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))
    (w : ContentCategory D Sc cutoff N (β + ([i] : Multiset I)))
    (b : ((restriction K).obj ((restriction Q₂).obj G)).obj w) :
    (contentAppendToRestrictionSquare D Sc cutoff N γ [i] δ hK G).hom.total w b =
      G.map (@eqToHom _ _ ((Q₂).obj ((K).obj w)) ((T).obj w.obj)
        (congrArg (fun F => F.obj w) sqK)) b := by
  let A₀ := (restriction K).obj ((restriction Q₂).obj G)
  change (𝟙 A₀ : A₀ ⟶ A₀).total w b = _
  rw [identity_total_apply]
  have hf : @eqToHom _ _ ((Q₂).obj ((K).obj w)) ((T).obj w.obj)
      (congrArg (fun F => F.obj w) sqK) = 𝟙 ((Q₂).obj ((K).obj w)) := rfl
  rw [hf]
  exact (module_map_id_apply G _ b).symm

private def literalCross (w : ContentCategory D Sc cutoff N β) :
    (J ⋙ K).obj w ⟶ (J ⋙ K).obj w := contentBlockDistinctCross D Sc cutoff N β i i w

private theorem literalCross_eq :
    literalCross D Sc cutoff N β i = contentBlockDistinctCross D Sc cutoff N β i i := rfl

private theorem literalCross_supernatural : IsSupernatural k (D.parity i) (literalCross D Sc cutoff N β i) where
  mem w := (hGiven).mem w
  naturality hf := (hGiven).naturality hf
local notation "hCross" => literalCross_supernatural D Sc cutoff N β i

private def principalMateLiteral (R : ContentModules D Sc cutoff N (β + ([i] : Multiset I))) :
    induced J ((restriction J).obj R) ⟶ (restriction K).obj (induced K R) :=
  orderedGridMateComponent J K hCross R

private theorem principalMateLiteral_eq (R : ContentModules D Sc cutoff N (β + ([i] : Multiset I))) :
    principalMateLiteral D Sc cutoff N β i R = orderedGridMateComponent J K hGiven R :=
  gridMate_congr J K hCross hGiven (literalCross_eq D Sc cutoff N β i) R

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
theorem contentPrincipalMate_square :
    orderedGridMateComponent J K hGiven M ≫ (Target).hom =
      (Source).hom ≫ (restriction Q₁).map (orderedMateComponent T hGlobalCross P) := by
  rw [← principalMateLiteral_eq D Sc cutoff N β i M]
  change orderedGridMateComponent J K hCross M ≫ (Target).hom = _
  apply principalSquare_of_raw J K Q₀ Q₁ Q₂ T sqJ sqK hGlobalCross M
    ((restriction J).obj M) (orderedGridMateComponent J K hCross M)
    (contentAppendToRestrictionExtensionIso D Sc cutoff N β i γ hJ M)
    (contentBlockRestrictionExtension_even D Sc cutoff N β i M)
    (contentAppendToRestrictionSquare D Sc cutoff N γ [i] δ hK (induced T P))
    (restrictionSquare_map_apply D Sc cutoff N β i (induced T P))
  intro w
  have h := contentBlockMatrixMate_square D Sc cutoff N β i M w
  have hOp := module_total_congr (principalMateLiteral_eq D Sc cutoff N β i M) w
  dsimp only [orderedGridMateLinear] at h ⊢
  dsimp only [principalMateLiteral] at hOp
  rw [← hOp] at h
  exact h

end OddMath.QuiverHecke.ELVOld
