/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVContentSupportedLocalInverse
import OddMath.SKM.AugmentedInverseNaturality

/-! # Principal inverse coordinates on supported content blocks

BE (1.13)–(1.14): the prescribed finite forward fields determine the principal inverse.
This compares every constructed content local record with the existing
weighted matrix inverse through the selected source and target charts,
without assuming a comparison of inverses or unfolding a choice.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open BalancedInduction CyclotomicCrossingTensor
universe u
section Uniqueness
variable {k : Type u} [CommRing k] {C : Type*} [Category C]
  [Preadditive C] [Linear k C] [Supercategory k C]
  {A B Z : C} {p : ZMod 2} {q : ℕ → ZMod 2} {n : ℕ}
private theorem principalFrom_coordinates {A' B' Z' : C}
    {f : B ⟶ A} {g : ℕ → (Z ⟶ A)} {F : B' ⟶ A'} {G : ℕ → (Z' ⟶ A')}
    (L : SKM.SuperSumInvFrom (k := k) f g p q n)
    (R : SKM.SuperSumInvFrom (k := k) F G p q n)
    (a : A ≅ A') (b : B ≅ B') (c : Z ≅ Z')
    (hf : b.hom ≫ F ≫ a.inv = f) (hg : ∀ m, c.hom ≫ G m ≫ a.inv = g m) :
    L.f' = a.hom ≫ R.f' ≫ b.inv := by
  symm
  apply L.hom_ext
  · calc
      f ≫ (a.hom ≫ R.f' ≫ b.inv) = b.hom ≫ (F ≫ R.f') ≫ b.inv := by
        rw [← hf]
        simp only [Category.assoc, Iso.inv_hom_id_assoc]
      _ = f ≫ L.f' := by rw [R.ff, Category.id_comp, b.hom_inv_id, L.ff]
  · intro m hm
    calc
      g m ≫ (a.hom ≫ R.f' ≫ b.inv) = c.hom ≫ (G m ≫ R.f') ≫ b.inv := by
        rw [← hg m]
        simp only [Category.assoc, Iso.inv_hom_id_assoc]
      _ = g m ≫ L.f' := by rw [R.gf m hm, Limits.zero_comp, Limits.comp_zero, L.gf m hm]
private theorem principalTo_coordinates {A' B' Z' : C}
    {f : A ⟶ B} {g : ℕ → (A ⟶ Z)} {F : A' ⟶ B'} {G : ℕ → (A' ⟶ Z')}
    (L : SKM.SuperSumInvTo (k := k) f g p q n)
    (R : SKM.SuperSumInvTo (k := k) F G p q n)
    (a : A ≅ A') (b : B ≅ B') (c : Z ≅ Z')
    (hf : a.hom ≫ F ≫ b.inv = f) (hg : ∀ m, a.hom ≫ G m ≫ c.inv = g m) :
    L.f' = b.hom ≫ R.f' ≫ a.inv := by
  symm
  apply L.hom_ext
  · calc
      (b.hom ≫ R.f' ≫ a.inv) ≫ f = b.hom ≫ (R.f' ≫ F) ≫ b.inv := by
        rw [← hf]
        simp only [Category.assoc, Iso.inv_hom_id_assoc]
      _ = L.f' ≫ f := by rw [R.ff, Category.id_comp, b.hom_inv_id, L.ff]
  · intro m hm
    calc
      (b.hom ≫ R.f' ≫ a.inv) ≫ g m = b.hom ≫ (R.f' ≫ G m) ≫ c.inv := by
        rw [← hg m]
        simp only [Category.assoc, Iso.inv_hom_id_assoc]
      _ = L.f' ≫ g m := by rw [R.fg m hm, Limits.zero_comp, Limits.comp_zero, L.fg m hm]
end Uniqueness

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

/-- The selected lower-loop chart, for the stored successor content. -/
def contentPrincipalSourceIso (β γ : Multiset I) (i : I)
    (hγ : β + ([i] : Multiset I) = γ) (M : ContentModules D Sc cutoff N γ) :=
  let J := contentAppendTo D Sc cutoff N β [i] γ hγ
  let Q₀ := contentInclusion D Sc cutoff N β
  let Q₁ := contentInclusion D Sc cutoff N γ
  let T := truncatedAppend D Sc cutoff N [i]
  let P := induced Q₁ M
  fullSquareSourceIso J Q₁ Q₀ T (contentAppendTo_inclusion D Sc cutoff N β [i] γ hγ)
    (Functor.obj (restriction J) M) (Functor.obj (restriction T) P)
    (contentAppendToRestrictionExtensionIso D Sc cutoff N β i γ hγ M)

/-- The selected upper-loop chart, for the stored successor content. -/
def contentPrincipalTargetIso (γ δ : Multiset I) (i : I)
    (hδ : γ + ([i] : Multiset I) = δ) (M : ContentModules D Sc cutoff N γ) :=
  let K := contentAppendTo D Sc cutoff N γ [i] δ hδ
  let Q₁ := contentInclusion D Sc cutoff N γ
  let Q₂ := contentInclusion D Sc cutoff N δ
  let T := truncatedAppend D Sc cutoff N [i]
  let P := induced Q₁ M
  let FE := Functor.obj (restriction T) (induced T P)
  fullSquareTargetRetargetIso K Q₂ Q₁ T (contentAppendTo_inclusion D Sc cutoff N γ [i] δ hδ)
    M FE FE (contentAppendToRestrictionSquare D Sc cutoff N γ [i] δ hδ (induced T P)) (Iso.refl FE)

section Canonical
variable (β : Multiset I) (i : I)
local notation "γ" => β + ([i] : Multiset I)
local notation "δ" => γ + ([i] : Multiset I)
local notation "hJ" => contentBlockCanonicalSum β [i]
local notation "hK" => contentBlockCanonicalSum γ [i]
local notation "J" => contentAppendTo D Sc cutoff N β [i] γ hJ
local notation "K" => contentAppendTo D Sc cutoff N γ [i] δ hK
local notation "Q₁" => contentInclusion D Sc cutoff N γ
local notation "T" => truncatedAppend D Sc cutoff N [i]
local notation "hCross" => contentBlockMatrixCross_supernatural D Sc cutoff N β i
local notation "hDotJ" => contentBlockMatrixDot_supernatural D Sc cutoff N β i
local notation "hDotK" => contentBlockMatrixDot_supernatural D Sc cutoff N γ i
variable (M : ContentModules D Sc cutoff N (β + ([i] : Multiset I)))
local notation "P" => induced Q₁ M
local notation "Source" => contentPrincipalSourceIso D Sc cutoff N β γ i hJ M
local notation "Target" => contentPrincipalTargetIso D Sc cutoff N γ δ i hK M
local notation "Value" => contentExtensionUnitIso D Sc cutoff N γ M

/-- Every unit-orientation local record with the prescribed forward
fields has the principal of the given weighted inverse in these charts. -/
theorem contentSupportedLocalInverseFrom_principal
    (L : SKM.SuperSumInvFrom (k := k) (orderedGridMateComponent J K hCross M)
      (unitDotColumn K hDotK M) (D.parity i) (fun n => n • D.parity i)
      (contentUnitCount D cutoff i γ))
    (hh : 0 ≤ contentCrossingHeight D cutoff i γ) :
    L.f' = (Target).hom ≫ (weightedContentLocalInverseFrom D Sc cutoff N i P γ hh).f' ≫ (Source).inv := by
  let B := weightedContentLocalInverseFrom D Sc cutoff N i P γ hh
  let a := Target
  let b := Source
  let c := Value
  have hf : b.hom ≫ (𝟭 (ContentModules D Sc cutoff N γ)).map
      ((restriction Q₁).map (weightedMatrixMate D Sc cutoff N i P)) ≫ a.inv =
      orderedGridMateComponent J K hCross M := by
    have hs := contentPrincipalMate_square D Sc cutoff N β i M
    rw [← weightedMatrixMate_eq_ordered D Sc cutoff N i P] at hs
    have he := congrArg (fun f => f ≫ a.inv) hs
    dsimp only [a, b, c, contentPrincipalSourceIso, contentPrincipalTargetIso] at he ⊢
    simpa only [Functor.id_map, Category.assoc, Iso.hom_inv_id, Category.comp_id] using he.symm
  have hg (n : ℕ) : c.hom ≫ (𝟭 (ContentModules D Sc cutoff N γ)).map
      ((restriction Q₁).map (unitDotColumn T (truncatedDot_supernatural D Sc cutoff N i) P n)) ≫ a.inv =
      unitDotColumn K hDotK M n := by
    have hs := contentUnitDotColumn_square D Sc cutoff N γ i M n
    have he := congrArg (fun f => f ≫ a.inv) hs
    dsimp only [a, b, c, contentPrincipalTargetIso] at he ⊢
    simpa only [Functor.id_map, Category.assoc, Iso.hom_inv_id, Category.comp_id] using he.symm
  exact principalFrom_coordinates L B a b c hf hg

/-- Every cap-orientation record has the same prescribed weighted
principal, independently of how the record was chosen. -/
theorem contentSupportedLocalInverseTo_principal
    (L : SKM.SuperSumInvTo (k := k) (orderedGridMateComponent J K hCross M)
      (capDotRow J hDotJ M) (D.parity i) (fun n => n • D.parity i)
      (contentCapCount D cutoff i γ))
    (hh : contentCrossingHeight D cutoff i γ ≤ 0) :
    L.f' = (Target).hom ≫ (weightedContentLocalInverseTo D Sc cutoff N i P γ hh).f' ≫ (Source).inv := by
  let B := weightedContentLocalInverseTo D Sc cutoff N i P γ hh
  let a := Source
  let b := Target
  let c := Value
  have hf : a.hom ≫ (𝟭 (ContentModules D Sc cutoff N γ)).map
      ((restriction Q₁).map (weightedMatrixMate D Sc cutoff N i P)) ≫ b.inv =
      orderedGridMateComponent J K hCross M := by
    have hs := contentPrincipalMate_square D Sc cutoff N β i M
    rw [← weightedMatrixMate_eq_ordered D Sc cutoff N i P] at hs
    have he := congrArg (fun f => f ≫ b.inv) hs
    dsimp only [a, b, c, contentPrincipalSourceIso, contentPrincipalTargetIso] at he ⊢
    simpa only [Functor.id_map, Category.assoc, Iso.hom_inv_id, Category.comp_id] using he.symm
  have hg (n : ℕ) : a.hom ≫ (𝟭 (ContentModules D Sc cutoff N γ)).map
      ((restriction Q₁).map (capDotRow T (truncatedDot_supernatural D Sc cutoff N i) P n)) ≫ c.inv =
      capDotRow J hDotJ M n := by
    have hs := contentMatrixCapDotRow_square D Sc cutoff N β i M n
    have he := congrArg (fun f => f ≫ c.inv) hs
    dsimp only [a, b, c, contentPrincipalSourceIso] at he ⊢
    simpa only [Functor.id_map, Category.assoc, Iso.hom_inv_id, Category.comp_id] using he.symm
  exact principalTo_coordinates L B a b c hf hg
end Canonical

private theorem principalSingletonDot_mem (i : I) :
    dotE D Sc [i] 0 ∈ parity (R := k) _ _ (D.parity i) := by
  simpa only [pow_one, one_nsmul] using firstDot_pow_parity D Sc i [] 1

section Targets
variable (β : Multiset I) (i : I) (γ δ : Multiset I)
  (hγ : β + ([i] : Multiset I) = γ) (hδ : γ + ([i] : Multiset I) = δ)
  (M : ContentModules D Sc cutoff N γ)
local notation "J" => contentAppendTo D Sc cutoff N β [i] γ hγ
local notation "K" => contentAppendTo D Sc cutoff N γ [i] δ hδ
local notation "hCross" => contentTargetsGridCross_supernatural D Sc cutoff N β γ δ i hγ hδ
local notation "hDotJ" => contentAppendTo_supernatural D Sc cutoff N hγ hγ
  (principalSingletonDot_mem D Sc i)
local notation "hDotK" => contentAppendTo_supernatural D Sc cutoff N hδ hδ
  (principalSingletonDot_mem D Sc i)
local notation "P" => induced (contentInclusion D Sc cutoff N γ) M
local notation "Source" => contentPrincipalSourceIso D Sc cutoff N β γ i hγ M
local notation "Target" => contentPrincipalTargetIso D Sc cutoff N γ δ i hδ M

end Targets

end OddMath.QuiverHecke.ELVOld
