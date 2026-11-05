/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightAbsentUnitInverse
import OddMath.SKM.AugmentedInverseNaturality
import OddMath.SKM.RouquierLeftCupCap

/-! # Input-natural weight unit inverses on absent blocks

BE (1.14): all inverse entries on a block without a lower predecessor
are supernatural in the whole input weight module. Naturality follows
from the selected homogeneous principal field and literal unit/powers,
with no naturality assumption on a chosen inverse.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELVOld
universe u
private theorem homogeneousTotal_postcompose
    {k C D E : Type*} [CommRing k]
    [Category C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category D] [Preadditive D] [Linear k D] [Supercategory k D]
    [Category E] [Preadditive E] [Linear k E] [Supercategory k E]
    {F G : Superfunctor k C D} {p : ZMod 2}
    (τ : F ⟶ G) (hτ : τ ∈ parity (R := k) F G p)
    (R : D ⥤ E) [R.Additive] [R.Linear k] [IsSuperfunctor k R] :
    IsSupernatural k p (F := F.toFunctor ⋙ R) (G := G.toFunctor ⋙ R)
      (fun M => R.map (τ.total M)) := by
  simpa only [OddMath.HomogeneousSuperfunctorIso.total_eq_app τ hτ] using
    (τ.isSupernatural p).whiskerRight R

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (i : I) (Λ : X) {x₀ x₁ x₂ : X}
  (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂)
  (δ : WeightBlocks D Λ x₁)
local notation "E₁" => elvE D Sc cutoff N i Λ h₁
local notation "F₁" => elvF D Sc cutoff N i Λ h₁
local notation "E₂" => elvE D Sc cutoff N i Λ h₂
local notation "F₂" => elvF D Sc cutoff N i Λ h₂
local notation "Ev" => CategoryTheory.Pi.eval (fun ε : WeightBlocks D Λ x₁ =>
  ContentModules D Sc cutoff N (Subtype.val ε)) δ
local notation "FE" => Superfunctor.comp (E₂ ≫ F₂) (Superfunctor.mk Ev)
local notation "EF" => Superfunctor.comp (F₁ ≫ E₁) (Superfunctor.mk Ev)
local notation "IdEv" => Superfunctor.comp
  (Superfunctor.id k (ELVWeightProduct D Sc cutoff N Λ x₁)) (Superfunctor.mk Ev)
local notation "φ" => SKM.rouquierMate
  (elvActionAdjunction D Sc cutoff N i Λ h₁)
  (elvActionAdjunction D Sc cutoff N i Λ h₂)
  (elvActionCross D Sc cutoff N i i Λ h₁ h₂ h₁ h₂)
local notation "τ" n => elvActionUnit D Sc cutoff N i Λ h₂ ≫
  SKM.rouquierPower (elvActionDot D Sc cutoff N i Λ h₂) n ▷ F₂

end OddMath.QuiverHecke.ELVOld
