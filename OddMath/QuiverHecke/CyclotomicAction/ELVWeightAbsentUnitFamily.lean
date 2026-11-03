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

/-- The prescribed principal field is supernatural after output-block evaluation. -/
theorem elvWeightPrincipal_block_supernatural :
    IsSupernatural k (D.parity i) (F := (EF).toFunctor) (G := (FE).toFunctor)
      (fun M => (φ).app (D.parity i) M δ) :=
  ((φ).isSupernatural (D.parity i)).whiskerRight Ev

/-- Literal upper unit/power totals retain every odd input naturality sign. -/
theorem elvWeightUnitPower_block_supernatural (n : ℕ) :
    IsSupernatural k (n • D.parity i) (F := (IdEv).toFunctor) (G := (FE).toFunctor)
      (fun M => (τ n).total M δ) := by
  have hu : elvActionUnit D Sc cutoff N i Λ h₂ ∈ parity (R := k) _ _ 0 :=
    (elvActionAdjunction D Sc cutoff N i Λ h₂).unit_mem
  have hd := SKM.rouquierPower_mem (elvActionDot_mem D Sc cutoff N i Λ h₂) n
  have ht : (τ n) ∈ parity (R := k) _ _ (n • D.parity i) := by
    simpa only [zero_add, nsmul_eq_mul] using comp_mem hu (TwoSupercategory.whiskerRight_mem F₂ hd)
  exact homogeneousTotal_postcompose (τ n) ht Ev

/-- The constructed absent-block inverse bundles on all input weight modules. -/
theorem elvWeightAbsentUnitFamily_nonempty
    (hcutoff : (cutoff i : ℤ) = D.h i Λ)
    (hδ : ¬ ∃ β, blockSucc D Λ i h₁ β = δ) :
    Nonempty (SKM.SuperSumInvFrom (k := k)
      (Superfunctor.homMk (F := EF) (G := FE)
        (elvWeightPrincipal_block_supernatural D Sc cutoff N i Λ h₁ h₂ δ).toSuperNatTrans)
      (fun n => Superfunctor.homMk (F := IdEv) (G := FE)
        (elvWeightUnitPower_block_supernatural D Sc cutoff N i Λ h₂ δ n).toSuperNatTrans)
      (D.parity i) (fun n => n • D.parity i) (-D.h i x₁).toNat) := by
  exact ⟨SKM.SuperSumInvFrom.ofSupernaturalComponents
    (fun M => Classical.choice
      (elvWeightAbsentUnitInverse_nonempty D Sc cutoff N i Λ h₁ h₂ δ hcutoff hδ M))
    (elvWeightPrincipal_block_supernatural D Sc cutoff N i Λ h₁ h₂ δ)
    (elvWeightUnitPower_block_supernatural D Sc cutoff N i Λ h₂ δ)⟩

end OddMath.QuiverHecke.ELVOld
