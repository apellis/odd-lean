/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightLocalMate
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightDot
import OddMath.Algebra.HomogeneousSuperfunctorIso
import OddMath.SKM.RouquierLeftCupCap

/-! # Input naturality of prescribed weight cap rows

BE (1.13): the literal lower dot-power/counit rows retain their signed
naturality in every whole input weight module. This is the forward row
family needed to bundle the local positive-height inverse.
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
  (i : I) (Λ : X) {x₀ x₁ : X}
  (h : x₀ + D.α i = x₁) (δ : WeightBlocks D Λ x₁)
local notation "E₁" => elvE D Sc cutoff N i Λ h
local notation "F₁" => elvF D Sc cutoff N i Λ h
local notation "Ev" => CategoryTheory.Pi.eval (fun ε : WeightBlocks D Λ x₁ =>
  ContentModules D Sc cutoff N (Subtype.val ε)) δ
local notation "EF" => Superfunctor.comp (F₁ ≫ E₁) (Superfunctor.mk Ev)
local notation "IdEv" => Superfunctor.comp
  (Superfunctor.id k (ELVWeightProduct D Sc cutoff N Λ x₁)) (Superfunctor.mk Ev)
local notation "ρ" n => F₁ ◁ SKM.rouquierPower (elvActionDot D Sc cutoff N i Λ h) n ≫
  elvActionCounit D Sc cutoff N i Λ h

/-- Every lower cap/power total has its required homogeneous row degree. -/
theorem elvWeightCapPower_mem (n : ℕ) :
    (ρ n) ∈ parity (R := k) _ _ (n • D.parity i) := by
  have hc : elvActionCounit D Sc cutoff N i Λ h ∈ parity (R := k) _ _ 0 :=
    (elvActionAdjunction D Sc cutoff N i Λ h).counit_mem
  have hd := SKM.rouquierPower_mem (elvActionDot_mem D Sc cutoff N i Λ h) n
  simpa only [add_zero, nsmul_eq_mul] using
    comp_mem (TwoSupercategory.whiskerLeft_mem F₁ hd) hc

/-- Literal cap/power rows preserve odd input-module naturality after output evaluation. -/
theorem elvWeightCapPower_block_supernatural (n : ℕ) :
    IsSupernatural k (n • D.parity i) (F := (EF).toFunctor) (G := (IdEv).toFunctor)
      (fun M => (ρ n).total M δ) :=
  homogeneousTotal_postcompose (ρ n) (elvWeightCapPower_mem D Sc cutoff N i Λ h n) Ev

end OddMath.QuiverHecke.ELVOld
