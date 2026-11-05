/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightAbsentUnitInverse
import OddMath.SKM.AugmentedInverseNaturality
import OddMath.SKM.RouquierLeftCupCap
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightCapRowFamily

/-! # Prescribed cap inversion at absent zero-height blocks

BE (1.13): an absent predecessor block in the nonnegative categorical
height range has height zero. The already constructed empty-window unit
inverse supplies the same principal inverse for the cap presentation.
Both pointwise and input-natural fields retain the prescribed maps.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELVOld
universe u
private def emptyFromTo
    {k C : Type*} [CommRing k] [Category C] [Preadditive C]
    [Linear k C] [Supercategory k C] {A B Z : C}
    {f : B ⟶ A} {u : ℕ → (Z ⟶ A)} {p : ZMod 2} {q : ℕ → ZMod 2} {m : ℕ}
    (J : SKM.SuperSumInvFrom (k := k) f u p q m) (hm : m = 0)
    (g : ℕ → (B ⟶ Z)) (hg : ∀ n, g n ∈ parity (R := k) _ _ (q n)) :
    SKM.SuperSumInvTo (k := k) f g p q 0 := by
  subst m
  exact {
    f' := J.f'
    g' := fun _ => 0
    f_mem := J.f_mem
    g_mem := hg
    f'_mem := J.f'_mem
    g'_mem := fun _ => Submodule.zero_mem _
    total := by simpa only [Finset.range_zero, Finset.sum_empty, add_zero] using J.ff
    ff := by simpa only [Finset.range_zero, Finset.sum_empty, add_zero] using J.total
    fg := fun n hn => (Nat.not_lt_zero n hn).elim
    gf := fun n hn => (Nat.not_lt_zero n hn).elim
    gg := fun n _ hn _ => (Nat.not_lt_zero n hn).elim }

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (i : I) (Λ : X) {x₀ x₁ x₂ : X}
  (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂)
  (δ : WeightBlocks D Λ x₁)
local notation "E₁" => elvE D Sc cutoff N i Λ h₁
local notation "F₁" => elvF D Sc cutoff N i Λ h₁
local notation "E₂" => elvE D Sc cutoff N i Λ h₂
local notation "F₂" => elvF D Sc cutoff N i Λ h₂
local notation "φ" => SKM.rouquierMate
  (elvActionAdjunction D Sc cutoff N i Λ h₁)
  (elvActionAdjunction D Sc cutoff N i Λ h₂)
  (elvActionCross D Sc cutoff N i i Λ h₁ h₂ h₁ h₂)
local notation "ρ" n => F₁ ◁ SKM.rouquierPower (elvActionDot D Sc cutoff N i Λ h₁) n ≫
  elvActionCounit D Sc cutoff N i Λ h₁

/-- The constructed empty-window unit inverse is also the prescribed cap
inverse at every absent block in the nonnegative-height range. -/
theorem elvWeightAbsentCapInverse_nonempty
    (hcutoff : (cutoff i : ℤ) = D.h i Λ)
    (hδ : ¬ ∃ β, blockSucc D Λ i h₁ β = δ) (hpos : 0 ≤ D.h i x₁)
    (M : ELVWeightProduct D Sc cutoff N Λ x₁) :
    Nonempty (SKM.SuperSumInvTo (k := k) ((φ).app (D.parity i) M δ)
      (fun n => (ρ n).total M δ) (D.parity i) (fun n => n • D.parity i)
      (D.h i x₁).toNat) := by
  have hz : D.h i x₁ = 0 := le_antisymm
    (elvWeightHeight_nonpos_of_absent D cutoff i Λ h₁ hcutoff δ hδ) hpos
  let J := Classical.choice (elvWeightAbsentUnitInverse_nonempty D Sc cutoff N i Λ h₁ h₂ δ hcutoff hδ M)
  have hm : (-D.h i x₁).toNat = 0 := by simp only [hz, neg_zero, Int.toNat_zero]
  have H := emptyFromTo J hm (fun n => (ρ n).total M δ)
    (fun n => (elvWeightCapPower_block_supernatural D Sc cutoff N i Λ h₁ δ n).mem M)
  exact ⟨by simpa only [hz, Int.toNat_zero] using H⟩

local notation "Ev" => CategoryTheory.Pi.eval (fun ε : WeightBlocks D Λ x₁ =>
  ContentModules D Sc cutoff N (Subtype.val ε)) δ
local notation "FE" => Superfunctor.comp (E₂ ≫ F₂) (Superfunctor.mk Ev)
local notation "EF" => Superfunctor.comp (F₁ ≫ E₁) (Superfunctor.mk Ev)
local notation "IdEv" => Superfunctor.comp
  (Superfunctor.id k (ELVWeightProduct D Sc cutoff N Λ x₁)) (Superfunctor.mk Ev)

/-- No inverse-naturality premise is needed for the absent zero-height cap family. -/
theorem elvWeightAbsentCapFamily_nonempty
    (hcutoff : (cutoff i : ℤ) = D.h i Λ)
    (hδ : ¬ ∃ β, blockSucc D Λ i h₁ β = δ) (hpos : 0 ≤ D.h i x₁) :
    Nonempty (SKM.SuperSumInvTo (k := k)
      (Superfunctor.homMk (F := EF) (G := FE)
        (elvWeightPrincipal_block_supernatural D Sc cutoff N i Λ h₁ h₂ δ).toSuperNatTrans)
      (fun n => Superfunctor.homMk (F := EF) (G := IdEv)
        (elvWeightCapPower_block_supernatural D Sc cutoff N i Λ h₁ δ n).toSuperNatTrans)
      (D.parity i) (fun n => n • D.parity i) (D.h i x₁).toNat) := by
  exact ⟨SKM.SuperSumInvTo.ofSupernaturalComponents
    (fun M => Classical.choice
      (elvWeightAbsentCapInverse_nonempty D Sc cutoff N i Λ h₁ h₂ δ hcutoff hδ hpos M))
    (elvWeightPrincipal_block_supernatural D Sc cutoff N i Λ h₁ h₂ δ)
    (elvWeightCapPower_block_supernatural D Sc cutoff N i Λ h₁ δ)⟩

end OddMath.QuiverHecke.ELVOld
