/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightSupportedLocalInverse
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightAbsentCapInverse
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightInverseProducts
import OddMath.SKM.AugmentedInverseProfile

/-! # Prescribed local inverses on entire weight fibres

BE (1.13)–(1.14): supported and absent block inverses assemble on every
output content of the categorical weight. The inverse families are then
bundled in the whole input weight module, retaining the exact native
principal, unit/power and cap/power maps of the Rouquier presentation.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELVOld
universe u
section Recovery
universe u₀ v₀ w₀
variable {k : Type w₀} {C A : Type u₀} [CommRing k]
  [Category.{v₀} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{v₀} A] [Preadditive A] [Linear k A] [Supercategory k A]
  {F G H : Superfunctor k C A} {p : ZMod 2} {q : ℕ → ZMod 2} {m : ℕ}

private theorem total_supernatural (f : F ⟶ G) (hf : f ∈ parity (R := k) F G p) :
    IsSupernatural k p (F := F.toFunctor) (G := G.toFunctor) (fun X => f.total X) := by
  simpa only [OddMath.HomogeneousSuperfunctorIso.total_eq_app f hf] using f.isSupernatural p

private theorem recover_component (f : F ⟶ G) (hf : f ∈ parity (R := k) F G p) :
    Superfunctor.homMk (F := F) (G := G) (f.isSupernatural p).toSuperNatTrans = f := by
  apply OddMath.HomogeneousSuperfunctorIso.total_ext
  intro X
  exact (OddMath.HomogeneousSuperfunctorIso.homogeneous_total (f.isSupernatural p) X).trans
    (OddMath.HomogeneousSuperfunctorIso.total_eq_app f hf X).symm

private theorem recover_total (f : F ⟶ G) (hf : f ∈ parity (R := k) F G p) :
    Superfunctor.homMk (F := F) (G := G) (total_supernatural f hf).toSuperNatTrans = f := by
  apply OddMath.HomogeneousSuperfunctorIso.total_ext
  intro X
  exact OddMath.HomogeneousSuperfunctorIso.homogeneous_total (total_supernatural f hf) X

private def exactFromFamily (f : G ⟶ F) (g : ℕ → (H ⟶ F))
    (hf : f ∈ parity (R := k) G F p) (hg : ∀ n, g n ∈ parity (R := k) H F (q n))
    (J : ∀ X, SKM.SuperSumInvFrom (k := k) (f.app p X) (fun n => (g n).total X) p q m) :
    SKM.SuperSumInvFrom (k := k) f g p q m := by
  have K := SKM.SuperSumInvFrom.ofSupernaturalComponents (k := k) (F := F) (G := G) (H := H) J (f.isSupernatural p)
    (fun n => total_supernatural (g n) (hg n))
  have heF := recover_component f hf
  have heG := funext (fun n => recover_total (g n) (hg n))
  dsimp only [Superfunctor.homMk] at K heF heG
  rw [heF, heG] at K
  exact K

private def exactToFamily (f : F ⟶ G) (g : ℕ → (F ⟶ H))
    (hf : f ∈ parity (R := k) F G p) (hg : ∀ n, g n ∈ parity (R := k) F H (q n))
    (J : ∀ X, SKM.SuperSumInvTo (k := k) (f.app p X) (fun n => (g n).total X) p q m) :
    SKM.SuperSumInvTo (k := k) f g p q m := by
  have K := SKM.SuperSumInvTo.ofSupernaturalComponents (k := k) (F := F) (G := G) (H := H) J (f.isSupernatural p)
    (fun n => total_supernatural (g n) (hg n))
  have heF := recover_component f hf
  have heG := funext (fun n => recover_total (g n) (hg n))
  dsimp only [Superfunctor.homMk] at K heF heG
  rw [heF, heG] at K
  exact K
end Recovery

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (i : I) (Λ : X) {x₀ x₁ x₂ : X}
  (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂)
local notation "E₁" => elvE D Sc cutoff N i Λ h₁
local notation "F₁" => elvF D Sc cutoff N i Λ h₁
local notation "E₂" => elvE D Sc cutoff N i Λ h₂
local notation "F₂" => elvF D Sc cutoff N i Λ h₂
local notation "φ" => SKM.rouquierMate
  (elvActionAdjunction D Sc cutoff N i Λ h₁)
  (elvActionAdjunction D Sc cutoff N i Λ h₂)
  (elvActionCross D Sc cutoff N i i Λ h₁ h₂ h₁ h₂)
local notation "U" n => elvActionUnit D Sc cutoff N i Λ h₂ ≫
  SKM.rouquierPower (elvActionDot D Sc cutoff N i Λ h₂) n ▷ F₂
local notation "CapField" n => F₁ ◁ SKM.rouquierPower (elvActionDot D Sc cutoff N i Λ h₁) n ≫
  elvActionCounit D Sc cutoff N i Λ h₁

/-- The actual given unit inverse exists on the entire weight fibre. -/
theorem elvWeightLocalUnitInverse_nonempty
    (M : ELVWeightProduct D Sc cutoff N Λ x₁)
    (hcutoff : (cutoff i : ℤ) = D.h i Λ) (hh : D.h i x₁ ≤ 0) :
    Nonempty (SKM.SuperSumInvFrom (k := k) ((φ).app (D.parity i) M)
      (fun n => (U n).total M) (D.parity i) (fun n => n • D.parity i) (-D.h i x₁).toNat) := by
  classical
  have h (δ : WeightBlocks D Λ x₁) :
      Nonempty (SKM.SuperSumInvFrom (k := k) ((φ).app (D.parity i) M δ)
        (fun n => (U n).total M δ) (D.parity i) (fun n => n • D.parity i) (-D.h i x₁).toNat) := by
    by_cases hδ : ∃ β, blockSucc D Λ i h₁ β = δ
    · rcases hδ with ⟨β, rfl⟩
      exact elvWeightSupportedUnitInverse_nonempty D Sc cutoff N i Λ h₁ h₂ β M hcutoff hh
    · exact elvWeightAbsentUnitInverse_nonempty D Sc cutoff N i Λ h₁ h₂ δ hcutoff hδ M
  exact ⟨SKM.SuperSumInvFrom.pi (fun δ => Classical.choice (h δ))⟩

/-- The given cap inverse also includes the derived absent zero-height case. -/
theorem elvWeightLocalCapInverse_nonempty
    (M : ELVWeightProduct D Sc cutoff N Λ x₁)
    (hcutoff : (cutoff i : ℤ) = D.h i Λ) (hh : 0 ≤ D.h i x₁) :
    Nonempty (SKM.SuperSumInvTo (k := k) ((φ).app (D.parity i) M)
      (fun n => (CapField n).total M) (D.parity i) (fun n => n • D.parity i) (D.h i x₁).toNat) := by
  classical
  have h (δ : WeightBlocks D Λ x₁) :
      Nonempty (SKM.SuperSumInvTo (k := k) ((φ).app (D.parity i) M δ)
        (fun n => (CapField n).total M δ) (D.parity i) (fun n => n • D.parity i) (D.h i x₁).toNat) := by
    by_cases hδ : ∃ β, blockSucc D Λ i h₁ β = δ
    · rcases hδ with ⟨β, rfl⟩
      exact elvWeightSupportedCapInverse_nonempty D Sc cutoff N i Λ h₁ h₂ β M hcutoff hh
    · exact elvWeightAbsentCapInverse_nonempty D Sc cutoff N i Λ h₁ h₂ δ hcutoff hδ hh M
  exact ⟨SKM.SuperSumInvTo.pi (fun δ => Classical.choice (h δ))⟩

/-- Literal upper unit/power fields have the whole Rouquier shift profile. -/
theorem elvWeightUnitPower_mem (n : ℕ) :
    (U n) ∈ parity (R := k) _ _ (n • D.parity i) := by
  have hu : elvActionUnit D Sc cutoff N i Λ h₂ ∈ parity (R := k) _ _ 0 :=
    (elvActionAdjunction D Sc cutoff N i Λ h₂).unit_mem
  have hd := SKM.rouquierPower_mem (elvActionDot_mem D Sc cutoff N i Λ h₂) n
  simpa only [zero_add, nsmul_eq_mul] using comp_mem hu (TwoSupercategory.whiskerRight_mem F₂ hd)

/-- The whole input-natural unit inverse retains the exact selected native fields. -/
theorem elvWeightLocalUnitFamily_nonempty
    (hcutoff : (cutoff i : ℤ) = D.h i Λ) (hh : D.h i x₁ ≤ 0) :
    Nonempty (SKM.SuperSumInvFrom (k := k) (φ) (fun n => U n)
      (D.parity i) (fun n => (n : ZMod 2) * D.parity i) (-D.h i x₁).toNat) := by
  exact ⟨(exactFromFamily (φ) (fun n => U n)
    (elvWeightRouquierMate_mem D Sc cutoff N i Λ h₁ h₂)
    (elvWeightUnitPower_mem D Sc cutoff N i Λ h₂)
    (fun M => Classical.choice
      (elvWeightLocalUnitInverse_nonempty D Sc cutoff N i Λ h₁ h₂ M hcutoff hh))).mulProfile⟩

/-- The whole input-natural cap inverse retains the exact selected native fields. -/
theorem elvWeightLocalCapFamily_nonempty
    (hcutoff : (cutoff i : ℤ) = D.h i Λ) (hh : 0 ≤ D.h i x₁) :
    Nonempty (SKM.SuperSumInvTo (k := k) (φ) (fun n => CapField n)
      (D.parity i) (fun n => (n : ZMod 2) * D.parity i) (D.h i x₁).toNat) := by
  exact ⟨(exactToFamily (φ) (fun n => CapField n)
    (elvWeightRouquierMate_mem D Sc cutoff N i Λ h₁ h₂)
    (elvWeightCapPower_mem D Sc cutoff N i Λ h₁)
    (fun M => Classical.choice
      (elvWeightLocalCapInverse_nonempty D Sc cutoff N i Λ h₁ h₂ M hcutoff hh))).mulProfile⟩

end OddMath.QuiverHecke.ELVOld
