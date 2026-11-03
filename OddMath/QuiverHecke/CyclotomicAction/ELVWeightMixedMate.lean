/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightCrossingComparison
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightSuperAdjunction
import OddMath.QuiverHecke.CyclotomicAction.ELVPiSCatRectangularMate

/-! # The prescribed mixed mate on original weight products

For Brundan–Ellis (1.12), bend the selected weight crossing by the lower
and upper j-adjunctions. The positive distinct crossing has reversed
indices in `elvActionCross`, because induction is contravariant in the
affine crossing. At an output without an i-predecessor, both actual
mixed-functor coordinates vanish, including the target after adding j.
-/
noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELVOld
universe u
private theorem isIso_between_zero
    {C : Type*} [Category C] [Limits.HasZeroMorphisms C] {M P : C} (f : M ⟶ P)
    (hM : Limits.IsZero M) (hP : Limits.IsZero P) : IsIso f := by
  let : Limits.HasZeroObject C := ⟨⟨M, hM⟩⟩
  rw [hM.eq_of_src f 0]
  exact (Limits.isIsoZero_iff_source_target_isZero M P).mpr ⟨hM, hP⟩

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (i j : I) (Λ : X) {x₀ xj xi xu : X}
  (h₁ : x₀ + D.α j = xj) (h₂ : xj + D.α i = xu)
  (h₃ : x₀ + D.α i = xi) (h₄ : xi + D.α j = xu)
local notation "Ei₀" => elvE D Sc cutoff bound i Λ h₃
local notation "Ei₁" => elvE D Sc cutoff bound i Λ h₂
local notation "Fj₀" => elvF D Sc cutoff bound j Λ h₁
local notation "Fj₁" => elvF D Sc cutoff bound j Λ h₄
local notation "Adj₀" => elvActionAdjunction D Sc cutoff bound j Λ h₁
local notation "Adj₁" => elvActionAdjunction D Sc cutoff bound j Λ h₄
local notation "Cross" => elvActionCross D Sc cutoff bound j i Λ h₃ h₄ h₁ h₂

/-- The actual weight-space cup, selected crossing, and cap. -/
def elvWeightMixedMate : Fj₀ ≫ Ei₀ ⟶ Ei₁ ≫ Fj₁ :=
  SKM.rectangularMate Adj₀ Adj₁ Ei₀ Ei₁ Cross

/-- The given weight mate retains the selected crossing degree. -/
theorem elvWeightMixedMate_mem :
    elvWeightMixedMate D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄ ∈
      parity (R := k) _ _ (D.parity i * D.parity j) := by
  have h := SKM.rectangularMate_piscat_mem Adj₀ Adj₁ Ei₀ Ei₁ Cross
    (elvActionCross_mem D Sc cutoff bound j i Λ h₃ h₄ h₁ h₂)
  simpa only [elvWeightMixedMate, mul_comm] using h

/-- Both j-adjunctions remain at their actual, different weight corners. -/
theorem elvWeightMixedMate_app (p : ZMod 2) (M : ELVWeightProduct D Sc cutoff bound Λ xj) :
    (elvWeightMixedMate D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄).app p M =
      (elvActionUnit D Sc cutoff bound j Λ h₄).app 0 ((Ei₀).obj ((Fj₀).obj M)) ≫
        (Fj₁).map ((Cross).app p ((Fj₀).obj M)) ≫
          (Fj₁).map ((Ei₁).map ((elvActionCounit D Sc cutoff bound j Λ h₁).app 0 M)) :=
  SKM.rectangularMate_piscat_app Adj₀ Adj₁ Ei₀ Ei₁ Cross
    (fun W => Superfunctor.app_eq_zero_of_mem (Adj₁).unit_mem (by decide) W)
    (fun W => Superfunctor.app_eq_zero_of_mem (Adj₀).counit_mem (by decide) W) p M

/-- Adding j preserves the existence of an i-predecessor when the colours differ. -/
theorem elvMixedPredecessor_iff (hij : i ≠ j) (δ : WeightBlocks D Λ xi) :
    (∃ γ, blockSucc D Λ i h₂ γ = blockSucc D Λ j h₄ δ) ↔
      ∃ β, blockSucc D Λ i h₃ β = δ := by
  rw [exists_blockSucc_iff, exists_blockSucc_iff]
  simp only [blockSucc_val, Multiset.mem_add, Multiset.mem_singleton]
  constructor
  · rintro (h | h)
    · exact (hij h).elim
    · exact h
  · exact Or.inr

/-- The actual source coordinate is zero at an absent i-predecessor. -/
theorem elvWeightMixedSource_isZero (δ : WeightBlocks D Λ xi)
    (hδ : ¬ ∃ β, blockSucc D Λ i h₃ β = δ)
    (M : ELVWeightProduct D Sc cutoff bound Λ xj) :
    Limits.IsZero (((Fj₀ ≫ Ei₀).obj M) δ) :=
  elvInductionComponent_isZero D Sc cutoff bound i Λ h₃ δ hδ ((Fj₀).obj M)

/-- The actual target coordinate also vanishes; adding j does not create i. -/
theorem elvWeightMixedTarget_isZero (hij : i ≠ j) (δ : WeightBlocks D Λ xi)
    (hδ : ¬ ∃ β, blockSucc D Λ i h₃ β = δ)
    (M : ELVWeightProduct D Sc cutoff bound Λ xj) :
    Limits.IsZero (((Ei₁ ≫ Fj₁).obj M) δ) := by
  have hUpper : ¬ ∃ γ, blockSucc D Λ i h₂ γ = blockSucc D Λ j h₄ δ :=
    fun h => hδ ((elvMixedPredecessor_iff D i j Λ h₂ h₃ h₄ hij δ).mp h)
  have hZero := elvInductionComponent_isZero D Sc cutoff bound i Λ h₂
    (blockSucc D Λ j h₄ δ) hUpper M
  exact (elvBlockRes D Sc cutoff bound j Λ h₄ δ).toFunctor.map_isZero hZero

/-- The prescribed mate is already invertible on every genuine absent output sector. -/
theorem elvWeightMixedMate_absent_isIso (hij : i ≠ j) (δ : WeightBlocks D Λ xi)
    (hδ : ¬ ∃ β, blockSucc D Λ i h₃ β = δ)
    (p : ZMod 2) (M : ELVWeightProduct D Sc cutoff bound Λ xj) :
    IsIso ((elvWeightMixedMate D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄).app p M δ) :=
  isIso_between_zero _
    (elvWeightMixedSource_isZero D Sc cutoff bound i j Λ h₁ h₃ δ hδ M)
    (elvWeightMixedTarget_isZero D Sc cutoff bound i j Λ h₂ h₃ h₄ hij δ hδ M)

end OddMath.QuiverHecke.ELVOld
