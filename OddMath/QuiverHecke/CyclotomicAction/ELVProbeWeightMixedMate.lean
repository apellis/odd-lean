import OddMath.QuiverHecke.CyclotomicAction.ELVProbeRouquierData
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeReindexDistinctMate

/-! # The selected OLD probe weight mixed mate

Brundan–Ellis (1.12): bend the selected weight crossing by the actual
lower and upper right adjunctions. A missing lower-i predecessor makes
both mixed-functor coordinates zero when the colours differ.
-/
noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELVOld CyclotomicAction
universe u

private theorem iso_between_zero
    {C : Type*} [Category C] [Limits.HasZeroMorphisms C] {M P : C} (f : M ⟶ P)
    (hM : Limits.IsZero M) (hP : Limits.IsZero P) : IsIso f := by
  let : Limits.HasZeroObject C := ⟨⟨M, hM⟩⟩
  rw [hM.eq_of_src f 0]
  exact (Limits.isIsoZero_iff_source_target_isZero M P).mpr ⟨hM, hP⟩

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (i j : I) (Λ : X) {x₀ xj xi xu : X}
  (h₁ : x₀ + D.α j = xj) (h₂ : xj + D.α i = xu)
  (h₃ : x₀ + D.α i = xi) (h₄ : xi + D.α j = xu)
local notation "Ei₀" => probeOldE D Sc m i Λ h₃
local notation "Ei₁" => probeOldE D Sc m i Λ h₂
local notation "Fj₀" => probeOldF D Sc m j Λ h₁
local notation "Fj₁" => probeOldF D Sc m j Λ h₄
local notation "Adj₀" => probeOldActionAdjunction D Sc m j Λ h₁
local notation "Adj₁" => probeOldActionAdjunction D Sc m j Λ h₄
local notation "Cross" => probeOldActionCross D Sc m Λ j i h₃ h₄ h₁ h₂

/-- The actual product-weight cup, selected crossing and cap. -/
def probeOldWeightMixedMate : Fj₀ ≫ Ei₀ ⟶ Ei₁ ≫ Fj₁ :=
  SKM.rectangularMate Adj₀ Adj₁ Ei₀ Ei₁ Cross

theorem probeOldWeightMixedMate_mem :
    probeOldWeightMixedMate D Sc m i j Λ h₁ h₂ h₃ h₄ ∈ parity (R := k) _ _
      (D.parity i * D.parity j) := by
  have h := SKM.rectangularMate_piscat_mem Adj₀ Adj₁ Ei₀ Ei₁ Cross
    (probeOldActionCross_mem D Sc m Λ j i h₃ h₄ h₁ h₂)
  simpa only [probeOldWeightMixedMate, mul_comm] using h

/-- Both adjunctions retain their different weight corners. -/
theorem probeOldWeightMixedMate_app (p : ZMod 2) (M : ProbeOldWeightProduct D Sc m Λ xj) :
    (probeOldWeightMixedMate D Sc m i j Λ h₁ h₂ h₃ h₄).app p M =
      (Adj₁).unit.app 0 ((Ei₀).obj ((Fj₀).obj M)) ≫
        (Fj₁).map ((Cross).app p ((Fj₀).obj M)) ≫
          (Fj₁).map ((Ei₁).map ((Adj₀).counit.app 0 M)) :=
  SKM.rectangularMate_piscat_app Adj₀ Adj₁ Ei₀ Ei₁ Cross
    (fun W => Superfunctor.app_eq_zero_of_mem (Adj₁).unit_mem (by decide) W)
    (fun W => Superfunctor.app_eq_zero_of_mem (Adj₀).counit_mem (by decide) W) p M

/-- Every output coordinate keeps the selected weight cup, crossing and cap. -/
theorem probeOldWeightMixedMate_app_block (p : ZMod 2)
    (M : ProbeOldWeightProduct D Sc m Λ xj) (δ : WeightBlocks D Λ xi) :
    (probeOldWeightMixedMate D Sc m i j Λ h₁ h₂ h₃ h₄).app p M δ =
      (probeOldWeightUnitApp D Sc m j Λ h₄ δ ((Ei₀).obj ((Fj₀).obj M)) ≫
        (probeOldBlockRes D Sc m j Λ h₄ δ).map
          ((Cross).app p ((Fj₀).obj M) (blockSucc D Λ j h₄ δ))) ≫
        (probeOldBlockRes D Sc m j Λ h₄ δ).map
          ((probeOldInductionComponent D Sc m i Λ h₂ (blockSucc D Λ j h₄ δ)).map
            ((probeOldWeightCounit D Sc m j Λ h₁).app M)) := by
  have h := congrFun (probeOldWeightMixedMate_app D Sc m i j Λ h₁ h₂ h₃ h₄ p M) δ
  dsimp only [probeOldActionAdjunction, ordinaryEvenSuperAdjunction, probeOldWeightAdjunction,
    SuperNatTrans.ofNatTrans, probeOldWeightUnit, probeOldF, probeOldE, probeOldEFunctor,
    productFunctor, Superfunctor.map, Superfunctor.obj] at h ⊢
  simp only [Pi.comp_apply] at h
  dsimp only [Functor.pi'] at h
  exact h.trans (Category.assoc _ _ _).symm

/-- Adding j does not create a missing i-predecessor at distinct colours. -/
theorem probeOldMixedPredecessor_iff (hij : i ≠ j) (δ : WeightBlocks D Λ xi) :
    (∃ γ, blockSucc D Λ i h₂ γ = blockSucc D Λ j h₄ δ) ↔
      ∃ β, blockSucc D Λ i h₃ β = δ := by
  rw [exists_blockSucc_iff, exists_blockSucc_iff]
  simp only [blockSucc_val, Multiset.mem_add, Multiset.mem_singleton]
  constructor
  · rintro (h | h)
    · exact (hij h).elim
    · exact h
  · exact Or.inr

theorem probeOldWeightMixedSource_isZero (δ : WeightBlocks D Λ xi)
    (hδ : ¬ ∃ β, blockSucc D Λ i h₃ β = δ) (M : ProbeOldWeightProduct D Sc m Λ xj) :
    Limits.IsZero (((Fj₀ ≫ Ei₀).obj M) δ) :=
  probeOldInductionComponent_isZero D Sc m i Λ h₃ δ hδ ((Fj₀).obj M)

theorem probeOldWeightMixedTarget_isZero (hij : i ≠ j) (δ : WeightBlocks D Λ xi)
    (hδ : ¬ ∃ β, blockSucc D Λ i h₃ β = δ) (M : ProbeOldWeightProduct D Sc m Λ xj) :
    Limits.IsZero (((Ei₁ ≫ Fj₁).obj M) δ) := by
  have hUpper : ¬ ∃ γ, blockSucc D Λ i h₂ γ = blockSucc D Λ j h₄ δ :=
    fun h => hδ ((probeOldMixedPredecessor_iff D i j Λ h₂ h₃ h₄ hij δ).mp h)
  have hZero := probeOldInductionComponent_isZero D Sc m i Λ h₂
    (blockSucc D Λ j h₄ δ) hUpper M
  exact (probeOldBlockRes D Sc m j Λ h₄ δ).toFunctor.map_isZero hZero

/-- The prescribed sideways crossing is invertible on every absent output sector. -/
theorem probeOldWeightMixedMate_absent_isIso (hij : i ≠ j) (δ : WeightBlocks D Λ xi)
    (hδ : ¬ ∃ β, blockSucc D Λ i h₃ β = δ) (p : ZMod 2)
    (M : ProbeOldWeightProduct D Sc m Λ xj) :
    IsIso ((probeOldWeightMixedMate D Sc m i j Λ h₁ h₂ h₃ h₄).app p M δ) :=
  iso_between_zero _
    (probeOldWeightMixedSource_isZero D Sc m i j Λ h₁ h₃ δ hδ M)
    (probeOldWeightMixedTarget_isZero D Sc m i j Λ h₂ h₃ h₄ hij δ hδ M)

end OddMath.QuiverHecke
