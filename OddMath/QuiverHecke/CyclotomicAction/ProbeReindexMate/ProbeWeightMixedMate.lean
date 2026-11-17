import Mathlib.CategoryTheory.Adjunction.Unique
import OddMath.QuiverHecke.CyclotomicAction.ProbeReindexMate.ProbeBlockDistinctSlides
import OddMath.QuiverHecke.CyclotomicAction.ProbeWeightDot.ProbeRouquierData

/-!
# Probe reindex mate

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # The selected OLD probe weight mixed mate

Brundan–Ellis (1.12): bend the selected weight crossing by the actual
lower and upper right adjunctions. A missing lower-i predecessor makes
both mixed-functor coordinates zero when the colours differ.
-/
noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELV CyclotomicAction
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
end

end

section

/-! # Supported mixed OLD probe weight coordinates

Brundan–Ellis (1.12): identify the prescribed source and target of the
weight mixed mate with the actual four stored-target append functors.
Every target permutation and selected predecessor is retained.
-/
noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELV ELV.BalancedInduction CyclotomicAction
universe u

private theorem rectangularCross_parity_change
    {k C A B E : Type u} [CommRing k]
    [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
    [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
    [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    (K : C ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
    (L : A ⥤ E) [L.Additive] [L.Linear k] [IsSuperfunctor k L]
    (U : B ⥤ E) [U.Additive] [U.Linear k] [IsSuperfunctor k U]
    {p q : ZMod 2} {α : ∀ s, (J ⋙ L).obj s ⟶ (K ⋙ U).obj s}
    (hp : p = q) (hα : IsSupernatural k p α) (hβ : IsSupernatural k q α)
    (N : Superfunctor k C (SVec k)) :
    rectangularCrossComponent J K L U hα N = rectangularCrossComponent J K L U hβ N := by
  subst q
  rfl

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)

/-- The stored target permutation determined by an actual weight predecessor. -/
theorem probeOldBlockTarget_perm (i : I) (Λ : X) {x y : X} (h : x + D.α i = y)
    (β : WeightBlocks D Λ x) (δ : WeightBlocks D Λ y) (hβ : blockSucc D Λ i h β = δ) :
    (i :: β.1.toList).Perm δ.1.toList := by
  apply Multiset.coe_eq_coe.mp
  rw [Multiset.coe_toList]
  change {i} + (β.1.toList : Multiset I) = δ.1
  rw [Multiset.coe_toList]
  exact congrArg Subtype.val hβ

/-- The selected block induction with its target kept as the literal output block. -/
abbrev probeOldBlockIndTo (i : I) (Λ : X) {x y : X} (h : x + D.α i = y)
    (β : WeightBlocks D Λ x) (δ : WeightBlocks D Λ y) (hβ : blockSucc D Λ i h β = δ) :
    Superfunctor k (ProbeCanonicalModules D Sc m β.1) (ProbeCanonicalModules D Sc m δ.1) :=
  ⟨probeEvaluatedAppendTo D Sc m β.1.toList i δ.1.toList
    (probeOldBlockTarget_perm D i Λ h β δ hβ)⟩

theorem probeOldInductionComponent_obj_of (i : I) (Λ : X) {x y : X} (h : x + D.α i = y)
    (β : WeightBlocks D Λ x) (δ : WeightBlocks D Λ y) (hβ : blockSucc D Λ i h β = δ)
    (M : ProbeOldWeightProduct D Sc m Λ x) :
    (probeOldInductionComponent D Sc m i Λ h δ).obj M =
      (probeOldBlockIndTo D Sc m i Λ h β δ hβ).obj (M β) := by
  subst δ
  exact probeOldInductionComponent_obj_blockSucc D Sc m i Λ h β M

theorem probeOldInductionComponent_map_of (i : I) (Λ : X) {x y : X} (h : x + D.α i = y)
    (β : WeightBlocks D Λ x) (δ : WeightBlocks D Λ y) (hβ : blockSucc D Λ i h β = δ)
    {M N : ProbeOldWeightProduct D Sc m Λ x} (f : M ⟶ N) :
    (probeOldInductionComponent D Sc m i Λ h δ).map f =
      eqToHom (probeOldInductionComponent_obj_of D Sc m i Λ h β δ hβ M) ≫
        (probeOldBlockIndTo D Sc m i Λ h β δ hβ).map (f β) ≫
          eqToHom (probeOldInductionComponent_obj_of D Sc m i Λ h β δ hβ N).symm := by
  subst δ
  exact probeOldInductionComponent_map_blockSucc D Sc m i Λ h β f

variable (i j : I) (Λ : X) {x₀ xj xi xu : X}
  (h₁ : x₀ + D.α j = xj) (h₂ : xj + D.α i = xu)
  (h₃ : x₀ + D.α i = xi) (h₄ : xi + D.α j = xu)
  (β : WeightBlocks D Λ x₀)
local notation "δj" => blockSucc D Λ j h₁ β
local notation "δi" => blockSucc D Λ i h₃ β
local notation "ε" => blockSucc D Λ j h₄ (blockSucc D Λ i h₃ β)
local notation "hComm" => blockSucc_comm D Λ i j h₁ h₂ h₃ h₄ β
local notation "hj" => probeOldBlockTarget_perm D j Λ h₁ β δj rfl
local notation "hi" => probeOldBlockTarget_perm D i Λ h₃ β δi rfl
local notation "hL" => probeOldBlockTarget_perm D i Λ h₂ δj ε hComm
local notation "hU" => probeOldBlockTarget_perm D j Λ h₄ δi ε rfl
local notation "Fj" => probeOldF D Sc m j Λ h₁
local notation "Ei" => probeOldE D Sc m i Λ h₃
local notation "J" => probeOldBlockAppend D Sc m j Λ h₁ β
local notation "K" => probeOldBlockAppend D Sc m i Λ h₃ β
local notation "U" => probeOldBlockAppend D Sc m j Λ h₄ δi
local notation "L" => oldContentAppendTo D Sc (probeCutoff D m)
  (Multiset.toList (Subtype.val δj)) i (Multiset.toList (Subtype.val ε)) hL
local notation "hα" => oldAppendToCross_supernatural D Sc (probeCutoff D m)
  (Multiset.toList (Subtype.val β)) i j hj hi hL hU
local notation "sourcePairEq" => probeOldEFunctor_comp₂_to D Sc m j i Λ h₃ h₄ β ε rfl
local notation "targetPairEq" => probeOldEFunctor_comp₂_to D Sc m i j Λ h₁ h₂ β ε hComm

attribute [local irreducible] rectangularCrossComponent

/-- The supported source is the stored-target lower restriction-induction. -/
theorem probeOldWeightMixedSource_obj (M : ProbeOldWeightProduct D Sc m Λ xj) :
    (((probeOldF D Sc m j Λ h₁ ≫ probeOldE D Sc m i Λ h₃).obj M) δi) =
      (probeAppendToDistinctMateSource D Sc m β.1.toList i j hj hi).obj (M δj) :=
  probeOldInductionComponent_obj_blockSucc D Sc m i Λ h₃ β ((Fj).obj M)

/-- The supported target uses the same literal common upper block. -/
theorem probeOldWeightMixedTarget_obj (M : ProbeOldWeightProduct D Sc m Λ xj) :
    (((probeOldE D Sc m i Λ h₂ ≫ probeOldF D Sc m j Λ h₄).obj M) δi) =
      (probeAppendToDistinctMateTarget D Sc m i j hL hU).obj (M δj) := by
  exact congrArg (fun P => (probeOldBlockRes D Sc m j Λ h₄ δi).obj P)
    (probeOldInductionComponent_obj_of D Sc m i Λ h₂ δj ε hComm M)

/-- The selected positive block crossing is the constructed stored-target crossing. -/
theorem probeOldBlockDistinctCross_mixed_eq :
    probeOldBlockDistinctCross D Sc m j i Λ h₃ h₄ h₁ h₂ β ε rfl =
      probeAppendToCross D Sc m β.1.toList i j hj hi hL hU := by
  let F := probeOldBlockPairIndTo D Sc m j i Λ h₃ h₄ β ε rfl
  let G := probeOldBlockPairIndTo D Sc m i j Λ h₁ h₂ β ε hComm
  apply HomogeneousSuperfunctorIso.total_ext (F := F) (G := G)
  intro N
  apply InducedCategory.hom_ext
  have hb := probeOldBlockDistinctCross_total D Sc m j i Λ h₃ h₄ h₁ h₂ β ε rfl N
  have hg := probeAppendToCross_direct_total D Sc m β.1.toList i j hj hi hL hU N
  have hblock : IsSupernatural k (D.parity j * D.parity i)
      (oldAppendToCross D Sc (probeCutoff D m) β.1.toList i j hj hi hL hU) :=
    probeOldBlockDistinctCrossArrow_supernatural D Sc m j i Λ h₃ h₄ h₁ h₂ β ε rfl
  have hx := rectangularCross_parity_change J K L U
    (mul_comm (D.parity j) (D.parity i)) hblock hα N.obj
  exact hb.trans (hx.trans hg.symm)

/-- The actual selected weight crossing retains its occupied rectangular coordinate. -/
theorem probeOldWeightMixedCross_comparison (hij : i ≠ j) (p : ZMod 2)
    (M : ProbeOldWeightProduct D Sc m Λ xj) :
    (probeOldActionCross D Sc m Λ j i h₃ h₄ h₁ h₂).app p ((Fj).obj M) ε =
      (eqToHom (Functor.congr_obj sourcePairEq ((Fj).obj M)) ≫
        (probeAppendToCross D Sc m β.1.toList i j hj hi hL hU).app p (((Fj).obj M) β)) ≫
        eqToHom (Functor.congr_obj targetPairEq ((Fj).obj M)).symm := by
  rw [probeOldActionCross_distinct D Sc m Λ j i hij.symm h₃ h₄ h₁ h₂]
  change probeOldWeightDistinctCrossComponent D Sc m j i Λ h₃ h₄ h₁ h₂ p ((Fj).obj M) ε = _
  rw [probeOldWeightDistinctCrossComponent_of D Sc m j i Λ h₃ h₄ h₁ h₂ p ((Fj).obj M) β ε rfl,
    probeOldWeightDistinctCrossVia_component D Sc m j i Λ h₃ h₄ h₁ h₂ β ε rfl p ((Fj).obj M),
    probeOldBlockDistinctCross_mixed_eq D Sc m i j Λ h₁ h₂ h₃ h₄ β]
  simp only [Category.assoc]

end OddMath.QuiverHecke
end

end

section

/-! # The selected probe weight cup and cap in mixed coordinates

Brundan–Ellis (1.12): paste the actual weight adjunction maps through
the occupied stored-content coordinates of the prescribed crossing.
-/
noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELV ELV.BalancedInduction CyclotomicAction
universe u

private theorem unit_transport
    {C A : Type*} [Category* C] [Category* A] (E : C ⥤ A) (F : A ⥤ C) (a : E ⊣ F)
    {P Q : C} {W : A} (hPQ : P = Q) (hWP : W = E.obj P) (hWQ : W = E.obj Q) :
    ((a.unit.app P ≫ F.map (eqToHom hWP.symm)) ≫ F.map (eqToHom hWQ)) =
      eqToHom hPQ ≫ a.unit.app Q := by
  subst Q
  subst W
  simp only [eqToHom_refl, CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]
  exact Category.comp_id _

private theorem map_counit_transport
    {A E : Type*} [Category* A] [Category* E] (L : A ⥤ E)
    {Y Z T : A} {P Q : E} (hYZ : Y = Z) (hP : P = L.obj Y)
    (hQ : Q = L.obj T) (hPZ : P = L.obj Z) (f : Z ⟶ T) :
    (eqToHom hP ≫ L.map (eqToHom hYZ ≫ f) ≫ eqToHom hQ.symm) ≫ eqToHom hQ =
      eqToHom hPZ ≫ L.map f := by
  subst Z
  subst P
  subst Q
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (i j : I) (Λ : X) {x₀ xj xi xu : X}
  (h₁ : x₀ + D.α j = xj) (h₂ : xj + D.α i = xu)
  (h₃ : x₀ + D.α i = xi) (h₄ : xi + D.α j = xu)
  (β : WeightBlocks D Λ x₀)
local notation "δj" => blockSucc D Λ j h₁ β
local notation "δi" => blockSucc D Λ i h₃ β
local notation "ε" => blockSucc D Λ j h₄ (blockSucc D Λ i h₃ β)
local notation "hComm" => blockSucc_comm D Λ i j h₁ h₂ h₃ h₄ β
local notation "ν" => Multiset.toList (Subtype.val β)
local notation "νj" => Multiset.toList (Subtype.val δj)
local notation "νi" => Multiset.toList (Subtype.val δi)
local notation "ν₂" => Multiset.toList (Subtype.val ε)
local notation "hj" => probeOldBlockTarget_perm D j Λ h₁ β δj rfl
local notation "hi" => probeOldBlockTarget_perm D i Λ h₃ β δi rfl
local notation "hL" => probeOldBlockTarget_perm D i Λ h₂ δj ε hComm
local notation "hU" => probeOldBlockTarget_perm D j Λ h₄ δi ε rfl
local notation "Fj" => probeOldF D Sc m j Λ h₁
local notation "Ei" => probeOldE D Sc m i Λ h₃
local notation "IndU" => probeOldBlockInd D Sc m j Λ h₄ δi
local notation "ResU" => probeOldBlockRes D Sc m j Λ h₄ δi
local notation "IndL" => probeOldBlockIndTo D Sc m i Λ h₂ δj ε hComm
local notation "sourcePairEq" => probeOldEFunctor_comp₂_to D Sc m j i Λ h₃ h₄ β ε rfl
local notation "targetPairEq" => probeOldEFunctor_comp₂_to D Sc m i j Λ h₁ h₂ β ε hComm

/-- The selected upper cup respects the source and pair coordinates. -/
theorem probeOldWeightMixedUnit_comparison (M : ProbeOldWeightProduct D Sc m Λ xj) :
    probeOldWeightUnitApp D Sc m j Λ h₄ δi ((Ei).obj ((Fj).obj M)) ≫
        (ResU).map (eqToHom (Functor.congr_obj sourcePairEq ((Fj).obj M))) =
      eqToHom (probeOldWeightMixedSource_obj D Sc m i j Λ h₁ h₃ β M) ≫
        (probeAppendToUnit D Sc m νi j ν₂ hU).app
          ((probeAppendToDistinctMateSource D Sc m ν i j hj hi).obj (M δj)) := by
  have h := unit_transport (IndU).toFunctor (ResU).toFunctor (probeOldBlockAdj D Sc m j Λ h₄ δi)
    (probeOldWeightMixedSource_obj D Sc m i j Λ h₁ h₃ β M)
    (probeOldInductionComponent_obj_blockSucc D Sc m j Λ h₄ δi ((Ei).obj ((Fj).obj M)))
    (Functor.congr_obj sourcePairEq ((Fj).obj M))
  dsimp only [probeOldWeightUnitApp, probeOldBlockAdj, probeAppendToAdjunction] at h ⊢
  exact h

/-- The selected lower cap respects the pair and target coordinates. -/
theorem probeOldWeightMixedCounit_comparison (M : ProbeOldWeightProduct D Sc m Λ xj) :
    (probeOldInductionComponent D Sc m i Λ h₂ ε).map
        ((probeOldWeightCounit D Sc m j Λ h₁).app M) ≫
        eqToHom (probeOldInductionComponent_obj_of D Sc m i Λ h₂ δj ε hComm M) =
      eqToHom (Functor.congr_obj targetPairEq ((Fj).obj M)) ≫
        (IndL).map ((probeAppendToCounit D Sc m ν j νj hj).app (M δj)) := by
  have hm := probeOldInductionComponent_map_of D Sc m i Λ h₂ δj ε hComm
    ((probeOldWeightCounit D Sc m j Λ h₁).app M)
  dsimp only [probeOldWeightCounit] at hm
  rw [probeOldWeightCounitComponent_blockSucc] at hm
  have ht := congrArg (fun f => f ≫
    eqToHom (probeOldInductionComponent_obj_of D Sc m i Λ h₂ δj ε hComm M)) hm
  have h := map_counit_transport (IndL).toFunctor
    (probeOldInductionComponent_obj_blockSucc D Sc m j Λ h₁ β ((Fj).obj M))
    (probeOldInductionComponent_obj_of D Sc m i Λ h₂ δj ε hComm
      ((probeOldE D Sc m j Λ h₁).obj ((Fj).obj M)))
    (probeOldInductionComponent_obj_of D Sc m i Λ h₂ δj ε hComm M)
    (Functor.congr_obj targetPairEq ((Fj).obj M))
    ((probeOldBlockAdj D Sc m j Λ h₁ β).counit.app (M δj))
  dsimp only [probeOldBlockAdj, probeAppendToAdjunction] at h ht ⊢
  exact ht.trans h

end OddMath.QuiverHecke
end

end
