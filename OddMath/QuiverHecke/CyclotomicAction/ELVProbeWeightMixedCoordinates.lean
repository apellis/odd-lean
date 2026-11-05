import OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightMixedMate
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeBlockDistinctSlides

/-! # Supported mixed OLD probe weight coordinates

Brundan–Ellis (1.12): identify the prescribed source and target of the
weight mixed mate with the actual four stored-target append functors.
Every target permutation and selected predecessor is retained.
-/
noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction CyclotomicAction
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
  have hg := probeAppendToCross_native_total D Sc m β.1.toList i j hj hi hL hU N
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
