import OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightDistinctCrossing
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeBlockDotComparison
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionGridDistinctSlides
import OddMath.QuiverHecke.CyclotomicAction.ELVOldDistinctSlides

/-! # Distinct slides on the selected OLD probe block pairs

Brundan–Ellis (1.8): the positive rectangular crossing and independently
chosen dots satisfy both slides at arbitrary canonical stored targets.
The literal OLD quotient equations supply the source relations.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction ELVOld.CyclotomicCrossingTensor CyclotomicAction
universe u
private theorem total_smul {k C A : Type*} [CommRing k]
    [Category C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category A] [Preadditive A] [Linear k A] [Supercategory k A]
    {F G : Superfunctor k C A} (a : k) (f : F ⟶ G) (N : C) :
    (a • f).total N = a • f.total N := by
  change a • f.app 0 N + a • f.app 1 N = a • (f.app 0 N + f.app 1 N)
  exact (smul_add _ _ _).symm

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
section Pair
variable (i j : I) (Λ : X) {x₀ x₁ xu : X}
  (h₁ : x₀ + D.α j = x₁) (h₂ : x₁ + D.α i = xu)

abbrev probeOldPairUpperInd (β : WeightBlocks D Λ x₀) (ε : WeightBlocks D Λ xu)
    (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε) :
    Superfunctor k (ProbeCanonicalModules D Sc m (blockSucc D Λ j h₁ β).1)
      (ProbeCanonicalModules D Sc m ε.1) :=
  ⟨probeEvaluatedAppendTo D Sc m (blockSucc D Λ j h₁ β).1.toList i ε.1.toList
    (probeOldPairUpper_perm D i j Λ h₁ h₂ β ε hε)⟩

abbrev probeOldPairUpperDot (β : WeightBlocks D Λ x₀) (ε : WeightBlocks D Λ xu)
    (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε) :=
  probeAppendToInductionDot D Sc m (blockSucc D Λ j h₁ β).1.toList i ε.1.toList
    (probeOldPairUpper_perm D i j Λ h₁ h₂ β ε hε)

abbrev probeOldBlockPairOuterDotTo (β : WeightBlocks D Λ x₀) (ε : WeightBlocks D Λ xu)
    (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε) :
    End (probeOldBlockPairIndTo D Sc m i j Λ h₁ h₂ β ε hε) :=
  Superfunctor.whiskerLeft (probeOldBlockInd D Sc m j Λ h₁ β)
    (probeOldPairUpperDot D Sc m i j Λ h₁ h₂ β ε hε)

abbrev probeOldBlockPairInnerDotTo (β : WeightBlocks D Λ x₀) (ε : WeightBlocks D Λ xu)
    (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε) :
    End (probeOldBlockPairIndTo D Sc m i j Λ h₁ h₂ β ε hε) :=
  Superfunctor.whiskerRight (probeOldBlockDot D Sc m j Λ h₁ β)
    (probeOldPairUpperInd D Sc m i j Λ h₁ h₂ β ε hε)

local notation "K" => probeOldBlockAppend D Sc m j Λ h₁
local notation "U" => probeOldPairUpperAppend D Sc m i j Λ h₁ h₂

theorem probeOldBlockPairOuterDotTo_total
    (β : WeightBlocks D Λ x₀) (ε : WeightBlocks D Λ xu)
    (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε) (N : ProbeCanonicalModules D Sc m β.1) :
    ((probeOldBlockPairOuterDotTo D Sc m i j Λ h₁ h₂ β ε hε).total N).hom =
      dotEnd (U β ε hε) (probeAppendToDot_supernatural D Sc m (blockSucc D Λ j h₁ β).1.toList i ε.1.toList
        (probeOldPairUpper_perm D i j Λ h₁ h₂ β ε hε)) ((induction (K β)).obj N.obj) := by
  change ((probeAppendToInductionDot D Sc m (blockSucc D Λ j h₁ β).1.toList i ε.1.toList
    (probeOldPairUpper_perm D i j Λ h₁ h₂ β ε hε)).total
      ((probeOldBlockInd D Sc m j Λ h₁ β).obj N)).hom = _
  rw [probeAppendToInductionDot_total]
  rfl

theorem probeOldBlockPairInnerDotTo_total
    (β : WeightBlocks D Λ x₀) (ε : WeightBlocks D Λ xu)
    (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε) (N : ProbeCanonicalModules D Sc m β.1) :
    ((probeOldBlockPairInnerDotTo D Sc m i j Λ h₁ h₂ β ε hε).total N).hom =
      (induction (U β ε hε)).map
        (dotEnd (K β) (probeOldBlockDotArrow_supernatural D Sc m j Λ h₁ β) N.obj) := by
  change (induction (U β ε hε)).map (((probeOldBlockDot D Sc m j Λ h₁ β).app 0 N).hom) +
    (induction (U β ε hε)).map (((probeOldBlockDot D Sc m j Λ h₁ β).app 1 N).hom) = _
  rw [← Functor.map_add]
  change (induction (U β ε hε)).map (((probeOldBlockDot D Sc m j Λ h₁ β).total N).hom) = _
  rw [probeOldBlockDot_total, inductionModuleDot_total]
end Pair

section Crossing
variable (i j : I) (Λ : X) {x₀ xj xi xu : X}
  (h₁ : x₀ + D.α j = xj) (h₂ : xj + D.α i = xu)
  (h₃ : x₀ + D.α i = xi) (h₄ : xi + D.α j = xu)
local notation "sw" => blockSucc₂_swap D i j Λ h₁ h₂ h₃ h₄
local notation "J" => probeOldBlockAppend D Sc m i Λ h₃
local notation "K" => probeOldBlockAppend D Sc m j Λ h₁
local notation "L" => (fun β ε hε => probeOldPairUpperAppend D Sc m j i Λ h₃ h₄ β ε (sw hε))
local notation "U" => probeOldPairUpperAppend D Sc m i j Λ h₁ h₂
local notation "hc" => probeOldBlockDistinctCrossArrow_supernatural D Sc m i j Λ h₁ h₂ h₃ h₄

theorem probeOldBlockDistinctCross_total
    (β : WeightBlocks D Λ x₀) (ε : WeightBlocks D Λ xu)
    (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε) (N : ProbeCanonicalModules D Sc m β.1) :
    ((probeOldBlockDistinctCross D Sc m i j Λ h₁ h₂ h₃ h₄ β ε hε).total N).hom =
      rectangularCrossComponent (J β) (K β) (L β ε hε) (U β ε hε) (hc β ε hε) N.obj := by
  change ((probeOldBlockDistinctCross D Sc m i j Λ h₁ h₂ h₃ h₄ β ε hε).app 0 N).hom +
    ((probeOldBlockDistinctCross D Sc m i j Λ h₁ h₂ h₃ h₄ β ε hε).app 1 N).hom = _
  rw [probeOldBlockDistinctCross_app, probeOldBlockDistinctCross_app]
  exact OddMath.HomogeneousSuperfunctorIso.homogeneous_total
    (F := ⟨(induction (K β)).comp (induction (U β ε hε))⟩)
    (G := ⟨(induction (J β)).comp (induction (L β ε hε))⟩)
    (rectangularCrossComponent_supernatural (J β) (K β) (L β ε hε) (U β ε hε) (hc β ε hε)) N.obj

/-- The chosen crossing carries the source outer dot to the target inner dot. -/
theorem probeOldBlockDistinctCross_slide_inner (hij : i ≠ j)
    (β : WeightBlocks D Λ x₀) (ε : WeightBlocks D Λ xu)
    (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε) :
    probeOldBlockDistinctCross D Sc m i j Λ h₁ h₂ h₃ h₄ β ε hε ≫
      probeOldBlockPairInnerDotTo D Sc m j i Λ h₃ h₄ β ε (sw hε) =
    sign k (D.parity i * D.parity j) •
      (probeOldBlockPairOuterDotTo D Sc m i j Λ h₁ h₂ β ε hε ≫
        probeOldBlockDistinctCross D Sc m i j Λ h₁ h₂ h₃ h₄ β ε hε) := by
  apply OddMath.HomogeneousSuperfunctorIso.total_ext
  intro N
  rw [Superfunctor.comp_total, total_smul, Superfunctor.comp_total]
  apply InducedCategory.hom_ext
  change ((probeOldBlockDistinctCross D Sc m i j Λ h₁ h₂ h₃ h₄ β ε hε).total N).hom ≫
      ((probeOldBlockPairInnerDotTo D Sc m j i Λ h₃ h₄ β ε (sw hε)).total N).hom =
    sign k (D.parity i * D.parity j) •
      (((probeOldBlockPairOuterDotTo D Sc m i j Λ h₁ h₂ β ε hε).total N).hom ≫
        ((probeOldBlockDistinctCross D Sc m i j Λ h₁ h₂ h₃ h₄ β ε hε).total N).hom)
  rw [probeOldBlockDistinctCross_total, probeOldBlockPairInnerDotTo_total,
    probeOldBlockPairOuterDotTo_total]
  have hr := rectangularCrossComponent_slide_inner_outer (J β) (K β) (L β ε hε) (U β ε hε)
    (hc β ε hε) (probeOldBlockDotArrow_supernatural D Sc m i Λ h₃ β)
    (probeAppendToDot_supernatural D Sc m (blockSucc D Λ j h₁ β).1.toList i ε.1.toList
      (probeOldPairUpper_perm D i j Λ h₁ h₂ β ε hε))
    (sign k (D.parity i * D.parity j))
    (fun s => Distinct.crossComponent_slide_first D Sc (probeCutoff D m) hij.symm s.obj) N.obj
  convert! hr using 1

/-- The other chosen dot follows the opposite strand through the same crossing. -/
theorem probeOldBlockDistinctCross_slide_outer (hij : i ≠ j)
    (β : WeightBlocks D Λ x₀) (ε : WeightBlocks D Λ xu)
    (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε) :
    probeOldBlockDistinctCross D Sc m i j Λ h₁ h₂ h₃ h₄ β ε hε ≫
      probeOldBlockPairOuterDotTo D Sc m j i Λ h₃ h₄ β ε (sw hε) =
    sign k (D.parity i * D.parity j) •
      (probeOldBlockPairInnerDotTo D Sc m i j Λ h₁ h₂ β ε hε ≫
        probeOldBlockDistinctCross D Sc m i j Λ h₁ h₂ h₃ h₄ β ε hε) := by
  apply OddMath.HomogeneousSuperfunctorIso.total_ext
  intro N
  rw [Superfunctor.comp_total, total_smul, Superfunctor.comp_total]
  apply InducedCategory.hom_ext
  change ((probeOldBlockDistinctCross D Sc m i j Λ h₁ h₂ h₃ h₄ β ε hε).total N).hom ≫
      ((probeOldBlockPairOuterDotTo D Sc m j i Λ h₃ h₄ β ε (sw hε)).total N).hom =
    sign k (D.parity i * D.parity j) •
      (((probeOldBlockPairInnerDotTo D Sc m i j Λ h₁ h₂ β ε hε).total N).hom ≫
        ((probeOldBlockDistinctCross D Sc m i j Λ h₁ h₂ h₃ h₄ β ε hε).total N).hom)
  rw [probeOldBlockDistinctCross_total, probeOldBlockPairOuterDotTo_total,
    probeOldBlockPairInnerDotTo_total]
  have hr := rectangularCrossComponent_slide_outer_inner (J β) (K β) (L β ε hε) (U β ε hε)
    (hc β ε hε)
    (probeAppendToDot_supernatural D Sc m (blockSucc D Λ i h₃ β).1.toList j ε.1.toList
      (probeOldPairUpper_perm D j i Λ h₃ h₄ β ε (sw hε)))
    (probeOldBlockDotArrow_supernatural D Sc m j Λ h₁ β)
    (sign k (D.parity i * D.parity j))
    (fun s => Distinct.crossComponent_slide_last D Sc (probeCutoff D m) hij.symm s.obj) N.obj
  convert! hr using 1
end Crossing
end OddMath.QuiverHecke
