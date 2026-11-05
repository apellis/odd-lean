/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightDotWhiskering
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeBlockDotComparison
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionGridRelations
import OddMath.QuiverHecke.CyclotomicAction.ELVEndEvaluation

/-! # The signed OLD probe block slides and chosen weight coordinates

Brundan–Ellis (1.8): retain the independent chosen weight dots and
negative equal crossing, using their literal stored-target module-grid
coordinates on every supported block and the actual zero absent sectors.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction CyclotomicAction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (i : I) (Λ : X) {x₀ x₁ x₂ : X}
  (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂)

local notation "J" β => probeOldBlockAppend D Sc m i Λ h₁ β
local notation "K" β => probeOldBlockAppend D Sc m i Λ h₂ (blockSucc D Λ i h₁ β)
local notation "hd₁" β => probeOldBlockDotArrow_supernatural D Sc m i Λ h₁ β
local notation "hd₂" β => probeOldBlockDotArrow_supernatural D Sc m i Λ h₂ (blockSucc D Λ i h₁ β)
local notation "hc" β => probeOldBlockEqualCrossArrow_supernatural D Sc m i Λ h₁ h₂ β

/-- The chosen outer dot on the actual two-step block induction. -/
abbrev probeOldBlockOuterDot (β : WeightBlocks D Λ x₀) :
    End (probeOldBlockPairInd D Sc m i i Λ h₁ h₂ β) :=
  Superfunctor.whiskerLeft (probeOldBlockInd D Sc m i Λ h₁ β)
    (probeOldBlockDot D Sc m i Λ h₂ (blockSucc D Λ i h₁ β))

/-- The chosen inner dot on the same two-step block induction. -/
abbrev probeOldBlockInnerDot (β : WeightBlocks D Λ x₀) :
    End (probeOldBlockPairInd D Sc m i i Λ h₁ h₂ β) :=
  Superfunctor.whiskerRight (probeOldBlockDot D Sc m i Λ h₁ β)
    (probeOldBlockInd D Sc m i Λ h₂ (blockSucc D Λ i h₁ β))

theorem probeOldBlockOuterDot_app (β : WeightBlocks D Λ x₀)
    (p : ZMod 2) (M : ProbeCanonicalModules D Sc m β.1) :
    ((probeOldBlockOuterDot D Sc m i Λ h₁ h₂ β).app p M).hom =
      (Superfunctor.whiskerLeft (inductionModuleCell (k := k) (J β))
        (inductionModuleDot (K β) (hd₂ β))).app p M.obj := by
  change ((probeOldBlockDot D Sc m i Λ h₂ (blockSucc D Λ i h₁ β)).app p
    ((probeOldBlockInd D Sc m i Λ h₁ β).obj M)).hom = _
  rw [probeOldBlockDot_app]
  rfl

theorem probeOldBlockInnerDot_app (β : WeightBlocks D Λ x₀)
    (p : ZMod 2) (M : ProbeCanonicalModules D Sc m β.1) :
    ((probeOldBlockInnerDot D Sc m i Λ h₁ h₂ β).app p M).hom =
      (Superfunctor.whiskerRight (inductionModuleDot (J β) (hd₁ β))
        (inductionModuleCell (k := k) (K β))).app p M.obj := by
  change (induction (K β)).map (((probeOldBlockDot D Sc m i Λ h₁ β).app p M).hom) = _
  rw [probeOldBlockDot_app]
  rfl

theorem probeOldBlockOuterDot_total (β : WeightBlocks D Λ x₀)
    (M : ProbeCanonicalModules D Sc m β.1) :
    ((probeOldBlockOuterDot D Sc m i Λ h₁ h₂ β).total M).hom =
      (Superfunctor.whiskerLeft (inductionModuleCell (k := k) (J β))
        (inductionModuleDot (K β) (hd₂ β))).total M.obj := by
  change ((probeOldBlockOuterDot D Sc m i Λ h₁ h₂ β).app 0 M).hom +
    ((probeOldBlockOuterDot D Sc m i Λ h₁ h₂ β).app 1 M).hom = _
  rw [probeOldBlockOuterDot_app, probeOldBlockOuterDot_app]
  rfl

theorem probeOldBlockInnerDot_total (β : WeightBlocks D Λ x₀)
    (M : ProbeCanonicalModules D Sc m β.1) :
    ((probeOldBlockInnerDot D Sc m i Λ h₁ h₂ β).total M).hom =
      (Superfunctor.whiskerRight (inductionModuleDot (J β) (hd₁ β))
        (inductionModuleCell (k := k) (K β))).total M.obj := by
  change ((probeOldBlockInnerDot D Sc m i Λ h₁ h₂ β).app 0 M).hom +
    ((probeOldBlockInnerDot D Sc m i Λ h₁ h₂ β).app 1 M).hom = _
  rw [probeOldBlockInnerDot_app, probeOldBlockInnerDot_app]
  rfl

/-- The entire chosen outer dot uses the same selected coordinate as the crossing. -/
theorem probeOldOuterDot_total (β : WeightBlocks D Λ x₀)
    (M : ProbeOldWeightProduct D Sc m Λ x₀) :
    ((probeOldE D Sc m i Λ h₁ ◁ probeOldActionDot D Sc m i Λ h₂).total M)
        (blockSucc₂ D i i Λ h₁ h₂ β) =
      eqToHom (probeOldWeightPair_obj_eq D Sc m i Λ h₁ h₂ β M) ≫
        (probeOldBlockOuterDot D Sc m i Λ h₁ h₂ β).total (M β) ≫
        eqToHom (probeOldWeightPair_obj_eq D Sc m i Λ h₁ h₂ β M).symm := by
  change ((probeOldE D Sc m i Λ h₁ ◁ probeOldActionDot D Sc m i Λ h₂).app 0 M)
      (blockSucc₂ D i i Λ h₁ h₂ β) +
    ((probeOldE D Sc m i Λ h₁ ◁ probeOldActionDot D Sc m i Λ h₂).app 1 M)
      (blockSucc₂ D i i Λ h₁ h₂ β) = _
  rw [probeOldOuterDot_component, probeOldOuterDot_component]
  change _ = eqToHom _ ≫
    ((probeOldBlockOuterDot D Sc m i Λ h₁ h₂ β).app 0 (M β) +
      (probeOldBlockOuterDot D Sc m i Λ h₁ h₂ β).app 1 (M β)) ≫ eqToHom _
  rw [Preadditive.add_comp, Preadditive.comp_add]
  simp only [probeOldBlockOuterDot, Superfunctor.whiskerLeft_app]

/-- The entire independently chosen inner dot uses that identical coordinate. -/
theorem probeOldInnerDot_total (β : WeightBlocks D Λ x₀)
    (M : ProbeOldWeightProduct D Sc m Λ x₀) :
    ((probeOldActionDot D Sc m i Λ h₁ ▷ probeOldE D Sc m i Λ h₂).total M)
        (blockSucc₂ D i i Λ h₁ h₂ β) =
      eqToHom (probeOldWeightPair_obj_eq D Sc m i Λ h₁ h₂ β M) ≫
        (probeOldBlockInnerDot D Sc m i Λ h₁ h₂ β).total (M β) ≫
        eqToHom (probeOldWeightPair_obj_eq D Sc m i Λ h₁ h₂ β M).symm := by
  change ((probeOldActionDot D Sc m i Λ h₁ ▷ probeOldE D Sc m i Λ h₂).app 0 M)
      (blockSucc₂ D i i Λ h₁ h₂ β) +
    ((probeOldActionDot D Sc m i Λ h₁ ▷ probeOldE D Sc m i Λ h₂).app 1 M)
      (blockSucc₂ D i i Λ h₁ h₂ β) = _
  rw [probeOldInnerDot_component, probeOldInnerDot_component]
  change _ = eqToHom _ ≫
    ((probeOldBlockInnerDot D Sc m i Λ h₁ h₂ β).app 0 (M β) +
      (probeOldBlockInnerDot D Sc m i Λ h₁ h₂ β).app 1 (M β)) ≫ eqToHom _
  rw [Preadditive.add_comp, Preadditive.comp_add]
  simp only [probeOldBlockInnerDot, Superfunctor.whiskerRight_app]

local notation "rawF" β => Superfunctor.comp (inductionModuleCell (k := k) (J β))
  (inductionModuleCell (k := k) (K β))
local notation "rawO" β => Superfunctor.whiskerLeft (inductionModuleCell (k := k) (J β))
  (inductionModuleDot (K β) (hd₂ β))
local notation "rawI" β => Superfunctor.whiskerRight (inductionModuleDot (J β) (hd₁ β))
  (inductionModuleCell (k := k) (K β))
local notation "rawC" β => inductionModuleCross (J β) (K β) (hc β)

/-- The exact chosen block dots and negative crossing satisfy the left signed slide. -/
theorem probeOldBlockEqualCross_slideLeft (β : WeightBlocks D Λ x₀) :
    probeOldBlockOuterDot D Sc m i Λ h₁ h₂ β ≫ probeOldBlockEqualCross D Sc m i Λ h₁ h₂ β -
      (koszulSign (D.parity i) (D.parity i) : ℤ) •
        (probeOldBlockEqualCross D Sc m i Λ h₁ h₂ β ≫ probeOldBlockInnerDot D Sc m i Λ h₁ h₂ β) = 𝟙 _ := by
  have hraw := inductionModuleCross_slide_left (J β) (K β) (hc β) (hd₁ β) (hd₂ β) (by
    intro t
    have h := oldContentEqualCross_slideLeft D Sc (probeCutoff D m) β.1.toList i t
    rw [koszulSign_smul (R := k)] at h
    convert! h using 1)
  apply OddMath.HomogeneousSuperfunctorIso.total_ext
  intro M
  let rc : End (rawF β) := rawC β
  let ro : End (rawF β) := rawO β
  let ri : End (rawF β) := rawI β
  let er := supernaturalEndEvaluation (rawF β) M.obj
  have hr := congrArg er hraw
  change er (rc * ro - (koszulSign (D.parity i) (D.parity i) : ℤ) • (ri * rc)) = er 1 at hr
  rw [map_sub, map_mul, map_zsmul, map_mul, map_one] at hr
  let e := supernaturalEndEvaluation (probeOldBlockPairInd D Sc m i i Λ h₁ h₂ β) M
  change e (probeOldBlockEqualCross D Sc m i Λ h₁ h₂ β * probeOldBlockOuterDot D Sc m i Λ h₁ h₂ β -
    (koszulSign (D.parity i) (D.parity i) : ℤ) •
      (probeOldBlockInnerDot D Sc m i Λ h₁ h₂ β * probeOldBlockEqualCross D Sc m i Λ h₁ h₂ β)) = e 1
  rw [map_sub, map_mul, map_zsmul, map_mul, map_one]
  apply InducedCategory.hom_ext
  change ((probeOldBlockOuterDot D Sc m i Λ h₁ h₂ β).total M).hom ≫
      ((probeOldBlockEqualCross D Sc m i Λ h₁ h₂ β).total M).hom -
    (koszulSign (D.parity i) (D.parity i) : ℤ) •
      (((probeOldBlockEqualCross D Sc m i Λ h₁ h₂ β).total M).hom ≫
        ((probeOldBlockInnerDot D Sc m i Λ h₁ h₂ β).total M).hom) = 𝟙 _
  rw [probeOldBlockOuterDot_total, probeOldBlockEqualCross_total,
    probeOldBlockInnerDot_total]
  exact hr

/-- The same chosen block generators satisfy the right signed slide. -/
theorem probeOldBlockEqualCross_slideRight (β : WeightBlocks D Λ x₀) :
    probeOldBlockEqualCross D Sc m i Λ h₁ h₂ β ≫ probeOldBlockOuterDot D Sc m i Λ h₁ h₂ β -
      (koszulSign (D.parity i) (D.parity i) : ℤ) •
        (probeOldBlockInnerDot D Sc m i Λ h₁ h₂ β ≫ probeOldBlockEqualCross D Sc m i Λ h₁ h₂ β) = 𝟙 _ := by
  have hraw := inductionModuleCross_slide_right (J β) (K β) (hc β) (hd₁ β) (hd₂ β) (by
    intro t
    have h := oldContentEqualCross_slideRight D Sc (probeCutoff D m) β.1.toList i t
    rw [koszulSign_smul (R := k)] at h
    convert! h using 1)
  apply OddMath.HomogeneousSuperfunctorIso.total_ext
  intro M
  let rc : End (rawF β) := rawC β
  let ro : End (rawF β) := rawO β
  let ri : End (rawF β) := rawI β
  let er := supernaturalEndEvaluation (rawF β) M.obj
  have hr := congrArg er hraw
  change er (ro * rc - (koszulSign (D.parity i) (D.parity i) : ℤ) • (rc * ri)) = er 1 at hr
  rw [map_sub, map_mul, map_zsmul, map_mul, map_one] at hr
  let e := supernaturalEndEvaluation (probeOldBlockPairInd D Sc m i i Λ h₁ h₂ β) M
  change e (probeOldBlockOuterDot D Sc m i Λ h₁ h₂ β * probeOldBlockEqualCross D Sc m i Λ h₁ h₂ β -
    (koszulSign (D.parity i) (D.parity i) : ℤ) •
      (probeOldBlockEqualCross D Sc m i Λ h₁ h₂ β * probeOldBlockInnerDot D Sc m i Λ h₁ h₂ β)) = e 1
  rw [map_sub, map_mul, map_zsmul, map_mul, map_one]
  apply InducedCategory.hom_ext
  change ((probeOldBlockEqualCross D Sc m i Λ h₁ h₂ β).total M).hom ≫
      ((probeOldBlockOuterDot D Sc m i Λ h₁ h₂ β).total M).hom -
    (koszulSign (D.parity i) (D.parity i) : ℤ) •
      (((probeOldBlockInnerDot D Sc m i Λ h₁ h₂ β).total M).hom ≫
        ((probeOldBlockEqualCross D Sc m i Λ h₁ h₂ β).total M).hom) = 𝟙 _
  rw [probeOldBlockOuterDot_total, probeOldBlockEqualCross_total,
    probeOldBlockInnerDot_total]
  exact hr

end OddMath.QuiverHecke
