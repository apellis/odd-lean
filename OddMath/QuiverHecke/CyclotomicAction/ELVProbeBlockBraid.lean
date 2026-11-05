/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightTripleInduction
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightCrossing
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionGridBraid
import OddMath.QuiverHecke.CyclotomicAction.ELVOldAppendBraid

/-! # The chosen OLD probe block braid

Brundan–Ellis (1.9): the independent chosen negative crossings on three
actual stored-target probe block inductions satisfy the braid. The literal
OLD source braid supplies the input to the changing-category induction grid;
no braid, comparison or scalar-specialization faithfulness premise is used.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction CyclotomicAction
universe u v w z t

private theorem braid_whiskerRight_total
    {k : Type u} [CommRing k] {C A B : Type v}
    [Category.{w} C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category.{z} A] [Preadditive A] [Linear k A] [Supercategory k A]
    [Category.{t} B] [Preadditive B] [Linear k B] [Supercategory k B]
    {F G : Superfunctor k C A} (x : F ⟶ G) (H : Superfunctor k A B) (M : C) :
    (Superfunctor.whiskerRight x H).total M = H.map (x.total M) := by
  change H.map (x.app 0 M) + H.map (x.app 1 M) = H.map (x.app 0 M + x.app 1 M)
  exact H.toFunctor.map_add.symm

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (i : I) (Λ : X) {x₀ x₁ x₂ x₃ : X}
  (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂) (h₃ : x₂ + D.α i = x₃)
local notation "J" β => probeOldBlockAppend D Sc m i Λ h₁ β
local notation "K" β => probeOldBlockAppend D Sc m i Λ h₂ (blockSucc D Λ i h₁ β)
local notation "L" β => probeOldBlockAppend D Sc m i Λ h₃ (blockSucc₂ D i i Λ h₁ h₂ β)
local notation "hγ" β => probeOldBlockEqualCrossArrow_supernatural D Sc m i Λ h₁ h₂ β
local notation "hδ" β => probeOldBlockEqualCrossArrow_supernatural D Sc m i Λ h₂ h₃ (blockSucc D Λ i h₁ β)

/-- The chosen first pair crossing, mapped by the actual third block induction. -/
abbrev probeOldBlockBraidPrefix (β : WeightBlocks D Λ x₀) :
    End (probeOldBlockTripleInd D Sc m i i i Λ h₁ h₂ h₃ β) :=
  Superfunctor.whiskerRight (probeOldBlockEqualCross D Sc m i Λ h₁ h₂ β)
    (probeOldBlockInd D Sc m i Λ h₃ (blockSucc₂ D i i Λ h₁ h₂ β))

/-- The independently chosen second pair crossing, after the first block induction. -/
abbrev probeOldBlockBraidSuffix (β : WeightBlocks D Λ x₀) :
    End (probeOldBlockTripleInd D Sc m i i i Λ h₁ h₂ h₃ β) :=
  Superfunctor.whiskerLeft (probeOldBlockInd D Sc m i Λ h₁ β)
    (probeOldBlockEqualCross D Sc m i Λ h₂ h₃ (blockSucc D Λ i h₁ β))

theorem probeOldBlockBraidPrefix_total (β : WeightBlocks D Λ x₀)
    (M : ProbeCanonicalModules D Sc m β.1) :
    (probeOldBlockBraidPrefix D Sc m i Λ h₁ h₂ h₃ β).total M =
      (probeOldBlockInd D Sc m i Λ h₃ (blockSucc₂ D i i Λ h₁ h₂ β)).map
        ((probeOldBlockEqualCross D Sc m i Λ h₁ h₂ β).total M) :=
  braid_whiskerRight_total _ _ M

theorem probeOldBlockBraidSuffix_total (β : WeightBlocks D Λ x₀)
    (M : ProbeCanonicalModules D Sc m β.1) :
    (probeOldBlockBraidSuffix D Sc m i Λ h₁ h₂ h₃ β).total M =
      (probeOldBlockEqualCross D Sc m i Λ h₂ h₃ (blockSucc D Λ i h₁ β)).total
        ((probeOldBlockInd D Sc m i Λ h₁ β).obj M) := rfl

/-- The first chosen block crossing whiskering retains its entire OLD module map. -/
theorem probeOldBlockBraidPrefix_native_total (β : WeightBlocks D Λ x₀)
    (M : ProbeCanonicalModules D Sc m β.1) :
    ((probeOldBlockBraidPrefix D Sc m i Λ h₁ h₂ h₃ β).total M).hom =
      (induction (L β)).map ((inductionModuleCross (J β) (K β) (hγ β)).total M.obj) := by
  rw [probeOldBlockBraidPrefix_total]
  change (induction (L β)).map (((probeOldBlockEqualCross D Sc m i Λ h₁ h₂ β).total M).hom) = _
  rw [probeOldBlockEqualCross_total]

/-- The second chosen block crossing retains the exact OLD pair crossing at its true input. -/
theorem probeOldBlockBraidSuffix_native_total (β : WeightBlocks D Λ x₀)
    (M : ProbeCanonicalModules D Sc m β.1) :
    ((probeOldBlockBraidSuffix D Sc m i Λ h₁ h₂ h₃ β).total M).hom =
      (inductionModuleCross (K β) (L β) (hδ β)).total ((induction (J β)).obj M.obj) := by
  rw [probeOldBlockBraidSuffix_total, probeOldBlockEqualCross_total]
  rfl

/-- The given negative block crossings satisfy the braid on all evaluated inputs. -/
theorem probeOldBlockEqualCross_braid (β : WeightBlocks D Λ x₀) :
    probeOldBlockBraidSuffix D Sc m i Λ h₁ h₂ h₃ β ≫
      probeOldBlockBraidPrefix D Sc m i Λ h₁ h₂ h₃ β ≫
        probeOldBlockBraidSuffix D Sc m i Λ h₁ h₂ h₃ β =
    probeOldBlockBraidPrefix D Sc m i Λ h₁ h₂ h₃ β ≫
      probeOldBlockBraidSuffix D Sc m i Λ h₁ h₂ h₃ β ≫
        probeOldBlockBraidPrefix D Sc m i Λ h₁ h₂ h₃ β := by
  apply OddMath.HomogeneousSuperfunctorIso.total_ext
  intro M
  rw [Superfunctor.comp_total, Superfunctor.comp_total,
    Superfunctor.comp_total, Superfunctor.comp_total]
  apply InducedCategory.hom_ext
  change ((probeOldBlockBraidSuffix D Sc m i Λ h₁ h₂ h₃ β).total M).hom ≫
      ((probeOldBlockBraidPrefix D Sc m i Λ h₁ h₂ h₃ β).total M).hom ≫
        ((probeOldBlockBraidSuffix D Sc m i Λ h₁ h₂ h₃ β).total M).hom =
    ((probeOldBlockBraidPrefix D Sc m i Λ h₁ h₂ h₃ β).total M).hom ≫
      ((probeOldBlockBraidSuffix D Sc m i Λ h₁ h₂ h₃ β).total M).hom ≫
        ((probeOldBlockBraidPrefix D Sc m i Λ h₁ h₂ h₃ β).total M).hom
  rw [probeOldBlockBraidPrefix_native_total, probeOldBlockBraidSuffix_native_total]
  exact (inductionModuleCross_braid (J β) (K β) (L β) (hγ β) (hδ β)
    (fun s => CyclotomicCrossingTensor.equalCrossComponent_braid D Sc (probeCutoff D m) i s.obj) M.obj).symm

end OddMath.QuiverHecke
