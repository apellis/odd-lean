/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.InductionComposition

/-!
# The two-induction functor comparison

Ports the comparison in `Categorification/KLR/CyclotomicAction/Comparison.lean`
and the induction functors in `CyclotomicAction/Induction.lean` to supermodules.
The balanced tensor associator identifies successive induction with tensoring
by the two-colour corner. This even natural isomorphism is the comparison
needed to transport the corner crossing to composed induction functors.
-/

noncomputable section
open CategoryTheory StringDiagrams SuperBimodule
namespace OddMath.QuiverHecke
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
variable (i j : I) (a : I → _root_.Polynomial k)
  (ha : CyclotomicPolynomialParity D a) (n : ℕ)

local notation "P" => inductionCorner D Sc i a ha (n + 1)
local notation "Q" => inductionCorner D Sc j a ha n
local notation "T" => compositionCorner D Sc i j a ha n
local notation "F" => cyclotomicSuperInduction D Sc j a ha n ⋙
  cyclotomicSuperInduction D Sc i a ha (n + 1)

/-- Induction by the two-colour corner. -/
def compositionCornerFunctor :
    CyclotomicSupermodules D Sc a ha n ⥤ CyclotomicSupermodules D Sc a ha (n + 1 + 1) where
  obj M := tensor T M
  map f := whiskerLeft T f
  map_id M := whiskerLeft_id _ M
  map_comp f g := whiskerLeft_comp _ f g

instance compositionCornerFunctor_additive :
    (compositionCornerFunctor D Sc i j a ha n).Additive where
  map_add := by intros; apply whiskerLeft_add

instance compositionCornerFunctor_linear :
    (compositionCornerFunctor D Sc i j a ha n).Linear k where
  map_smul := by intros; apply whiskerLeft_smul

instance compositionCornerFunctor_super :
    Supercategory.IsSuperfunctor k (compositionCornerFunctor D Sc i j a ha n) where
  map_mem := fun hf => whiskerLeft_mem _ _ hf

/-- The corner isomorphism after tensoring with a supermodule. -/
def inductionCompositionTensorIso (M : CyclotomicSupermodules D Sc a ha n) :
    tensor (tensor P Q) M ≅ tensor T M where
  hom := whiskerRight (inductionCompositionIso D Sc i j a ha n).hom M
  inv := whiskerRight (inductionCompositionIso D Sc i j a ha n).inv M
  hom_inv_id := by rw [← comp_whiskerRight, Iso.hom_inv_id, id_whiskerRight]
  inv_hom_id := by rw [← comp_whiskerRight, Iso.inv_hom_id, id_whiskerRight]

/-- Reassociate, then multiply the two induction corners. -/
def inductionFunctorComparisonApp (M : CyclotomicSupermodules D Sc a ha n) :
    (F).obj M ≅ (compositionCornerFunctor D Sc i j a ha n).obj M :=
  (assoc P Q M).symm ≪≫ inductionCompositionTensorIso D Sc i j a ha n M

/-- The comparison has even parity. -/
theorem inductionFunctorComparisonApp_hom_mem (M : CyclotomicSupermodules D Sc a ha n) :
    (inductionFunctorComparisonApp D Sc i j a ha n M).hom ∈
      Supercategory.parity (R := k) _ _ 0 := by
  change ((assoc P Q M).inv ≫
    whiskerRight (inductionCompositionIso D Sc i j a ha n).hom M) ∈
      Supercategory.parity (R := k) (tensor P (tensor Q M)) (tensor T M) 0
  simpa only [add_zero] using Supercategory.comp_mem
    (assoc_inv_mem P Q M)
    (whiskerRight_mem _ (inductionCompositionIso_hom_mem D Sc i j a ha n) M)

/-- Its inverse is even as well. -/
theorem inductionFunctorComparisonApp_inv_mem (M : CyclotomicSupermodules D Sc a ha n) :
    (inductionFunctorComparisonApp D Sc i j a ha n M).inv ∈
      Supercategory.parity (R := k) _ _ 0 := by
  change (whiskerRight (inductionCompositionIso D Sc i j a ha n).inv M ≫
    (assoc P Q M).hom) ∈
      Supercategory.parity (R := k) (tensor T M) (tensor P (tensor Q M)) 0
  simpa only [add_zero] using Supercategory.comp_mem
    (whiskerRight_mem _ (inductionCompositionIso_inv_mem D Sc i j a ha n) M)
    (assoc_hom_mem P Q M)

/-- Naturality includes all homogeneous and inhomogeneous module maps. -/
theorem inductionFunctorComparisonApp_naturality
    {M N : CyclotomicSupermodules D Sc a ha n} (f : M ⟶ N) :
    (F).map f ≫ (inductionFunctorComparisonApp D Sc i j a ha n N).hom =
      (inductionFunctorComparisonApp D Sc i j a ha n M).hom ≫
        (compositionCornerFunctor D Sc i j a ha n).map f := by
  have hassoc : whiskerLeft P (whiskerLeft Q f) ≫ (assoc P Q N).inv =
      (assoc P Q M).inv ≫ whiskerLeft (tensor P Q) f := by
    apply (cancel_mono (assoc P Q N).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [assoc_naturality_right P Q M f, Iso.inv_hom_id_assoc]
  have hcorner : whiskerLeft (tensor P Q) f ≫
      whiskerRight (inductionCompositionIso D Sc i j a ha n).hom N =
      whiskerRight (inductionCompositionIso D Sc i j a ha n).hom M ≫ whiskerLeft T f := by
    refine Supercategory.induction_on (R := k) f ?_ (fun q g hg => ?_)
      (fun g h hg hh => ?_)
    · rw [whiskerLeft_zero, whiskerLeft_zero, Limits.zero_comp, Limits.comp_zero]
    · have h := super_interchange (tensor P Q) g
        (inductionCompositionIso_hom_mem D Sc i j a ha n) hg
      rw [Supercategory.koszulSign_zero_left, one_smul] at h
      exact h.symm
    · rw [whiskerLeft_add, whiskerLeft_add, Preadditive.add_comp,
        Preadditive.comp_add, hg, hh]
  change whiskerLeft P (whiskerLeft Q f) ≫ ((assoc P Q N).inv ≫
    whiskerRight (inductionCompositionIso D Sc i j a ha n).hom N) =
    ((assoc P Q M).inv ≫ whiskerRight (inductionCompositionIso D Sc i j a ha n).hom M) ≫
      whiskerLeft T f
  rw [← Category.assoc, hassoc, Category.assoc, hcorner, Category.assoc]

/-- Successive cyclotomic induction is naturally isomorphic to two-colour corner induction. -/
def inductionFunctorComparison : F ≅ compositionCornerFunctor D Sc i j a ha n :=
  NatIso.ofComponents (inductionFunctorComparisonApp D Sc i j a ha n)
    (fun f => inductionFunctorComparisonApp_naturality D Sc i j a ha n f)

/-- On pure tensors the comparison multiplies the two corner factors in order. -/
@[simp] theorem inductionFunctorComparison_hom_btmul
    (M : CyclotomicSupermodules D Sc a ha n) (x : (P).toSVec) (y : (Q).toSVec)
    (m : M.toSVec) :
    ((inductionFunctorComparison D Sc i j a ha n).hom.app M).1
      (btmul P (tensor Q M) x (btmul Q M y m)) =
      btmul T M (compositionCornerBi D Sc i j a ha n x y) m := by
  change (whiskerRight (inductionCompositionIso D Sc i j a ha n).hom M).1
    ((assoc P Q M).inv.1 (btmul P (tensor Q M) x (btmul Q M y m))) = _
  rw [assoc_inv_btmul, whiskerRight_btmul]
  rfl

end OddMath.QuiverHecke
