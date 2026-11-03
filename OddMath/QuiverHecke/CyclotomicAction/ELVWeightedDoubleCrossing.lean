import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedDoubleAppend
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedAppendCrossing
import OddMath.Algebra.FiniteSupermoduleFunctor

/-! # Signed crossing on the iterated weighted comparison

The iterated crossing in DeformedMatrixComparison (2), (4) is conjugated by
the chosen induction flattenings. The weighted comparison must intertwine
these given module maps, before the ordinary-adjunction mate is compared.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u

private theorem transform_total
    {k : Type u} [CommRing k] {C A : Type u} [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
    (M : Superfunctor k C (SVec k)) (w : A) :
    (BalancedInduction.transformComponent hα M).total w =
      BalancedInduction.transformLinear hα M w := by
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    simp only [SuperNatTrans.total, BalancedInduction.transformComponent_app,
      ite_true, ite_false, zero_ne_one, one_ne_zero, add_zero, zero_add]

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

private theorem descendedTransform_total
    (J : OldCategory D Sc cutoff ⥤ OldCategory D Sc cutoff)
    [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (hM : KillsWeightedCoefficients D Sc cutoff N (BalancedInduction.induced J M))
    (w : TruncatedCategory D Sc cutoff N) :
    (weightedModuleHom D Sc cutoff N _ _ hM hM
      (BalancedInduction.transformComponent hα M)).total w =
        BalancedInduction.transformLinear hα M (⟨w.word⟩ : OldCategory D Sc cutoff) := by
  exact transform_total J hα M ⟨w.word⟩

private theorem descended_conjugate
    (A B : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (hA : KillsWeightedCoefficients D Sc cutoff N A)
    (hB : KillsWeightedCoefficients D Sc cutoff N B) (e : A ≅ B) (x : B ⟶ B) :
    weightedModuleHom D Sc cutoff N A A hA hA (e.hom ≫ x ≫ e.inv) =
      (weightedModuleIso D Sc cutoff N A B hA hB e).hom ≫
        weightedModuleHom D Sc cutoff N B B hB hB x ≫
          (weightedModuleIso D Sc cutoff N A B hA hB e).inv := by
  rw [weightedModuleHom_comp, weightedModuleHom_comp]
  rfl

private theorem conjugated_square
    {C : Type*} [Category* C] {A B E F : C}
    (e : A ≅ B) (c : B ≅ E) (t : F ≅ E) (x : B ⟶ B) (y : E ⟶ E)
    (h : c.hom ≫ y = x ≫ c.hom) :
    (e ≪≫ c ≪≫ t.symm).hom ≫ (t.hom ≫ y ≫ t.inv) =
      (e.hom ≫ x ≫ e.inv) ≫ (e ≪≫ c ≪≫ t.symm).hom := by
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc c.hom y t.inv, h]
  simp only [Category.assoc]

private theorem descended_neg
    (A : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (hA : KillsWeightedCoefficients D Sc cutoff N A) (f : A ⟶ A) :
    weightedModuleHom D Sc cutoff N A A hA hA (-f) =
      -weightedModuleHom D Sc cutoff N A A hA hA f := by
  apply Superfunctor.hom_ext
  intro p v
  rfl

private theorem negative_square {C : Type*} [Category* C] [Preadditive C]
    {A B : C} (c : A ⟶ B) (x : A ⟶ A) (y : B ⟶ B)
    (h : c ≫ y = x ≫ c) : c ≫ (-y) = (-x) ≫ c := by
  rw [Preadditive.comp_neg, Preadditive.neg_comp, h]

variable (i : I)
local notation "J" => CyclotomicCrossingTensor.append D Sc cutoff i
local notation "Q" => oldTruncateFunctor D Sc cutoff N
local notation "T" => truncatedAppend D Sc cutoff N [i]
variable (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))
local notation "RM" => weightedRestriction D Sc cutoff N M
local notation "FP" => BalancedInduction.induced (J ⋙ J) RM
local notation "hFP" => pairInduced_killsWeightedCoefficients D Sc cutoff N i i RM
  (weightedRestriction_kills D Sc cutoff N M)

/-- The given crossing map on the descended old composed induction. -/
def weightedPairCrossing : weightedModule D Sc cutoff N FP hFP ⟶
    weightedModule D Sc cutoff N FP hFP :=
  weightedModuleHom D Sc cutoff N FP FP hFP hFP
    (BalancedInduction.transformComponent
      (CyclotomicCrossingTensor.equalCross_supernatural D Sc cutoff i) RM)

/-- The selected pair isomorphism intertwines the given module morphisms. -/
theorem pairWeightedModuleIso_crossing :
    (pairWeightedModuleIso D Sc cutoff N i i M).hom ≫
        BalancedInduction.transformComponent (truncatedEqualCross_supernatural D Sc cutoff N i) M =
      weightedPairCrossing D Sc cutoff N i M ≫
        (pairWeightedModuleIso D Sc cutoff N i i M).hom := by
  apply FiniteSupermodule.hom_ext_total
  intro v
  have hl := BalancedInduction.composition_total_linear
    (pairWeightedModuleIso D Sc cutoff N i i M).hom
    (BalancedInduction.transformComponent (truncatedEqualCross_supernatural D Sc cutoff N i) M) v
  have hr := BalancedInduction.composition_total_linear
    (weightedPairCrossing D Sc cutoff N i M)
    (pairWeightedModuleIso D Sc cutoff N i i M).hom v
  rw [transform_total] at hl
  have ho := descendedTransform_total D Sc cutoff N (J ⋙ J)
    (CyclotomicCrossingTensor.equalCross_supernatural D Sc cutoff i) RM hFP v
  change (weightedPairCrossing D Sc cutoff N i M).total v = _ at ho
  rw [ho] at hr
  exact hl.trans ((pairWeightedModuleIso_hom_crossing D Sc cutoff N i M ⟨v.word⟩).symm.trans hr.symm)

local notation "FI" => Functor.obj (BalancedInduction.induction J ⋙ BalancedInduction.induction J) RM
local notation "hFI" => doubleInduced_killsWeightedCoefficients D Sc cutoff N i i M

/-- Descent of the given old double-induction crossing, before its extra minus. -/
def weightedDoubleCrossing : weightedModule D Sc cutoff N FI hFI ⟶
    weightedModule D Sc cutoff N FI hFI :=
  weightedModuleHom D Sc cutoff N FI FI hFI hFI
    (CyclotomicCrossingTensor.equalCrossOnDoubleInduction D Sc cutoff i RM)

/-- The existing truncated last crossing conjugated by the selected flattening. -/
def truncatedDoubleCrossing :
    (BalancedInduction.induction T ⋙ BalancedInduction.induction T).obj M ⟶
      (BalancedInduction.induction T ⋙ BalancedInduction.induction T).obj M :=
  (BalancedInduction.inductionComp T T).hom.app M ≫
    BalancedInduction.transformComponent (truncatedEqualCross_supernatural D Sc cutoff N i) M ≫
      (BalancedInduction.inductionComp T T).inv.app M

private theorem weightedDoubleCrossing_eq :
    weightedDoubleCrossing D Sc cutoff N i M =
      (weightedInductionFlattening D Sc cutoff N i i M).hom ≫
        weightedPairCrossing D Sc cutoff N i M ≫
          (weightedInductionFlattening D Sc cutoff N i i M).inv :=
  descended_conjugate D Sc cutoff N FI FP hFI hFP
    ((BalancedInduction.inductionComp J J).app RM)
      (BalancedInduction.transformComponent
        (CyclotomicCrossingTensor.equalCross_supernatural D Sc cutoff i) RM)

/-- The selected iterated comparison intertwines the given old crossing and
its prescribed truncated crossing, with both flattenings attached. -/
theorem doubleWeightedModuleIso_crossing :
    (doubleWeightedModuleIso D Sc cutoff N i i M).hom ≫ truncatedDoubleCrossing D Sc cutoff N i M =
      weightedDoubleCrossing D Sc cutoff N i M ≫
        (doubleWeightedModuleIso D Sc cutoff N i i M).hom := by
  rw [weightedDoubleCrossing_eq]
  exact conjugated_square (weightedInductionFlattening D Sc cutoff N i i M)
    (pairWeightedModuleIso D Sc cutoff N i i M) ((BalancedInduction.inductionComp T T).app M)
    (weightedPairCrossing D Sc cutoff N i M)
    (BalancedInduction.transformComponent (truncatedEqualCross_supernatural D Sc cutoff N i) M)
    (pairWeightedModuleIso_crossing D Sc cutoff N i M)

/-- The exact given signed old crossing, descended at its prescribed degree. -/
def weightedSignedDoubleCrossing : weightedModule D Sc cutoff N FI hFI ⟶
    weightedModule D Sc cutoff N FI hFI :=
  weightedModuleHom D Sc cutoff N FI FI hFI hFI
    ((CyclotomicCrossingTensor.signedEqualInductionCross D Sc cutoff i).app
      (D.parity i * D.parity i) RM)

private theorem weightedSignedDoubleCrossing_eq :
    weightedSignedDoubleCrossing D Sc cutoff N i M = -weightedDoubleCrossing D Sc cutoff N i M := by
  unfold weightedSignedDoubleCrossing
  rw [CyclotomicCrossingTensor.signedEqualInductionCross_app, ite_eq_left rfl, descended_neg]
  rfl

/-- The given signed double-induction crossing is preserved by the selected
iterated weighted isomorphism. The prescribed extra minus appears on both sides. -/
theorem doubleWeightedModuleIso_signedCrossing :
    (doubleWeightedModuleIso D Sc cutoff N i i M).hom ≫ (-truncatedDoubleCrossing D Sc cutoff N i M) =
      weightedSignedDoubleCrossing D Sc cutoff N i M ≫
        (doubleWeightedModuleIso D Sc cutoff N i i M).hom := by
  rw [weightedSignedDoubleCrossing_eq]
  exact negative_square _ _ _ (doubleWeightedModuleIso_crossing D Sc cutoff N i M)

end OddMath.QuiverHecke.ELVOld
