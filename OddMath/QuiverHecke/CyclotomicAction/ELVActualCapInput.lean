import OddMath.QuiverHecke.CyclotomicAction.ELVOldAppendDot

/-! # Actual cap and input-dot maps on arbitrary old Hom endpoints

The cap is the actual shifted adjunction counit followed by total output
parity. The input dot is the actual induction dot composed with actual
source grading. Since coefficient(1) is parity shifted, this source grading
contains an extra minus on tensors. No quotient annihilation or chosen
replacement map is assumed.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

abbrev actualShiftedSourceSpace (i : I) (v t : List I) : SVec k :=
  ((BalancedInduction.induction (append D Sc cutoff i)).obj
    (coefficientOneModule D Sc cutoff i v)).obj (⟨t⟩ : OldCategory D Sc cutoff)

/-- An actual counit component, followed by the prescribed full output twist. -/
def actualShiftedInputContraction (i : I) (v t : List I) :
    actualShiftedSourceSpace D Sc cutoff i v t →ₗ[k] Old D Sc cutoff v t :=
  (oldTwist D Sc cutoff 1 v t).comp
    ((shiftedSourceCounit D Sc cutoff i v).total (⟨t⟩ : OldCategory D Sc cutoff))

/-- Actual grading on the shifted source, then the actual induction dot.
The coefficient shift is part of this grading and must not be discarded. -/
def actualShiftedInputDot (j : {j : I // D.parity j = 1}) (v t : List I) :
    actualShiftedSourceSpace D Sc cutoff j.1 v t →ₗ[k]
      actualShiftedSourceSpace D Sc cutoff j.1 v t :=
  (actualInductionDot D Sc cutoff j.1 (coefficientOneModule D Sc cutoff j.1 v)
    (⟨t⟩ : OldCategory D Sc cutoff)).comp
      ((actualShiftedSourceSpace D Sc cutoff j.1 v t).sgn 1)

/-- The actual cap on the literal independently defined source. -/
def actualSourceInputContraction (j : {j : I // D.parity j = 1}) (v t : List I) :
    Source D Sc cutoff j.1 v t →ₗ[k] Old D Sc cutoff v t :=
  (actualShiftedInputContraction D Sc cutoff j.1 v t).comp
    (coefficientOneSourceEquiv D Sc cutoff j v t).symm.toLinearMap

/-- The actual input dot on the literal independently defined source. -/
def actualSourceInputDot (j : {j : I // D.parity j = 1}) (v t : List I) :
    Source D Sc cutoff j.1 v t →ₗ[k] Source D Sc cutoff j.1 v t :=
  (coefficientOneSourceEquiv D Sc cutoff j v t).toLinearMap.comp
    ((actualShiftedInputDot D Sc cutoff j v t).comp
      (coefficientOneSourceEquiv D Sc cutoff j v t).symm.toLinearMap)

theorem actualSourceInputContraction_carrier (j : {j : I // D.parity j = 1})
    (v t : List I) (z : actualShiftedSourceSpace D Sc cutoff j.1 v t) :
    actualSourceInputContraction D Sc cutoff j v t
      (coefficientOneSourceEquiv D Sc cutoff j v t z) =
      actualShiftedInputContraction D Sc cutoff j.1 v t z := by
  simp only [actualSourceInputContraction, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]

theorem actualSourceInputDot_carrier (j : {j : I // D.parity j = 1})
    (v t : List I) (z : actualShiftedSourceSpace D Sc cutoff j.1 v t) :
    actualSourceInputDot D Sc cutoff j v t
      (coefficientOneSourceEquiv D Sc cutoff j v t z) =
      coefficientOneSourceEquiv D Sc cutoff j v t
        (actualShiftedInputDot D Sc cutoff j v t z) := by
  simp only [actualSourceInputDot, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]

theorem parityIso_total_apply
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (t : OldCategory D Sc cutoff) (b : M.obj t) :
    (supermoduleParityIso M).hom.total t b = b := by
  change (0 : M.obj t) + b = b
  exact zero_add b

/-- The coefficient module comparison is identity on every underlying vector. -/
theorem inducedCoefficientForward_total_tensor (i : I) (v s t : List I)
    (g : Old D Sc cutoff (s ++ [i]) t) (b : Old D Sc cutoff v (s ++ [i])) :
    ((BalancedInduction.induction (append D Sc cutoff i)).map
      (coefficientModuleForward D Sc cutoff i v)).total (⟨t⟩ : OldCategory D Sc cutoff)
      (BalancedInduction.tensor (append D Sc cutoff i)
        (coefficientOneModule D Sc cutoff i v).toFunctor (⟨s⟩ : OldCategory D Sc cutoff) g b) =
      BalancedInduction.tensor (append D Sc cutoff i)
        (parityRestrictedRepresentable D Sc cutoff i v).toFunctor
        (⟨s⟩ : OldCategory D Sc cutoff) g b := by
  change (BalancedInduction.moduleMap (append D Sc cutoff i)
    (coefficientModuleForward D Sc cutoff i v)).total _
      (BalancedInduction.tensor _ _ _ g b) = _
  rw [BalancedInduction.moduleMap_total_tensor]
  simp only [coefficientModuleForward_app, ↓reduceIte, one_ne_zero,
    LinearMap.id_apply, LinearMap.zero_apply, BalancedInduction.tensor_zero_right, add_zero]

/-- The actual shifted counit acts by composition with the full kernel twist. -/
theorem shiftedSourceCounit_total_tensor (i : I) (v s t : List I)
    (g : Old D Sc cutoff (s ++ [i]) t) (b : Old D Sc cutoff v (s ++ [i])) :
    (shiftedSourceCounit D Sc cutoff i v).total (⟨t⟩ : OldCategory D Sc cutoff)
      (BalancedInduction.tensor (append D Sc cutoff i)
        (coefficientOneModule D Sc cutoff i v).toFunctor (⟨s⟩ : OldCategory D Sc cutoff) g b) =
      oldComp D Sc cutoff v (s ++ [i]) t b (oldTwist D Sc cutoff 1 (s ++ [i]) t g) := by
  rw [shiftedSourceCounit, Superfunctor.comp_total, Superfunctor.comp_total]
  simp only [SVec.comp_apply]
  rw [inducedCoefficientForward_total_tensor, parityIso_total_apply]
  change (BalancedInduction.counitTransform (append D Sc cutoff i)
    (supermoduleParityObj (oldRepresentable D Sc cutoff
      (⟨v⟩ : OldCategory D Sc cutoff)))).total _
      (BalancedInduction.tensor _ _ _ g b) = _
  simp only [SuperNatTrans.total, BalancedInduction.counitTransform_app,
    ↓reduceIte, one_ne_zero, SVec.add_apply, SVec.zero_apply, zero_add, add_zero]
  rw [BalancedInduction.counit_tensor]
  change (twist k 1 ((oldRepresentable D Sc cutoff
    (⟨v⟩ : OldCategory D Sc cutoff)).map g)) b = _
  rw [← Superfunctor.map_twist, oldCategory_twist]
  rfl

/-- The actual cap retains parity on the entire coefficient, with arbitrary endpoints. -/
theorem actualShiftedInputContraction_tensor (i : I) (v s t : List I)
    (g : Old D Sc cutoff (s ++ [i]) t) (b : Old D Sc cutoff v (s ++ [i])) :
    actualShiftedInputContraction D Sc cutoff i v t
      (BalancedInduction.tensor (append D Sc cutoff i)
        (coefficientOneModule D Sc cutoff i v).toFunctor (⟨s⟩ : OldCategory D Sc cutoff) g b) =
      oldComp D Sc cutoff v (s ++ [i]) t
        (oldTwist D Sc cutoff 1 v (s ++ [i]) b) g := by
  rw [actualShiftedInputContraction, LinearMap.comp_apply,
    shiftedSourceCounit_total_tensor]
  obtain ⟨g, rfl⟩ := (ideal D Sc cutoff (s ++ [i]) t).mkQ_surjective g
  obtain ⟨b, rfl⟩ := (ideal D Sc cutoff v (s ++ [i])).mkQ_surjective b
  change (ideal D Sc cutoff v t).mkQ (twist k 1 (b ≫ twist k 1 g)) =
    (ideal D Sc cutoff v t).mkQ (twist k 1 b ≫ g)
  rw [twist_comp, twist_twist]

/-- Actual grading on coefficient(1) contributes the shift minus, including
the entire old coefficient and the kernel-arrow parity. -/
theorem actualShiftedSource_sgn_tensor (i : I) (v s t : List I)
    (g : Old D Sc cutoff (s ++ [i]) t) (b : Old D Sc cutoff v (s ++ [i])) :
    (actualShiftedSourceSpace D Sc cutoff i v t).sgn 1
      (BalancedInduction.tensor (append D Sc cutoff i)
        (coefficientOneModule D Sc cutoff i v).toFunctor (⟨s⟩ : OldCategory D Sc cutoff) g b) =
      -BalancedInduction.tensor (append D Sc cutoff i)
        (coefficientOneModule D Sc cutoff i v).toFunctor (⟨s⟩ : OldCategory D Sc cutoff)
        (twist k 1 g) (oldTwist D Sc cutoff 1 v (s ++ [i]) b) := by
  have hb0 : ((coefficient D Sc cutoff 1 i v).obj (⟨s⟩ : OldCategory D Sc cutoff)).proj 0 b =
      oldProj D Sc cutoff v (s ++ [i]) 1 b := by
    rw [coefficientOne_obj_proj, SVec.piObj_proj, zero_add,
      Supercategory.homSVec_proj, oldCategory_proj]
  have hb1 : ((coefficient D Sc cutoff 1 i v).obj (⟨s⟩ : OldCategory D Sc cutoff)).proj 1 b =
      oldProj D Sc cutoff v (s ++ [i]) 0 b := by
    rw [coefficientOne_obj_proj, SVec.piObj_proj, SVec.zmod2_one_add_one,
      Supercategory.homSVec_proj, oldCategory_proj]
  rw [← oldCategory_twist D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)
    (⟨s ++ [i]⟩ : OldCategory D Sc cutoff) 1 b]
  change (BalancedInduction.superspace (append D Sc cutoff i)
      (coefficientOneModule D Sc cutoff i v).toFunctor (⟨t⟩ : OldCategory D Sc cutoff)).proj 0
        (BalancedInduction.tensor _ _ _ g b) -
    (BalancedInduction.superspace (append D Sc cutoff i)
      (coefficientOneModule D Sc cutoff i v).toFunctor (⟨t⟩ : OldCategory D Sc cutoff)).proj 1
        (BalancedInduction.tensor _ _ _ g b) =
      -BalancedInduction.tensor _ _ _ (twist k 1 g) (twist k 1 b)
  rw [BalancedInduction.proj_tensor, BalancedInduction.proj_tensor]
  simp only [zero_add, SVec.zmod2_one_add_one, hb0, hb1]
  rw [twist_apply, twist_apply]
  rw [oldCategory_proj D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)
      (⟨s ++ [i]⟩ : OldCategory D Sc cutoff) 0 b,
    oldCategory_proj D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)
      (⟨s ++ [i]⟩ : OldCategory D Sc cutoff) 1 b]
  change _ = -BalancedInduction.tensor _ _ _
    (proj k 0 g - proj k 1 g)
    (oldProj D Sc cutoff v (s ++ [i]) 0 b - oldProj D Sc cutoff v (s ++ [i]) 1 b)
  simp only [BalancedInduction.tensor, TensorProduct.sub_tmul, TensorProduct.tmul_sub,
    map_sub]
  abel

/-- The specified input-dot representative formula follows from the actual
dot and actual shifted grading, rather than from an assumed kernel map. -/
theorem actualShiftedInputDot_tensor (j : {j : I // D.parity j = 1})
    (v s t : List I) (g : Old D Sc cutoff (s ++ [j.1]) t)
    (b : Old D Sc cutoff v (s ++ [j.1])) :
    actualShiftedInputDot D Sc cutoff j v t
      (BalancedInduction.tensor (append D Sc cutoff j.1)
        (coefficientOneModule D Sc cutoff j.1 v).toFunctor (⟨s⟩ : OldCategory D Sc cutoff) g b) =
      -BalancedInduction.tensor (append D Sc cutoff j.1)
        (coefficientOneModule D Sc cutoff j.1 v).toFunctor (⟨s⟩ : OldCategory D Sc cutoff)
        (oldAppendDotComponent D Sc cutoff j.1 (⟨s⟩ : OldCategory D Sc cutoff) ≫ g)
        (oldTwist D Sc cutoff 1 v (s ++ [j.1]) b) := by
  rw [actualShiftedInputDot, LinearMap.comp_apply, actualShiftedSource_sgn_tensor,
    map_neg, actualInductionDot_tensor, j.property, twist_twist]

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
