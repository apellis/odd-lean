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

/-- The fixed balanced quotient, named before constructing its grading. -/
abbrev actualShiftedCarrier (i : I) (v t : List I) :=
  BalancedInduction.Obj (append D Sc cutoff i) (coefficient D Sc cutoff 1 i v)
    (⟨t⟩ : OldCategory D Sc cutoff)

def actualShiftedSourceSpace (i : I) (v t : List I) : SVec k :=
  BalancedInduction.superspace (append D Sc cutoff i) (coefficient D Sc cutoff 1 i v)
    (⟨t⟩ : OldCategory D Sc cutoff)

/-- An actual counit component, followed by the prescribed full output twist. -/
def actualShiftedInputContraction (i : I) (v t : List I) :
    actualShiftedCarrier D Sc cutoff i v t →ₗ[k] Old D Sc cutoff v t :=
  (oldTwist D Sc cutoff 1 v t).comp
    ((shiftedSourceCounit D Sc cutoff i v).total (⟨t⟩ : OldCategory D Sc cutoff))

/-- Actual grading on the shifted source, then the actual induction dot.
The coefficient shift is part of this grading and must not be discarded. -/
def actualShiftedInputDot (j : {j : I // D.parity j = 1}) (v t : List I) :
    actualShiftedCarrier D Sc cutoff j.1 v t →ₗ[k]
      actualShiftedCarrier D Sc cutoff j.1 v t :=
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
    (v t : List I) (z : actualShiftedCarrier D Sc cutoff j.1 v t) :
    actualSourceInputContraction D Sc cutoff j v t
      (coefficientOneSourceEquiv D Sc cutoff j v t z) =
      actualShiftedInputContraction D Sc cutoff j.1 v t z := by
  simp only [actualSourceInputContraction, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]

theorem actualSourceInputDot_carrier (j : {j : I // D.parity j = 1})
    (v t : List I) (z : actualShiftedCarrier D Sc cutoff j.1 v t) :
    actualSourceInputDot D Sc cutoff j v t
      (coefficientOneSourceEquiv D Sc cutoff j v t z) =
      coefficientOneSourceEquiv D Sc cutoff j v t
        (actualShiftedInputDot D Sc cutoff j v t z) := by
  simp only [actualSourceInputDot, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]

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
  simp only [coefficientModuleForward_app, ↓reduceIte, one_ne_zero]
  change BalancedInduction.tensor (append D Sc cutoff i)
      (parityRestrictedRepresentable D Sc cutoff i v).toFunctor
      (⟨s⟩ : OldCategory D Sc cutoff) g b +
    BalancedInduction.tensor (append D Sc cutoff i)
      (parityRestrictedRepresentable D Sc cutoff i v).toFunctor
      (⟨s⟩ : OldCategory D Sc cutoff)
      (twist k 1 (X := (append D Sc cutoff i).obj (⟨s⟩ : OldCategory D Sc cutoff))
        (Y := (⟨t⟩ : OldCategory D Sc cutoff)) g) 0 =
    BalancedInduction.tensor (append D Sc cutoff i)
      (parityRestrictedRepresentable D Sc cutoff i v).toFunctor
      (⟨s⟩ : OldCategory D Sc cutoff) g b
  rw [BalancedInduction.tensor_zero_right, add_zero]

/-- The actual shifted counit acts by composition with the full kernel twist. -/
theorem shiftedSourceCounit_total_tensor (i : I) (v s t : List I)
    (g : Old D Sc cutoff (s ++ [i]) t) (b : Old D Sc cutoff v (s ++ [i])) :
    (shiftedSourceCounit D Sc cutoff i v).total (⟨t⟩ : OldCategory D Sc cutoff)
      (BalancedInduction.tensor (append D Sc cutoff i)
        (coefficientOneModule D Sc cutoff i v).toFunctor (⟨s⟩ : OldCategory D Sc cutoff) g b) =
      oldComp D Sc cutoff v (s ++ [i]) t b (oldTwist D Sc cutoff 1 (s ++ [i]) t g) := by
  have hmap : ((BalancedInduction.induction (append D Sc cutoff i)).mapIso
      (coefficientParityModuleIso D Sc cutoff i v)).hom =
      (BalancedInduction.induction (append D Sc cutoff i)).map
        (coefficientModuleForward D Sc cutoff i v) := rfl
  rw [shiftedSourceCounit, hmap, Superfunctor.comp_total, Superfunctor.comp_total]
  simp only [SVec.comp_apply]
  rw [inducedCoefficientForward_total_tensor]
  change (0 : Old D Sc cutoff v t) +
    ((show Old D Sc cutoff v t from BalancedInduction.counit (append D Sc cutoff i)
      (supermoduleParityObj (oldRepresentable D Sc cutoff
        (⟨v⟩ : OldCategory D Sc cutoff))).toFunctor (⟨t⟩ : OldCategory D Sc cutoff)
      (BalancedInduction.tensor (append D Sc cutoff i)
        ((append D Sc cutoff i) ⋙
          (supermoduleParityObj (oldRepresentable D Sc cutoff
            (⟨v⟩ : OldCategory D Sc cutoff))).toFunctor)
        (⟨s⟩ : OldCategory D Sc cutoff) g b)) + (0 : Old D Sc cutoff v t)) = _
  rw [add_zero, zero_add, BalancedInduction.counit_tensor]
  change (twist k 1
    (X := (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)).obj
      (⟨s ++ [i]⟩ : OldCategory D Sc cutoff))
    (Y := (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)).obj
      (⟨t⟩ : OldCategory D Sc cutoff))
    ((oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)).map
      (X := (⟨s ++ [i]⟩ : OldCategory D Sc cutoff))
      (Y := (⟨t⟩ : OldCategory D Sc cutoff)) g)) b = _
  rw [← Supercategory.map_twist, oldCategory_twist]
  rfl

/-- The actual cap retains parity on the entire coefficient, with arbitrary endpoints. -/
theorem actualShiftedInputContraction_tensor (i : I) (v s t : List I)
    (g : Old D Sc cutoff (s ++ [i]) t) (b : Old D Sc cutoff v (s ++ [i])) :
    actualShiftedInputContraction D Sc cutoff i v t
      (BalancedInduction.tensor (append D Sc cutoff i)
        (coefficientOneModule D Sc cutoff i v).toFunctor (⟨s⟩ : OldCategory D Sc cutoff) g b) =
      oldComp D Sc cutoff v (s ++ [i]) t
        (oldTwist D Sc cutoff 1 v (s ++ [i]) b) g := by
  have h := congrArg (oldTwist D Sc cutoff 1 v t)
    (shiftedSourceCounit_total_tensor D Sc cutoff i v s t g b)
  change oldTwist D Sc cutoff 1 v t
    ((shiftedSourceCounit D Sc cutoff i v).total (⟨t⟩ : OldCategory D Sc cutoff)
      (BalancedInduction.tensor (append D Sc cutoff i)
        (coefficientOneModule D Sc cutoff i v).toFunctor ⟨s⟩ g b)) = _
  refine h.trans ?_
  obtain ⟨g, rfl⟩ := (ideal D Sc cutoff (s ++ [i]) t).mkQ_surjective g
  obtain ⟨b, rfl⟩ := (ideal D Sc cutoff v (s ++ [i])).mkQ_surjective b
  change (ideal D Sc cutoff v t).mkQ (twist k 1 (b ≫ twist k 1 g)) =
    (ideal D Sc cutoff v t).mkQ (twist k 1 b ≫ g)
  rw [twist_comp, twist_twist]

private theorem induced_sgn_tensor
    {C T : Type u} [Category.{u} C] [Category.{u} T]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive T] [Linear k T] [Supercategory k T]
    (J : C ⥤ T) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    (M : Superfunctor k C (SVec k)) (v : C) (w : T)
    (h : J.obj v ⟶ w) (m : M.obj v) :
    (BalancedInduction.superspace J M.toFunctor w).sgn 1
        (BalancedInduction.tensor J M.toFunctor v h m) =
      BalancedInduction.tensor J M.toFunctor v
        (twist k 1 (X := J.obj v) (Y := w) h) ((M.obj v).sgn 1 m) := by
  rw [SVec.sgn_apply (BalancedInduction.superspace J M.toFunctor w) 1
    (BalancedInduction.tensor J M.toFunctor v h m), SVec.sgn_apply]
  simp only [sign_one, neg_one_smul, ← sub_eq_add_neg]
  rw [BalancedInduction.proj_tensor, BalancedInduction.proj_tensor]
  simp only [zero_add, SVec.zmod2_one_add_one]
  rw [twist_apply, sign_one, neg_one_smul, ← sub_eq_add_neg]
  simp only [BalancedInduction.tensor, TensorProduct.sub_tmul, TensorProduct.tmul_sub, map_sub]
  abel

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
  have hbt : oldTwist D Sc cutoff 1 v (s ++ [i]) b =
      oldProj D Sc cutoff v (s ++ [i]) 0 b - oldProj D Sc cutoff v (s ++ [i]) 1 b := by
    obtain ⟨a, rfl⟩ := (ideal D Sc cutoff v (s ++ [i])).mkQ_surjective b
    rw [oldProj_mk, oldProj_mk]
    change (ideal D Sc cutoff v (s ++ [i])).mkQ (twist k 1 a) = _
    rw [twist_apply, sign_one, neg_one_smul, ← sub_eq_add_neg, map_sub]
  have hsum : oldProj D Sc cutoff v (s ++ [i]) 0 b +
      oldProj D Sc cutoff v (s ++ [i]) 1 b = b := by
    obtain ⟨a, rfl⟩ := (ideal D Sc cutoff v (s ++ [i])).mkQ_surjective b
    rw [oldProj_mk, oldProj_mk, ← map_add, proj_add_proj]
  have hb : ((coefficientOneModule D Sc cutoff i v).obj
      (⟨s⟩ : OldCategory D Sc cutoff)).sgn 1 b =
      -oldTwist D Sc cutoff 1 v (s ++ [i]) b := by
    rw [SVec.sgn_apply ((coefficientOneModule D Sc cutoff i v).obj
      (⟨s⟩ : OldCategory D Sc cutoff)) 1 b, sign_one, neg_one_smul, ← sub_eq_add_neg]
    change (b - oldProj D Sc cutoff v (s ++ [i]) (1 + 1) b) -
      oldProj D Sc cutoff v (s ++ [i]) (1 + 1) b = _
    rw [SVec.zmod2_one_add_one, hbt]
    have hbsub : b - oldProj D Sc cutoff v (s ++ [i]) 0 b =
        oldProj D Sc cutoff v (s ++ [i]) 1 b :=
      sub_eq_iff_eq_add.mpr (hsum.symm.trans (add_comm _ _))
    rw [hbsub]
    abel
  have h := induced_sgn_tensor (append D Sc cutoff i)
    (coefficientOneModule D Sc cutoff i v) (⟨s⟩ : OldCategory D Sc cutoff)
    (⟨t⟩ : OldCategory D Sc cutoff) g b
  refine h.trans ?_
  rw [hb]
  simp only [BalancedInduction.tensor, TensorProduct.tmul_neg, map_neg]

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
  change actualInductionDot D Sc cutoff j.1 (coefficientOneModule D Sc cutoff j.1 v)
    (⟨t⟩ : OldCategory D Sc cutoff)
      ((actualShiftedSourceSpace D Sc cutoff j.1 v t).sgn 1
        (BalancedInduction.tensor (append D Sc cutoff j.1)
          (coefficientOneModule D Sc cutoff j.1 v).toFunctor ⟨s⟩ g b)) = _
  rw [actualShiftedSource_sgn_tensor,
    map_neg, actualInductionDot_tensor, j.property, twist_twist]

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
