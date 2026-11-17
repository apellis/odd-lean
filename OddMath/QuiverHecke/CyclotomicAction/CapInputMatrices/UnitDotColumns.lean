import StringDiagrams.Super.SVec
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.Module.LinearMap.End
import OddMath.Algebra.FiniteSupermoduleFunctor
import OddMath.QuiverHecke.CyclotomicAction.AppendContent.AppendDot
import OddMath.QuiverHecke.CyclotomicAction.AppendSourceRows.SourceSplitting
import OddMath.QuiverHecke.CyclotomicAction.InductionGridMate.InductionRepresentable
import OddMath.SKM.RouquierHomPostNaturalInverse

/-!
# Cap input matrices

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # Ordinary unit and dot columns of the positive matrix

The positive columns in DeformedMatrixComparison (4) are the ordinary
adjunction unit followed by induction-dot powers. Under the canonical
upper-Hom equivalence they are the literal output-polynomial columns,
with the prescribed odd dot-power scalar retained. Both moving parities
and complete old Hom coefficients are included.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The scalar introduced by iterating the ordinary induction dot. -/
def inductionUnitDotSign (p : ZMod 2) (n : ℕ) : k := sign k (n.choose 2 • p)

theorem inductionUnitDotSign_succ (p : ZMod 2) (n : ℕ) :
    inductionUnitDotSign (k := k) p (n + 1) =
      sign k (n • p) * inductionUnitDotSign (k := k) p n := by
  have he : (n + 1).choose 2 = n + n.choose 2 := by
    simpa only [Nat.choose_one_right] using Nat.choose_succ_succ n 1
  simp only [inductionUnitDotSign, he, add_nsmul, sign_add]

private def oldAppendPower (i : I) (t : OldCategory D Sc cutoff) (n : ℕ) :
    (append D Sc cutoff i).obj t ⟶ (append D Sc cutoff i).obj t :=
  (ideal D Sc cutoff _ _).mkQ (appendMovingPower D Sc cutoff i t.word n)

private theorem oldAppendPower_mem (i : I) (t : OldCategory D Sc cutoff) (n : ℕ) :
    oldAppendPower D Sc cutoff i t n ∈ parity (R := k) _ _ (n • D.parity i) := by
  apply Submodule.mem_map_of_mem
  rw [appendMovingPower_whisker]
  exact appendComponent_mem D Sc cutoff (firstDot_pow_parity D Sc i [] n) t.word

private theorem oldAppendPower_zero (i : I) (t : OldCategory D Sc cutoff) :
    oldAppendPower D Sc cutoff i t 0 = 𝟙 _ := by
  simp only [oldAppendPower, appendMovingPower, pow_zero, End.one_def, affineUnit_id]
  rfl

private theorem oldAppendPower_succ (i : I) (t : OldCategory D Sc cutoff) (n : ℕ) :
    oldAppendDotComponent D Sc cutoff i t ≫ oldAppendPower D Sc cutoff i t n =
      oldAppendPower D Sc cutoff i t (n + 1) := by
  rw [oldAppendDotComponent_eq]
  change (ideal D Sc cutoff _ _).mkQ
    (appendMovingPower D Sc cutoff i t.word 1 ≫ appendMovingPower D Sc cutoff i t.word n) = _
  congr 1
  unfold appendMovingPower
  rw [← affineUnit_comp]
  change affineUnit D Sc cutoff _ _
    ((dotE D Sc (t.word ++ [i]) t.word.length) ^ n *
      (dotE D Sc (t.word ++ [i]) t.word.length) ^ 1) = _
  rw [pow_one, ← pow_succ]

private theorem tensor_smul_first (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (s t : OldCategory D Sc cutoff) (c : k)
    (g : (append D Sc cutoff i).obj s ⟶ t) (b : M.obj s) :
    BalancedInduction.tensor (append D Sc cutoff i) M.toFunctor s (c • g) b =
      c • BalancedInduction.tensor (append D Sc cutoff i) M.toFunctor s g b := by
  simp only [BalancedInduction.tensor, ← TensorProduct.smul_tmul', map_smul]

/-- Powers on the actual unit tensor, including the odd power scalar. -/
theorem inductionDot_iterate_unit (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (t : OldCategory D Sc cutoff) (n : ℕ) (b : M.obj t) :
    (inductionDot D Sc cutoff i M ((append D Sc cutoff i).obj t))^[n]
      (BalancedInduction.unit (append D Sc cutoff i) M.toFunctor t b) =
      inductionUnitDotSign (k := k) (D.parity i) n •
        BalancedInduction.tensor (append D Sc cutoff i) M.toFunctor t
          (oldAppendPower D Sc cutoff i t n) b := by
  induction n with
  | zero =>
    simp only [Function.iterate_zero, id_eq, inductionUnitDotSign, Nat.choose_zero_succ,
      zero_nsmul, sign_zero, one_smul, oldAppendPower_zero, BalancedInduction.unit_apply]
  | succ n ih =>
    have hp : D.parity i * (n • D.parity i) = n • D.parity i := by
      rcases parity_eq_zero_or_one (D.parity i) with h | h <;> rw [h] <;> simp
    rw [Function.iterate_succ_apply', ih, map_smul, inductionDot_tensor,
      twist_of_mem (D.parity i) (oldAppendPower_mem D Sc cutoff i t n), hp,
      Linear.comp_smul, tensor_smul_first, smul_smul,
      oldAppendPower_succ, inductionUnitDotSign_succ, mul_comm]

/-- The packaged adjunction unit is the existing raw unit on every coefficient. -/
theorem adjunctionUnit_total_apply (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (t : OldCategory D Sc cutoff) (b : M.obj t) :
    ((BalancedInduction.adjunctionUnit (append D Sc cutoff i)).app M).total t b =
      BalancedInduction.unit (append D Sc cutoff i) M.toFunctor t b := by
  simp only [BalancedInduction.adjunctionUnit, Superfunctor.homMk, SuperNatTrans.total,
    BalancedInduction.unitTransform_app, ↓reduceIte, one_ne_zero, add_zero]
  rfl

/-- The ordinary categorical unit/dot column, in its canonical upper-Hom coordinates. -/
def inductionUnitDotColumn (i : I) (v t : List I) (n : ℕ) :
    Old D Sc cutoff v t →ₗ[k] Old D Sc cutoff (v ++ [i]) (t ++ [i]) :=
  (OldInductionRepresentable.upperHomEquiv D Sc cutoff i
    (⟨v⟩ : OldCategory D Sc cutoff) (⟨t⟩ : OldCategory D Sc cutoff)).toLinearMap.comp
      (((inductionDot D Sc cutoff i
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))
        ((append D Sc cutoff i).obj (⟨t⟩ : OldCategory D Sc cutoff))) ^ n).comp
        (BalancedInduction.unit (append D Sc cutoff i)
          (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)).toFunctor
          (⟨t⟩ : OldCategory D Sc cutoff)))

/-- No coefficient projection occurs: the actual categorical column equals
its prescribed scalar times the literal polynomial column on full Old(v,t). -/
theorem inductionUnitDotColumn_apply (i : I) (v t : List I) (n : ℕ)
    (b : Old D Sc cutoff v t) :
    inductionUnitDotColumn D Sc cutoff i v t n b =
      inductionUnitDotSign (k := k) (D.parity i) n •
        canonicalAppendTarget D Sc cutoff i v (t ++ [i])
          (appendOutputEmbedding D Sc cutoff i v t (Finsupp.single n b)) := by
  change OldInductionRepresentable.upperHomEquiv D Sc cutoff i
    (⟨v⟩ : OldCategory D Sc cutoff) (⟨t⟩ : OldCategory D Sc cutoff)
    (((inductionDot D Sc cutoff i
      (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))
      ((append D Sc cutoff i).obj (⟨t⟩ : OldCategory D Sc cutoff))) ^ n)
      (BalancedInduction.unit (append D Sc cutoff i)
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)).toFunctor
        (⟨t⟩ : OldCategory D Sc cutoff) b)) = _
  rw [Module.End.pow_apply, inductionDot_iterate_unit, map_smul]
  congr 1
  have hforward := OldInductionRepresentable.upperHomEquiv_tensor D Sc cutoff i
    (⟨v⟩ : OldCategory D Sc cutoff) (⟨t⟩ : OldCategory D Sc cutoff)
    (⟨t⟩ : OldCategory D Sc cutoff) (oldAppendPower D Sc cutoff i ⟨t⟩ n)
    (show (⟨v⟩ : OldCategory D Sc cutoff) ⟶ (⟨t⟩ : OldCategory D Sc cutoff) from b)
  refine hforward.trans ?_
  obtain ⟨r, rfl⟩ := (ideal D Sc cutoff v t).mkQ_surjective b
  rw [appendOutputEmbedding_single, canonicalAppendTarget_projection]
  rfl

/-- Finite polynomial assembly of the prescribed scalar-normalized ordinary columns. -/
def unitDotPolynomialMap (i : I) (v t : List I) :
    (ℕ →₀ Old D Sc cutoff v t) →ₗ[k] Old D Sc cutoff (v ++ [i]) (t ++ [i]) :=
  Finsupp.lsum k fun n => inductionUnitDotSign (k := k) (D.parity i) n •
    inductionUnitDotColumn D Sc cutoff i v t n

@[simp] theorem unitDotPolynomialMap_single (i : I) (v t : List I) (n : ℕ)
    (b : Old D Sc cutoff v t) :
    unitDotPolynomialMap D Sc cutoff i v t (Finsupp.single n b) =
      canonicalAppendTarget D Sc cutoff i v (t ++ [i])
        (appendOutputEmbedding D Sc cutoff i v t (Finsupp.single n b)) := by
  rw [unitDotPolynomialMap, Finsupp.lsum_single, LinearMap.smul_apply,
    inductionUnitDotColumn_apply, smul_smul]
  simp only [inductionUnitDotSign, Supercategory.sign_mul_self, one_smul]

/-- The whole polynomial column map equals the actual ordinary unit/dot assembly. -/
theorem unitDotPolynomialMap_eq (i : I) (v t : List I) :
    unitDotPolynomialMap D Sc cutoff i v t =
      (canonicalAppendTarget D Sc cutoff i v (t ++ [i])).comp
        (appendOutputEmbedding D Sc cutoff i v t) := by
  apply LinearMap.ext
  intro f
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add f g hf hg => simp only [map_add, hf, hg]
  | single n b => exact unitDotPolynomialMap_single D Sc cutoff i v t n b

end OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
end

end

section

/-! # The linear equivalence of the canonical actual source isomorphism

The component totals of the fixed shiftedSourceParityIso are inverse linear
maps. Composing with the literal coefficient(1) comparison identifies the
actual induction-restriction carrier with the prescribed balanced Source.
The actual counit square is retained. Higher dot/cap normalization is separate.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The underlying component equivalence of the fixed actual source isomorphism. -/
def shiftedSourceCanonicalEquiv (j : {j : I // D.parity j = 1}) (v t : List I) :
    ((BalancedInduction.induction (append D Sc cutoff j.1)).obj
      ((BalancedInduction.restriction (append D Sc cutoff j.1)).obj
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)))).obj
          (⟨t⟩ : OldCategory D Sc cutoff) ≃ₗ[k]
      Source D Sc cutoff j.1 v t :=
  (moduleIsoLinearEquiv (shiftedSourceParityIso D Sc cutoff j.1 v)
    (⟨t⟩ : OldCategory D Sc cutoff)).trans
      (coefficientOneSourceEquiv D Sc cutoff j v t)

@[simp] theorem shiftedSourceCanonicalEquiv_apply (j : {j : I // D.parity j = 1})
    (v t : List I)
    (x : ((BalancedInduction.induction (append D Sc cutoff j.1)).obj
      ((BalancedInduction.restriction (append D Sc cutoff j.1)).obj
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)))).obj
          (⟨t⟩ : OldCategory D Sc cutoff)) :
    shiftedSourceCanonicalEquiv D Sc cutoff j v t x =
      coefficientOneSourceEquiv D Sc cutoff j v t
        ((shiftedSourceParityIso D Sc cutoff j.1 v).hom.total
          (⟨t⟩ : OldCategory D Sc cutoff) x) := rfl

end OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
end

end

section

/-! # Actual cap and input-dot maps on arbitrary old Hom endpoints

The cap is the actual shifted adjunction counit followed by total output
parity. The input dot is the actual induction dot composed with actual
source grading. Since coefficient(1) is parity shifted, this source grading
contains an extra minus on tensors. No quotient annihilation or chosen
replacement map is assumed.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The fixed balanced quotient, named before constructing its grading. -/
abbrev shiftedCarrier (i : I) (v t : List I) :=
  BalancedInduction.Obj (append D Sc cutoff i) (coefficient D Sc cutoff 1 i v)
    (⟨t⟩ : OldCategory D Sc cutoff)

def shiftedSourceSpace (i : I) (v t : List I) : SVec k :=
  BalancedInduction.superspace (append D Sc cutoff i) (coefficient D Sc cutoff 1 i v)
    (⟨t⟩ : OldCategory D Sc cutoff)

/-- An actual counit component, followed by the prescribed full output twist. -/
def shiftedInputContraction (i : I) (v t : List I) :
    shiftedCarrier D Sc cutoff i v t →ₗ[k] Old D Sc cutoff v t :=
  (oldTwist D Sc cutoff 1 v t).comp
    ((shiftedSourceCounit D Sc cutoff i v).total (⟨t⟩ : OldCategory D Sc cutoff))

/-- Actual grading on the shifted source, then the actual induction dot.
The coefficient shift is part of this grading and must not be discarded. -/
def shiftedInputDot (j : {j : I // D.parity j = 1}) (v t : List I) :
    shiftedCarrier D Sc cutoff j.1 v t →ₗ[k]
      shiftedCarrier D Sc cutoff j.1 v t :=
  (inductionDot D Sc cutoff j.1 (coefficientOneModule D Sc cutoff j.1 v)
    (⟨t⟩ : OldCategory D Sc cutoff)).comp
      ((shiftedSourceSpace D Sc cutoff j.1 v t).sgn 1)

/-- The actual cap on the literal independently defined source. -/
def sourceInputContraction (j : {j : I // D.parity j = 1}) (v t : List I) :
    Source D Sc cutoff j.1 v t →ₗ[k] Old D Sc cutoff v t :=
  (shiftedInputContraction D Sc cutoff j.1 v t).comp
    (coefficientOneSourceEquiv D Sc cutoff j v t).symm.toLinearMap

/-- The actual input dot on the literal independently defined source. -/
def sourceInputDot (j : {j : I // D.parity j = 1}) (v t : List I) :
    Source D Sc cutoff j.1 v t →ₗ[k] Source D Sc cutoff j.1 v t :=
  (coefficientOneSourceEquiv D Sc cutoff j v t).toLinearMap.comp
    ((shiftedInputDot D Sc cutoff j v t).comp
      (coefficientOneSourceEquiv D Sc cutoff j v t).symm.toLinearMap)

theorem sourceInputContraction_carrier (j : {j : I // D.parity j = 1})
    (v t : List I) (z : shiftedCarrier D Sc cutoff j.1 v t) :
    sourceInputContraction D Sc cutoff j v t
      (coefficientOneSourceEquiv D Sc cutoff j v t z) =
      shiftedInputContraction D Sc cutoff j.1 v t z := by
  simp only [sourceInputContraction, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]

theorem sourceInputDot_carrier (j : {j : I // D.parity j = 1})
    (v t : List I) (z : shiftedCarrier D Sc cutoff j.1 v t) :
    sourceInputDot D Sc cutoff j v t
      (coefficientOneSourceEquiv D Sc cutoff j v t z) =
      coefficientOneSourceEquiv D Sc cutoff j v t
        (shiftedInputDot D Sc cutoff j v t z) := by
  simp only [sourceInputDot, LinearMap.comp_apply,
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
theorem shiftedInputContraction_tensor (i : I) (v s t : List I)
    (g : Old D Sc cutoff (s ++ [i]) t) (b : Old D Sc cutoff v (s ++ [i])) :
    shiftedInputContraction D Sc cutoff i v t
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
theorem shiftedSource_sgn_tensor (i : I) (v s t : List I)
    (g : Old D Sc cutoff (s ++ [i]) t) (b : Old D Sc cutoff v (s ++ [i])) :
    (shiftedSourceSpace D Sc cutoff i v t).sgn 1
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
theorem shiftedInputDot_tensor (j : {j : I // D.parity j = 1})
    (v s t : List I) (g : Old D Sc cutoff (s ++ [j.1]) t)
    (b : Old D Sc cutoff v (s ++ [j.1])) :
    shiftedInputDot D Sc cutoff j v t
      (BalancedInduction.tensor (append D Sc cutoff j.1)
        (coefficientOneModule D Sc cutoff j.1 v).toFunctor (⟨s⟩ : OldCategory D Sc cutoff) g b) =
      -BalancedInduction.tensor (append D Sc cutoff j.1)
        (coefficientOneModule D Sc cutoff j.1 v).toFunctor (⟨s⟩ : OldCategory D Sc cutoff)
        (oldAppendDotComponent D Sc cutoff j.1 (⟨s⟩ : OldCategory D Sc cutoff) ≫ g)
        (oldTwist D Sc cutoff 1 v (s ++ [j.1]) b) := by
  change inductionDot D Sc cutoff j.1 (coefficientOneModule D Sc cutoff j.1 v)
    (⟨t⟩ : OldCategory D Sc cutoff)
      ((shiftedSourceSpace D Sc cutoff j.1 v t).sgn 1
        (BalancedInduction.tensor (append D Sc cutoff j.1)
          (coefficientOneModule D Sc cutoff j.1 v).toFunctor ⟨s⟩ g b)) = _
  rw [shiftedSource_sgn_tensor,
    map_neg, inductionDot_tensor, j.property, twist_twist]

end OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
end

end

section

/-! # The input moving dot on the prescribed crossing source

The existing append moving operator is transported through the concrete
crossing decoder. Corrected rho and the actual short-column square prove
preservation of the Pprime relations, so the operator descends to the
independently prescribed cyclotomic source. This is input-oriented and
is not yet identified with the categorical signed-dot normalization.
-/
noncomputable section
namespace OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
open CategoryTheory StringDiagrams Supercategory
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

def crossingInputDotAffine (j : {j : I // D.parity j = 1}) (v : List I) :
    ShortTarget D Sc cutoff j.1 v v →ₗ[k] ShortTarget D Sc cutoff j.1 v v :=
  ShortCrossCoordinates.decode D Sc cutoff j.1 v v ∘ₗ
    appendMovingPowerTarget D Sc cutoff j.1 v (v ++ [j.1]) 1 ∘ₗ
      shortCross D Sc cutoff j.1 v v

/-- The concrete decoder retains the crossing residual and removes exactly
the existing output-polynomial coordinate. -/
theorem shortCross_decode_residual (i : I) (v t : List I)
    (z : AppendTarget D Sc cutoff i v (t ++ [i])) :
    shortCross D Sc cutoff i v t (ShortCrossCoordinates.decode D Sc cutoff i v t z) =
      z - appendOutputEmbedding D Sc cutoff i v t (appendC0 D Sc cutoff i v t z) := by
  have hz := appendC0_residual_mem D Sc cutoff i v t z
  rw [← ShortCrossCoordinates.range_shortCross] at hz
  obtain ⟨y, hy⟩ := hz
  have hd := congrArg (ShortCrossCoordinates.decode D Sc cutoff i v t) hy
  simp only [ShortCrossCoordinates.decode_shortCross, map_sub,
    ShortCrossCoordinates.decode_embedding, sub_zero] at hd
  rw [hd] at hy
  exact hy

/-- The moving input dot sends every Pprime relation to another Pprime relation. -/
theorem crossingInputDotAffine_pprime (j : {j : I // D.parity j = 1}) (v : List I)
    (a : PprimeDomain D Sc cutoff j.1 v v) :
    crossingInputDotAffine D Sc cutoff j v (pprime D Sc cutoff j.1 v v a) ∈
      LinearMap.range (pprime D Sc cutoff j.1 v v) := by
  have hz : boundaryRho D Sc cutoff j v (v ++ [j.1]) (alpha D Sc cutoff j.1 v v a) ∈
      LinearMap.range (alpha D Sc cutoff j.1 v v) := by
    rw [← ker_outputLongExtraction_eq_range_alpha D Sc cutoff 0 j.1 v,
      LinearMap.mem_ker, outputLongExtraction_boundaryRho,
      outputLongExtraction_alpha, map_zero]
  obtain ⟨a', ha'⟩ := hz
  refine ⟨a', ?_⟩
  change pprime D Sc cutoff j.1 v v a' =
    ShortCrossCoordinates.decode D Sc cutoff j.1 v v
      (appendMovingPowerTarget D Sc cutoff j.1 v (v ++ [j.1]) 1
        (shortCross D Sc cutoff j.1 v v (pprime D Sc cutoff j.1 v v a)))
  have hs := LinearMap.congr_fun (shortColumn_square D Sc cutoff j.1 v v) a
  have hs' := LinearMap.congr_fun (shortColumn_square D Sc cutoff j.1 v v) a'
  simp only [LinearMap.comp_apply] at hs hs'
  rw [← hs, ← pMap_boundaryRho, ← ha', hs', ShortCrossCoordinates.decode_shortCross]

theorem crossingInputDotAffine_ker_q (j : {j : I // D.parity j = 1}) (v : List I) :
    LinearMap.ker (q D Sc cutoff j.1 v v) ≤
      (LinearMap.ker (q D Sc cutoff j.1 v v)).comap
        (crossingInputDotAffine D Sc cutoff j v) := by
  intro z hz
  rw [← range_pprime_eq_ker_q] at hz
  obtain ⟨a, rfl⟩ := hz
  change crossingInputDotAffine D Sc cutoff j v (pprime D Sc cutoff j.1 v v a) ∈
    LinearMap.ker (q D Sc cutoff j.1 v v)
  rw [← range_pprime_eq_ker_q]
  exact crossingInputDotAffine_pprime D Sc cutoff j v a

/-- Concrete transport of the moving input dot to the original cyclotomic source. -/
def crossingInputDot (j : {j : I // D.parity j = 1}) (v : List I) :
    Source D Sc cutoff j.1 v v →ₗ[k] Source D Sc cutoff j.1 v v :=
  let e := (q D Sc cutoff j.1 v v).quotKerEquivOfSurjective (q_surjective D Sc cutoff j.1 v v)
  e.toLinearMap ∘ₗ
    (LinearMap.ker (q D Sc cutoff j.1 v v)).mapQ
      (LinearMap.ker (q D Sc cutoff j.1 v v)) (crossingInputDotAffine D Sc cutoff j v)
      (crossingInputDotAffine_ker_q D Sc cutoff j v) ∘ₗ e.symm.toLinearMap

@[simp] theorem crossingInputDot_q (j : {j : I // D.parity j = 1}) (v : List I)
    (z : ShortTarget D Sc cutoff j.1 v v) :
    crossingInputDot D Sc cutoff j v (q D Sc cutoff j.1 v v z) =
      q D Sc cutoff j.1 v v (crossingInputDotAffine D Sc cutoff j v z) := by
  simp only [crossingInputDot, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.mapQ_apply,
    LinearMap.quotKerEquivOfSurjective_apply_mk]

end OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
end

end
