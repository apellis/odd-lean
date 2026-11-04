import OddMath.QuiverHecke.CyclotomicAction.ELVProbePaddedVacuumBend
import OddMath.QuiverHecke.CyclotomicAction.ELVUnitDotComponents
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedPowerCoefficients
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightTensorVacuum
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open scoped TensorProduct
open CategoryTheory StringDiagrams Supercategory BicategoryStruct OddMath OddMath.QuiverHecke
open ELVOld.PowerVacuumCoefficient ELVOld ELVOld.BalancedInduction ELVOld.CyclotomicCrossingTensor CyclotomicAction
namespace NonVacuity.ELVProbePaddedVacuumBend
private abbrev D := AsymmetricParameters.datum
private abbrev originalSc := AsymmetricParameters.scalars
private abbrev Sc := parameterTwist D originalSc
private def cutoff (i : Bool) : ℕ := if i then 5 else 4
private def L (_ : Bool × ℕ) : ℕ := 4
private abbrev bound := SKM.SYM.elvPowerWeightBound D cutoff L + 1
private def Λ : Bool → ℤ := fun i => cutoff i
private theorem hc (i : Bool) : (cutoff i : ℤ) = D.h i Λ := rfl
private def raised (i : Bool) : Bool → ℤ := -Λ + D.α i
private theorem edge (i : Bool) : -Λ + D.α i = raised i := rfl
private def m (i : Bool) : ℕ := if i then 2 else 1
private def ΛP : Bool → ℤ := fun i => probeCutoff D m i
private theorem hcP (i : Bool) : (probeCutoff D m i : ℤ) = D.h i ΛP := rfl
private def muP (i : Bool) : Bool → ℤ := ΛP - D.α i
private theorem edgeP (i : Bool) : -ΛP + D.α i = -muP i := by unfold muP; abel
private theorem positive (i : Bool) : 0 < probeCutoff D m i := by cases i <;> decide
private abbrev W := elvRouquierFamily D Sc cutoff bound Λ hc
private def N : ELVWeightProduct D Sc cutoff bound Λ (-Λ) := fun β =>
  (restriction (contentInclusion D Sc cutoff bound β.1)).obj (weightedVacuum D Sc cutoff L)
private abbrev δ := WeightTensorVacuum.emptyBlock D Λ
private abbrev star : ContentCategory D Sc cutoff bound 0 := ⟨⟨[]⟩, rfl⟩
private def block (β : WeightBlocks D Λ (-Λ)) :=
  VacuumTensor.superfunctor (N β) (probeOldVacuumObject D Sc m)
private def outputFunctor : ProbeVacuumCap.modulePiCategory D Sc m ⥤ ELVWeightProduct D Sc cutoff bound Λ (-Λ) :=
  Functor.pi' fun β => (block β).toFunctor
private instance : outputFunctor.Additive where
  map_add := funext fun β => (block β).toFunctor.map_add
private instance : outputFunctor.Linear ℚ where
  map_smul f r := funext fun β => (block β).toFunctor.map_smul r f
private instance : IsSuperfunctor ℚ outputFunctor where
  map_mem hf β := IsSuperfunctor.map_mem (F := (block β).toFunctor) hf
private def H : ProbeVacuumCap.modulePiCategory D Sc m ⟶ W.obj (-Λ) := ⟨outputFunctor⟩
-- Both odd colours use the chosen occupied tensor-Hom input, with the
-- homogeneous parameter and all finite-window hypotheses discharged.
example (i : Bool) :=
  WeightTensorVacuum.paddedVacuumDx_odd D originalSc m cutoff bound ΛP Λ hcP hc H i
    AsymmetricParameters.symmetrizer AsymmetricParameters.homogeneous (positive i) rfl

private theorem large (i : Bool) : 4 ≤ cutoff i := by cases i <;> decide
private theorem powers_high (a : Bool × ℕ) : 4 ≤ L a * SKM.SYM.elementaryWeight D a := by
  change 4 ≤ 4 * SKM.SYM.elementaryWeight D a
  have hw : 0 < SKM.SYM.elementaryWeight D a := by
    unfold SKM.SYM.elementaryWeight
    split_ifs <;> omega
  omega
private abbrev AQ := CoefficientPowerQuotient (k := ℚ) D cutoff L
private def deltaClass : AQ :=
  coefficientPowerQuotientMap (k := ℚ) D cutoff L (SKM.SYM.delta D ℚ ⟨false, rfl⟩)
private theorem delta_ne_zero : deltaClass ≠ 0 := by
  intro hz
  have hi := coefficientPowerQuotient_injective (k := ℚ) D cutoff L 1 4 (by decide) large powers_high
  have he := hi (a₁ := ⟨_, SKM.SYM.delta_mem_coefficientAtMost D ℚ ⟨false, rfl⟩⟩) (a₂ := 0)
    (by simpa only [deltaClass, ZeroMemClass.coe_zero, map_zero] using hz)
  have hδ : SKM.SYM.delta D ℚ ⟨false, rfl⟩ ≠ 0 := by
    rw [← SKM.SYM.coefficientBasis_delta]
    exact (SKM.SYM.coefficientBasis D ℚ).ne_zero _
  exact hδ (congrArg Subtype.val he)
private def occupied : (N δ).obj star := weightedEmptyEquiv D Sc cutoff L deltaClass
private theorem occupied_ne_zero : occupied ≠ 0 := by
  intro hz
  exact delta_ne_zero ((weightedEmptyEquiv D Sc cutoff L).injective (hz.trans (map_zero _).symm))
example : occupied ≠ 0 := occupied_ne_zero
private abbrev tensorOutput := VacuumTensor.probeFunctor D Sc m cutoff bound (N δ)
private def occupiedTensor : (tensorOutput.obj (probeOldVacuumRegular D Sc m)).obj star :=
  occupied ⊗ₜ[ℚ] (probeVacuumScalarEquiv D Sc m 1)
private theorem occupiedTensor_ne_zero : occupiedTensor ≠ 0 := by
  intro hz
  let f := SVec.toLinearMap ((VacuumTensor.probeVacuumIso D Sc m cutoff bound (N δ)).hom.total star)
  have he := VacuumTensor.probeVacuumIso_hom_tmul D Sc m cutoff bound (N δ) star occupied
  change f occupiedTensor = occupied at he
  exact occupied_ne_zero (he.symm.trans ((congrArg f hz).trans f.map_zero))
example : occupiedTensor ≠ 0 := occupiedTensor_ne_zero
example : probeOldVacuumVector D Sc m ≠ 0 := probeOldVacuumVector_ne_zero D Sc m


private theorem count_pos (i : Bool) : 0 < contentUnitCount D cutoff i δ.1 := by
  change 0 < contentUnitCount D cutoff i (([] : List Bool) : Multiset Bool)
  rw [VacuumCoefficient.count]
  have := large i
  omega
private abbrev K (i : Bool) := elvBlockAppend D Sc cutoff bound i Λ (edge i) δ
private def inverse (i : Bool) := Classical.choice
  (contentAbsentUnitTargetInverse_nonempty D Sc cutoff bound δ.1
    (blockSucc D Λ i (edge i) δ).1 i (elvBlockSucc_content_eq D i Λ (edge i) δ)
    (by change i ∉ (0 : Multiset Bool); simp) (N δ))

private theorem column_ne_zero {C : Type*} [Category* C] [Preadditive C]
    {A B : C} (g : A ⟶ B) (r : B ⟶ A) (hr : g ≫ r = 𝟙 A)
    (hid : (𝟙 A : A ⟶ A) ≠ 0) : g ≠ 0 := by
  intro h
  rw [h, Limits.zero_comp] at hr
  exact hid hr.symm
private theorem occupied_id_ne_zero : (𝟙 (N δ) : End (N δ)) ≠ 0 := by
  intro h
  have he := congrArg (fun f : End (N δ) => f.total star occupied) h
  simp only [SuperNatTrans.total, Superfunctor.id_app_zero, Superfunctor.id_app_one,
    Superfunctor.zero_app, add_zero] at he
  change occupied = 0 at he
  exact occupied_ne_zero he

-- The compared post-unit has an occupied first coefficient column.
private theorem first_column_nonzero (i : Bool) :
    unitDotColumn (K i) (elvBlockGridDot_supernatural D Sc cutoff bound i Λ (edge i) δ) (N δ) 0 ≠ 0 := by
  apply column_ne_zero _ ((inverse i).g' 0) _ occupied_id_ne_zero
  simpa only [ite_true] using (inverse i).gg 0 0 (count_pos i) (count_pos i)
example (i : Bool) :
    unitDotColumn (K i) (elvBlockGridDot_supernatural D Sc cutoff bound i Λ (edge i) δ) (N δ) 0 ≠ 0 :=
  first_column_nonzero i
end NonVacuity.ELVProbePaddedVacuumBend
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for owner in #[`OddMath.SKM.RouquierHomWeightCoordinates,
      `OddMath.QuiverHecke.CyclotomicAction.ELVProbePaddedVacuumBend] do
    let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
    let names := env.header.moduleData[idx]!.constNames
    if names.isEmpty then throwError "Empty owned declarations"
    for name in names do
      for ax in ← Lean.collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Unexpected axiom {ax} in {name}"
    logInfo m!"Audited all {names.size} owned declarations of {owner}: standard axioms only"
