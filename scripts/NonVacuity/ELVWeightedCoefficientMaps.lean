import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedCoefficientMaps
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import OddMath.SKM.BubbleSubstitution
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
open BalancedInduction CyclotomicCrossingTensor PowerVacuumCoefficient
namespace NonVacuity.ELVWeightedCoefficientMaps
private theorem module_ne_zero_of_extracts
    {k C A : Type*} [CommRing k] [Category* C] [Preadditive C] [Linear k C] [Supercategory k C]
    [AddCommGroup A] [Module k A]
    {F G : Superfunctor k C (SVec k)} (f : F ⟶ G) (w : C)
    (decode : G.obj w →ₗ[k] A) (v : F.obj w) (a : A) (ha : a ≠ 0)
    (h : decode (f.total w v) = a) : f ≠ 0 := by
  intro hz
  have hf : f.total w v = 0 := by
    rw [hz]
    simp only [SuperNatTrans.total, Superfunctor.zero_app, zero_add, SVec.zero_apply]
  exact ha (h.symm.trans ((congrArg decode hf).trans decode.map_zero))

private abbrev D := CyclotomicAction.AsymmetricParameters.datum
private abbrev Sc := CyclotomicAction.AsymmetricParameters.scalars
private def cutoff (_ : Bool) : ℕ := 4
private def L (_ : Bool × ℕ) : ℕ := 4
private abbrev AQ := CoefficientPowerQuotient (k := ℚ) D cutoff L
private abbrev W := weightedVacuum D Sc cutoff L
private abbrev bound := SKM.SYM.elvPowerWeightBound D cutoff L + 1
private abbrev T (i : Bool) := truncatedAppend D Sc cutoff bound [i]
private abbrev s := (oldTruncateFunctor D Sc cutoff bound).obj (⟨[]⟩ : OldCategory D Sc cutoff)
private abbrev s₀ : ContentCategory D Sc cutoff bound 0 := ⟨⟨[]⟩, rfl⟩
private def topVector (i : Bool) (a : AQ) :=
  (unitDotColumn (T i) (truncatedDot_supernatural D Sc cutoff bound i) W 3).total s
    (weightedEmptyEquiv D Sc cutoff L a)
private theorem powers_high (a : Bool × ℕ) :
    4 ≤ L a * SKM.SYM.elementaryWeight D a := by
  change 4 ≤ 4 * SKM.SYM.elementaryWeight D a
  have hw : 0 < SKM.SYM.elementaryWeight D a := by
    unfold SKM.SYM.elementaryWeight
    split_ifs <;> omega
  omega
private def deltaClass (j : Bool) : AQ :=
  coefficientPowerQuotientMap (k := ℚ) D cutoff L (SKM.SYM.delta D ℚ ⟨j, rfl⟩)
private theorem deltaClass_ne_zero (j : Bool) : deltaClass j ≠ 0 := by
  intro hz
  have hi := coefficientPowerQuotient_injective (k := ℚ) D cutoff L 1 4 (by norm_num [cutoff])
    (fun _ => by rfl) powers_high
  have he := hi (a₁ := ⟨_, SKM.SYM.delta_mem_coefficientAtMost D ℚ ⟨j, rfl⟩⟩)
    (a₂ := 0) (by simpa only [deltaClass, ZeroMemClass.coe_zero, map_zero] using hz)
  have hδ : SKM.SYM.delta D ℚ ⟨j, rfl⟩ ≠ 0 := by
    rw [← SKM.SYM.coefficientBasis_delta]
    exact (SKM.SYM.coefficientBasis D ℚ).ne_zero _
  exact hδ (congrArg Subtype.val he)


private theorem extracts (i : Bool) (a : AQ) :
    (weightedEmptyEquiv D Sc cutoff L).symm
      ((weightedCoefficientCap D Sc cutoff i L (by norm_num [cutoff])).total s₀ (topVector i a)) = a := by
  have hc := weightedFunctional_coefficientCap D Sc cutoff i L (by norm_num [cutoff]) (topVector i a)
  have hw := weightedFunctional_unitDotColumn D Sc cutoff L i (by norm_num [cutoff])
    3 (by norm_num [cutoff]) a
  exact hc.symm.trans hw

private theorem row_degree (i : Bool) : (cutoff i - 1) • D.parity i = (1 : ZMod 2) := by
  cases i <;> decide

/-- The actual canonical-content inverse cap is an odd module morphism,
with both independent odd coefficient directions occupied. -/
example (i : Bool) : weightedCoefficientCap D Sc cutoff i L (by norm_num [cutoff]) ∈
    parity (R := ℚ) _ _ 1 := by
  simpa only [row_degree] using weightedCoefficientCap_mem D Sc cutoff i L (by norm_num [cutoff])

example (i j : Bool) : weightedCoefficientCap D Sc cutoff i L (by norm_num [cutoff]) ≠ 0 :=
  module_ne_zero_of_extracts _ s₀ (weightedEmptyEquiv D Sc cutoff L).symm.toLinearMap
    (topVector i (deltaClass j)) (deltaClass j) (deltaClass_ne_zero j) (extracts i (deltaClass j))

/-- The decoded module-map field extracts every actual A/T coefficient,
not only a scalar-valued special case. -/
example (i : Bool) (a : AQ) := extracts i a
end NonVacuity.ELVWeightedCoefficientMaps
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVWeightedCoefficientMaps
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing module: {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module: {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited {names.size} owned declarations in {owner}: standard axioms"
