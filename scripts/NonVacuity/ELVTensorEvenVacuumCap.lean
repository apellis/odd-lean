import OddMath.QuiverHecke.CyclotomicAction.ELVTensorEvenVacuumCap
import OddMath.QuiverHecke.CyclotomicAction.ELVVacuumTensorCoordinates
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedPowerCoefficients
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open scoped TensorProduct
open ELVOld ELVOld.BalancedInduction ELVOld.CyclotomicCrossingTensor ELVOld.PowerVacuumCoefficient
open ELVOld.ProbeVacuumCap
namespace NonVacuity.ELVTensorEvenVacuumCap
private theorem nonzero_of_linear_image {U V : Type*} [AddCommGroup U] [Module ℚ U]
    [AddCommGroup V] [Module ℚ V] (f : U →ₗ[ℚ] V) (u : U) (v : V)
    (hv : v ≠ 0) (he : f u = v) : u ≠ 0 := by
  intro hu
  exact hv (he.symm.trans ((congrArg f hu).trans f.map_zero))
private def D : SKM.Datum Bool (Bool → ℤ) :=
  { CyclotomicAction.AsymmetricParameters.datum with
    parity := fun i => if i then 1 else 0
    even_of_odd := fun i j _ => CyclotomicAction.AsymmetricParameters.datum.even_of_odd i j rfl }
private def Sc : SKM.Scalars D ℚ where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := by intro _; norm_num
private def sy : SKM.Symmetrizer D where
  d := fun i => if i then 1 else 2
  pos := by intro i; cases i <;> norm_num
  symm := by intro i j; cases i <;> cases j <;> rfl
private theorem hc : Sc.Homogeneous := by
  intro _ _ _ _ _ _ _ _ h
  exact (h rfl).elim
private def m (_ : Bool) : ℕ := 2
private def cutoff (i : Bool) : ℕ := if i then 5 else 4
private def L (_ : Bool × ℕ) : ℕ := 4
private abbrev bound := SKM.SYM.elvPowerWeightBound D cutoff L + 1
private abbrev R₀ := contentModuleTarget D Sc cutoff bound (0 : Multiset Bool)
private abbrev W : ContentModules D Sc cutoff bound 0 :=
  (restriction (contentInclusion D Sc cutoff bound 0)).obj (weightedVacuum D Sc cutoff L)
private def H : modulePiCategory D Sc m ⟶ R₀ := VacuumTensor.probeFunctor D Sc m cutoff bound W
private abbrev N₀ := probeOldVacuumRegular D Sc m
private abbrev star : ContentCategory D Sc cutoff bound 0 := ⟨⟨[]⟩, rfl⟩
private theorem positive (i : Bool) : 0 < probeCutoff D m i := by cases i <;> decide
private theorem large (i : Bool) : 4 ≤ cutoff i := by cases i <;> decide
private theorem powers_high (a : Bool × ℕ) : 4 ≤ L a * SKM.SYM.elementaryWeight D a := by
  change 4 ≤ 4 * SKM.SYM.elementaryWeight D a
  have hw : 0 < SKM.SYM.elementaryWeight D a := by
    unfold SKM.SYM.elementaryWeight
    split_ifs <;> omega
  omega
private abbrev AQ := CoefficientPowerQuotient (k := ℚ) D cutoff L
private def deltaClass : AQ :=
  coefficientPowerQuotientMap (k := ℚ) D cutoff L (SKM.SYM.delta D ℚ ⟨true, rfl⟩)
private theorem delta_ne_zero : deltaClass ≠ 0 := by
  intro hz
  have hi := coefficientPowerQuotient_injective (k := ℚ) D cutoff L 1 4 (by decide) large powers_high
  have he := hi (a₁ := ⟨_, SKM.SYM.delta_mem_coefficientAtMost D ℚ ⟨true, rfl⟩⟩) (a₂ := 0)
    (by simpa only [deltaClass, ZeroMemClass.coe_zero, map_zero] using hz)
  have hδ : SKM.SYM.delta D ℚ ⟨true, rfl⟩ ≠ 0 := by
    rw [← SKM.SYM.coefficientBasis_delta]
    exact (SKM.SYM.coefficientBasis D ℚ).ne_zero _
  exact hδ (congrArg Subtype.val he)
private def occupied : (H.obj N₀).obj star :=
  (weightedEmptyEquiv D Sc cutoff L deltaClass) ⊗ₜ[ℚ] (probeVacuumScalarEquiv D Sc m 1)
private abbrev e := VacuumTensor.probeVacuumIso D Sc m cutoff bound W
private theorem vacuum_vector_nonzero : weightedEmptyEquiv D Sc cutoff L deltaClass ≠ 0 := by
  intro hz
  exact delta_ne_zero ((weightedEmptyEquiv D Sc cutoff L).injective (hz.trans (map_zero _).symm))
private theorem image_occupied : e.hom.total star occupied = weightedEmptyEquiv D Sc cutoff L deltaClass :=
  VacuumTensor.probeVacuumIso_hom_tmul D Sc m cutoff bound W star _

private theorem occupied_ne_zero : occupied ≠ 0 :=
  nonzero_of_linear_image (SVec.toLinearMap (e.hom.total star)) occupied _ vacuum_vector_nonzero image_occupied

example : occupied ≠ 0 := occupied_ne_zero
example : D.parity false = 0 ∧ D.parity true = 1 := by decide

/-- Strictly negative height uses the actual even polynomial and inverse cap. -/
example := evaluatedMixedBend_even_polynomialCap_zero D Sc m cutoff L sy hc false rfl
  (positive false) (by decide) (by decide)

private def m₀ : Bool → ℕ := fun _ => 4
private theorem positive₀ (i : Bool) : 0 < probeCutoff D m₀ i := by cases i <;> decide
private def H₀ : modulePiCategory D Sc m₀ ⟶ R₀ :=
  VacuumTensor.probeFunctor D Sc m₀ cutoff bound W
private abbrev probe₀ := probeOldVacuumRegular D Sc m₀
private abbrev e₀ := VacuumTensor.probeVacuumIso D Sc m₀ cutoff bound W
private def occupied₀ : (H₀.obj probe₀).obj star :=
  (weightedEmptyEquiv D Sc cutoff L deltaClass) ⊗ₜ[ℚ] (probeVacuumScalarEquiv D Sc m₀ 1)
private theorem occupied₀_ne_zero : occupied₀ ≠ 0 :=
  nonzero_of_linear_image (SVec.toLinearMap (e₀.hom.total star)) occupied₀ _ vacuum_vector_nonzero
    (VacuumTensor.probeVacuumIso_hom_tmul D Sc m₀ cutoff bound W star _)
example : occupied₀ ≠ 0 := occupied₀_ne_zero

/-- At height zero the same cap comparison returns the chosen pre-cap exactly. -/
example := evaluatedMixedBend_even_polynomialCap_eq_preCap D Sc m₀ cutoff L sy hc false rfl
  (positive₀ false) (by decide) rfl
end NonVacuity.ELVTensorEvenVacuumCap
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for owner in #[`OddMath.QuiverHecke.CyclotomicAction.ELVTensorEvenVacuumCap] do
    let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing module: {owner}"
    let names := env.header.moduleData[idx]!.constNames
    if names.isEmpty then throwError "Empty module: {owner}"
    for name in names do
      for ax in ← Lean.collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {name}"
    logInfo m!"Audited {names.size} owned declarations in {owner}: standard axioms"
