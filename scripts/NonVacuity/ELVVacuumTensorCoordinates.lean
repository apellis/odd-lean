import OddMath.QuiverHecke.CyclotomicAction.ELVVacuumTensorCoordinates
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedPowerCoefficients
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import OddMath.SKM.BubbleSubstitution
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open scoped TensorProduct
open ELVOld ELVOld.BalancedInduction ELVOld.CyclotomicCrossingTensor ELVOld.PowerVacuumCoefficient
open ELVOld.ProbeVacuumCap
namespace NonVacuity.ELVVacuumTensorCoordinates
private theorem nonzero_of_linear_image {U V : Type*} [AddCommGroup U] [Module ℚ U]
    [AddCommGroup V] [Module ℚ V] (f : U →ₗ[ℚ] V) (u : U) (v : V)
    (hv : v ≠ 0) (he : f u = v) : u ≠ 0 := by
  intro hu
  exact hv (he.symm.trans ((congrArg f hu).trans f.map_zero))
private theorem module_map_nonzero
    {C : Type*} [Category* C] [Preadditive C] [Linear ℚ C] [Supercategory ℚ C]
    {M N : Superfunctor ℚ C (SVec ℚ)} (f : M ⟶ N) (w : C)
    (u : M.obj w) (v : N.obj w) (hv : v ≠ 0) (he : f.total w u = v) : f ≠ 0 := by
  intro hf
  have hz : f.total w u = 0 := by
    rw [hf]
    simp only [SuperNatTrans.total, Superfunctor.zero_app, zero_add, SVec.zero_apply]
  exact hv (he.symm.trans hz)
private abbrev D := CyclotomicAction.AsymmetricParameters.datum
private abbrev Sc := CyclotomicAction.AsymmetricParameters.scalars
private def m (i : Bool) : ℕ := if i then 2 else 1
private def cutoff (i : Bool) : ℕ := if i then 6 else 4
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
private def occupied : (H.obj N₀).obj star :=
  (weightedEmptyEquiv D Sc cutoff L deltaClass) ⊗ₜ[ℚ] (probeVacuumScalarEquiv D Sc m 1)
private abbrev e := VacuumTensor.probeVacuumIso D Sc m cutoff bound W
private theorem vacuum_vector_nonzero : weightedEmptyEquiv D Sc cutoff L deltaClass ≠ 0 := by
  intro hz
  exact delta_ne_zero ((weightedEmptyEquiv D Sc cutoff L).injective (hz.trans (map_zero _).symm))
private theorem image_occupied : e.hom.total star occupied = weightedEmptyEquiv D Sc cutoff L deltaClass :=
  VacuumTensor.probeVacuumIso_hom_tmul D Sc m cutoff bound W star _

/-- The same surviving odd exterior coefficient occupies the tensor
vacuum and is sent to its unchanged literal A/T reservoir coordinate. -/
example : occupied ≠ 0 :=
  nonzero_of_linear_image (SVec.toLinearMap (e.hom.total star)) occupied _ vacuum_vector_nonzero image_occupied
example : e.hom.total star occupied = weightedEmptyEquiv D Sc cutoff L deltaClass := image_occupied
example : e.hom ≠ 0 := module_map_nonzero e.hom star occupied _ vacuum_vector_nonzero image_occupied

/-- Both directions of the genuine module isomorphism are even. -/
example : e.hom ∈ parity (R := ℚ) _ _ 0 := VacuumTensor.probeVacuumIso_hom_mem D Sc m cutoff bound W
example : e.inv ∈ parity (R := ℚ) _ _ 0 := VacuumTensor.probeVacuumIso_inv_mem D Sc m cutoff bound W

/-- The inverse identities are whole module identities, and the coordinate
formula applies to every vector, without scalar-only extraction. -/
example : e.hom ≫ e.inv = 𝟙 _ := e.hom_inv_id
example : e.inv ≫ e.hom = 𝟙 _ := e.inv_hom_id
example (c : ContentCategory D Sc cutoff bound 0) (v : W.obj c) :
    e.hom.total c (v ⊗ₜ[ℚ] probeVacuumScalarEquiv D Sc m 1) = v :=
  VacuumTensor.probeVacuumIso_hom_tmul D Sc m cutoff bound W c v
end NonVacuity.ELVVacuumTensorCoordinates
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVVacuumTensorCoordinates
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing module: {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module: {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited {names.size} owned declarations in {owner}: standard axioms"
