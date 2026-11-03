import OddMath.QuiverHecke.CyclotomicAction.ELVVacuumTensor
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedPowerCoefficients
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open scoped TensorProduct
open ELVOld ELVOld.BalancedInduction ELVOld.CyclotomicCrossingTensor ELVOld.PowerVacuumCoefficient
open ELVOld.ProbeVacuumCap
namespace NonVacuity.ELVVacuumTensor
private def tensorDetector {U V : Type*} [AddCommGroup U] [Module ℚ U]
    [AddCommGroup V] [Module ℚ V] (e : ℚ ≃ₗ[ℚ] V) : U ⊗[ℚ] V →ₗ[ℚ] U :=
  (TensorProduct.rid ℚ U).toLinearMap ∘ₗ TensorProduct.map LinearMap.id e.symm.toLinearMap
private theorem tensorDetector_tmul {U V : Type*} [AddCommGroup U] [Module ℚ U]
    [AddCommGroup V] [Module ℚ V] (e : ℚ ≃ₗ[ℚ] V) (u : U) :
    tensorDetector e (u ⊗ₜ[ℚ] e 1) = u := by
  simp only [tensorDetector, LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, TensorProduct.rid_tmul, one_smul]
private theorem module_id_ne_zero
    {C : Type*} [Category* C] [Preadditive C] [Linear ℚ C] [Supercategory ℚ C]
    (M : Superfunctor ℚ C (SVec ℚ)) (w : C) (z : M.obj w) (hz : z ≠ 0) : (𝟙 M : M ⟶ M) ≠ 0 := by
  intro h
  have hh := congrArg (fun f : M ⟶ M => f.total w z) h
  simp only [SuperNatTrans.total, Superfunctor.id_app_zero, Superfunctor.id_app_one,
    Superfunctor.zero_app, add_zero] at hh
  change z = 0 at hh
  exact hz hh
private theorem iso_hom_ne_zero {C : Type*} [Category* C] [Preadditive C]
    {M N : C} (e : M ≅ N) (hM : (𝟙 M : M ⟶ M) ≠ 0) : e.hom ≠ 0 := by
  intro hz
  have h := e.hom_inv_id
  rw [hz, Limits.zero_comp] at h
  exact hM h.symm

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
private theorem occupied_ne_zero : occupied ≠ 0 := by
  intro hz
  have hh := congrArg (tensorDetector (U := W.obj star) (probeVacuumScalarEquiv D Sc m)) hz
  change tensorDetector (probeVacuumScalarEquiv D Sc m)
    (weightedEmptyEquiv D Sc cutoff L deltaClass ⊗ₜ[ℚ] probeVacuumScalarEquiv D Sc m 1) = 0 at hh
  rw [tensorDetector_tmul] at hh
  exact delta_ne_zero ((weightedEmptyEquiv D Sc cutoff L).injective
    (hh.trans (map_zero _).symm))

/-- This is the literal tensor vacuum H, occupied by a surviving exterior
coefficient; it is not a zero Hom object. -/
example : occupied ≠ 0 := occupied_ne_zero


/-- The input map is the actual odd inverse of the module parity isomorphism. -/
private def oddInput : N₀ ⟶ supermoduleParityObj N₀ := (supermoduleParityIso N₀).inv
private theorem oddInput_mem : oddInput ∈ parity (R := ℚ) _ _ 1 :=
  inv_mem (supermoduleParityIso N₀) (supermoduleParityIso_hom_mem N₀)

/-- The actual odd input is preserved as a nonzero odd module map. -/
example : H.map oddInput ∈ parity (R := ℚ) _ _ 1 := IsSuperfunctor.map_mem oddInput_mem
example : H.map oddInput ≠ 0 :=
  iso_hom_ne_zero ((H.toFunctor).mapIso (supermoduleParityIso N₀).symm)
    (module_id_ne_zero (H.obj N₀) star occupied occupied_ne_zero)

/-- Both vector parities and an actual odd input arrow retain the Koszul factor. -/
example (p : ZMod 2) (v : W.obj star) (hv : v ∈ (W.obj star).part p)
    (w : N₀.obj (probeOldVacuumObject D Sc m)) :
    (H.map oddInput).app 1 star (v ⊗ₜ[ℚ] w) =
      sign ℚ (p * 1) • (v ⊗ₜ[ℚ] oddInput.app 1 (probeOldVacuumObject D Sc m) w) :=
  VacuumTensor.superfunctor_map_app_tmul W (probeOldVacuumObject D Sc m) oddInput p 1 star v hv w

/-- Evaluation on the actual regular probe has a surviving exterior vector. -/
example : (H.obj N₀).obj star := occupied
end NonVacuity.ELVVacuumTensor
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVVacuumTensor
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing module: {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module: {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited {names.size} owned declarations in {owner}: standard axioms"
