import OddMath.QuiverHecke.CyclotomicAction.ELVTensorVacuumCap
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedPowerCoefficients
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import OddMath.SKM.BubbleSubstitution
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open scoped TensorProduct
open ELVOld ELVOld.BalancedInduction ELVOld.CyclotomicCrossingTensor ELVOld.PowerVacuumCoefficient
open ELVOld.ProbeVacuumCap
namespace NonVacuity.ELVTensorVacuumCap
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

private abbrev K (i : Bool) := contentAppendTo D Sc cutoff bound (0 : Multiset Bool) [i]
  ((0 : Multiset Bool) + ([i] : Multiset Bool)) (contentBlockCanonicalSum 0 [i])
private abbrev hDot (i : Bool) := contentBlockMatrixDot_supernatural D Sc cutoff bound 0 i
private theorem reservoir_positive (i : Bool) : 0 < cutoff i := by have := large i; omega
private def inverse (i : Bool) := Classical.choice
  (contentAbsentUnitInverse_nonempty D Sc cutoff bound 0 i (by simp) (H.obj N₀))
private theorem module_id_ne_zero
    {C : Type*} [Category* C] [Preadditive C] [Linear ℚ C] [Supercategory ℚ C]
    (M : Superfunctor ℚ C (SVec ℚ)) (w : C) (z : M.obj w) (hz : z ≠ 0) : (𝟙 M : M ⟶ M) ≠ 0 := by
  intro h
  have hh := congrArg (fun f : M ⟶ M => f.total w z) h
  simp only [SuperNatTrans.total, Superfunctor.id_app_zero, Superfunctor.id_app_one,
    Superfunctor.zero_app, add_zero] at hh
  change z = 0 at hh
  exact hz hh
private theorem row_ne_zero {C : Type*} [Category* C] [Preadditive C]
    {A B : C} (g : A ⟶ B) (r : B ⟶ A) (hr : g ≫ r = 𝟙 A)
    (hid : (𝟙 A : A ⟶ A) ≠ 0) : r ≠ 0 := by
  intro h
  rw [h, Limits.comp_zero] at hr
  exact hid hr.symm
private theorem occupied_ne_zero : occupied ≠ 0 :=
  nonzero_of_linear_image (SVec.toLinearMap (e.hom.total star)) occupied _ vacuum_vector_nonzero image_occupied

/-- The normalized cap on the literal tensor vacuum is the last native
inverse row, for odd colours with even and odd reservoir cutoffs. -/
example (i : Bool) : tensorPowerVacuumCap D Sc m cutoff L i (reservoir_positive i) =
    (inverse i).g' (cutoff i - 1) :=
  tensorPowerVacuumCap_eq_inverseRow D Sc m cutoff L i (reservoir_positive i) (inverse i)

example (i : Bool) : tensorPowerVacuumCap D Sc m cutoff L i (reservoir_positive i) ≠ 0 := by
  apply row_ne_zero (unitDotColumn (K i) (hDot i) (H.obj N₀) (cutoff i - 1))
  · exact (tensorPowerVacuumCap_unitDotColumn D Sc m cutoff L i (reservoir_positive i)
      (cutoff i - 1) (by have := reservoir_positive i; omega)).trans (ite_eq_left (by have := reservoir_positive i; omega))
  · exact module_id_ne_zero (H.obj N₀) star occupied occupied_ne_zero

/-- The comparison is a whole module square through the genuine even
H(N0) coordinate, retaining the same literal A/T cap. -/
example (i : Bool) := tensorPowerVacuumCap_compare D Sc m cutoff L i (reservoir_positive i)
example (i : Bool) := tensorPowerVacuumCap_mem D Sc m cutoff L i (reservoir_positive i)

/-- The exact unit/y/ell operator window holds on every vector, with all
hypotheses proved on the same occupied tensor-vacuum carrier. -/
example (i : Bool) (a : ℕ) (ha : a < cutoff i) :=
  tensorPowerVacuumCap_window D Sc m cutoff L i (reservoir_positive i) a ha
end NonVacuity.ELVTensorVacuumCap
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVTensorVacuumCap
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing module: {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module: {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited {names.size} owned declarations in {owner}: standard axioms"
