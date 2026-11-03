import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedPolynomialCaps
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
open BalancedInduction CyclotomicCrossingTensor PowerVacuumCoefficient
namespace NonVacuity.ELVWeightedPolynomialCaps
private theorem shifted_difference {A : Type*} [Ring A] [Algebra ℚ A] (x z : A) :
    (x + 2) * z - (x - 2) * z = (4 : ℚ) • z := by
  rw [Algebra.smul_def]
  simp only [map_ofNat]
  noncomm_ring

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
private def cutoff (i : Bool) : ℕ := if i then 5 else 4
private def L (_ : Bool × ℕ) : ℕ := 4
private theorem positive (i : Bool) : 0 < cutoff i := by cases i <;> decide
private abbrev AQ := CoefficientPowerQuotient (k := ℚ) D cutoff L
private def plusSecond : Module.End ℚ AQ :=
  weightedPolynomialCapMoment D Sc cutoff L false (positive false) 2 1
private def minusSecond : Module.End ℚ AQ :=
  weightedCapMomentLinear D Sc cutoff L false (positive false) 1
    ((weightedModuleDot D Sc cutoff L false ^ 2 - 1) ^ 2)
private theorem large (i : Bool) : 4 ≤ cutoff i := by cases i <;> decide
private theorem powers_high (a : Bool × ℕ) : 4 ≤ L a * SKM.SYM.elementaryWeight D a := by
  change 4 ≤ 4 * SKM.SYM.elementaryWeight D a
  have hw : 0 < SKM.SYM.elementaryWeight D a := by
    unfold SKM.SYM.elementaryWeight
    split_ifs <;> omega
  omega
private def deltaClass (i : Bool) : AQ :=
  coefficientPowerQuotientMap (k := ℚ) D cutoff L (SKM.SYM.delta D ℚ ⟨i, rfl⟩)
private def chiClass (i : Bool) : AQ :=
  coefficientPowerQuotientMap (k := ℚ) D cutoff L (SKM.SYM.e D ℚ i 0)
private theorem delta_ne_zero (i : Bool) : deltaClass i ≠ 0 := by
  intro hz
  have hi := coefficientPowerQuotient_injective (k := ℚ) D cutoff L 1 4 (by decide) large powers_high
  have he := hi (a₁ := ⟨_, SKM.SYM.delta_mem_coefficientAtMost D ℚ ⟨i, rfl⟩⟩) (a₂ := 0)
    (by simpa only [deltaClass, ZeroMemClass.coe_zero, map_zero] using hz)
  have hδ : SKM.SYM.delta D ℚ ⟨i, rfl⟩ ≠ 0 := by
    rw [← SKM.SYM.coefficientBasis_delta]
    exact (SKM.SYM.coefficientBasis D ℚ).ne_zero _
  exact hδ (congrArg Subtype.val he)

/-- The closures are the given polynomial module-cap fields at every
exponent and on every coefficient input, without an extractor premise. -/
example (i : Bool) (M n : ℕ) (a : AQ) :=
  weightedPolynomialCapMoment_moduleCap D Sc cutoff L i (positive i) M n a

/-- Zero and strictly negative external heights retain their respective
reservoir cutoff signs on all input coefficients. -/
example (i : Bool) :
    weightedPolynomialCapMoment D Sc cutoff L i (positive i) 2 (cutoff i - 4) =
      LinearMap.mulLeft ℚ ((-1 : ℚ) ^ (cutoff i + 1) • deltaClass i) :=
  weightedPolynomialCapMoment_nonpositive_first_odd D Sc cutoff L i rfl (positive i) 2 (large i)

private theorem first_extract (i : Bool) :
    weightedPolynomialCapMoment D Sc cutoff L i (positive i) 2 (cutoff i - 4) (1 : AQ) =
      (-1 : ℚ) ^ (cutoff i + 1) • deltaClass i := by
  have h := LinearMap.congr_fun
    (weightedPolynomialCapMoment_nonpositive_first_odd D Sc cutoff L i rfl (positive i) 2 (large i)) (1 : AQ)
  change weightedPolynomialCapMoment D Sc cutoff L i (positive i) 2 (cutoff i - 4) 1 =
    (((-1 : ℚ) ^ (cutoff i + 1)) • deltaClass i) * 1 at h
  exact h.trans (mul_one _)

/-- The actual polynomial module cap itself is occupied at both heights. -/
example (i : Bool) : weightedPolynomialCap D Sc cutoff L i (positive i) 2 ≠ 0 := by
  have hv : (-1 : ℚ) ^ (cutoff i + 1) • deltaClass i ≠ 0 :=
    smul_ne_zero (pow_ne_zero _ (by norm_num : (-1 : ℚ) ≠ 0)) (delta_ne_zero i)
  have hc := weightedPolynomialCapMoment_moduleCap D Sc cutoff L i (positive i) 2 (cutoff i - 4) (1 : AQ)
  let w : ContentCategory D Sc cutoff (SKM.SYM.elvPowerWeightBound D cutoff L + 1) 0 :=
    ⟨⟨[]⟩, rfl⟩
  exact module_ne_zero_of_extracts _ w (weightedEmptyEquiv D Sc cutoff L).symm.toLinearMap
    _ _ hv (hc.symm.trans (first_extract i))

private theorem plus_eq : plusSecond = LinearMap.mulLeft ℚ (chiClass false + 2) :=
  weightedPolynomialCapMoment_second_four D Sc cutoff L false rfl (positive false) rfl
private theorem minus_eq : minusSecond = LinearMap.mulLeft ℚ (chiClass false - 2) :=
  weightedCapMomentLinear_minus_second_four D Sc cutoff L false rfl (positive false) rfl

/-- The plus-one and minus-one polynomials give chi_1+2 and chi_1-2
on the SAME actual weighted cap/dot/unit fields. -/
example (a : AQ) : plusSecond a = (chiClass false + 2) * a := by rw [plus_eq]; rfl
example (a : AQ) : minusSecond a = (chiClass false - 2) * a := by rw [minus_eq]; rfl
private theorem second_difference (a : AQ) : plusSecond a - minusSecond a = (4 : ℚ) • a := by
  rw [plus_eq, minus_eq]
  exact shifted_difference _ a

/-- The second closure distinguishes the probe polynomial sign on an
actual nonzero odd input, beyond their common monic first odd closure. -/
example : plusSecond (deltaClass true) ≠ minusSecond (deltaClass true) := by
  intro he
  have hz : (4 : ℚ) • deltaClass true = 0 :=
    (second_difference (deltaClass true)).symm.trans (sub_eq_zero.mpr he)
  have hfour : (4 : ℚ) ≠ 0 := by norm_num
  exact delta_ne_zero true ((smul_eq_zero (R := ℚ)).mp hz |>.resolve_left hfour)

end NonVacuity.ELVWeightedPolynomialCaps
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVWeightedPolynomialCaps
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing module: {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module: {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited {names.size} owned declarations in {owner}: standard axioms"
