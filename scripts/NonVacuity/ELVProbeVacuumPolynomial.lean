import OddMath.QuiverHecke.CyclotomicAction.ELVProbeVacuumPolynomial
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Mathlib.Tactic.FinCases
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.CyclotomicAction
namespace NonVacuity.ELVProbeVacuumPolynomial
private abbrev D := AsymmetricParameters.datum
private abbrev Sc := AsymmetricParameters.scalars
private def m (i : Bool) : ℕ := if i then 2 else 1
private abbrev a := probePolynomial (k := ℚ) (probeDotExponent D) m
private abbrev R₀ := SuperBimodule.regular (heightParity D Sc a (probePolynomial_parity D m) 0)
private abbrev M₀ := probeOldModule D m Sc [] R₀
private abbrev O₀ := probeOrdinaryModuleSuperfunctor D Sc m [] M₀
  (probeOldModule_evaluatesCoefficients D m Sc [] R₀)
private abbrev vac : OrdinaryContentCategory D Sc a [] := ⟨[], List.Perm.refl _⟩
private abbrev J (i : Bool) := probeOrdinaryAppend D Sc m [] i
private abbrev w (i : Bool) := (J i).obj vac
private abbrev P (i : Bool) := ELVOld.BalancedInduction.induced (J i) O₀
private def x (i : Bool) : End (P i) := ELVOld.BalancedInduction.transformComponent
  (probeOrdinaryAppendDot_supernatural D Sc m [] i) O₀

/-- The actual source relation is checked at both probe degrees two and four. -/
example (i : Bool) :
    ((End.of (probeOrdinaryAppendDot D Sc m [] i vac)) ^ probeDotExponent D i - 1) ^ m i = 0 :=
  probeOrdinaryVacuumDot_polynomial D Sc m i vac

example (i : Bool) :
    (ELVOld.BalancedInduction.transformLinear
      (probeOrdinaryAppendDot_supernatural D Sc m [] i) O₀ (w i) ^ 2 + 1) ^ m i = 0 :=
  probeOrdinaryVacuumInductionDot_odd D Sc m i rfl O₀ (w i)

/-- The relation holds before component evaluation, on the full induced supermodule. -/
example (i : Bool) : (x i ^ 2 + 1) ^ m i = 0 :=
  probeOrdinaryVacuumModuleDot_odd D Sc m i rfl O₀

/-- The hprobe input is the literal precomposition operator on supernatural Homs. -/
example (i : Bool) :
    SwappedVacuum.capPolynomial ((Polynomial.X ^ 2 + 1 : Polynomial ℚ) ^ m i).coeff (2 * m i)
      (show End (ModuleCat.of ℚ (P i ⟶ P i)) from
        ModuleCat.ofHom (Linear.leftComp ℚ (P i) (x i))) = 0 :=
  probeOrdinaryVacuumModuleHom_capPolynomial D Sc m i rfl O₀ (P i)

example (i : Bool) :
    let V := ELVOld.BalancedInduction.superspace (J i) O₀.toFunctor (w i)
    let d : End V := ELVOld.BalancedInduction.transformLinear
      (probeOrdinaryAppendDot_supernatural D Sc m [] i) O₀ (w i)
    (((PiSupercategory.pi (R := ℚ)).mapEnd V d) ^ 2 + 1) ^ m i = 0 :=
  probeOrdinaryVacuumParityDot_odd D Sc m i rfl O₀ (w i)

/-- An occupied signed plane independently detects the polynomial sign on Hom precomposition. -/
private abbrev Plane := ModuleCat.of ℚ (Fin 2 → ℚ)
private def d : Module.End ℚ (Fin 2 → ℚ) :=
  LinearMap.pi fun j => if j = 0 then -LinearMap.proj 1 else LinearMap.proj 0
private def matrixDot : End Plane := ModuleCat.ofHom d
private theorem square_plus_one : matrixDot ^ 2 + 1 = 0 := by
  apply (ModuleCat.endRingEquiv Plane).injective
  rw [map_add, map_pow, map_one, map_zero]
  change d ^ 2 + 1 = 0
  apply LinearMap.ext
  intro f
  funext j
  fin_cases j <;> simp [d, pow_two, Module.End.mul_apply]

private theorem matrixDot_ne_zero : matrixDot ≠ 0 := by
  intro hz
  have h := congrArg (ModuleCat.endRingEquiv Plane) hz
  change d = 0 at h
  have hh := congrFun (LinearMap.congr_fun h (fun j => if j = 0 then (1 : ℚ) else 0)) 1
  norm_num [d] at hh

example : (Linear.leftComp ℚ Plane matrixDot ^ 2 + 1) ^ 1 = 0 :=
  ELVOld.BalancedInduction.precompose_odd_probe_polynomial matrixDot 1
    (by simpa only [pow_one] using square_plus_one)

example : Linear.leftComp ℚ Plane matrixDot (𝟙 Plane) ≠ 0 := by
  simpa only [Linear.leftComp_apply, Category.comp_id] using matrixDot_ne_zero

end NonVacuity.ELVProbeVacuumPolynomial

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for owner in #[`OddMath.QuiverHecke.CyclotomicAction.ELVInductionPolynomialSigns,
      `OddMath.QuiverHecke.CyclotomicAction.ELVProbeVacuumPolynomial] do
    let some idx := env.header.moduleNames.idxOf? owner | throwError "Module not imported: {owner}"
    let names := env.header.moduleData[idx]!.constNames
    if names.isEmpty then throwError "No owned declarations: {owner}"
    for name in names do
      for axiomName in ← Lean.collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
          throwError "Disallowed axiom {axiomName} in {name}"
    logInfo m!"Audited {names.size} owned declarations in {owner}: standard axioms only"
