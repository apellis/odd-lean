import OddMath.QuiverHecke.CyclotomicAction.ELVProbeOldVacuumPolynomial
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Mathlib.Tactic.FinCases
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.CyclotomicAction
namespace NonVacuity.ELVProbeOldVacuumPolynomial
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

private abbrev vOld := ELVOld.oldContentObject D Sc (probeCutoff D m) []
  ⟨[], List.Perm.refl _⟩
private abbrev oldJ (i : Bool) := ELVOld.oldContentAppend D Sc (probeCutoff D m) [] i
private abbrev oldW (i : Bool) := (oldJ i).obj vOld
private abbrev oldP (i : Bool) := ELVOld.BalancedInduction.induced (oldJ i) M₀
private def oldX (i : Bool) : End (oldP i) := ELVOld.BalancedInduction.transformComponent
  (probeOldContentAppendDot_supernatural D Sc m [] i) M₀
private abbrev evaluates := probeOldModule_evaluatesCoefficients D m Sc [] R₀

example (i : Bool) : (probeOldContentInductionDot D Sc m [] i M₀ (oldW i) ^ 2 + 1) ^ m i = 0 :=
  probeOldVacuumInductionDot_odd D Sc m M₀ evaluates i rfl (oldW i)

example (i : Bool) : (oldX i ^ 2 + 1) ^ m i = 0 :=
  probeOldVacuumModuleDot_odd D Sc m M₀ evaluates i rfl

example (i : Bool) :
    SwappedVacuum.capPolynomial ((Polynomial.X ^ 2 + 1 : Polynomial ℚ) ^ m i).coeff (2 * m i)
      (show End (ModuleCat.of ℚ (oldP i ⟶ oldP i)) from
        ModuleCat.ofHom (Linear.leftComp ℚ (oldP i) (oldX i))) = 0 :=
  probeOldVacuumModuleHom_capPolynomial D Sc m M₀ evaluates i rfl (oldP i)

end NonVacuity.ELVProbeOldVacuumPolynomial

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVProbeOldVacuumPolynomial
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Module not imported: {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "No owned declarations: {owner}"
  for name in names do
    for axiomName in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
  logInfo m!"Audited {names.size} owned declarations in {owner}: standard axioms only"
