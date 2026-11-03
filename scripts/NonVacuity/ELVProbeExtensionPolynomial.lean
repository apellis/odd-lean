import OddMath.QuiverHecke.CyclotomicAction.ELVProbeExtensionPolynomial
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeVacuumUnit
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.ELVOld OddMath.QuiverHecke.ELVOld.BalancedInduction
open OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
namespace NonVacuity.ELVProbeExtensionPolynomial
private abbrev D := CyclotomicAction.AsymmetricParameters.datum
private abbrev Sc := CyclotomicAction.AsymmetricParameters.scalars
private def m (i : Bool) : ℕ := if i then 2 else 1
private theorem positive (i : Bool) : 0 < probeCutoff D m i := by cases i <;> decide
private abbrev N := probeOldVacuumRegular D Sc m
private abbrev J := oldContentInclusion D Sc (probeCutoff D m) []
private abbrev L := induced J N
private abbrev t := OldContentCategory.obj (probeOldVacuumObject D Sc m)
private abbrev w (i : Bool) :=
  (oldContentAppend D Sc (probeCutoff D m) [] i).obj (probeOldVacuumObject D Sc m)
private abbrev V (i : Bool) := Obj (append D Sc (probeCutoff D m) i) L.toFunctor (w i).obj
private def d (i : Bool) : Module.End ℚ (V i) :=
  actualInductionDot D Sc (probeCutoff D m) i L (w i).obj

open ProbeExtensionCoefficient
private def z (i : Bool) : V i :=
  unit (append D Sc (probeCutoff D m) i) L.toFunctor t (scalarUnit D Sc m 1)

private theorem z_ne_zero (i : Bool) : z i ≠ 0 := by
  intro hz
  have hinj := oldVacuumInductionUnit_injective D Sc (probeCutoff D m) L i (positive i)
  have hs : scalarUnit D Sc m (1 : ℚ) = 0 := hinj (hz.trans (map_zero _).symm)
  have h := scalarCoordinate_unit D Sc m (1 : ℚ)
  rw [hs, map_zero] at h
  norm_num at h

example (i : Bool) : z i ≠ 0 := z_ne_zero i

private theorem polynomial (i : Bool) : (d i ^ 2 + 1) ^ m i = 0 :=
  extensionDot_odd D Sc m i rfl (w i)

private theorem signed_square : d false (d false (z false)) = -(z false) := by
  have h := polynomial false
  change d false ^ 2 + 1 = 0 at h
  have hv := LinearMap.congr_fun h (z false)
  change d false (d false (z false)) + z false = 0 at hv
  exact eq_neg_of_add_eq_zero_left hv

example : d false (d false (z false)) = -(z false) := signed_square

example : (d false ^ 2 - 1 : Module.End ℚ (V false)) (z false) ≠ 0 := by
  intro h
  have hh : d false (d false (z false)) - z false = 0 := h
  rw [signed_square] at hh
  have hp : z false + z false = 0 := by
    simpa only [sub_eq_add_neg, neg_add_rev, neg_neg, neg_zero] using congrArg Neg.neg hh
  have hs : (2 : ℚ) • z false = 0 := by simpa only [two_smul] using hp
  exact z_ne_zero false ((smul_eq_zero.mp hs).resolve_left (by norm_num))

example : (d true ^ 2 + 1) ^ 2 = 0 := polynomial true

end NonVacuity.ELVProbeExtensionPolynomial

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVProbeExtensionPolynomial
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Module not imported: {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "No owned declarations: {owner}"
  for name in names do
    for axiomName in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
  logInfo m!"Audited {names.size} owned declarations in {owner}: standard axioms only"
