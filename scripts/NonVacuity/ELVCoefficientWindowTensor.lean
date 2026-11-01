import OddMath.QuiverHecke.CyclotomicAction.ELVCoefficientWindowTensor
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Tactic.NormNum
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams
open OddMath OddMath.QuiverHecke
namespace OddMath.QuiverHecke.CoefficientWindowExamples
private abbrev D := CyclotomicAction.AsymmetricParameters.datum
private abbrev Sc := CyclotomicAction.AsymmetricParameters.scalars
private abbrev U := SKM.SYM.CoefficientAtMost D ℚ 3
private abbrev H :=
  (pres D Sc).obj (ob D [false, true]) ⟶ (pres D Sc).obj (ob D [true, false])

private theorem crossingTarget :
    tgt [false, true] (cw (Categorification.TypeA.canWord 2 (Equiv.swap 0 1))) = [true, false] := by
  apply List.ext_getElem (by simp)
  intro n hn hm
  have hn2 : n < 2 := by simpa using hn
  let q : Fin 2 := ⟨n, hn2⟩
  have he := tgt_cw_getElem
    (Categorification.TypeA.validWord_canWord 2 (Equiv.swap 0 1))
    (t := [false, true]) rfl q
  rw [Categorification.TypeA.wordProd_canWord] at he
  rw [he]
  interval_cases n <;> norm_num [q, Equiv.swap_apply_def, Fin.ext_iff]

private def crossingIndex : NFIdx [false, true] [true, false] := by
  refine ⟨([], Equiv.swap 0 1), by simp, by simp, ?_⟩
  change SChain [false, true]
    (pl [false, true] (cw (Categorification.TypeA.canWord 2 (Equiv.swap 0 1)))) [true, false]
  have ht := crossingTarget
  simpa only [ht] using
    sChain_pl [false, true] (cw (Categorification.TypeA.canWord 2 (Equiv.swap 0 1)))


private def exteriorIndex : SKM.SYM.CoefficientIndex D :=
  (0, {⟨false, rfl⟩})

private def oddCoefficient : U :=
  ⟨SKM.SYM.coefficientBasis D ℚ exteriorIndex,
    Submodule.subset_span ⟨exteriorIndex, by
      simp [exteriorIndex, SKM.SYM.coefficientWeight], rfl⟩⟩

private def crossing : H := basisNF D Sc [false, true] [true, false] crossingIndex

private def testTensor : coefficientWindowTensor D Sc 3 [false, true] [true, false] :=
  oddCoefficient ⊗ₜ[ℚ] crossing

private theorem testTensor_ne_zero : testTensor ≠ 0 := by
  have hc : oddCoefficient ≠ 0 := by
    intro h
    apply (SKM.SYM.coefficientBasis D ℚ).ne_zero exteriorIndex
    exact congrArg (fun a : U => a.val) h
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one ℚ hc
  intro hz
  have he : (TensorProduct.lid ℚ H)
      (TensorProduct.map φ (LinearMap.id : H →ₗ[ℚ] H) testTensor) = 0 := by
    rw [hz, map_zero, map_zero]
  change (TensorProduct.lid ℚ H) (φ oddCoefficient ⊗ₜ[ℚ] crossing) = 0 at he
  rw [hφ] at he
  have hf : crossing = 0 := by simpa using he
  exact (basisNF D Sc [false, true] [true, false]).ne_zero crossingIndex hf

example : Function.Injective
    (coefficientWindowMap D Sc (fun _ => 8) 3 [false, true] [true, false]) :=
  coefficientWindowMap_injective D Sc (fun _ => 8) 3 (fun _ => by decide) _ _

/-- An odd coefficient on a nonzero mixed crossing survives the actual quotient. -/
example : coefficientWindowMap D Sc (fun _ => 8) 3 [false, true] [true, false]
    testTensor ≠ 0 := by
  intro h
  apply testTensor_ne_zero
  exact coefficientWindowMap_injective D Sc (fun _ => 8) 3 (fun _ => by decide) _ _
    (h.trans (map_zero _).symm)

example : Function.Injective
    (fun x : coefficientWindowSource D Sc 3 [false, true] [true, false] =>
      elvHomQuotient D Sc (fun _ => 8) [false, true] [true, false] x.val) :=
  elvHomQuotient_injective_coefficientWindow D Sc (fun _ => 8) 3 (fun _ => by decide) _ _

end OddMath.QuiverHecke.CoefficientWindowExamples

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVCoefficientWindowTensor
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"
