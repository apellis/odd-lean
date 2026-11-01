import OddMath.QuiverHecke.CyclotomicAction.ELVBoundedSourceDetection
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Mathlib.Tactic.NormNum
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams
open OddMath OddMath.QuiverHecke
namespace OddMath.QuiverHecke.BoundedSourceExamples
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
  let φ : U →ₗ[ℚ] ℚ :=
    ((SKM.SYM.coefficientBasis D ℚ).coord exteriorIndex).comp
      (SKM.SYM.CoefficientAtMost D ℚ 3).subtype
  have hφ : φ oddCoefficient = 1 := by
    change ((SKM.SYM.coefficientBasis D ℚ).repr
      (SKM.SYM.coefficientBasis D ℚ exteriorIndex)) exteriorIndex = 1
    simp
  intro hz
  have he : (TensorProduct.lid ℚ H)
      (TensorProduct.map φ (LinearMap.id : H →ₗ[ℚ] H) testTensor) = 0 := by
    rw [hz, map_zero, map_zero]
  change (TensorProduct.lid ℚ H) (φ oddCoefficient ⊗ₜ[ℚ] crossing) = 0 at he
  rw [hφ] at he
  have hf : crossing = 0 := by simpa using he
  exact (basisNF D Sc [false, true] [true, false]).ne_zero crossingIndex hf

open ELVOld
private def B : ℤ :=
  SKM.SYM.coefficientDegree D CyclotomicAction.AsymmetricParameters.symmetrizer exteriorIndex +
    crossingIndex.deg D CyclotomicAction.AsymmetricParameters.symmetrizer + 1

private def point :
    jointPBWWindow D CyclotomicAction.AsymmetricParameters.symmetrizer Sc
      3 [false,true] [true,false] B :=
  ⟨sourceCoefficientHom D Sc (SKM.SYM.coefficientBasis D ℚ exteriorIndex)
      crossingIndex.nf,
    Submodule.subset_span ⟨(exteriorIndex, crossingIndex), ⟨by
      simp [exteriorIndex, SKM.SYM.coefficientWeight], by
      dsimp only [Prod.fst, Prod.snd, B]
      omega⟩, rfl⟩⟩

private theorem point_ne_zero : point ≠ 0 := by
  intro hz
  have hp : sourceCoefficientHom D Sc (SKM.SYM.coefficientBasis D ℚ exteriorIndex)
      crossingIndex.nf = 0 := congrArg Subtype.val hz
  have hq : coefficientWindowMap D Sc (fun _ => 8) 3 [false,true] [true,false]
      testTensor = 0 := by
    rw [← elvHomQuotient_coefficientWindowSourceMap]
    simp only [testTensor, coefficientWindowSourceMap_tmul, oddCoefficient,
      crossing, basisNF_apply]
    rw [hp, map_zero]
  exact testTensor_ne_zero
    (coefficientWindowMap_injective D Sc (fun _ => 8) 3 (fun _ => by decide) _ _
      (hq.trans (map_zero _).symm))


private def recoveryPoint : ExtendedAtMost D Sc [false,true] [true,false] 3 :=
  ⟨point.val, by
    change sourceCoefficientHom D Sc (SKM.SYM.coefficientBasis D ℚ exteriorIndex)
      crossingIndex.nf ∈ _
    rw [← extensionBasis_apply]
    apply Submodule.subset_span
    refine ⟨(exteriorIndex,crossingIndex), ?_, rfl⟩
    norm_num [extensionDegree, exteriorIndex, SKM.SYM.coefficientWeight,
      crossingIndex]⟩

private theorem recoveryPoint_ne_zero : recoveryPoint ≠ 0 := by
  intro h
  apply point_ne_zero
  apply Subtype.ext
  exact congrArg (fun z : ExtendedAtMost D Sc [false,true] [true,false] 3 => z.val) h

/-- The exact recovery window detects this nonzero odd-coefficient crossing. -/
example : ∃ K : ℕ, ∀ N : ℕ, K ≤ N →
    (truncatedIdeal D Sc (fun _ => N) N [false,true] [true,false]).mkQ
      (elvHomQuotient D Sc (fun _ => N) [false,true] [true,false] recoveryPoint.val) ≠ 0 := by
  obtain ⟨K, hK⟩ := extendedAtMost_detected_at_high_cutoffs D
    CyclotomicAction.AsymmetricParameters.symmetrizer Sc
    CyclotomicAction.AsymmetricParameters.homogeneous [false,true] [true,false] 3
  refine ⟨K, fun N hN hz => recoveryPoint_ne_zero ?_⟩
  apply hK (fun _ => N) N (fun _ => hN) hN
  exact hz.trans (map_zero _).symm

example (d : ℕ) : ∃ K : ℕ, ∀ (cutoff : Bool → ℕ) (N : ℕ),
    (∀ i, K ≤ cutoff i) → K ≤ N →
    Function.Injective (fun x : ExtendedAtMost D Sc [] [] d =>
        (truncatedIdeal D Sc cutoff N [] []).mkQ
          (elvHomQuotient D Sc cutoff [] [] x.val)) :=
  extendedAtMost_detected_at_high_cutoffs D
    CyclotomicAction.AsymmetricParameters.symmetrizer Sc
    CyclotomicAction.AsymmetricParameters.homogeneous [] [] d

/-- The empty-Hom case needs no permutation witness. -/
example (d : ℕ) : ∃ K : ℕ, ∀ (cutoff : Bool → ℕ) (N : ℕ),
    (∀ i, K ≤ cutoff i) → K ≤ N →
    Function.Injective (fun x : ExtendedAtMost D Sc [] [false] d =>
        (truncatedIdeal D Sc cutoff N [] [false]).mkQ
          (elvHomQuotient D Sc cutoff [] [false] x.val)) :=
  extendedAtMost_detected_at_high_cutoffs D
    CyclotomicAction.AsymmetricParameters.symmetrizer Sc
    CyclotomicAction.AsymmetricParameters.homogeneous [] [false] d

example (f : coefficientObj D Sc [false,true] ⟶ coefficientObj D Sc [true,false])
    (hf : ∀ N : ℕ, (truncatedIdeal D Sc (fun _ => N) N [false,true] [true,false]).mkQ
      (elvHomQuotient D Sc (fun _ => N) [false,true] [true,false] f) = 0) : f = 0 :=
  truncated_quotients_jointly_detect D CyclotomicAction.AsymmetricParameters.symmetrizer Sc
    CyclotomicAction.AsymmetricParameters.homogeneous _ _ f hf

end OddMath.QuiverHecke.BoundedSourceExamples

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVBoundedSourceDetection
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"
