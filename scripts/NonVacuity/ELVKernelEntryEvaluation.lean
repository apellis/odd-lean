import OddMath.QuiverHecke.CyclotomicAction.ELVKernelEntryEvaluation
import OddMath.QuiverHecke.CyclotomicAction.ELVEvenCoefficientModule
import OddMath.QuiverHecke.CyclotomicAction.ELVBoundedSourceDetection
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Mathlib.Tactic.NormNum
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath OddMath.QuiverHecke
namespace OddMath.QuiverHecke.EvenCoefficientModuleExamples
private abbrev A := CyclotomicAction.AsymmetricParameters.datum
private def D : SKM.Datum Bool (Bool → ℤ) :=
  { A with
    parity := fun i => if i then 1 else 0
    even_of_odd := fun i j _ => A.even_of_odd i j rfl }
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

private theorem homogeneous : Sc.Homogeneous := by
  intro _ _ _ _ _ _ _ _ h
  exact (h rfl).elim
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
  (0, {⟨true, rfl⟩})

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
  SKM.SYM.coefficientDegree D sy exteriorIndex +
    crossingIndex.deg D sy + 1

private def point :
    jointPBWWindow D sy Sc
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


open ELVOld.CyclotomicCrossingTensor
private def evenColour : {i : Bool // D.parity i = 0} := ⟨false,rfl⟩
private def oldVector (N : ℕ) : Old D Sc (fun _ => N) [false,true] [true,false] :=
  (ideal D Sc (fun _ => N) [false,true] [true,false]).mkQ
    (elvHomQuotient D Sc (fun _ => N) [false,true] [true,false] recoveryPoint.val)

private def sourceVector (N : ℕ) : Source D Sc (fun _ => N) false [false,true] [true,false] :=
  tensor D Sc (fun _ => N) false [false,true] [true] [true,false]
    (𝟙 (⟨[true,false]⟩ : OldCategory D Sc (fun _ => N))) (oldVector N)

example (N : ℕ) :
    (coefficientRestrictionModuleIso D Sc (fun _ => N) false [false,true]).hom.app 0
      (⟨[true]⟩ : OldCategory D Sc (fun _ => N)) (oldVector N) = oldVector N := rfl

example (N : ℕ) (q : ZMod 2) :
    ((coefficientZeroModule D Sc (fun _ => N) false [false,true]).obj
      (⟨[true]⟩ : OldCategory D Sc (fun _ => N))).proj q =
    ((restrictedRepresentable D Sc (fun _ => N) false [false,true]).obj
      (⟨[true]⟩ : OldCategory D Sc (fun _ => N))).proj q :=
  coefficientZero_obj_proj D Sc (fun _ => N) false [false,true] ⟨[true]⟩ q

/-- The actual even cap has the additional constant minus on an odd
coefficient from the other colour, with no source or output twist. -/
private theorem contraction_value (N : ℕ) :
    evenSourceInputContraction D Sc (fun _ => N) evenColour
      [false,true] [true,false] (sourceVector N) = -oldVector N := by
  have h := evenSourceInputContraction_tensor D Sc (fun _ => N) evenColour
    [false,true] [true] [true,false]
    (𝟙 (⟨[true,false]⟩ : OldCategory D Sc (fun _ => N))) (oldVector N)
  have hi : oldComp D Sc (fun _ => N) [false,true] [true,false] [true,false]
      (oldVector N) (𝟙 (⟨[true,false]⟩ : OldCategory D Sc (fun _ => N))) = oldVector N := by
    change (oldVector N : (⟨[false,true]⟩ : OldCategory D Sc (fun _ => N)) ⟶ ⟨[true,false]⟩) ≫
      𝟙 (⟨[true,false]⟩ : OldCategory D Sc (fun _ => N)) = oldVector N
    exact Category.comp_id _
  exact h.trans (congrArg Neg.neg hi)

example (N : ℕ) (z : Source D Sc (fun _ => N) false [false,true] [true,false]) :
    evenSourceEquiv D Sc (fun _ => N) evenColour [false,true] [true,false]
      ((evenSourceEquiv D Sc (fun _ => N) evenColour [false,true] [true,false]).symm z) = z :=
  (evenSourceEquiv D Sc (fun _ => N) evenColour [false,true] [true,false]).apply_symm_apply z

/-- The cap/source test is nonzero at every sufficiently large cutoff,
proved through the actual weighted quotient detector. -/
private theorem source_nonzero : ∃ K : ℕ, ∀ N : ℕ, K ≤ N →
    oldVector N ≠ 0 ∧ sourceVector N ≠ 0 := by
  obtain ⟨K, hK⟩ := extendedAtMost_detected_at_high_cutoffs D sy Sc homogeneous
    [false,true] [true,false] 3
  refine ⟨K, fun N hN => ?_⟩
  have hb : oldVector N ≠ 0 := by
    intro h
    have ht := congrArg (truncateOld D Sc (fun _ => N) N [false,true] [true,false]) h
    change (truncatedIdeal D Sc (fun _ => N) N [false,true] [true,false]).mkQ
      (elvHomQuotient D Sc (fun _ => N) [false,true] [true,false] recoveryPoint.val) = 0 at ht
    apply recoveryPoint_ne_zero
    apply hK (fun _ => N) N (fun _ => hN) hN
    exact ht.trans (map_zero _).symm
  refine ⟨hb, fun hz => ?_⟩
  have he := congrArg (evenSourceInputContraction D Sc (fun _ => N) evenColour
    [false,true] [true,false]) hz
  rw [contraction_value, map_zero] at he
  exact hb (neg_eq_zero.mp he)


private abbrev fullRep (N : ℕ) :=
  oldRepresentable D Sc (fun _ => N) (⟨[false,true]⟩ : OldCategory D Sc (fun _ => N))


private abbrev C (N : ℕ) := OldCategory D Sc (fun _ => N)
private abbrev J (N : ℕ) (i : Bool) := append D Sc (fun _ => N) i
private abbrev v (N : ℕ) : C N := ⟨[false,true]⟩
private abbrev t (N : ℕ) : C N := ⟨[true,false]⟩
private def kernelSourceVector (N : ℕ) (i : Bool) :
    IndResKernel.Component (k := ℚ) (J N i) (v N) (t N) := by
  cases i
  · exact BalancedInduction.tensor (J N false)
      ((J N false) ⋙ IndResKernel.homModule (k := ℚ) (v N)) ⟨[true]⟩
      (𝟙 (t N)) (oldVector N)
  · exact BalancedInduction.tensor (J N true)
      ((J N true) ⋙ IndResKernel.homModule (k := ℚ) (v N)) ⟨[false]⟩
      (oldVector N) (𝟙 (v N))

private theorem counit_sourceVector (N : ℕ) (i : Bool) :
    actualCounitKernelComponent D Sc (fun _ => N) i (v N) (t N)
      (kernelSourceVector N i) = oldVector N := by
  cases i
  · rw [kernelSourceVector, actualCounitKernelComponent_tensor]
    exact Category.comp_id _
  · rw [kernelSourceVector, actualCounitKernelComponent_tensor]
    exact Category.id_comp _

example (N : ℕ) (i : Bool) :
    kernelMateEvaluation D Sc (fun _ => N) i (fullRep N) (v N) (t N)
      (𝟙 (v N)) (kernelSourceVector N i) =
    moduleMateEvaluation D Sc (fun _ => N) i (fullRep N) (v N) (t N)
      (𝟙 (v N)) (kernelSourceVector N i) :=
  LinearMap.congr_fun (actualMateKernel_evaluate D Sc (fun _ => N) i
    (fullRep N) (v N) (t N) (𝟙 (v N))) (kernelSourceVector N i)

example (N : ℕ) (i : Bool) (n : ℕ) :
    (fullRep N).map
      (actualCapKernelComponent D Sc (fun _ => N) i n (v N) (t N)
        (kernelSourceVector N i)) (𝟙 (v N)) =
      (moduleCapRow D Sc (fun _ => N) i (fullRep N) n).total (t N)
        (IndResKernel.evaluate (J N i) (fullRep N).toFunctor (v N) (t N)
          (𝟙 (v N)) (kernelSourceVector N i)) :=
  actualCapKernel_evaluate_moduleCapRow D Sc (fun _ => N) i (fullRep N)
    (v N) (t N) (𝟙 (v N)) n (kernelSourceVector N i)

example (N : ℕ) (i : Bool) (n : ℕ) :
    BalancedInduction.tensor (J N i) (fullRep N).toFunctor (v N)
      (actualUnitKernelComponent D Sc (fun _ => N) i n (v N) (t N) (oldVector N))
      (𝟙 (v N)) =
      (moduleUnitColumn D Sc (fun _ => N) i (fullRep N) n).total (t N)
        ((fullRep N).map (oldVector N) (𝟙 (v N))) :=
  actualUnitKernel_evaluate D Sc (fun _ => N) i (fullRep N) (v N) (t N)
    (𝟙 (v N)) n (oldVector N)

example : ∃ K : ℕ, ∀ N : ℕ, K ≤ N → ∀ i : Bool, kernelSourceVector N i ≠ 0 := by
  obtain ⟨K,hK⟩ := source_nonzero
  refine ⟨K, fun N hN i hz => ?_⟩
  have h := congrArg (actualCounitKernelComponent D Sc (fun _ => N) i (v N) (t N)) hz
  rw [counit_sourceVector, map_zero] at h
  exact (hK N hN).1 h

end OddMath.QuiverHecke.EvenCoefficientModuleExamples

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVKernelEntryEvaluation
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"
