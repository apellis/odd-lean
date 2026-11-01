import OddMath.QuiverHecke.CyclotomicAction.ELVContentExtensionAppend
import OddMath.QuiverHecke.CyclotomicAction.ELVBoundedSourceDetection
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Mathlib.Tactic.NormNum
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath OddMath.QuiverHecke
namespace OddMath.QuiverHecke.ContentExtensionExamples
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


private abbrev C (N : ℕ) := OldCategory D Sc (fun _ => N)
private abbrev CC (N : ℕ) := OldContentCategory D Sc (fun _ => N) [false,true]
private abbrev J (N : ℕ) := oldContentInclusion D Sc (fun _ => N) [false,true]
private abbrev M (N : ℕ) := (BalancedInduction.restriction (J N)).obj
  (oldRepresentable D Sc (fun _ => N) (⟨[false,true]⟩ : C N))
private def w (N : ℕ) : CC N := ⟨⟨[true,false]⟩, List.Perm.swap false true []⟩


private abbrev App (N : ℕ) (i : Bool) := oldContentAppend D Sc (fun _ => N) [false,true] i
private abbrev L (N : ℕ) (i : Bool) := BalancedInduction.induced (App N i) (M N)
private def e (N : ℕ) (i : Bool) := oldContentAppendRestrictionIso D Sc (fun _ => N) [false,true] i (M N)

private def z (N : ℕ) (i : Bool) : (L N i).obj ((App N i).obj (w N)) :=
  BalancedInduction.unit (App N i) (M N).toFunctor (w N) (oldVector N)

example (N : ℕ) :
    ((e N false).hom ≫ (e N false).inv).total ((App N false).obj (w N))
      (z N false) = z N false := by
  rw [(e N false).hom_inv_id]
  simp only [SuperNatTrans.total, Superfunctor.id_app_zero, Superfunctor.id_app_one, add_zero]
  rfl

example (N : ℕ) :
    ((e N true).hom ≫ (e N true).inv).total ((App N true).obj (w N))
      (z N true) = z N true := by
  rw [(e N true).hom_inv_id]
  simp only [SuperNatTrans.total, Superfunctor.id_app_zero, Superfunctor.id_app_one, add_zero]
  rfl

example (N : ℕ) :
    (oldContentAppendExtensionIso D Sc (fun _ => N) [false,true] true).hom.app (M N) =
      ((oldContentAppendExtensionIso D Sc (fun _ => N) [false,true] true).app (M N)).hom := rfl

end OddMath.QuiverHecke.ContentExtensionExamples

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVContentExtensionAppend
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"
