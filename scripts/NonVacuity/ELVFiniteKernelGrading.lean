import OddMath.QuiverHecke.CyclotomicAction.ELVFiniteKernelGrading
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionKernelGrading
import OddMath.QuiverHecke.CyclotomicAction.ELVOldSupermodules
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
namespace FiniteKernelGradingConsumer
open CyclotomicAction.AsymmetricParameters
private def mixedDatum : SKM.Datum Bool (Bool → ℤ) :=
  { datum with
    parity := fun i => if i then 1 else 0
    even_of_odd := fun i j _ => datum.even_of_odd i j rfl }

private def mixedScalars : SKM.Scalars mixedDatum ℚ where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := by intro _; norm_num



open Opposite
open ELVOld.BalancedKernelTensor

abbrev Slots := Option (Fin 2)
abbrev C := OldCategory mixedDatum mixedScalars (fun _ => 4)
private def targetWord : Slots → List Bool
  | none => [false, true]
  | some _ => [true, false]
private def kernels (a : Slots) : Cᵒᵖ ⥤ ModuleCat ℚ :=
  inductionKernel (𝟭 C) (⟨targetWord a⟩ : C)
private def coeffModule :=
  (oldRepresentable mixedDatum mixedScalars (fun _ => 4) (⟨[false, true]⟩ : C)).toFunctor

private instance kernels_additive (a : Slots) : (kernels a).Additive := by
  change (inductionKernel (k := ℚ) (𝟭 C) (⟨targetWord a⟩ : C)).Additive
  infer_instance

private def profile (i : Bool) : Slots → ZMod 2
  | none => mixedDatum.parity i
  | some r => r.val • mixedDatum.parity i

private def gradings (i : Bool) (a : Slots) : CoefficientGrading (kernels a) :=
  shiftCoefficientGrading
    (inductionKernelGrading (k := ℚ) (𝟭 C) (⟨targetWord a⟩ : C)) (profile i a)

private theorem kernels_graded (i : Bool) (a : Slots) :
    IsGradedKernel (kernels a) (gradings i a) :=
  shiftCoefficientGrading_isGraded
    (inductionKernelGrading (k := ℚ) (𝟭 C) (⟨targetWord a⟩ : C))
    (inductionKernel_isGraded (k := ℚ) (𝟭 C) (⟨targetWord a⟩ : C)) (profile i a)

private def coeffSuperModule :=
  oldRepresentable mixedDatum mixedScalars (fun _ => 4) (⟨[false, true]⟩ : C)

example (i : Bool) :
    ((piEquiv kernels coeffSuperModule.toFunctor).toLinearMap :
      superspace (piKernel kernels) (piCoefficientGrading kernels (gradings i))
        coeffSuperModule.toFunctor (piKernel_isGraded kernels (gradings i) (kernels_graded i)) ⟶
      OddMath.FiniteSuperspace.product (fun a => superspace (kernels a) (gradings i a)
        coeffSuperModule.toFunctor (kernels_graded i a))) ∈
    parity (R := ℚ)
      (superspace (piKernel kernels) (piCoefficientGrading kernels (gradings i))
        coeffSuperModule.toFunctor (piKernel_isGraded kernels (gradings i) (kernels_graded i)))
      (OddMath.FiniteSuperspace.product (fun a => superspace (kernels a) (gradings i a)
        coeffSuperModule.toFunctor (kernels_graded i a))) 0 :=
  piEquiv_even kernels (gradings i) (kernels_graded i) coeffSuperModule

example (i : Bool) (v : C) (q : ZMod 2)
    (x : (piKernel kernels).obj (op v)) (a : Slots) :
    coefficientProj (piCoefficientGrading kernels (gradings i)) v q x a =
      coefficientProj (gradings i a) v q (x a) :=
  piCoefficientGrading_proj kernels (gradings i) v q x a

end FiniteKernelGradingConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVFiniteKernelGrading
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner"
  for name in names do
    for ax in (← Lean.collectAxioms name) do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited ALL {names.size} owned declarations including private/generated"
