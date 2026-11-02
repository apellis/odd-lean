import OddMath.QuiverHecke.CyclotomicAction.ELVDistinctModuleInverse
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
open scoped TensorProduct
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction
open CyclotomicCrossingTensor CyclotomicCrossingTensor.Distinct
namespace DistinctModuleInverseExamples

private def D : SKM.Datum Bool (Bool → ℤ) :=
  { AsymmetricParameters.datum with
    parity := fun i => if i then 1 else 0
    even_of_odd := fun i j _ => AsymmetricParameters.datum.even_of_odd i j rfl }
private def Sc : SKM.Scalars D ℚ where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := by intro _; norm_num
private def cutoff (n : ℕ) (_ : Bool) := n
private theorem distinct (i : Bool) : i ≠ !i := by cases i <;> decide

private def shiftedModule (n : ℕ) (v : List Bool) :=
  supermoduleParityObj (oldRepresentable D Sc (cutoff n) (⟨v⟩ : OldCategory D Sc (cutoff n)))

/-- Both mixed moving parities act on a parity-shifted input module. -/
example (n : ℕ) (i : Bool) := moduleMateUnderlyingEquiv D Sc (cutoff n)
  i (!i) (distinct i) (shiftedModule n [!i]) (⟨[i]⟩ : OldCategory D Sc (cutoff n))
example (n : ℕ) (i : Bool) := moduleMateUnderlyingEquiv_toLinearMap D Sc (cutoff n)
  i (!i) (distinct i) (shiftedModule n [!i]) (⟨[i]⟩ : OldCategory D Sc (cutoff n))

/-- Empty words and zero cutoff keep their actual coend domains. -/
example (i : Bool) := moduleMateUnderlyingEquiv D Sc (cutoff 0)
  i (!i) (distinct i) (shiftedModule 0 []) (⟨[]⟩ : OldCategory D Sc (cutoff 0))

private def exteriorEnd (n : ℕ) (j : Bool) :
    (⟨[j]⟩ : OldCategory D Sc (cutoff n)) ⟶ ⟨[j]⟩ :=
  (ideal D Sc (cutoff n) [j] [j]).mkQ
    (SKM.SYM.elvCoefficientQuotient D (cutoff n) (SKM.SYM.delta D ℚ ⟨true, rfl⟩) ⊗ₜ[ℚ]
      𝟙 ((pres D Sc).obj (ob D [j])))

/-- Literal ordinary right covariance retains an odd exterior precomposition. -/
example (n : ℕ) (i : Bool) := kernelMateComponent_precompose D Sc (cutoff n)
  i (!i) (⟨[!i]⟩ : OldCategory D Sc (cutoff n)) ⟨[!i]⟩ ⟨[i]⟩ (exteriorEnd n (!i))

/-- Distinct odd colours test the nontrivial crossing parity on a shifted module. -/
example (n : ℕ) := moduleMateUnderlyingEquiv AsymmetricParameters.datum AsymmetricParameters.scalars
  (cutoff n) false true (by decide)
  (supermoduleParityObj (oldRepresentable AsymmetricParameters.datum AsymmetricParameters.scalars
    (cutoff n) (⟨[true]⟩ : OldCategory AsymmetricParameters.datum AsymmetricParameters.scalars (cutoff n))))
  (⟨[false]⟩ : OldCategory AsymmetricParameters.datum AsymmetricParameters.scalars (cutoff n))

end DistinctModuleInverseExamples

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for owner in #[`OddMath.QuiverHecke.CyclotomicAction.ELVMixedIndResKernel,
      `OddMath.QuiverHecke.CyclotomicAction.ELVMixedMateKernelMap,
      `OddMath.QuiverHecke.CyclotomicAction.ELVInductionCoefficientIso,
      `OddMath.QuiverHecke.CyclotomicAction.ELVMixedMateLinear,
      `OddMath.QuiverHecke.CyclotomicAction.ELVDistinctMateKernel,
      `OddMath.QuiverHecke.CyclotomicAction.ELVDistinctModuleInverse] do
    let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owned module {owner}"
    let names := env.header.moduleData[idx]!.constNames
    if names.isEmpty then throwError "Empty owned module {owner}"
    for name in names do
      for ax in ← Lean.collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {name}"
    logInfo m!"Audited all {names.size} declarations in {owner}"
