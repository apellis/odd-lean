import OddMath.QuiverHecke.CyclotomicAction.ELVTripleCorrectionPolynomial
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import OddMath.QuiverHecke.CyclotomicAction.ELVVacuumRepresentable
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Data.Matrix.Notation
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.TripleCorrectionPolynomialExamples
open CyclotomicAction.AsymmetricParameters
private def A : Matrix (Fin 2) (Fin 2) ℚ := !![0,1;0,0]
private def B : Matrix (Fin 2) (Fin 2) ℚ := !![0,0;1,0]
private def C : Matrix (Fin 2) (Fin 2) ℚ := !![1,0;0,-1]
private def φ : Matrix (Fin 2) (Fin 2) ℚ →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℚ :=
  (Matrix.reindexAlgEquiv ℚ ℚ (Equiv.swap (0 : Fin 2) 1)).toAlgHom

/-- Nontrivial basis permutation and noncommuting operator examples. -/
example := tripleDotCorrectionSum_map datum φ false true 2 1 2 A B C
example := tripleDotCorrectionPolynomial_map datum scalars φ false true A B C

/-- The original Sc canonical-content correction on an actual regular vacuum
and actual three-letter output, with both outer-colour choices. -/
example (i j : Bool) := contentMixedBraidPolynomial_eq_ordered datum scalars (fun _ => 12) 12
  0 i j (vacuumModule datum (parameterTwist datum scalars) (fun _ => 12) 12)
  (⟨⟨[i,j,i]⟩, by simp⟩ : ContentCategory datum (parameterTwist datum scalars) (fun _ => 12) 12
    (0 + ([i,j,i] : Multiset Bool)))
end OddMath.QuiverHecke.ELVOld.TripleCorrectionPolynomialExamples

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVTripleCorrectionPolynomial
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owned module"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"
