import OddMath.QuiverHecke.CyclotomicAction.CyclotomicMatrixEntries
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams OddMath OddMath.QuiverHecke
open CyclotomicAction.AsymmetricParameters
namespace CyclotomicMatrixEntriesConsumer

private def polys (_ : Bool) : _root_.Polynomial ℚ :=
  _root_.Polynomial.X ^ 2 + _root_.Polynomial.X + 1
private def targetWord : Word Bool 2 := ⟨[false, true], rfl⟩
private def sourceWord : Word Bool 2 := ⟨[true, false], rfl⟩

/-- Actual Hn ideal generators, with arbitrary right coefficients, have ordinary ideal entries. -/
example (b : Hn datum scalars 2) :
    (cyclotomicGenerator datum scalars polys targetWord * b) (targetWord, sourceWord) ∈
      cycHom datum scalars polys sourceWord.val targetWord.val :=
  cyclotomicIdeal_entry_mem_cycHom datum scalars polys 1
    (Submodule.subset_span ⟨targetWord, b, rfl⟩) targetWord sourceWord

/-- Arbitrary left matrix multiplication is included in the same comparison. -/
example (b z : Hn datum scalars 2) :
    (z * (cyclotomicGenerator datum scalars polys targetWord * b)) (targetWord, sourceWord) ∈
      cycHom datum scalars polys sourceWord.val targetWord.val :=
  cyclotomicIdeal_entry_mem_cycHom datum scalars polys 1
    (Ideal.mul_mem_left _ z (Submodule.subset_span ⟨targetWord, b, rfl⟩))
    targetWord sourceWord

example (f : wordObj datum scalars sourceWord ⟶ wordObj datum scalars targetWord) :
    FiniteHomMatrix.single targetWord sourceWord f ∈ cyclotomicIdeal datum scalars polys 1 ↔
      f ∈ cycHom datum scalars polys sourceWord.val targetWord.val :=
  single_mem_cyclotomicIdeal_iff datum scalars polys 1 targetWord sourceWord f

end CyclotomicMatrixEntriesConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.CyclotomicMatrixEntries
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Module was not imported"
  let names := env.header.moduleData[idx]!.constNames
  unless names.size > 0 do throwError "Empty declaration inventory"
  for name in names do
    for axiomName in (← Lean.collectAxioms name) do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
  logInfo m!"Audited ALL {names.size} owned declarations including private/generated"
