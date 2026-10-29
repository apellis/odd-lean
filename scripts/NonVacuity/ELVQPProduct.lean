import OddMath.QuiverHecke.CyclotomicAction.ELVQPProduct

noncomputable section
namespace ELVQPProductConsumer
open CategoryTheory StringDiagrams OddMath OddMath.QuiverHecke ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The consumer retains all words, cutoffs, and arbitrary full-coefficient continuations. -/
theorem allWords (i : I) (μ σ z : List I)
    (h : hom D Sc cutoff ((i :: μ) ++ σ) z) :
    qpEval D Sc cutoff i μ σ z h
      (moveHom D Sc i [] μ ≫ lastToFirstHom D Sc i μ) =
    qpEval D Sc cutoff i μ σ z h (qpProduct D Sc i μ) :=
  qp_product D Sc cutoff i μ σ z h

#print axioms qp_product
#print axioms qp_projection_product
#print axioms qpFactor_mem_relationPreserving
end ELVQPProductConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVQPProduct
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Module was not imported: {owner}"
  let mut count : Nat := 0
  for name in env.header.moduleData[idx]!.constNames do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
    count := count + 1
  if count == 0 then throwError "Empty declaration inventory: {owner}"
  logInfo m!"Audited {count} declarations in {owner}; all axioms allowed."
