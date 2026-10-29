import OddMath.QuiverHecke.CyclotomicAction.ELVQPRepeated
import NonVacuity.ELVPrefixKilling

noncomputable section
namespace ELVQPRepeatedConsumer
open CategoryTheory StringDiagrams OddMath OddMath.QuiverHecke ELVOld
open ELVPrefixKillingConsumer

/-- Arbitrary cutoff, repeated prefix and nonempty spectator context. -/
example (N : ℕ) :=
  qp_repeated_even (datum 0) (scalars 0) (fun _ => N) () rfl
    [(), ()] [()] [(), (), (), (), ()] (𝟙 _)

/-- The first repeated-colour step does not exclude zero cutoff. -/
example := qp_repeated_even (datum 0) (scalars 0) (fun _ => 0) () rfl
  [] [] [(), ()] (𝟙 _)

/-- An arbitrary coefficient-category continuation is allowed. -/
example (N : ℕ)
    (h : hom (datum 0) (scalars 0) (fun _ => N) [(), (), ()] [(), (), ()]) :=
  qp_repeated_even (datum 0) (scalars 0) (fun _ => N) () rfl
    [()] [] [(), (), ()] h

#print axioms qp_repeated_even
end ELVQPRepeatedConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVQPRepeated
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
