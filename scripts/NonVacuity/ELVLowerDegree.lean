import OddMath.QuiverHecke.CyclotomicAction.ELVLowerDegree
noncomputable section
open OddMath OddMath.QuiverHecke
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (sy : SKM.Symmetrizer D)
  (Sc : SKM.Scalars D k) (hc : Sc.Homogeneous)

example (v w : List I) :
    ∃ L : ℤ, ∀ cutoff : I → ℕ, ∀ n, n < L →
      elvHomDegree D sy Sc hc cutoff v w n = ⊥ :=
  exists_elvHomDegree_lower_bound D sy Sc hc v w

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVLowerDegree
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Module was not imported: {owner}"
  let mut count : Nat := 0
  for name in env.header.moduleData[idx]!.constNames do
    for axiomName in (← Lean.collectAxioms name) do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
    count := count + 1
  if count == 0 then throwError "Empty declaration inventory: {owner}"
  logInfo m!"Audited {count} declarations in {owner}; all axioms allowed."
