import OddMath.QuiverHecke.CyclotomicAction.ELVAppendSpanning
noncomputable section
open CategoryTheory OddMath OddMath.QuiverHecke ELVOld
universe u
variable {I L k : Type u} [AddCommGroup L] [CommRing k]
  (D : SKM.Datum I L) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

example (N : ℕ) (i : I) (v w : List I) :
    appendFiniteRangeSpan D Sc cutoff N i v w = ⊤ :=
  appendFiniteRangeSpan_eq_top D Sc cutoff N i v w

example (i : I) (v w : List I) : Finite (AppendCrossingSkeleton i v w) :=
  inferInstance

example (N : ℕ) (i : I) (v t w : List I) (j : ℕ)
    (h : hom D Sc cutoff (t ++ [i]) w) (r : hom D Sc cutoff v t) :
    appendBoundedOldMap D Sc cutoff N i v t w j h
      ((truncatedIdeal D Sc cutoff N v t).mkQ r) =
    (truncatedIdeal D Sc cutoff N (v ++ [i]) w).mkQ
      (appendSourcePower D Sc cutoff i v j ≫ rightContext D Sc cutoff [i] v t r ≫ h) :=
  appendBoundedOldMap_mk D Sc cutoff N i v t w j h r

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owners := #[`OddMath.QuiverHecke.CyclotomicAction.ELVAppendSpanning]
  for owner in owners do
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
