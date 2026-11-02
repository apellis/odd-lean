import OddMath.QuiverHecke.CyclotomicAction.ELVOutputLastShuffle
import Lean.Util.CollectAxioms

noncomputable section
open Categorification.TypeA
open OddMath.QuiverHecke
namespace OutputLastShuffleExamples

private def crossingIndex : NFIdx [false, true, false] [false, false, true] := by
  let w := wordProd 3 [1]
  refine ⟨([], w), by simp, by simp, ?_⟩
  change SChain [false, true, false]
    (pl [false, true, false] (cw (canWord 3 w))) [false, false, true]
  have ht := tgt_cw_eq (validWord_canWord 3 w)
    (show ValidWord 3 [1] from by simp [ValidWord])
    (wordProd_canWord 3 w) (t := [false, true, false]) rfl
  have hs := sChain_pl [false, true, false] (cw (canWord 3 w))
  rw [ht] at hs
  exact hs

private def crossingShuffle : ShIdx
    (show [false, false].length + [true].length = [false, true, false].length from rfl) :=
  (ShIdx.leadEquiv _).symm crossingIndex

/-- A nonidentity tail crossing with a repeated first colour retains that
first strand as a spectator throughout its canonical shuffle word. -/
example := outputLast_tail_factor (by decide : false ≠ true) [true, false] 2 rfl
  crossingShuffle.1 (outputLast_last_block crossingShuffle)

example := outputLast_nonlong_of_distinct (by decide : false ≠ true)
  [true, false] [false, false] crossingShuffle

/-- Forward and inverse append shuffle conventions differ already in degree
three; the output word is the descending run. -/
example : canWord 4 (appendRun 3 ⟨1, by decide⟩).1 = [2, 1] :=
  canWord_appendRun_forward 3 ⟨1, by decide⟩

example : tgt [false, true, false, true] (cw (descRun 0 3)) =
    [true, false, true, false] := outputLast_long_target false [true, false, true]

end OutputLastShuffleExamples

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVOutputLastShuffle
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owned module"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"
