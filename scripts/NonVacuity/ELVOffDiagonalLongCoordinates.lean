import OddMath.QuiverHecke.CyclotomicAction.ELVOffDiagonalLongCoordinates
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open CyclotomicAction.AsymmetricParameters

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

/-- A genuinely off-diagonal old Hom on connected odd data, with every
index and scalar hypothesis supplied. -/
example (f : ℕ →₀ Old datum scalars (fun _ => 12) [false, true] [true, false]) :
    longHomExtraction datum scalars (fun _ => 12) 1 false crossingIndex
      (longHomSection datum scalars (fun _ => 12) 1 false crossingIndex f) = f :=
  longHomExtraction_section datum scalars (fun _ => 12) 1 false crossingIndex f

example : Function.Surjective
    (longHomExtraction datum scalars (fun _ => 12) 0 true crossingIndex) :=
  longHomExtraction_surjective datum scalars (fun _ => 12) 0 true crossingIndex

example (f : ℕ →₀ Old datum scalars (fun _ => 12) [false, true] [true, false]) :
    offDiagonalLongExtraction datum scalars (fun _ => 12) 1 false [false, true] [true, false]
      (offDiagonalLongSection datum scalars (fun _ => 12) 1 false [false, true] [true, false] f) = f :=
  offDiagonalLongExtraction_section datum scalars (fun _ => 12) 1 false _ _ f

/-- Different strand counts give an empty old Hom; no index is silently assumed. -/
example (f : ℕ →₀ Old datum scalars (fun _ => 12) [] [false]) :
    offDiagonalLongExtraction datum scalars (fun _ => 12) 0 true [] [false]
      (offDiagonalLongSection datum scalars (fun _ => 12) 0 true [] [false] f) = f :=
  offDiagonalLongExtraction_section datum scalars (fun _ => 12) 0 true _ _ f

private def dottedCrossingIndex : NFIdx [false, true] [true, false] := by
  refine ⟨([0], Equiv.swap 0 1), by decide, by decide, ?_⟩
  change SChain [false, true]
    (pl [false, true] (PG.dot 0 :: cw (Categorification.TypeA.canWord 2 (Equiv.swap 0 1))))
    [true, false]
  have ht : tgt [false, true]
      (PG.dot 0 :: cw (Categorification.TypeA.canWord 2 (Equiv.swap 0 1))) = [true, false] := by
    change tgt [false, true]
      (([0] : List ℕ).map PG.dot ++ cw (Categorification.TypeA.canWord 2 (Equiv.swap 0 1))) =
      [true, false]
    rw [tgt_append, tgt_map_dot]
    exact crossingTarget
  simpa only [ht] using
    sChain_pl [false, true] (PG.dot 0 :: cw (Categorification.TypeA.canWord 2 (Equiv.swap 0 1)))

/-- Different old normal forms compute the same long coordinate functional. -/
example (z : Target datum scalars (fun _ => 12) false [false, true] ([true, false] ++ [false])) :
    longHomCoordinate datum scalars (fun _ => 12) 1 false crossingIndex 3 z =
      longHomCoordinate datum scalars (fun _ => 12) 1 false dottedCrossingIndex 3 z :=
  longHomCoordinate_independent datum scalars (fun _ => 12) 1 false
    crossingIndex dottedCrossingIndex 3 z

example :
    longHomSection datum scalars (fun _ => 12) 0 true crossingIndex =
      longHomSection datum scalars (fun _ => 12) 0 true dottedCrossingIndex :=
  longHomSection_independent datum scalars (fun _ => 12) 0 true
    crossingIndex dottedCrossingIndex

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVOffDiagonalLongCoordinates
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owned module"
  let names := env.header.moduleData[idx]!.constNames
  unless names.size > 0 do throwError "Empty owned module"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited ALL {names.size} owned declarations including private/generated"
