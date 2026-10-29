import OddMath.QuiverHecke.CyclotomicAction.ELVPCentral

/-! Consumers of `DeformedSquareResolution.md` §§1,3 on the prescribed quotients.
No commutation, descent, old balance, nonzero-cutoff or parity restriction is
an input to the combined central-variable assertion. -/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

example (i : I) (v w : List I) (z : Target D Sc cutoff i v w) :
    pMap D Sc cutoff i v w (centralSource D Sc cutoff i v w z) =
      centralAppend D Sc cutoff i v w (pMap D Sc cutoff i v w z) :=
  pMap_central D Sc cutoff i v w z

example (i : I) (v w : List I) (z : Target D Sc (fun _ => 0) i v w) :
    pMap D Sc (fun _ => 0) i v w (centralSource D Sc (fun _ => 0) i v w z) =
      centralAppend D Sc (fun _ => 0) i v w (pMap D Sc (fun _ => 0) i v w z) :=
  pMap_central D Sc (fun _ => 0) i v w z

example (i : I) (v w : List I) (z : Target D Sc (fun _ => 2) i v w) :
    pMap D Sc (fun _ => 2) i v w
      (movingPowerTarget D Sc (fun _ => 2) i v w 2
        ((by decide : ∀ q : ZMod 2, (2 : ℕ) • q = 0) (D.parity i)) z) =
      appendMovingPowerTarget D Sc (fun _ => 2) i v w 2
        (pMap D Sc (fun _ => 2) i v w z) :=
  pMap_movingSquare D Sc (fun _ => 2) i v w z

example (i : I) (hi : D.parity i = 0) (v w : List I) (z : Target D Sc cutoff i v w) :
    pMap D Sc cutoff i v w (movingPowerTarget D Sc cutoff i v w 1 (by simp [hi]) z) =
      appendMovingPowerTarget D Sc cutoff i v w 1 (pMap D Sc cutoff i v w z) :=
  pMap_movingEvenDot D Sc cutoff i hi v w z

example (i : I) (v w : List I) (f : Polynomial k) (z : CentralTarget D Sc cutoff i v w) :
    pCentralMap D Sc cutoff i v w (f • z) = f • pCentralMap D Sc cutoff i v w z :=
  (pCentralMap D Sc cutoff i v w).map_smul f z

example (i : I) (v w : List I) (c : hom D Sc cutoff v v)
    (z : CentralTarget D Sc cutoff i v w) :
    pCentralMap D Sc cutoff i v w (centralOldSource D Sc cutoff i v w c z) =
      centralOldAppend D Sc cutoff i v w c (pCentralMap D Sc cutoff i v w z) :=
  pCentralMap_oldSource D Sc cutoff i v w c z

example (i : I) (v w : List I) (z : CentralTarget D Sc cutoff i v w) :
    centralOldSource D Sc cutoff i v w 0 z = 0 :=
  centralOldSource_ideal D Sc cutoff i v w (Submodule.zero_mem _) z

#print axioms pMap_movingSquare
#print axioms pMap_movingEvenDot
#print axioms pCentralMap
#print axioms pCentralMap_oldSource

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut total : Nat := 0
  for owner in #[`OddMath.QuiverHecke.CyclotomicAction.ELVAppendMovingSlide,
      `OddMath.QuiverHecke.CyclotomicAction.ELVPCentral] do
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
    total := total + count
  logInfo m!"Audited {total} declarations in the central-linearity modules."
