import OddMath.QuiverHecke.CyclotomicAction.ELVContentMatrixHeight
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
open ELVOld.CyclotomicCrossingTensor
namespace ContentMatrixHeightConsumer
open CyclotomicAction.AsymmetricParameters
private def mixedDatum : SKM.Datum Bool (Bool → ℤ) :=
  { datum with
    parity := fun i => if i then 1 else 0
    even_of_odd := fun i j _ => datum.even_of_odd i j rfl }

private def mixedScalars : SKM.Scalars mixedDatum ℚ where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := by intro _; norm_num




def oldOpp (n : ℕ) (ν : List Bool) : OldContentCategory mixedDatum mixedScalars (fun _ => n) ν :=
  ⟨⟨ν.reverse⟩, List.reverse_perm ν⟩
def truncatedOpp (n bound : ℕ) (ν : List Bool) :
    ContentCategory mixedDatum mixedScalars (fun _ => n) bound (ν : Multiset Bool) :=
  ⟨⟨ν.reverse⟩, Multiset.coe_eq_coe.mpr (List.reverse_perm ν)⟩

theorem oddUnitSign : 0 ≤ contentCrossingHeight mixedDatum (fun _ => 4) true ([false,true] : Multiset Bool) := by
  norm_num [contentCrossingHeight, mixedDatum, datum, SKM.Datum.h, SKM.Datum.α]
theorem oddUnitCount : contentUnitCount mixedDatum (fun _ => 4) true ([false,true] : Multiset Bool) = 6 := by
  norm_num [contentUnitCount, contentCrossingHeight, mixedDatum, datum, SKM.Datum.h, SKM.Datum.α]

example : endpointQPDegree mixedDatum (fun _ => 4) true (oldOpp 4 [false,true]).obj.word = outputSDegree mixedDatum true (oldOpp 4 [false,true]).obj.word + 6 := by
  simpa only [oddUnitCount] using oldContent_unitCount_height mixedDatum mixedScalars (fun _ => 4) true
    [false,true] oddUnitSign (oldOpp 4 [false,true])

example (bound : ℕ) : endpointQPDegree mixedDatum (fun _ => 4) true (truncatedOpp 4 bound [false,true]).obj.word = outputSDegree mixedDatum true (truncatedOpp 4 bound [false,true]).obj.word + 6 := by
  simpa only [oddUnitCount] using contentCategory_unitCount_height mixedDatum mixedScalars (fun _ => 4) true
    bound ([false,true] : Multiset Bool) oddUnitSign (truncatedOpp 4 bound [false,true])

theorem evenUnitSign : 0 ≤ contentCrossingHeight mixedDatum (fun _ => 4) false ([false,true] : Multiset Bool) := by
  norm_num [contentCrossingHeight, mixedDatum, datum, SKM.Datum.h, SKM.Datum.α]
theorem evenUnitCount : contentUnitCount mixedDatum (fun _ => 4) false ([false,true] : Multiset Bool) = 4 := by
  norm_num [contentUnitCount, contentCrossingHeight, mixedDatum, datum, SKM.Datum.h, SKM.Datum.α]

example : endpointQPDegree mixedDatum (fun _ => 4) false (oldOpp 4 [false,true]).obj.word = outputSDegree mixedDatum false (oldOpp 4 [false,true]).obj.word + 4 := by
  simpa only [evenUnitCount] using oldContent_unitCount_height mixedDatum mixedScalars (fun _ => 4) false
    [false,true] evenUnitSign (oldOpp 4 [false,true])

example (bound : ℕ) : endpointQPDegree mixedDatum (fun _ => 4) false (truncatedOpp 4 bound [false,true]).obj.word = outputSDegree mixedDatum false (truncatedOpp 4 bound [false,true]).obj.word + 4 := by
  simpa only [evenUnitCount] using contentCategory_unitCount_height mixedDatum mixedScalars (fun _ => 4) false
    bound ([false,true] : Multiset Bool) evenUnitSign (truncatedOpp 4 bound [false,true])

theorem oddCapSign : contentCrossingHeight mixedDatum (fun _ => 1) true ([false,true,true,true,true] : Multiset Bool) ≤ 0 := by
  norm_num [contentCrossingHeight, mixedDatum, datum, SKM.Datum.h, SKM.Datum.α]
theorem oddCapCount : contentCapCount mixedDatum (fun _ => 1) true ([false,true,true,true,true] : Multiset Bool) = 3 := by
  norm_num [contentCapCount, contentCrossingHeight, mixedDatum, datum, SKM.Datum.h, SKM.Datum.α]

example : outputSDegree mixedDatum true (oldOpp 1 [false,true,true,true,true]).obj.word = endpointQPDegree mixedDatum (fun _ => 1) true (oldOpp 1 [false,true,true,true,true]).obj.word + 3 := by
  simpa only [oddCapCount] using oldContent_capCount_height mixedDatum mixedScalars (fun _ => 1) true
    [false,true,true,true,true] oddCapSign (oldOpp 1 [false,true,true,true,true])

example (bound : ℕ) : outputSDegree mixedDatum true (truncatedOpp 1 bound [false,true,true,true,true]).obj.word = endpointQPDegree mixedDatum (fun _ => 1) true (truncatedOpp 1 bound [false,true,true,true,true]).obj.word + 3 := by
  simpa only [oddCapCount] using contentCategory_capCount_height mixedDatum mixedScalars (fun _ => 1) true
    bound ([false,true,true,true,true] : Multiset Bool) oddCapSign (truncatedOpp 1 bound [false,true,true,true,true])

theorem evenCapSign : contentCrossingHeight mixedDatum (fun _ => 1) false ([false,false,false,true] : Multiset Bool) ≤ 0 := by
  norm_num [contentCrossingHeight, mixedDatum, datum, SKM.Datum.h, SKM.Datum.α]
theorem evenCapCount : contentCapCount mixedDatum (fun _ => 1) false ([false,false,false,true] : Multiset Bool) = 3 := by
  norm_num [contentCapCount, contentCrossingHeight, mixedDatum, datum, SKM.Datum.h, SKM.Datum.α]

example : outputSDegree mixedDatum false (oldOpp 1 [false,false,false,true]).obj.word = endpointQPDegree mixedDatum (fun _ => 1) false (oldOpp 1 [false,false,false,true]).obj.word + 3 := by
  simpa only [evenCapCount] using oldContent_capCount_height mixedDatum mixedScalars (fun _ => 1) false
    [false,false,false,true] evenCapSign (oldOpp 1 [false,false,false,true])

example (bound : ℕ) : outputSDegree mixedDatum false (truncatedOpp 1 bound [false,false,false,true]).obj.word = endpointQPDegree mixedDatum (fun _ => 1) false (truncatedOpp 1 bound [false,false,false,true]).obj.word + 3 := by
  simpa only [evenCapCount] using contentCategory_capCount_height mixedDatum mixedScalars (fun _ => 1) false
    bound ([false,false,false,true] : Multiset Bool) evenCapSign (truncatedOpp 1 bound [false,false,false,true])

theorem zeroUnitSign : 0 ≤ contentCrossingHeight mixedDatum (fun _ => 2) false ([false] : Multiset Bool) := by
  norm_num [contentCrossingHeight, mixedDatum, datum, SKM.Datum.h, SKM.Datum.α]
theorem zeroUnitCount : contentUnitCount mixedDatum (fun _ => 2) false ([false] : Multiset Bool) = 0 := by
  norm_num [contentUnitCount, contentCrossingHeight, mixedDatum, datum, SKM.Datum.h, SKM.Datum.α]

example : endpointQPDegree mixedDatum (fun _ => 2) false (oldOpp 2 [false]).obj.word = outputSDegree mixedDatum false (oldOpp 2 [false]).obj.word + 0 := by
  simpa only [zeroUnitCount] using oldContent_unitCount_height mixedDatum mixedScalars (fun _ => 2) false
    [false] zeroUnitSign (oldOpp 2 [false])

example (bound : ℕ) : endpointQPDegree mixedDatum (fun _ => 2) false (truncatedOpp 2 bound [false]).obj.word = outputSDegree mixedDatum false (truncatedOpp 2 bound [false]).obj.word + 0 := by
  simpa only [zeroUnitCount] using contentCategory_unitCount_height mixedDatum mixedScalars (fun _ => 2) false
    bound ([false] : Multiset Bool) zeroUnitSign (truncatedOpp 2 bound [false])

theorem zeroCapSign : contentCrossingHeight mixedDatum (fun _ => 2) false ([false] : Multiset Bool) ≤ 0 := by
  norm_num [contentCrossingHeight, mixedDatum, datum, SKM.Datum.h, SKM.Datum.α]
theorem zeroCapCount : contentCapCount mixedDatum (fun _ => 2) false ([false] : Multiset Bool) = 0 := by
  norm_num [contentCapCount, contentCrossingHeight, mixedDatum, datum, SKM.Datum.h, SKM.Datum.α]

example : outputSDegree mixedDatum false (oldOpp 2 [false]).obj.word = endpointQPDegree mixedDatum (fun _ => 2) false (oldOpp 2 [false]).obj.word + 0 := by
  simpa only [zeroCapCount] using oldContent_capCount_height mixedDatum mixedScalars (fun _ => 2) false
    [false] zeroCapSign (oldOpp 2 [false])

example (bound : ℕ) : outputSDegree mixedDatum false (truncatedOpp 2 bound [false]).obj.word = endpointQPDegree mixedDatum (fun _ => 2) false (truncatedOpp 2 bound [false]).obj.word + 0 := by
  simpa only [zeroCapCount] using contentCategory_capCount_height mixedDatum mixedScalars (fun _ => 2) false
    bound ([false] : Multiset Bool) zeroCapSign (truncatedOpp 2 bound [false])

example : (oldOpp 4 [false,true]).obj.word ≠ [false,true] := by decide
end ContentMatrixHeightConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVContentMatrixHeight
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner"
  for name in names do
    for ax in (← Lean.collectAxioms name) do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited ALL {names.size} owned declarations including private/generated"
