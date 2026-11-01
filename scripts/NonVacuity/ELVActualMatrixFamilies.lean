import OddMath.QuiverHecke.CyclotomicAction.ELVActualMatrixFamilies
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
open ELVOld.CyclotomicCrossingTensor
namespace ActualMatrixFamiliesConsumer
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




private abbrev oddColour : {i : Bool // mixedDatum.parity i = 1} := ⟨true, rfl⟩
private abbrev evenColour : {i : Bool // mixedDatum.parity i = 0} := ⟨false, rfl⟩
abbrev H (N : ℕ) (v : List Bool) := oldRepresentable mixedDatum mixedScalars (fun _ => N)
  (⟨v⟩ : OldCategory mixedDatum mixedScalars (fun _ => N))
abbrev UnitF (i : Bool) (N m : ℕ) (v t : List Bool) := (a : Option (Fin m)) →
  (unitMatrixFamily mixedDatum mixedScalars (fun _ => N) i (H N v) m a).obj
    (⟨t⟩ : OldCategory mixedDatum mixedScalars (fun _ => N))
abbrev CapF (i : Bool) (N m : ℕ) (v t : List Bool) := (a : Option (Fin m)) →
  (capMatrixFamily mixedDatum mixedScalars (fun _ => N) i (H N v) m a).obj
    (⟨t⟩ : OldCategory mixedDatum mixedScalars (fun _ => N))
abbrev Ordinary (i : Bool) (N : ℕ) (v t : List Bool) :=
  (actualUnshiftedSourceModule mixedDatum mixedScalars (fun _ => N) i v).obj
    (⟨t⟩ : OldCategory mixedDatum mixedScalars (fun _ => N))
abbrev Upper (i : Bool) (N : ℕ) (v t : List Bool) :=
  Old mixedDatum mixedScalars (fun _ => N) (v ++ [i]) (t ++ [i])

theorem oddUnitHeight : endpointQPDegree mixedDatum (fun _ => 4) oddColour.1 [false,true] = outputSDegree mixedDatum oddColour.1 [false,true] + 6 := by
  norm_num [oddColour, outputSDegree, endpointQPDegree, appendQPDegree, SKM.Datum.dn,
    SKM.Datum.d, SKM.Datum.h, SKM.Datum.α, mixedDatum, datum, List.range_succ, List.getD]

def oddUnit : (UnitF oddColour.1 4 6 [false,true] [true,false]) ≃ₗ[ℚ] (Upper oddColour.1 4 [false,true] [true,false]) :=
  unitFamilyComponentEquiv mixedDatum mixedScalars (fun _ => 4) 0 oddColour [false,true] [true,false] 6 oddUnitHeight
example (x : UnitF oddColour.1 4 6 [false,true] [true,false]) : oddUnit.symm (oddUnit x) = x := oddUnit.symm_apply_apply x
example (y : Upper oddColour.1 4 [false,true] [true,false]) : oddUnit (oddUnit.symm y) = y := oddUnit.apply_symm_apply y

example (x : UnitF oddColour.1 4 6 [false,true] [true,false]) : oddUnit x =
    matrixMateRow mixedDatum mixedScalars (fun _ => 4) oddColour.1 [false,true] [true,false] (unitFamilyPlainCoordinates mixedDatum mixedScalars (fun _ => 4) oddColour.1 [false,true] [true,false] 6 x).1 +
      ∑ r : Fin 6, inductionUnitDotColumn mixedDatum mixedScalars (fun _ => 4) oddColour.1 [false,true] [true,false] r.val
        ((unitFamilyPlainCoordinates mixedDatum mixedScalars (fun _ => 4) oddColour.1 [false,true] [true,false] 6 x).2 r) :=
  unitFamilyComponentEquiv_actual mixedDatum mixedScalars (fun _ => 4) 0 oddColour [false,true] [true,false] 6 oddUnitHeight x

theorem evenUnitHeight : endpointQPDegree mixedDatum (fun _ => 4) evenColour.1 [false,true] = outputSDegree mixedDatum evenColour.1 [false,true] + 4 := by
  norm_num [evenColour, outputSDegree, endpointQPDegree, appendQPDegree, SKM.Datum.dn,
    SKM.Datum.d, SKM.Datum.h, SKM.Datum.α, mixedDatum, datum, List.range_succ, List.getD]

def evenUnit : (UnitF evenColour.1 4 4 [false,true] [true,false]) ≃ₗ[ℚ] (Upper evenColour.1 4 [false,true] [true,false]) :=
  evenUnitFamilyComponentEquiv mixedDatum mixedScalars (fun _ => 4) 0 evenColour [false,true] [true,false] 4 evenUnitHeight
example (x : UnitF evenColour.1 4 4 [false,true] [true,false]) : evenUnit.symm (evenUnit x) = x := evenUnit.symm_apply_apply x
example (y : Upper evenColour.1 4 [false,true] [true,false]) : evenUnit (evenUnit.symm y) = y := evenUnit.apply_symm_apply y

example (x : UnitF evenColour.1 4 4 [false,true] [true,false]) : evenUnit x =
    matrixMateRow mixedDatum mixedScalars (fun _ => 4) evenColour.1 [false,true] [true,false] (unitFamilyPlainCoordinates mixedDatum mixedScalars (fun _ => 4) evenColour.1 [false,true] [true,false] 4 x).1 +
      ∑ r : Fin 4, inductionUnitDotColumn mixedDatum mixedScalars (fun _ => 4) evenColour.1 [false,true] [true,false] r.val
        ((unitFamilyPlainCoordinates mixedDatum mixedScalars (fun _ => 4) evenColour.1 [false,true] [true,false] 4 x).2 r) :=
  evenUnitFamilyComponentEquiv_actual mixedDatum mixedScalars (fun _ => 4) 0 evenColour [false,true] [true,false] 4 evenUnitHeight x

theorem oddCapHeight : outputSDegree mixedDatum oddColour.1 [false,true,true,true,true] = endpointQPDegree mixedDatum (fun _ => 1) oddColour.1 [false,true,true,true,true] + 3 := by
  norm_num [oddColour, outputSDegree, endpointQPDegree, appendQPDegree, SKM.Datum.dn,
    SKM.Datum.d, SKM.Datum.h, SKM.Datum.α, mixedDatum, datum, List.range_succ, List.getD]

def oddCap : (Ordinary oddColour.1 1 [false,true,true,true,true] [true,true,true,true,false]) ≃ₗ[ℚ] (CapF oddColour.1 1 3 [false,true,true,true,true] [true,true,true,true,false]) :=
  capFamilyComponentEquiv mixedDatum mixedScalars (fun _ => 1) 0 oddColour [false,true,true,true,true] [true,true,true,true,false] 3 oddCapHeight
example (x : Ordinary oddColour.1 1 [false,true,true,true,true] [true,true,true,true,false]) : oddCap.symm (oddCap x) = x := oddCap.symm_apply_apply x
example (y : CapF oddColour.1 1 3 [false,true,true,true,true] [true,true,true,true,false]) : oddCap (oddCap.symm y) = y := oddCap.apply_symm_apply y

example (z : Ordinary oddColour.1 1 [false,true,true,true,true] [true,true,true,true,false]) :
    capFamilyComponentCoordinates mixedDatum mixedScalars (fun _ => 1) oddColour.1 [false,true,true,true,true] [true,true,true,true,false] 3 (oddCap z) =
      (matrixMateRow mixedDatum mixedScalars (fun _ => 1) oddColour.1 [false,true,true,true,true] [true,true,true,true,false] z,
        fun r : Fin 3 => (moduleCapRow mixedDatum mixedScalars (fun _ => 1) oddColour.1 (H 1 [false,true,true,true,true]) r.val).total
          (⟨[true,true,true,true,false]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 1)) z) :=
  capFamilyComponentEquiv_actual mixedDatum mixedScalars (fun _ => 1) 0 oddColour [false,true,true,true,true] [true,true,true,true,false] 3 oddCapHeight z

theorem evenCapHeight : outputSDegree mixedDatum evenColour.1 [false,false,false,true] = endpointQPDegree mixedDatum (fun _ => 1) evenColour.1 [false,false,false,true] + 3 := by
  norm_num [evenColour, outputSDegree, endpointQPDegree, appendQPDegree, SKM.Datum.dn,
    SKM.Datum.d, SKM.Datum.h, SKM.Datum.α, mixedDatum, datum, List.range_succ, List.getD]

def evenCap : (Ordinary evenColour.1 1 [false,false,false,true] [true,false,false,false]) ≃ₗ[ℚ] (CapF evenColour.1 1 3 [false,false,false,true] [true,false,false,false]) :=
  evenCapFamilyComponentEquiv mixedDatum mixedScalars (fun _ => 1) 0 evenColour [false,false,false,true] [true,false,false,false] 3 evenCapHeight
example (x : Ordinary evenColour.1 1 [false,false,false,true] [true,false,false,false]) : evenCap.symm (evenCap x) = x := evenCap.symm_apply_apply x
example (y : CapF evenColour.1 1 3 [false,false,false,true] [true,false,false,false]) : evenCap (evenCap.symm y) = y := evenCap.apply_symm_apply y

example (z : Ordinary evenColour.1 1 [false,false,false,true] [true,false,false,false]) :
    capFamilyComponentCoordinates mixedDatum mixedScalars (fun _ => 1) evenColour.1 [false,false,false,true] [true,false,false,false] 3 (evenCap z) =
      (matrixMateRow mixedDatum mixedScalars (fun _ => 1) evenColour.1 [false,false,false,true] [true,false,false,false] z,
        fun r : Fin 3 => (moduleCapRow mixedDatum mixedScalars (fun _ => 1) evenColour.1 (H 1 [false,false,false,true]) r.val).total
          (⟨[true,false,false,false]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 1)) z) :=
  evenCapFamilyComponentEquiv_actual mixedDatum mixedScalars (fun _ => 1) 0 evenColour [false,false,false,true] [true,false,false,false] 3 evenCapHeight z
end ActualMatrixFamiliesConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVActualMatrixFamilies
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner"
  for name in names do
    for ax in (← Lean.collectAxioms name) do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited ALL {names.size} owned declarations including private/generated"
