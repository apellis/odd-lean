import OddMath.QuiverHecke.CyclotomicAction.ELVFiniteMatrixComponents
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
open ELVOld.CyclotomicCrossingTensor
namespace FiniteMatrixComponentsConsumer
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
abbrev Ordinary (i : Bool) (N : ℕ) (v t : List Bool) :=
  (actualUnshiftedSourceModule mixedDatum mixedScalars (fun _ => N) i v).obj
    (⟨t⟩ : OldCategory mixedDatum mixedScalars (fun _ => N))
abbrev PositiveTarget (i : Bool) (N : ℕ) (v t : List Bool) :=
  ((BalancedInduction.restriction (append mixedDatum mixedScalars (fun _ => N) i)).obj
    ((BalancedInduction.induction (append mixedDatum mixedScalars (fun _ => N) i)).obj
      (H N v))).obj (⟨t⟩ : OldCategory mixedDatum mixedScalars (fun _ => N))

theorem oddUnitHeight : endpointQPDegree mixedDatum (fun _ => 4) oddColour.1 [false,true] = outputSDegree mixedDatum oddColour.1 [false,true] + 6 := by
  norm_num [oddColour, outputSDegree, endpointQPDegree, appendQPDegree, SKM.Datum.dn,
    SKM.Datum.d, SKM.Datum.h, SKM.Datum.α, mixedDatum, datum, List.range_succ, List.getD]

def oddUnit : (unitMatrixSourceSpace mixedDatum mixedScalars (fun _ => 4) oddColour.1 (H 4 [false,true]) 6
    (⟨[true,false]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 4))) ≅ (PositiveTarget oddColour.1 4 [false,true] [true,false]) :=
  unitMatrixComponentIso mixedDatum mixedScalars (fun _ => 4) 0 oddColour [false,true] [true,false] 6 oddUnitHeight

example : oddUnit.hom = unitMatrixComponent mixedDatum mixedScalars (fun _ => 4) oddColour.1 (H 4 [false,true]) 6
    (⟨[true,false]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 4)) :=
  unitMatrixComponentIso_hom mixedDatum mixedScalars (fun _ => 4) 0 oddColour [false,true] [true,false] 6 oddUnitHeight
example : oddUnit.inv ∈ parity (R := ℚ) _ _ 0 :=
  unitMatrixComponentIso_inv_even mixedDatum mixedScalars (fun _ => 4) 0 oddColour [false,true] [true,false] 6 oddUnitHeight
example (x : unitMatrixSourceSpace mixedDatum mixedScalars (fun _ => 4) oddColour.1 (H 4 [false,true]) 6
    (⟨[true,false]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 4))) : oddUnit.inv (oddUnit.hom x) = x := by
  have h := congrArg (fun f : (unitMatrixSourceSpace mixedDatum mixedScalars (fun _ => 4) oddColour.1 (H 4 [false,true]) 6
    (⟨[true,false]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 4))) ⟶ (unitMatrixSourceSpace mixedDatum mixedScalars (fun _ => 4) oddColour.1 (H 4 [false,true]) 6
    (⟨[true,false]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 4))) => f x) oddUnit.hom_inv_id
  simpa only [SVec.comp_apply, SVec.id_apply] using h
example (y : PositiveTarget oddColour.1 4 [false,true] [true,false]) : oddUnit.hom (oddUnit.inv y) = y := by
  have h := congrArg (fun f : (PositiveTarget oddColour.1 4 [false,true] [true,false]) ⟶ (PositiveTarget oddColour.1 4 [false,true] [true,false]) => f y) oddUnit.inv_hom_id
  simpa only [SVec.comp_apply, SVec.id_apply] using h

theorem evenUnitHeight : endpointQPDegree mixedDatum (fun _ => 4) evenColour.1 [false,true] = outputSDegree mixedDatum evenColour.1 [false,true] + 4 := by
  norm_num [evenColour, outputSDegree, endpointQPDegree, appendQPDegree, SKM.Datum.dn,
    SKM.Datum.d, SKM.Datum.h, SKM.Datum.α, mixedDatum, datum, List.range_succ, List.getD]

def evenUnit : (unitMatrixSourceSpace mixedDatum mixedScalars (fun _ => 4) evenColour.1 (H 4 [false,true]) 4
    (⟨[true,false]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 4))) ≅ (PositiveTarget evenColour.1 4 [false,true] [true,false]) :=
  evenUnitMatrixComponentIso mixedDatum mixedScalars (fun _ => 4) 0 evenColour [false,true] [true,false] 4 evenUnitHeight

example : evenUnit.hom = unitMatrixComponent mixedDatum mixedScalars (fun _ => 4) evenColour.1 (H 4 [false,true]) 4
    (⟨[true,false]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 4)) :=
  evenUnitMatrixComponentIso_hom mixedDatum mixedScalars (fun _ => 4) 0 evenColour [false,true] [true,false] 4 evenUnitHeight
example : evenUnit.inv ∈ parity (R := ℚ) _ _ 0 :=
  evenUnitMatrixComponentIso_inv_even mixedDatum mixedScalars (fun _ => 4) 0 evenColour [false,true] [true,false] 4 evenUnitHeight
example (x : unitMatrixSourceSpace mixedDatum mixedScalars (fun _ => 4) evenColour.1 (H 4 [false,true]) 4
    (⟨[true,false]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 4))) : evenUnit.inv (evenUnit.hom x) = x := by
  have h := congrArg (fun f : (unitMatrixSourceSpace mixedDatum mixedScalars (fun _ => 4) evenColour.1 (H 4 [false,true]) 4
    (⟨[true,false]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 4))) ⟶ (unitMatrixSourceSpace mixedDatum mixedScalars (fun _ => 4) evenColour.1 (H 4 [false,true]) 4
    (⟨[true,false]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 4))) => f x) evenUnit.hom_inv_id
  simpa only [SVec.comp_apply, SVec.id_apply] using h
example (y : PositiveTarget evenColour.1 4 [false,true] [true,false]) : evenUnit.hom (evenUnit.inv y) = y := by
  have h := congrArg (fun f : (PositiveTarget evenColour.1 4 [false,true] [true,false]) ⟶ (PositiveTarget evenColour.1 4 [false,true] [true,false]) => f y) evenUnit.inv_hom_id
  simpa only [SVec.comp_apply, SVec.id_apply] using h

theorem oddCapHeight : outputSDegree mixedDatum oddColour.1 [false,true,true,true,true] = endpointQPDegree mixedDatum (fun _ => 1) oddColour.1 [false,true,true,true,true] + 3 := by
  norm_num [oddColour, outputSDegree, endpointQPDegree, appendQPDegree, SKM.Datum.dn,
    SKM.Datum.d, SKM.Datum.h, SKM.Datum.α, mixedDatum, datum, List.range_succ, List.getD]

def oddCap : (Ordinary oddColour.1 1 [false,true,true,true,true] [true,true,true,true,false]) ≅ (capMatrixTargetSpace mixedDatum mixedScalars (fun _ => 1) oddColour.1 (H 1 [false,true,true,true,true]) 3
    (⟨[true,true,true,true,false]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 1))) :=
  capMatrixComponentIso mixedDatum mixedScalars (fun _ => 1) 0 oddColour [false,true,true,true,true] [true,true,true,true,false] 3 oddCapHeight

example : oddCap.hom = capMatrixComponent mixedDatum mixedScalars (fun _ => 1) oddColour.1 (H 1 [false,true,true,true,true]) 3
    (⟨[true,true,true,true,false]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 1)) :=
  capMatrixComponentIso_hom mixedDatum mixedScalars (fun _ => 1) 0 oddColour [false,true,true,true,true] [true,true,true,true,false] 3 oddCapHeight
example : oddCap.inv ∈ parity (R := ℚ) _ _ 0 :=
  capMatrixComponentIso_inv_even mixedDatum mixedScalars (fun _ => 1) 0 oddColour [false,true,true,true,true] [true,true,true,true,false] 3 oddCapHeight
example (x : Ordinary oddColour.1 1 [false,true,true,true,true] [true,true,true,true,false]) : oddCap.inv (oddCap.hom x) = x := by
  have h := congrArg (fun f : (Ordinary oddColour.1 1 [false,true,true,true,true] [true,true,true,true,false]) ⟶ (Ordinary oddColour.1 1 [false,true,true,true,true] [true,true,true,true,false]) => f x) oddCap.hom_inv_id
  simpa only [SVec.comp_apply, SVec.id_apply] using h
example (y : capMatrixTargetSpace mixedDatum mixedScalars (fun _ => 1) oddColour.1 (H 1 [false,true,true,true,true]) 3
    (⟨[true,true,true,true,false]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 1))) : oddCap.hom (oddCap.inv y) = y := by
  have h := congrArg (fun f : (capMatrixTargetSpace mixedDatum mixedScalars (fun _ => 1) oddColour.1 (H 1 [false,true,true,true,true]) 3
    (⟨[true,true,true,true,false]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 1))) ⟶ (capMatrixTargetSpace mixedDatum mixedScalars (fun _ => 1) oddColour.1 (H 1 [false,true,true,true,true]) 3
    (⟨[true,true,true,true,false]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 1))) => f y) oddCap.inv_hom_id
  simpa only [SVec.comp_apply, SVec.id_apply] using h

theorem evenCapHeight : outputSDegree mixedDatum evenColour.1 [false,false,false,true] = endpointQPDegree mixedDatum (fun _ => 1) evenColour.1 [false,false,false,true] + 3 := by
  norm_num [evenColour, outputSDegree, endpointQPDegree, appendQPDegree, SKM.Datum.dn,
    SKM.Datum.d, SKM.Datum.h, SKM.Datum.α, mixedDatum, datum, List.range_succ, List.getD]

def evenCap : (Ordinary evenColour.1 1 [false,false,false,true] [true,false,false,false]) ≅ (capMatrixTargetSpace mixedDatum mixedScalars (fun _ => 1) evenColour.1 (H 1 [false,false,false,true]) 3
    (⟨[true,false,false,false]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 1))) :=
  evenCapMatrixComponentIso mixedDatum mixedScalars (fun _ => 1) 0 evenColour [false,false,false,true] [true,false,false,false] 3 evenCapHeight

example : evenCap.hom = capMatrixComponent mixedDatum mixedScalars (fun _ => 1) evenColour.1 (H 1 [false,false,false,true]) 3
    (⟨[true,false,false,false]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 1)) :=
  evenCapMatrixComponentIso_hom mixedDatum mixedScalars (fun _ => 1) 0 evenColour [false,false,false,true] [true,false,false,false] 3 evenCapHeight
example : evenCap.inv ∈ parity (R := ℚ) _ _ 0 :=
  evenCapMatrixComponentIso_inv_even mixedDatum mixedScalars (fun _ => 1) 0 evenColour [false,false,false,true] [true,false,false,false] 3 evenCapHeight
example (x : Ordinary evenColour.1 1 [false,false,false,true] [true,false,false,false]) : evenCap.inv (evenCap.hom x) = x := by
  have h := congrArg (fun f : (Ordinary evenColour.1 1 [false,false,false,true] [true,false,false,false]) ⟶ (Ordinary evenColour.1 1 [false,false,false,true] [true,false,false,false]) => f x) evenCap.hom_inv_id
  simpa only [SVec.comp_apply, SVec.id_apply] using h
example (y : capMatrixTargetSpace mixedDatum mixedScalars (fun _ => 1) evenColour.1 (H 1 [false,false,false,true]) 3
    (⟨[true,false,false,false]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 1))) : evenCap.hom (evenCap.inv y) = y := by
  have h := congrArg (fun f : (capMatrixTargetSpace mixedDatum mixedScalars (fun _ => 1) evenColour.1 (H 1 [false,false,false,true]) 3
    (⟨[true,false,false,false]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 1))) ⟶ (capMatrixTargetSpace mixedDatum mixedScalars (fun _ => 1) evenColour.1 (H 1 [false,false,false,true]) 3
    (⟨[true,false,false,false]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 1))) => f y) evenCap.inv_hom_id
  simpa only [SVec.comp_apply, SVec.id_apply] using h

theorem zeroCapHeight : outputSDegree mixedDatum evenColour.1 [false] = endpointQPDegree mixedDatum (fun _ => 2) evenColour.1 [false] + 0 := by
  norm_num [evenColour, outputSDegree, endpointQPDegree, appendQPDegree, SKM.Datum.dn,
    SKM.Datum.d, SKM.Datum.h, SKM.Datum.α, mixedDatum, datum, List.range_succ, List.getD]

def zeroCap : (Ordinary evenColour.1 2 [false] [false]) ≅ (capMatrixTargetSpace mixedDatum mixedScalars (fun _ => 2) evenColour.1 (H 2 [false]) 0
    (⟨[false]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 2))) :=
  evenCapMatrixComponentIso mixedDatum mixedScalars (fun _ => 2) 0 evenColour [false] [false] 0 zeroCapHeight

example : zeroCap.hom = capMatrixComponent mixedDatum mixedScalars (fun _ => 2) evenColour.1 (H 2 [false]) 0
    (⟨[false]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 2)) :=
  evenCapMatrixComponentIso_hom mixedDatum mixedScalars (fun _ => 2) 0 evenColour [false] [false] 0 zeroCapHeight
example : zeroCap.inv ∈ parity (R := ℚ) _ _ 0 :=
  evenCapMatrixComponentIso_inv_even mixedDatum mixedScalars (fun _ => 2) 0 evenColour [false] [false] 0 zeroCapHeight
example (x : Ordinary evenColour.1 2 [false] [false]) : zeroCap.inv (zeroCap.hom x) = x := by
  have h := congrArg (fun f : (Ordinary evenColour.1 2 [false] [false]) ⟶ (Ordinary evenColour.1 2 [false] [false]) => f x) zeroCap.hom_inv_id
  simpa only [SVec.comp_apply, SVec.id_apply] using h
example (y : capMatrixTargetSpace mixedDatum mixedScalars (fun _ => 2) evenColour.1 (H 2 [false]) 0
    (⟨[false]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 2))) : zeroCap.hom (zeroCap.inv y) = y := by
  have h := congrArg (fun f : (capMatrixTargetSpace mixedDatum mixedScalars (fun _ => 2) evenColour.1 (H 2 [false]) 0
    (⟨[false]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 2))) ⟶ (capMatrixTargetSpace mixedDatum mixedScalars (fun _ => 2) evenColour.1 (H 2 [false]) 0
    (⟨[false]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 2))) => f y) zeroCap.inv_hom_id
  simpa only [SVec.comp_apply, SVec.id_apply] using h
end FiniteMatrixComponentsConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVFiniteMatrixComponents
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner"
  for name in names do
    for ax in (← Lean.collectAxioms name) do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited ALL {names.size} owned declarations including private/generated"
