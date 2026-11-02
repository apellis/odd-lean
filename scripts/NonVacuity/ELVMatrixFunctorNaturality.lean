import OddMath.QuiverHecke.CyclotomicAction.ELVMatrixFunctorNaturality
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
open ELVOld.CyclotomicCrossingTensor
open CyclotomicAction.AsymmetricParameters
namespace MatrixFunctorNaturalityConsumer
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
private def cutoff (_ : Bool) : ℕ := 4
private abbrev C := OldCategory mixedDatum mixedScalars cutoff
private def M := oldRepresentable mixedDatum mixedScalars cutoff (⟨[true, false]⟩ : C)
private def N := oldRepresentable mixedDatum mixedScalars cutoff (⟨[false, true]⟩ : C)

/-- Both moving parities and every finite count admit arbitrary input maps. -/
example (i : Bool) (m : ℕ) (f : M ⟶ N) :
    (unitMatrixSourceFunctor mixedDatum mixedScalars cutoff i m).map f ≫
      (unitMatrixModuleNatTrans mixedDatum mixedScalars cutoff i m).app N =
    (unitMatrixModuleNatTrans mixedDatum mixedScalars cutoff i m).app M ≫
      (BalancedInduction.induction (append mixedDatum mixedScalars cutoff i) ⋙
        BalancedInduction.restriction (append mixedDatum mixedScalars cutoff i)).map f :=
  NatTrans.naturality _ f

example (i : Bool) (m : ℕ) (f : M ⟶ N) :
    (BalancedInduction.restriction (append mixedDatum mixedScalars cutoff i) ⋙
      BalancedInduction.induction (append mixedDatum mixedScalars cutoff i)).map f ≫
        (capMatrixModuleNatTrans mixedDatum mixedScalars cutoff i m).app N =
    (capMatrixModuleNatTrans mixedDatum mixedScalars cutoff i m).app M ≫
      (capMatrixTargetFunctor mixedDatum mixedScalars cutoff i m).map f :=
  NatTrans.naturality _ f

/-- With no finite dotted slots, the whole matrix is still natural. -/
example (i : Bool) (f : M ⟶ N) :
    (unitMatrixSourceFunctor mixedDatum mixedScalars cutoff i 0).map f ≫
      (unitMatrixModuleNatTrans mixedDatum mixedScalars cutoff i 0).app N =
    (unitMatrixModuleNatTrans mixedDatum mixedScalars cutoff i 0).app M ≫
      (BalancedInduction.induction (append mixedDatum mixedScalars cutoff i) ⋙
        BalancedInduction.restriction (append mixedDatum mixedScalars cutoff i)).map f :=
  NatTrans.naturality _ f

local instance : PiSupercategory ℚ (Superfunctor ℚ C (SVec ℚ)) :=
  supermodulePiSupercategory

/-- A specified odd isomorphism supplies an input map, with no parity hypothesis assumed. -/
example (i : Bool) :
    (unitMatrixSourceFunctor mixedDatum mixedScalars cutoff i 4).map
      ((SKM.homParityShiftDatum (k := ℚ) 1).iso M).inv ∈ parity (R := ℚ) _ _ 1 :=
  IsSuperfunctor.map_mem ((SKM.homParityShiftDatum (k := ℚ) 1).inv_mem M)

example (i : Bool) :
    (capMatrixTargetFunctor mixedDatum mixedScalars cutoff i 4).map
      ((SKM.homParityShiftDatum (k := ℚ) 1).iso M).inv ∈ parity (R := ℚ) _ _ 1 :=
  IsSuperfunctor.map_mem ((SKM.homParityShiftDatum (k := ℚ) 1).inv_mem M)

end MatrixFunctorNaturalityConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for owner in #[`OddMath.Algebra.FiniteSupermoduleFunctor,
      `OddMath.QuiverHecke.CyclotomicAction.ELVMatrixFunctorNaturality] do
    let some idx := env.header.moduleNames.idxOf? owner | throwError "Module was not imported"
    let names := env.header.moduleData[idx]!.constNames
    unless names.size > 0 do throwError "Empty declaration inventory"
    for name in names do
      for axiomName in (← Lean.collectAxioms name) do
        unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
          throwError "Disallowed axiom {axiomName} in {name}"
    logInfo m!"Audited ALL {names.size} declarations in {owner}"
