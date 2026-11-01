import OddMath.QuiverHecke.CyclotomicAction.ELVMatrixEntryTotals
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
open ELVOld.CyclotomicCrossingTensor
namespace MatrixEntryTotalsConsumer
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



local instance : PiSupercategory ℚ (Superfunctor ℚ (OldCategory mixedDatum mixedScalars (fun _ => 4)) (SVec ℚ)) :=
  supermodulePiSupercategory

abbrev H := oldRepresentable mixedDatum mixedScalars (fun _ => 4)
  (⟨[false,true]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 4))
abbrev t : OldCategory mixedDatum mixedScalars (fun _ => 4) := ⟨[true,false]⟩
abbrev Coeff := Old mixedDatum mixedScalars (fun _ => 4) [false,true] [true,false]

example (i : Bool) (n : ℕ) (b : Coeff) :
    OldInductionRepresentable.upperHomEquiv mixedDatum mixedScalars (fun _ => 4) i
      (⟨[false,true]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 4)) t
      ((moduleUnitColumn mixedDatum mixedScalars (fun _ => 4) i H n).total t b) =
      inductionUnitDotColumn mixedDatum mixedScalars (fun _ => 4) i
        [false,true] [true,false] n b :=
  moduleUnitColumn_upper mixedDatum mixedScalars (fun _ => 4) i [false,true] [true,false] n b

example (i : Bool) (r : Fin 3)
    (b : (unitMatrixFamily mixedDatum mixedScalars (fun _ => 4) i H 3 (some r)).obj t) :
    OldInductionRepresentable.upperHomEquiv mixedDatum mixedScalars (fun _ => 4) i
      (⟨[false,true]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 4)) t
      ((unitMatrixEntry mixedDatum mixedScalars (fun _ => 4) i H 3 (some r)).total t b) =
      inductionUnitDotColumn mixedDatum mixedScalars (fun _ => 4) i [false,true] [true,false] r.val
        (moduleIsoLinearEquiv ((SKM.homParityShiftDatum (k := ℚ) (r.val • mixedDatum.parity i)).iso H) t b) :=
  unitMatrixEntry_some_upper mixedDatum mixedScalars (fun _ => 4) i [false,true] [true,false] 3 r b

example (i : Bool) (r : Fin 3)
    (z : ((BalancedInduction.induction (append mixedDatum mixedScalars (fun _ => 4) i)).obj
      ((BalancedInduction.restriction (append mixedDatum mixedScalars (fun _ => 4) i)).obj H)).obj t) :
    moduleIsoLinearEquiv ((SKM.homParityShiftDatum (k := ℚ) (r.val • mixedDatum.parity i)).iso H) t
      ((capMatrixEntry mixedDatum mixedScalars (fun _ => 4) i H 3 (some r)).total t z) =
      (moduleCapRow mixedDatum mixedScalars (fun _ => 4) i H r.val).total t z :=
  capMatrixEntry_some_total mixedDatum mixedScalars (fun _ => 4) i H t 3 r z

end MatrixEntryTotalsConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVMatrixEntryTotals
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner"
  for name in names do
    for ax in (← Lean.collectAxioms name) do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited ALL {names.size} owned declarations including private/generated"

