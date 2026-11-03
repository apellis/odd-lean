import OddMath.Algebra.FiniteSupermoduleFamily
import OddMath.QuiverHecke.CyclotomicAction.ELVShiftedMatrixFamilies
import OddMath.QuiverHecke.CyclotomicAction.ELVContentEFComparison
import OddMath.QuiverHecke.CyclotomicAction.ELVContentAppendDot
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import OddMath.QuiverHecke.CyclotomicAction.ELVOldSupermodules
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
open ELVOld.CyclotomicCrossingTensor
open CategoryTheory.Functor
namespace FiniteSupermoduleFamilyConsumer
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



abbrev C := OldCategory mixedDatum mixedScalars (fun _ => 4)

private abbrev v : C := ⟨[false, true]⟩
private abbrev source : OldContentCategory mixedDatum mixedScalars (fun _ => 4) [false, true] :=
  ⟨v, List.Perm.refl _⟩
private def block : Superfunctor ℚ
    (OldContentCategory mixedDatum mixedScalars (fun _ => 4) [false, true]) (SVec ℚ) :=
  (BalancedInduction.restriction
    (oldContentInclusion mixedDatum mixedScalars (fun _ => 4) [false, true])).obj
    (oldRepresentable mixedDatum mixedScalars (fun _ => 4) v)
private def upperBlock (i : Bool) : Superfunctor ℚ
    (OldContentCategory mixedDatum mixedScalars (fun _ => 4) (i :: [false, true])) (SVec ℚ) :=
  (BalancedInduction.restriction
    (oldContentInclusion mixedDatum mixedScalars (fun _ => 4) (i :: [false, true]))).obj
    (oldRepresentable mixedDatum mixedScalars (fun _ => 4)
      ((append mixedDatum mixedScalars (fun _ => 4) i).obj v))

local instance (i : Bool) : PiSupercategory ℚ
    (Superfunctor ℚ (OldContentCategory mixedDatum mixedScalars (fun _ => 4)
      (i :: [false, true])) (SVec ℚ)) := supermodulePiSupercategory

private def chart (i : Bool) (a : Bool) :=
  isoWhiskerRight
    (oldContentEFRestrictionNaturalIso mixedDatum mixedScalars (fun _ => 4) [false, true] i)
    (SKM.homParityShift (k := ℚ) (if a then 1 else 0))

/-- Both canonical parity shifts retain the selected content E/F comparison. -/
example (i : Bool) := FiniteSupermodule.familyNatIso (chart i)

/-- Naturality includes the given odd dot on the induced mixed module. -/
example := (FiniteSupermodule.familyNatIso (chart true)).hom.naturality
  (oldContentInductionDotComponent mixedDatum mixedScalars (fun _ => 4) [false, true] true block)

/-- It also includes the sum of identity and odd dot, with both components present. -/
example := (FiniteSupermodule.familyNatIso (chart true)).hom.naturality
  (𝟙 _ + oldContentInductionDotComponent mixedDatum mixedScalars (fun _ => 4)
    [false, true] true block)

example : oldContentInductionDotComponent mixedDatum mixedScalars (fun _ => 4)
    [false, true] true block ∈ parity (R := ℚ) _ _ 1 :=
  (oldContentInductionDotComponent_supernatural mixedDatum mixedScalars (fun _ => 4)
    [false, true] true).mem block

end FiniteSupermoduleFamilyConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.Algebra.FiniteSupermoduleFamily
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner"
  for name in names do
    for ax in (← Lean.collectAxioms name) do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited ALL {names.size} owned declarations including private/generated"
