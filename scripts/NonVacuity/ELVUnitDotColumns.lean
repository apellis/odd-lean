import OddMath.QuiverHecke.CyclotomicAction.ELVUnitDotColumns
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
open ELVOld.CyclotomicCrossingTensor
namespace UnitDotColumnsConsumer
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



abbrev Coeff := Old mixedDatum mixedScalars (fun _ => 4) [false, true] [true, false]

example (b : Coeff) : inductionUnitDotColumn mixedDatum mixedScalars (fun _ => 4) true
    [false, true] [true, false] 2 b =
    -canonicalAppendTarget mixedDatum mixedScalars (fun _ => 4) true [false, true]
      ([true, false] ++ [true])
      (appendOutputEmbedding mixedDatum mixedScalars (fun _ => 4) true [false, true] [true, false]
        (Finsupp.single 2 b)) := by
  rw [inductionUnitDotColumn_apply, inductionUnitDotSign_eq]
  norm_num [mixedDatum]

example (b : Coeff) : inductionUnitDotColumn mixedDatum mixedScalars (fun _ => 4) false
    [false, true] [true, false] 5 b =
    canonicalAppendTarget mixedDatum mixedScalars (fun _ => 4) false [false, true]
      ([true, false] ++ [false])
      (appendOutputEmbedding mixedDatum mixedScalars (fun _ => 4) false [false, true] [true, false]
        (Finsupp.single 5 b)) := by
  rw [inductionUnitDotColumn_apply, inductionUnitDotSign_eq]
  norm_num [mixedDatum]

example (i : Bool) (f : ℕ →₀ Coeff) :
    unitDotPolynomialMap mixedDatum mixedScalars (fun _ => 4) i [false, true] [true, false] f =
    canonicalAppendTarget mixedDatum mixedScalars (fun _ => 4) i [false, true] ([true, false] ++ [i])
      (appendOutputEmbedding mixedDatum mixedScalars (fun _ => 4) i [false, true] [true, false] f) :=
  LinearMap.congr_fun (unitDotPolynomialMap_eq mixedDatum mixedScalars (fun _ => 4) i
    [false, true] [true, false]) f

example (i : Bool) (n : ℕ) (b : Coeff) :
    inductionUnitDotColumn mixedDatum mixedScalars (fun _ => 4) i [false, true] [true, false] n b =
      OldInductionRepresentable.upperHomEquiv mixedDatum mixedScalars (fun _ => 4) i
        (⟨[false, true]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 4))
        (⟨[true, false]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 4))
        ((actualInductionDot mixedDatum mixedScalars (fun _ => 4) i
          (oldRepresentable mixedDatum mixedScalars (fun _ => 4)
            (⟨[false, true]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 4)))
          ((append mixedDatum mixedScalars (fun _ => 4) i).obj
            (⟨[true, false]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 4))))^[n]
          (((BalancedInduction.adjunctionUnit (append mixedDatum mixedScalars (fun _ => 4) i)).app
            (oldRepresentable mixedDatum mixedScalars (fun _ => 4)
              (⟨[false, true]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 4)))).total
            (⟨[true, false]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 4)) b)) :=
  inductionUnitDotColumn_categorical mixedDatum mixedScalars (fun _ => 4) i
    [false, true] [true, false] n b

end UnitDotColumnsConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVUnitDotColumns
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner"
  for name in names do
    for ax in (← Lean.collectAxioms name) do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited ALL {names.size} owned declarations including private/generated"
