import OddMath.QuiverHecke.CyclotomicAction.ELVEvenSRightProduct
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
open scoped TensorProduct
namespace EvenSRightProductConsumer
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

/-- The top coefficient retains an arbitrary full old class at mixed data. -/
example (b : Old mixedDatum mixedScalars (fun _ => 4) [false, true] [false, true]) :
    independentSRightProduct mixedDatum mixedScalars (fun _ => 4) false [false, true]
      (Finsupp.single 2 b) (2 + outputSDegree mixedDatum false [false, true]) = b := by
  have hb : ∀ n, 2 < n →
      (Finsupp.single 2 b : ℕ →₀ Old mixedDatum mixedScalars (fun _ => 4) [false, true] [false, true]) n = 0 := by
    intro n hn
    exact Finsupp.single_eq_of_ne (by omega)
  simpa only [Finsupp.single_eq_same] using
    independentSRightProduct_even_top mixedDatum mixedScalars (fun _ => 4)
      false rfl [false, true] (Finsupp.single 2 b) 2 hb

example (b : Old mixedDatum mixedScalars (fun _ => 4) [false, true] [false, true]) :
    independentSRightProduct mixedDatum mixedScalars (fun _ => 4) false [false, true]
      (Finsupp.single 2 b) =
    ∑ n ∈ (independentOutputS mixedDatum mixedScalars (fun _ => 4) false [false, true]).support,
      Finsupp.single (n + 2) (oldComp mixedDatum mixedScalars (fun _ => 4)
        [false, true] [false, true] [false, true] b
        (independentOutputS mixedDatum mixedScalars (fun _ => 4) false [false, true] n)) :=
  independentSRightProduct_even_single mixedDatum mixedScalars (fun _ => 4)
    false rfl [false, true] 2 b

example (f : ℕ →₀ Old mixedDatum mixedScalars (fun _ => 4) [false, true] [false, true]) :
    f = f ∧ (0 : ℕ →₀ Old mixedDatum mixedScalars (fun _ => 4) [false, true] [false, true]) = 0 :=
  independentS_even_division_unique mixedDatum mixedScalars (fun _ => 4)
    false rfl [false, true] f f 0 0 (by simp) (by simp) rfl
end EvenSRightProductConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVEvenSRightProduct
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Module was not imported"
  let names := env.header.moduleData[idx]!.constNames
  unless names.size > 0 do throwError "Empty declaration inventory"
  for name in names do
    for axiomName in (← Lean.collectAxioms name) do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
  logInfo m!"Audited ALL {names.size} owned declarations including private/generated"

