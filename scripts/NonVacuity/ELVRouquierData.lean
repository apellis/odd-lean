import OddMath.QuiverHecke.CyclotomicAction.ELVRouquierData
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import OddMath.QuiverHecke.CyclotomicAction.ELVVacuumRepresentable
import Lean.Util.CollectAxioms

noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELVRouquierDataExamples

private def D : SKM.Datum Bool (Bool → ℤ) :=
  { AsymmetricParameters.datum with
    parity := fun i => if i then 1 else 0
    even_of_odd := fun i j _ => AsymmetricParameters.datum.even_of_odd i j rfl }
private def Sc : SKM.Scalars D ℚ where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := by intro _; norm_num
private abbrev X := Bool → ℤ
private theorem step (i : Bool) : (0 : X) + D.α i = D.α i := zero_add _
private theorem step₂ (i j : Bool) : D.α j + D.α i = D.α j + D.α i := rfl
private theorem step₄ (i j : Bool) : D.α i + D.α j = D.α j + D.α i := add_comm _ _
private abbrev R := elvRouquierData D (parameterTwist D Sc) (fun _ => 12) 12 (0 : X)

/-- The native square field is instantiated on both repeated parities in
actual PiSCat weight categories. -/
example (i : Bool) := elvRouquierData_square
  D (parameterTwist D Sc) (fun _ => 12) 12 i (0 : X) (step i) (step₂ i i)

/-- The bundle retains the prescribed degrees of both mixed crossing orders. -/
example (i j : Bool) : R.cross i j (step j) (step₂ i j) (step i) (step₄ i j) ∈
    parity (R := ℚ) _ _ (D.parity i * D.parity j) :=
  R.cross_mem i j (step j) (step₂ i j) (step i) (step₄ i j)

example (i : Bool) : R.dot i (step i) ∈ parity (R := ℚ) _ _ (D.parity i) :=
  R.dot_mem i (step i)

/-- The already chosen right adjunction uses exactly the bundled E field. -/
example (i : Bool) : SKM.SuperAdjunction (k := ℚ) (R.E i (step i))
    (elvF D (parameterTwist D Sc) (fun _ => 12) 12 i (0 : X) (step i)) :=
  elvActionAdjunction D (parameterTwist D Sc) (fun _ => 12) 12 i (0 : X) (step i)

end OddMath.QuiverHecke.ELVRouquierDataExamples

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVRouquierData
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owned module"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"
