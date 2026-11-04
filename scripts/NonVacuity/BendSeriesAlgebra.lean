import OddMath.QuiverHecke.SwappedAssembly.Sigma.BendSeriesAlgebra
import Mathlib.Data.Matrix.Notation
import Lean.Util.CollectAxioms

open OddMath.QuiverHecke.SwappedAssembly
namespace NonVacuity.BendSeriesAlgebra
private abbrev A := Matrix (Fin 2) (Fin 2) ℚ
private def x : A := !![0, 1; 1, 0]
private def y : A := !![0, 1; 0, 0]
private theorem xx : x*x = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [x, Matrix.mul_apply, Fin.sum_univ_two]
private def xu : Aˣ := ⟨x, x, xx, xx⟩
private theorem hx : IsUnit x := xu.isUnit

-- The two dots used in these arithmetic tests do not commute.
example : x*y ≠ y*x := by
  intro h
  have h₀ := congrArg (fun a : A => a 0 0) h
  norm_num [x, y, Matrix.mul_apply, Fin.sum_univ_two] at h₀

example : Ring.inverse x = x := bend_inverse_eq hx xx
example := bend_map_inverse (RingHom.id A) hx
example := bend_inverse_neg hx
example (r : ℕ) := bend_neg_monomial x y r
example (r : ℕ) := bend_inverse_neg_monomial hx y r
example (r : ℕ) := bendInsertion_alternating (AddMonoidHom.id A) r y
example (n : ℕ) := bend_odd_probe_series (AddMonoidHom.id A) (fun r => x^(r+1)*y^r) n
example (n : ℕ) := bend_odd_reservoir_series (AddMonoidHom.id A) (fun r => x^(r+1)*y^r) n
end NonVacuity.BendSeriesAlgebra

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.SwappedAssembly.Sigma.BendSeriesAlgebra
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned declarations"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"
