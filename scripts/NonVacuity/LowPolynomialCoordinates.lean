import OddMath.Algebra.LowPolynomialCoordinates
import Lean.Util.CollectAxioms
noncomputable section
open OddMath.LowPolynomialCoordinates

example (b : ℤ) :
    ((lowVectorEquiv (k := ℤ) (M := ℤ) 3 (Pi.single (1 : Fin 3) b)) : ℕ →₀ ℤ) =
      Finsupp.single 1 b := lowVectorEquiv_single 3 1 b

example (f : Fin 3 → ℤ) :
    (lowVectorEquiv (k := ℤ) (M := ℤ) 3).symm
      (lowVectorEquiv (k := ℤ) (M := ℤ) 3 f) = f := LinearEquiv.symm_apply_apply _ f

example (b : ℤ) :
    reversedVector (k := ℤ) 3 (Pi.single (1 : Fin 3) b) = Pi.single (1 : Fin 3).rev b :=
  reversedVector_single 3 1 b

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.Algebra.LowPolynomialCoordinates
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner"
  for name in names do
    for ax in (← Lean.collectAxioms name) do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited ALL {names.size} owned declarations including private/generated"
