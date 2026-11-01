import OddMath.QuiverHecke.CyclotomicAction.ProbePolynomialParity
import OddMath.QuiverHecke.CyclotomicAction.SuperDot
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams
open OddMath.QuiverHecke
namespace OddMath.QuiverHecke.ProbePolynomialParityExamples
private abbrev D := CyclotomicAction.AsymmetricParameters.datum
private abbrev Sc := CyclotomicAction.AsymmetricParameters.scalars
private abbrev a : Bool → Polynomial ℚ :=
  probePolynomial (probeDotExponent D) (fun _ => 3)
private theorem ha : CyclotomicPolynomialParity D a :=
  probePolynomial_parity D (fun _ => 3)

/-- The actual odd probe now has a closed superinduction-dot construction. -/
example :
    inductionSuperDot D Sc false a ha 2 ∈ Supercategory.parity (R := ℚ)
      (inductionCorner D Sc false a ha 2) (inductionCorner D Sc false a ha 2) 1 := by
  exact inductionSuperDot_parity D Sc false a ha 2

example : (a false).coeff 1 = 0 := by
  by_contra h
  have hd := probePolynomial_support_dvd (k := ℚ) (probeDotExponent D)
    (fun _ => 3) false (by decide) h
  have he : probeDotExponent D false = 2 := rfl
  rw [he] at hd
  exact (by decide : ¬ (2 ∣ (1 : ℕ))) hd

example : CyclotomicPolynomialParity (k := ℚ) D
    (probePolynomial (probeDotExponent D) (fun _ => 0)) :=
  probePolynomial_parity D (fun _ => 0)
end OddMath.QuiverHecke.ProbePolynomialParityExamples

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ProbePolynomialParity
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"
