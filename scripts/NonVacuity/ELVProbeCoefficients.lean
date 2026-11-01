import OddMath.QuiverHecke.CyclotomicAction.ELVProbeCoefficients
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams OddMath OddMath.QuiverHecke OddMath.SKM.SYM
namespace ELVProbeCoefficientsConsumer
private def D : SKM.Datum Bool (Bool → ℤ) where
  cd :=
    { root := fun i j => if i = j then 2 else 0
      coroot := fun i => LinearMap.proj i
      coroot_root_self := fun i => by simp }
  isGCM :=
    { diag := fun i => by simp [CartanDatum.cartanMatrix_apply]
      offDiag_nonpos := fun i j h => by
        simp [CartanDatum.cartanMatrix_apply, Ne.symm h]
      zero_comm := fun i j => by
        by_cases h : i = j
        · subst j
          simp [CartanDatum.cartanMatrix_apply]
        · simp [CartanDatum.cartanMatrix_apply, h, Ne.symm h] }
  parity := fun i => if i then 0 else 1
  even_of_odd := by
    intro i j _
    change Even (if j = i then (2 : ℤ) else 0)
    split_ifs <;> norm_num

private def Sc : SKM.Scalars D ℚ where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := fun _ => (by norm_num : (2 : ℚ) ≠ 0).isUnit

private def m : Bool → ℕ := fun i => if i then 5 else 3

example : scalarCoefficientPolynomial D (probeScalarValues D m) 6
    (elvMonicCoefficient D ℚ ⟨false,rfl⟩ 6) = (Polynomial.X^2 - 1)^3 :=
  scalarCoefficientPolynomial_probe_odd D m ⟨false,rfl⟩

example : scalarCoefficientPolynomial D (probeScalarValues D m) 5
    (evenMonicCoefficient D ℚ true 5) = (Polynomial.X - 1)^5 :=
  scalarCoefficientPolynomial_probe_even D m true rfl

example :
    (elvProbeAffineSpecialization D m Sc).map
      (elvQuotientMap D Sc (probeCutoff D m) _ _
        (coefficientDotPolynomial D Sc [false,true] 0 (probeCutoff D m false)
          (probeMonicCoefficient D m false))) =
      Polynomial.aeval (dotE D Sc [false,true] 0)
        (probePolynomial (k := ℚ) (probeDotExponent D) m false) :=
  elvProbeAffineSpecialization_dotPolynomial D m Sc false [false,true] 0

end ELVProbeCoefficientsConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVProbeCoefficients
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing owned module {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited {names.size} declarations in {owner}."
