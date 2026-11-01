import OddMath.SKM.ELVScalarSpecialization
import Lean.Util.CollectAxioms

noncomputable section
open OddMath OddMath.SKM OddMath.SKM.SYM
namespace ELVScalarSpecializationConsumer

private def D : SKM.Datum Unit ℤ where
  cd :=
    { root := fun _ => 2
      coroot := fun _ => LinearMap.id
      coroot_root_self := fun _ => rfl }
  isGCM :=
    { diag := fun _ => rfl
      offDiag_nonpos := fun i j h => absurd (Subsingleton.elim i j) h
      zero_comm := fun _ _ => Iff.rfl }
  parity := fun _ => 1
  even_of_odd := fun _ _ _ => even_two


private def cutoff : Unit → ℕ := fun _ => 4
private def values : Unit × ℕ → ℚ := fun p => if p.2 = 0 then 3 else 0

private theorem hvalues : ∀ i r, elvElementaryRank D cutoff i ≤ r → values (i,r) = 0 := by
  intro i r hr
  have hr' : 2 ≤ r := by simpa [D, cutoff, elvElementaryRank] using hr
  simp [values, show r ≠ 0 by omega]

example : elvScalarEvaluation D cutoff values hvalues
    (elvCoefficientQuotient D cutoff (e D ℚ () 0)) = 3 := by
  rw [elvScalarEvaluation_quotient, scalarEvaluation_e]
  rfl

example : elvScalarEvaluation D cutoff values hvalues
    (elvCoefficientQuotient D cutoff (delta D ℚ ⟨(), rfl⟩)) = 0 := by
  rw [elvScalarEvaluation_quotient, scalarEvaluation_delta]

/-- A positive-degree elementary coefficient specializes to a nonnilpotent
scalar. Thus this map is not obtained from a positive-weight truncation. -/
example : (elvScalarEvaluation D cutoff values hvalues
    (elvCoefficientQuotient D cutoff (e D ℚ () 0))) ^ 5 ≠ 0 := by
  rw [elvScalarEvaluation_quotient, scalarEvaluation_e]
  norm_num [values]

end ELVScalarSpecializationConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.SKM.ELVScalarSpecialization
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing owned module {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited {names.size} declarations in {owner}."
