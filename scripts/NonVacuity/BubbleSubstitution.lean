import OddMath.SKM.BubbleSubstitution
import OddMath.QuiverHecke.SwappedVacuumRecovery
import Lean.Util.CollectAxioms

noncomputable section
open OddMath.QuiverHecke OddMath.SKM
open scoped Classical

private def oddDatum : Datum Bool (Bool → ℤ) where
  cd :=
    { root := fun j i => if i = j then 2 else 0
      coroot := fun i => LinearMap.proj i
      coroot_root_self := fun i => by simp }
  isGCM :=
    { diag := fun i => by simp [CartanDatum.cartanMatrix_apply]
      offDiag_nonpos := fun i j h => by simp [CartanDatum.cartanMatrix_apply, h]
      zero_comm := fun i j => by simp [CartanDatum.cartanMatrix_apply, eq_comm] }
  parity := fun i => if i then 1 else 0
  even_of_odd := by
    intro i j _
    change Even (if i = j then (2 : ℤ) else 0)
    split <;> simp

/-- The vacuum substitution at one odd and one even colour preserves the
coefficient-weight filtration, in both directions. -/
example (M N : Bool → ℕ) :
    PreservesCoefficientWeight oddDatum (SYM.probeSubstitution oddDatum ℚ M N).toLinearMap ∧
      PreservesCoefficientWeight oddDatum
        (SYM.probeSubstitution oddDatum ℚ M N).symm.toLinearMap :=
  ⟨fun n _ hx => SYM.probeSubstitution_mem_coefficientAtMost oddDatum ℚ M N n hx,
    fun n _ hx => SYM.probeSubstitution_symm_mem_coefficientAtMost oddDatum ℚ M N n hx⟩

/-- On the odd generator the substitution is the stated sign. -/
example (M N : Bool → ℕ) :
    SYM.probeSubstitution oddDatum ℚ M N (SYM.delta oddDatum ℚ ⟨true, rfl⟩) =
      (-1 : ℚ) ^ (N true + 1) • SYM.delta oddDatum ℚ ⟨true, rfl⟩ := by
  rw [SYM.probeSubstitution, SYM.substitutionEquiv_apply, SYM.substitutionHom_delta,
    SYM.probeSign]

#print axioms SYM.substitutionEquiv
#print axioms SYM.preservesWeight_of_generators
#print axioms SYM.probeSubstitution_mem_coefficientAtMost

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for i in [:env.header.moduleNames.size] do
    if env.header.moduleNames[i]! == `OddMath.SKM.BubbleSubstitution then
      for name in env.header.moduleData[i]!.constNames do
        for axiomName in ← Lean.collectAxioms name do
          unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
            throwError "Disallowed axiom {axiomName} in {name}"
        count := count + 1
  if count == 0 then throwError "No owned declarations found"
  logInfo m!"Audited {count} owned declarations: standard axioms only"
