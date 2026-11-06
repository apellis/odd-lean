import OddMath.QuiverHecke.IntegralNondegeneracy
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

/-!
Non-vacuity of the Nondegeneracy Conjecture for the integral form: a mixed even/odd datum with
homogeneous parameters over `ZMod 2`, where `2` is not a unit, with every hypothesis proved.
-/

noncomputable section
open OddMath OddMath.SKM OddMath.QuiverHecke
namespace IntegralNondegeneracyConsumer
private abbrev D := ELVOld.WeightedAppendFixture.datum

private def sy : Symmetrizer D where
  d := fun i => if i then 1 else 2
  pos := by intro i; cases i <;> norm_num
  symm := by intro i j; cases i <;> cases j <;> rfl

/-- Integral parameters over `ZMod 2`: some colour is odd, and `2 = 0`. -/
private def Sc : IntegralScalars D (ZMod 2) where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := fun _ => trivial

private theorem hc : Sc.Homogeneous := by
  intro _ _ _ _ _ _ _ _ h
  exact (h rfl).elim

private def bubbles : CScalars Sc where
  c := fun _ _ => 1
  shift := fun _ _ _ => by simp [Sc]

/-- The datum has an odd colour and `2` is not a unit in `ZMod 2`. -/
example : (∃ i, D.parity i = 1) ∧ ¬ IsUnit (2 : ZMod 2) :=
  ⟨⟨true, rfl⟩, by decide⟩

/-- The Nondegeneracy Conjecture for the integral form over `ZMod 2`, with every hypothesis
proved. -/
example : NondegeneracyConjecture bubbles :=
  integral_nondegeneracy_of_symmetrizer sy hc bubbles

#print axioms integral_nondegeneracy_of_symmetrizer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for i in [:env.header.moduleNames.size] do
    let m := env.header.moduleNames[i]!
    if m == `OddMath.QuiverHecke.IntegralNondegeneracy || m == `OddMath.SKM.IntegralNondegeneracy ||
        m == `OddMath.SKM.IntegralParameters then
      for name in env.header.moduleData[i]!.constNames do
        for axiomName in ← Lean.collectAxioms name do
          unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
            throwError "Disallowed axiom {axiomName} in {name}"
        count := count + 1
  if count == 0 then throwError "No owned declarations found"
  logInfo m!"Audited {count} owned declarations: standard axioms only"

end IntegralNondegeneracyConsumer
