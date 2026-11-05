import OddMath.QuiverHecke.VacuumRouteSwappedRightNegative
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open OddMath OddMath.SKM OddMath.QuiverHecke
namespace SwappedRouteNondegeneracyConsumer
private abbrev D := ELVOld.WeightedAppendFixture.datum
private abbrev Sc := ELVOld.WeightedAppendFixture.scalars
private def sy : Symmetrizer D where
  d := fun i => if i then 1 else 2
  pos := by intro i; cases i <;> norm_num
  symm := by intro i j; cases i <;> cases j <;> rfl
private theorem hc : Sc.Homogeneous := by
  intro _ _ _ _ _ _ _ _ h
  exact (h rfl).elim
private def bubbles : CScalars Sc where
  c := fun _ _ => 1
  shift := fun _ _ _ => by simp [Sc, ELVOld.WeightedAppendFixture.scalars]

/-- The Nondegeneracy Conjecture for a mixed even/odd datum with homogeneous scalars over `ℚ`,
with every hypothesis proved. -/
example : NondegeneracyConjecture bubbles :=
  nondegeneracy_of_symmetrizer sy (by norm_num) hc bubbles

#print axioms nondegeneracy_of_symmetrizer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for i in [:env.header.moduleNames.size] do
    if env.header.moduleNames[i]! == `OddMath.QuiverHecke.VacuumRouteSwappedRightNegative then
      for name in env.header.moduleData[i]!.constNames do
        for axiomName in ← Lean.collectAxioms name do
          unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
            throwError "Disallowed axiom {axiomName} in {name}"
        count := count + 1
  if count == 0 then throwError "No owned declarations found"
  logInfo m!"Audited {count} owned declarations: standard axioms only"

end SwappedRouteNondegeneracyConsumer
