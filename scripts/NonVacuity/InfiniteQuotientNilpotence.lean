import OddMath

/-! Non-vacuity checks in `NonVacuity.InfiniteQuotientNilpotence`.
Conventions are in `scripts/NonVacuity.lean`. -/

open CategoryTheory

noncomputable section

namespace NonVacuity.InfiniteQuotientNilpotence

open OddMath.CoveringQuantum.UDot
open GenericVerma VermaWeightExamples IntegrableQuotientExamples

example : toIntegrable datum highestWeight 1 ≠ 0 :=
  toIntegrable_one_ne_zero datum highestWeight dominant

example :
    (∃ n : ℕ, (integrableChevalley datum highestWeight false 0 ^ n)
      (toIntegrable datum highestWeight representative) = 0) ∧
    (∃ n : ℕ, (integrableChevalley datum highestWeight true 1 ^ n)
      (toIntegrable datum highestWeight representative) = 0) :=
  ⟨integrableChevalley_false_locally_nilpotent datum highestWeight _ 0,
    NativeLeading.integrableChevalley_true_locally_nilpotent datum highestWeight _ 1⟩

end NonVacuity.InfiniteQuotientNilpotence
