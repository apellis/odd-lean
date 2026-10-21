import OddMath

/-! Non-vacuity checks in `NonVacuity.WeightDuality`.
Conventions are in `scripts/NonVacuity.lean`. -/

open CategoryTheory

noncomputable section

namespace NonVacuity.WeightDuality

open OddMath.CoveringQuantum.SourceWeightLatticeConsumer
open OddMath.CoveringQuantum.FiniteWeightDualityConsumer

example (x : lattice) : e.symm (e x) = x := roundtrip x
example (μ : Y →+ ℤ) : e (e.symm μ) = μ := roundtrip_dual μ
example : e centralInWindow ≠ 0 := central_survives
example : ∃ y : Y, e centralInWindow y ≠ 0 := central_detected
example (i : colours) :
    (restrictedDatum.toSuperCartanDatum.rootDatumOf R).h i (e centralInWindow) = 0 :=
  central_pairing i
example : e.symm (e seedInWindow) = seedInWindow := seed_roundtrip
example : LinearIndependent ℤ (restrictedDatum.toSuperCartanDatum.rootDatumOf R).α :=
  OddMath.CoveringQuantum.FiniteWeightDualityConsumer.roots_independent
example : LinearIndependent ℤ R.coroot :=
  OddMath.CoveringQuantum.FiniteWeightDualityConsumer.coroots_independent

end NonVacuity.WeightDuality
