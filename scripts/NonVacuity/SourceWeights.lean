import OddMath

/-! Non-vacuity checks in `NonVacuity.SourceWeights`.
Conventions are in `scripts/NonVacuity.lean`. -/

open CategoryTheory

noncomputable section

namespace NonVacuity.SourceWeights

open OddMath.CoveringQuantum.SourceWeightLatticeConsumer

example : Module.Finite ℤ lattice := inferInstance
example : Module.Free ℤ lattice := inferInstance
example : LinearIndependent ℤ restrictedDatum.cd.coroot :=
  OddMath.CoveringQuantum.SourceWeightLattice.window_coroot_linearIndependent
    h cartan alpha cartan_eval coroots_independent colours weights
example : LinearIndependent ℤ restrictedDatum.α :=
  OddMath.CoveringQuantum.SourceWeightLattice.window_root_linearIndependent
    h cartan alpha cartan_eval coroots_independent colours weights roots_independent
example : Set.Infinite
    (Function.support (fun i ↦ OddMath.CoveringQuantum.SourceWeightLattice.coroot h i seed)) :=
  seed_support_infinite
example : centralInWindow ≠ 0 := central_nonzero
example (i : ℕ) :
    OddMath.CoveringQuantum.SourceWeightLattice.coroot h i (centralInWindow : P) = 0 :=
  central_coroot_zero i

end NonVacuity.SourceWeights
