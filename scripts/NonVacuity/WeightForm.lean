import OddMath

/-! Non-vacuity checks in `NonVacuity.WeightForm`.
Conventions are in `scripts/NonVacuity.lean`. -/

noncomputable section

namespace NonVacuity.WeightForm

open OddMath.CoveringQuantum
open OddMath.CoveringQuantum.UDot
open OddMath.CoveringQuantum.SourceWeightLatticeConsumer
open OddMath.CoveringQuantum.FiniteWeightFormConsumer

local instance : DecidableEq lattice := Classical.decEq _
local instance : DecidableEq (FiniteWeightDuality.coweight lattice →+ ℤ) := Classical.decEq _

/-- Form transport on the finite window of the infinite-colour complex fixture. -/
example (x y : modified restrictedDatum Coefficients.q Coefficients.pi) :
    GenericTensor.sesquilinearForm (FiniteWeightDuality.dualDatum restrictedDatum)
      (FiniteWeightAlgebra.modifiedEquiv restrictedDatum Coefficients.q Coefficients.pi x)
      (FiniteWeightAlgebra.modifiedEquiv restrictedDatum Coefficients.q Coefficients.pi y) =
        GenericTensor.sesquilinearForm restrictedDatum x y :=
  FiniteWeightForm.sesquilinearForm_modifiedEquiv restrictedDatum x y

open scoped Classical in
/-- Nondegeneracy for one odd colour on the weight lattice `ℤ`, with every
hypothesis discharged. -/
example (x : modified oddDatum Coefficients.q Coefficients.pi)
    (hx : ∀ y, GenericTensor.sesquilinearForm oddDatum x y = 0) : x = 0 :=
  FiniteWeightForm.sesquilinearForm_nondegenerate oddDatum
    odd_root_independent odd_coroot_independent x hx

end NonVacuity.WeightForm
