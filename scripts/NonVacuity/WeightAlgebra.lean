import OddMath

/-! Non-vacuity checks in `NonVacuity.WeightAlgebra`.
Conventions are in `scripts/NonVacuity.lean`. -/

open CategoryTheory

noncomputable section

namespace NonVacuity.WeightAlgebra

open OddMath.CoveringQuantum.UDot
open OddMath.CoveringQuantum.SourceWeightLatticeConsumer
open OddMath.CoveringQuantum.FiniteWeightAlgebraConsumer

local instance : DecidableEq lattice := Classical.decEq _

example : Function.Bijective (transport (1 : ℤˣ) (1 : ℤ)) :=
  (transport (1 : ℤˣ) (1 : ℤ)).bijective

example (x y : A (1 : ℤˣ) (1 : ℤ)) :
    transport (1 : ℤˣ) (1 : ℤ) (x * y) = transport 1 1 x * transport 1 1 y :=
  transport_mul 1 1 x y

example (i : colours) :
    (transport (1 : ℤˣ) (1 : ℤ)).symm
      (transport (1 : ℤˣ) (1 : ℤ) ⟨E restrictedDatum (1 : ℤˣ) (1 : ℤ) i centralInWindow,
        E_mem_modified restrictedDatum (1 : ℤˣ) (1 : ℤ) i centralInWindow⟩) =
      ⟨E restrictedDatum (1 : ℤˣ) (1 : ℤ) i centralInWindow,
        E_mem_modified restrictedDatum (1 : ℤˣ) (1 : ℤ) i centralInWindow⟩ :=
  centralInWindow_E_roundtrip (1 : ℤˣ) (1 : ℤ) i

example (i : colours) :
    (transport (1 : ℤˣ) (1 : ℤ)).symm
      (transport (1 : ℤˣ) (1 : ℤ) ⟨F restrictedDatum (1 : ℤˣ) (1 : ℤ) i seedInWindow,
        F_mem_modified restrictedDatum (1 : ℤˣ) (1 : ℤ) i seedInWindow⟩) =
      ⟨F restrictedDatum (1 : ℤˣ) (1 : ℤ) i seedInWindow,
        F_mem_modified restrictedDatum (1 : ℤˣ) (1 : ℤ) i seedInWindow⟩ :=
  seedInWindow_F_roundtrip (1 : ℤˣ) (1 : ℤ) i

end NonVacuity.WeightAlgebra
