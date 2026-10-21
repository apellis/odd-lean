import OddMath

noncomputable section
namespace NonVacuity.LaurentianParityK0
open CategoryTheory StringDiagrams OddMath.SKM

example (a b : LaurentianK0Examples.B) :=
  LaurentianParityK0Examples.decomposition a b

example : (CliffordK0.laurentDecomposition ℚ).symm
    (K₀.mk (CliffordK0.gradedRegular ℚ)) ≠ 0 :=
  LaurentianParityK0Examples.clifford_coordinates_ne_zero

example : Nonempty (CoveringLaurent.FixedRep
    (KrullSchmidt.laurentParity ℚ (C := CliffordK0.GradedProjectives ℚ))) :=
  LaurentianParityK0Examples.clifford_typeQ_nonempty

example (o : KrullSchmidt.ShiftOrbit ℚ (C := CliffordK0.GradedProjectives ℚ)) :
    KrullSchmidt.laurentParity ℚ o = o := CliffordK0.laurentParity_eq_self ℚ o

end NonVacuity.LaurentianParityK0
