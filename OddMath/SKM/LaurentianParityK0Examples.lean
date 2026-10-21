/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.LaurentianParityK0
import OddMath.SKM.LaurentianK0Examples

/-!
# Consumers of the corrected BE2 §11 mixed decomposition

The two-odd-colour rational SKM datum discharges the hypotheses on completed
Hom categories. The Clifford envelope has nonzero decomposition coordinates
and a nonempty type-Q orbit set, as required by ERRATA [BE2] 10.
-/

noncomputable section
namespace OddMath.SKM.LaurentianParityK0Examples
open CategoryTheory StringDiagrams
open CoveringQuantum.UDot.ContextualExchangeExamples DimensionFormulaExamples

/-- Mixed type-M/type-Q coordinates for the concrete completed SKM homs. -/
def decomposition (a b : LaurentianK0Examples.B) :=
  UDot.laurentDecomposition twoOddDatum.skmSymmetrizer cScalars homogeneous locallyFinite a b

/-- The rational Clifford regular object has nonzero mixed coordinates. -/
theorem clifford_coordinates_ne_zero :
    (CliffordK0.laurentDecomposition ℚ).symm (K₀.mk (CliffordK0.gradedRegular ℚ)) ≠ 0 :=
  CliffordK0.laurent_coordinates_ne_zero ℚ

/-- The quotient summands in the mixed decomposition cannot be discarded. -/
theorem clifford_typeQ_nonempty :
    Nonempty (CoveringLaurent.FixedRep
      (KrullSchmidt.laurentParity ℚ (C := CliffordK0.GradedProjectives ℚ))) :=
  CliffordK0.typeQ_orbits_nonempty ℚ

#print axioms decomposition
#print axioms clifford_coordinates_ne_zero
#print axioms clifford_typeQ_nonempty
end OddMath.SKM.LaurentianParityK0Examples
