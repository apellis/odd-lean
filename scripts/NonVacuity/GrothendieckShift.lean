import OddMath

/-! # The Grothendieck ring has no `ℤ[q, q⁻¹]`-torsion, on a concrete datum

The two-odd-colour rational datum of `OddMath.SKM.LaurentianK0Examples`, where every hypothesis
of `SKM.UDot.int_smul_eq_zero` is proved, with the nonzero Laurent polynomial `q + 1`.
-/

noncomputable section
namespace NonVacuity.GrothendieckShift
open CategoryTheory StringDiagrams LaurentPolynomial OddMath.SKM
open LaurentianK0Examples OddMath.CoveringQuantum.UDot.ContextualExchangeExamples
open OddMath.SKM.DimensionFormulaExamples

theorem q_add_one_ne_zero : (T 1 + 1 : LaurentPolynomial ℤ) ≠ 0 := by
  intro h
  have := congrArg (LaurentPolynomial.eval₂ (RingHom.id ℤ) (1 : ℤˣ)) h
  simp at this

example (x : K₀Ring (UDot twoOddDatum.toSKM scalars twoOddDatum.skmSymmetrizer homogeneous))
    (h : (letI := GSKAR.moduleLaurent ℚ B
      AddMonoidAlgebra.mapRingHom ℤ (Int.castRingHom Zπ) (T 1 + 1) • x) = 0) : x = 0 :=
  UDot.int_smul_eq_zero twoOddDatum.skmSymmetrizer cScalars homogeneous locallyFinite _
    q_add_one_ne_zero x h

#print axioms OddMath.SKM.UDot.int_smul_eq_zero
#print axioms OddMath.GrothendieckShift.laurentEnd_int_eq

end NonVacuity.GrothendieckShift
