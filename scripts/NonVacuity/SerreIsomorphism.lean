import NonVacuity.SerreClass
import OddMath.QuiverHecke.SerreIsomorphism

/-! # BE2 Proposition 11.2, the isomorphism, on a rank-two datum

The datum, scalars and symmetrizer of `scripts/NonVacuity/SerreClass.lean` (type `B₂`, `true`
odd, `d_{true,false} = 2`, `d_{false,true} = 1`). Both orders of the two colours are exercised,
and the parity shifts are evaluated.
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.SerreComplex NonVacuity.SerreClass

namespace NonVacuity.SerreIsomorphism

/-- `i` odd, `j` even, `M = 3`: `P(i^{(3)} j) ⊕ Π P(i^{(1)} j i^{(2)}) ≅
P(i^{(2)} j i^{(1)}) ⊕ Π P(j i^{(3)})`, with the shifts of BE2. -/
example : Nonempty ((⨁ fun r : SplitComplex.terms 3 true =>
      term symmetrizer homogeneous true false 3 (3 - r.1)) ≅
    ⨁ fun r : SplitComplex.terms 3 false =>
      term symmetrizer homogeneous true false 3 (3 - r.1)) :=
  nonempty_iso_even_odd symmetrizer homogeneous (by decide) (by rw [dn_true_false])

/-- `i` even, `M = 2`. -/
example : Nonempty ((⨁ fun r : SplitComplex.terms 2 true =>
      term symmetrizer homogeneous false true 2 (2 - r.1)) ≅
    ⨁ fun r : SplitComplex.terms 2 false =>
      term symmetrizer homogeneous false true 2 (2 - r.1)) :=
  nonempty_iso_even_odd symmetrizer homogeneous (by decide) (by rw [dn_false_true])

/-- The parity shifts for `i` odd and `M = 3`: `r = 2` gives `|i| = 1`, `r = 1` gives
`|i||j| = 0`, `r = 3` gives `|i| + |i||j| = 1`. -/
example : par datum true false 3 (3 - 2 * 1) = 1 ∧ par datum true false 3 (3 - (2 * 0 + 1)) = 0 ∧
    par datum true false 3 (3 - (2 * 1 + 1)) = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [par_sub_two_mul (by omega)]; simp [datum]
  · rw [par_sub_two_mul_add_one (by omega)]; simp [datum]
  · rw [par_sub_two_mul_add_one (by omega)]; simp [datum]

#print axioms OddMath.QuiverHecke.SerreComplex.nonempty_iso_even_odd
#print axioms OddMath.QuiverHecke.SplitComplex.IsSplitK.nonempty_revSum_iso

end NonVacuity.SerreIsomorphism
