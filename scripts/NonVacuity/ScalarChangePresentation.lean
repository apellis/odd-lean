import OddMath.SKM.ScalarChangeExamples

/-! Brundan–Ellis Definition 1.5: the presented Hom coefficient map on two
odd colours over the noninjective specialization `ZMod 9 → ZMod 3`.
The datum and all admissibility proofs are constructed in the imported module. -/

open OddMath.SKM OddMath.SKM.ScalarChangeExamples

example := target_two_isUnit
example := target_bubble_shift (0 : Bool → ℤ) false true
example := specialization_kills_nonzero
example := odd_dot_specializes (0 : Bool → ℤ) false
example := three_times_odd_dot_specializes_to_zero (0 : Bool → ℤ) true
example := odd_relation_specializes (.quadEq false 0)
example := odd_relation_specializes (.invP₁ false 0 (by decide))
example := odd_relation_specializes (.invM₁ true 0 (by decide))
example := mixed_inverse_specializes (0 : Bool → ℤ)
example := odd_left_adjunction_specializes (0 : Bool → ℤ) false
example := odd_left_adjunction_specializes (fun _ => 1) true
example := odd_left_adjunction_specializes (fun _ => -1) false
example := odd_identity_specializes (0 : Bool → ℤ)
