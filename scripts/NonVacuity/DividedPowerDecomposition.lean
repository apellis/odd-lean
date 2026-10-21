import OddMath

open OddMath.SKM.DividedPowerDecomposition
open OddMath.Frontier

example (x : NilHeckeAction.Presented 2) :
    (oddDecomposition 2).symm (oddDecomposition 2 x) = x :=
  (oddDecomposition 2).symm_apply_apply x

example : ∑ ℓ, summand 1 ℓ = 1 := sum_summand 1

example : Fintype.card (BoxPartitionCount.Sq 4) = 24 := by
  rw [summand_count]
  norm_num

#print axioms Examples.even_twoStrand_coefficient
#print axioms normalized_degree
#print axioms multiplicity_degree
#print axioms oppositeProjector_primitive
#print axioms oddDecompositionMap
#print axioms oddDecomposition_symm_parity
#print axioms oddDecompositionAll
#print axioms summand_mul
#print axioms oddDecomposition_degree
#print axioms oddDecomposition_symm_degree
#print axioms oddDecomposition_parity
#print axioms sum_multiplicity
#print axioms complement_eq_shift
