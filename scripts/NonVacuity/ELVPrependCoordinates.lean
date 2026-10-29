import OddMath.QuiverHecke.CyclotomicAction.ELVPrependCoordinates

noncomputable section
namespace ELVPrependConsumer
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open ELVOld
open scoped TensorProduct
open Categorification.TypeA

def datum : SKM.Datum Unit ℤ where
  cd := {
    root := fun _ => 2
    coroot := fun _ => LinearMap.id
    coroot_root_self := fun _ => rfl }
  isGCM := {
    diag := fun _ => rfl
    offDiag_nonpos := fun i j h => absurd (Subsingleton.elim i j) h
    zero_comm := fun _ _ => Iff.rfl }
  parity := fun _ => 1
  even_of_odd := fun _ _ _ => even_two

def scalars : SKM.Scalars datum ℚ where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := fun _ => isUnit_iff_ne_zero.mpr (by norm_num)

def oddColour : {i : Unit // datum.parity i = 1} := ⟨(), rfl⟩

private theorem canWord_one (n : ℕ) : canWord n 1 = [] := by
  apply List.length_eq_zero_iff.mp
  rw [length_canWord, length_one]

/-- One moving odd dot, one old strand, and no moving crossing. -/
def movingIndex : PrependIdx () [()] [(), ()] :=
  ⟨(1, [], 1, ⟨1, isShuffle_one _⟩), by simp, by simp,
    by simp [prependCrossingWord, canWord_one, shiftWord, cw]⟩

example : prependTailParity datum movingIndex = 1 := by
  simp [prependTailParity, movingIndex, PrependIdx.oldTarget, canWord_one, cw,
    pl, PG.ld, Shape.parity, datum]

def delta : SKM.SYM.ELVCoefficientAlgebra (k := ℚ) datum (fun _ => 3) :=
  SKM.SYM.elvCoefficientQuotient datum (fun _ => 3) (SKM.SYM.delta datum ℚ oddColour)

example := prependAffineEquiv datum scalars (fun _ => 3) () [()] [(), ()]
example := prependAffineEquiv_symm_single datum scalars (fun _ => 3) movingIndex (1 + delta)
example := balancedEquiv_prependBalancedTerm datum scalars (fun _ => 3) 1 movingIndex (1 + delta)
example := balancedEquiv_prependExpansion datum scalars (fun _ => 3) 1 () [()] [(), ()]
  (Finsupp.single movingIndex (1 + delta))
example := prependBalancedExpansion_surjective datum scalars (fun _ => 3) 1 () [()] [(), ()]
example := prependBalancedExpansion_eq_zero_iff datum scalars (fun _ => 3) 1 () [()] [(), ()]
  (Finsupp.single movingIndex delta)

#print axioms prependAffineEquiv
#print axioms prepend_insert_twisted_coefficient
#print axioms balancedEquiv_prependExpansion
#print axioms prependBalancedExpansion_surjective
#print axioms prependBalancedExpansion_eq_zero_iff
end ELVPrependConsumer
