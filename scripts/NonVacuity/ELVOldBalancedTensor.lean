import OddMath.QuiverHecke.CyclotomicAction.ELVOldBalancedTensor

noncomputable section
namespace ELVOldBalancedConsumer
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open ELVOld
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

example := balancedEquiv datum scalars (fun _ => 3) 1 () [()] [(), ()]
example := balancedEquiv datum scalars (fun _ => 2) 0 () [()] [(), ()]
example := balancedEquiv datum scalars (fun _ => 0) 1 () [] [()]
example := balancedEquiv_tmul datum scalars (fun _ => 3) 1 ()
  (v := [()]) (t := [()]) (w := [(), ()]) (𝟙 _)
  (relation datum scalars (fun _ => 3) () [])
example := balancedBackward_projection datum scalars (fun _ => 3) 1 ()
  (v := [()]) (w := [(), ()])
  ((elvQuotientFunctor datum scalars (fun _ => 3)).map
    (elvDotPolynomial datum scalars oddColour [(), ()] 0 3))
#print axioms balancedEquiv
#print axioms balancedEquiv_tmul
#print axioms balancedTmul_balance
end ELVOldBalancedConsumer
