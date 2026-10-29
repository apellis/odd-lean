import OddMath.QuiverHecke.CyclotomicAction.ELVOldPolynomialTransport

noncomputable section
namespace ELVOldTransportConsumer
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

example := oldPolynomial_move datum scalars (fun _ => 3) () oddColour [(), ()]
example := projection_move_oldPolynomial datum scalars (fun _ => 3) () oddColour
  [(), ()] [(), (), (), ()] (𝟙 _)
example := projection_move_oldPolynomial datum scalars (fun _ => 2) () oddColour
  [] [(), ()] (𝟙 _)
example := projection_move_oldPolynomial datum scalars (fun _ => 0) () oddColour
  [] [(), ()] (𝟙 _)
#print axioms oldPolynomial_move
#print axioms projection_move_oldPolynomial
end ELVOldTransportConsumer
