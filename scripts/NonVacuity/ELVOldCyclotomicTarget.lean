import OddMath.QuiverHecke.CyclotomicAction.ELVOldCyclotomicTarget

noncomputable section
namespace ELVOldCyclotomicConsumer
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

/-- The old second-position polynomial is killed at positive odd cutoff. -/
example := projection_elvPolynomial datum scalars (fun _ => 3) () oddColour [] [(), ()] (𝟙 _)
example := projection_elvPolynomial datum scalars (fun _ => 2) () oddColour [] [(), ()] (𝟙 _)
example := insert_elvPolynomial datum scalars (fun _ => 3) () oddColour []
example := relation_mem_parity datum scalars (fun _ => 3) () []
example := projection_relation datum scalars (fun _ => 0) () () [] [(), ()] (𝟙 _)
example := pair_id datum scalars (fun _ => 3) 1 () (v := []) (𝟙 _)

/-- The moving polynomial remains a class, not an imposed relation.
Its nonvanishing in this target still requires the right PBW comparison. -/
def movingClass : Target datum scalars (fun _ => 3) () [()] [(), ()] :=
  projection datum scalars (fun _ => 3) () [()] [(), ()]
    ((elvQuotientFunctor datum scalars (fun _ => 3)).map
      (elvDotPolynomial datum scalars oddColour [(), ()] 0 3))

example := pair_balance datum scalars (fun _ => 3) 1 ()
  (v := [()]) (s := [()]) (t := [()]) (w := [(), ()]) (𝟙 _) (𝟙 _) (𝟙 _)
example := pair_balance_homogeneous datum scalars (fun _ => 3) 1 ()
  (v := [()]) (s := [()]) (t := [()]) (w := [(), ()]) (𝟙 _)
  (relation_mem_parity datum scalars (fun _ => 3) () []) (𝟙 _)
example := projection_top datum scalars (fun _ => 2) () [()] [(), ()] oddColour rfl (𝟙 _)
example := oldTwist_twice datum scalars (fun _ => 3) 1 [()] [()] 0
example := act_id datum scalars (fun _ => 3) () movingClass

#print axioms insert_comp
#print axioms projection_old_ideal
#print axioms relation_mem_parity
#print axioms twist_ideal
#print axioms pair_balance
#print axioms pair_balance_homogeneous
#print axioms projection_top
#print axioms insert_elvPolynomial
#print axioms projection_elvPolynomial
#print axioms act_comp
#print axioms projection_eq_zero_iff
end ELVOldCyclotomicConsumer
