import OddMath.SKM.PairedSorting

noncomputable section
open CategoryTheory StringDiagrams OddMath.SKM
namespace NonVacuity.PairedSorting
private def D : Datum Unit ℤ where
  cd :=
    { root := fun _ => 2
      coroot := fun _ => LinearMap.id
      coroot_root_self := fun _ => rfl }
  isGCM :=
    { diag := fun _ => rfl
      offDiag_nonpos := fun _ _ h => (h (Subsingleton.elim _ _)).elim
      zero_comm := fun _ _ => Iff.rfl }
  parity := fun _ => 1
  even_of_odd := fun _ _ _ => even_two
private def Sc : Scalars D ℚ where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := fun _ => isUnit_iff_ne_zero.mpr (by norm_num)
private def cs : CScalars Sc where
  c := fun _ _ => 1
  shift := fun _ _ _ => by simp [Sc]

example : etaP cs () 2 ≫ cpow (uLM D Sc () 2) 1 ≫ eLM D Sc () 2 0 = 𝟙 _ := by
  simpa [D, cs, Datum.h] using paired_target_low cs () 2 1 0 (by decide)

example : hLM D Sc () (-2) 0 ≫ cpow (uRM D Sc () (-2)) 1 ≫ epsP cs () (-2) = 𝟙 _ := by
  simpa [D, cs, Datum.h] using paired_source_low cs () (-2) 0 1 (by decide)

example : etaP cs () 2 ≫ cpow (uLM D Sc () 2) 0 ≫ eLM D Sc () 2 0 = 0 := by
  simpa [D, cs, Datum.h] using paired_target_low cs () 2 0 0 (by decide)

example : etaP cs () 0 ≫ sgM D Sc () 0 = hLM D Sc () 0 0 := by
  simpa [D, cs, ipar, Datum.h, zsign] using paired_target_initial cs () 0 (by decide)

example : etaP cs () 2 ≫ sgM D Sc () 2 = 0 :=
  etaP_sg_pos cs () 2 (by decide)

example : etaP cs () 0 ≫ cpow (uLM D Sc () 0) 1 ≫ sgM D Sc () 0 =
    -(etaP cs () 0 ≫ sgM D Sc () 0 ≫ cpow (uRM D Sc () 0) 1) +
      etaP cs () 0 ≫ eLM D Sc () 0 0 ≫ hLM D Sc () 0 0 := by
  simpa [D, zsign] using paired_target_expansion cs () 0 1

example : etaP cs () 2 ≫ cpow (uLM D Sc () 2) 3 ≫ sgM D Sc () 2 =
    -hLM D Sc () 2 1 + etaP cs () 2 ≫ eLM D Sc () 2 2 ≫ hLM D Sc () 2 0 := by
  simpa [D, cs, zsign] using paired_target_leading_pos cs () 2 2 1 rfl (by decide)

example : sgM D Sc () (-2) ≫ cpow (uRM D Sc () (-2)) 3 ≫ epsP cs () (-2) =
    -eLM D Sc () (-2) 1 + eLM D Sc () (-2) 0 ≫ hLM D Sc () (-2) 2 ≫ epsP cs () (-2) := by
  simpa [D, cs, zsign] using paired_source_leading_neg cs () (-2) 2 1 rfl (by decide)

#print axioms cpow_uL_eL
#print axioms hL_cpow_uR
#print axioms paired_target_low
#print axioms paired_source_low
#print axioms paired_target_step
#print axioms paired_source_step
#print axioms paired_target_initial
#print axioms paired_source_initial
#print axioms paired_target_expansion
#print axioms paired_source_expansion
#print axioms paired_target_leading_pos
#print axioms paired_source_leading_neg
#print axioms paired_target_leading_nonpos
#print axioms paired_source_leading_nonneg
#print axioms paired_target_pivot_isUnit
#print axioms paired_source_pivot_isUnit
#print axioms paired_target_initial_pivot_isUnit
#print axioms paired_source_initial_pivot_isUnit
#print axioms paired_inverse_indices_lower
#print axioms paired_slide_indices_lower
end NonVacuity.PairedSorting
