import OddMath.SKM.CoupledBubbleEvaluation
import Mathlib.Algebra.TrivSqZeroExt.Basic

noncomputable section
open CategoryTheory StringDiagrams OddMath.SKM
namespace NonVacuity.CoupledBubbleEvaluation

private def D : Datum Unit ℤ where
  cd :=
    { root := fun _ => 2
      coroot := fun _ => LinearMap.id
      coroot_root_self := fun _ => rfl }
  isGCM :=
    { diag := fun _ => rfl
      offDiag_nonpos := fun i j h => absurd (Subsingleton.elim i j) h
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

-- The inverse witness comes from the actual source inversion relation.
example : oddBubble cs () 0 =
    cl D Sc 0 [] [dn (), up ()] (etaL () 0) ≫
      (-cl D Sc 0 [dn (), up ()] [up (), dn ()] (lcrossL () ())) ≫
      cl D Sc 0 [up (), dn ()] [] (epsL () 0) := by
  apply oddBubble_zero_inverse_mate cs () 0 rfl rfl
  have h := eq_2_12_b (Sc := Sc) () 0
  rw [← cl_comp (sChain_lcrossL () ()) (sChain_sigmaL () ())] at h
  simpa [D, cl_nil] using congrArg Neg.neg h

example : (↑(cs.c 0 ())⁻¹ : ℚ) • bubL cs () 0 1 =
    cl D Sc 0 [] [dn (), up ()] (etaL () 0) ≫
      (-cl D Sc 0 [dn (), up ()] [up (), dn ()] (lcrossL () ())) ≫
      cl D Sc 0 [up (), dn ()] [] (epsL () 1) := by
  apply normalized_bubL_zero_inverse_mate cs () 0 1 rfl rfl
  have h := eq_2_12_b (Sc := Sc) () 0
  rw [← cl_comp (sChain_lcrossL () ()) (sChain_sigmaL () ())] at h
  simpa [D, cl_nil] using congrArg Neg.neg h

-- A nonzero nilpotent element is allowed in the series coefficient ring.
example (A A' P : ℕ → TrivSqZeroExt ℚ ℚ) (hP : P 0 = 1)
    (h : ∀ n ≤ 4, ∑ r ∈ Finset.range (n + 1), A (n-r) * P r =
      ∑ r ∈ Finset.range (n + 1), A' (n-r) * P r) : A 4 = A' 4 :=
  bubble_convolution_right_cancel_upto A A' P 4 hP h 4 le_rfl

#print axioms OddMath.SKM.oddBubble_zero_inverse_mate
#print axioms OddMath.SKM.normalized_bubL_zero_inverse_mate
#print axioms OddMath.SKM.bubble_convolution_right_cancel_upto
end NonVacuity.CoupledBubbleEvaluation
