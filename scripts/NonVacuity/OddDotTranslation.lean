import OddMath.SKM.OddDotTranslation
import OddMath.Diagrams.OddNilHecke.ExteriorDeformation
import Mathlib.CategoryTheory.Preadditive.SingleObj

noncomputable section
open CategoryTheory StringDiagrams OddMath.SKM
open OddMath.OddNilHecke

namespace NonVacuity.OddDotTranslation
open ExteriorDeformation

example : exterior dualParameter ≠ 0 ∧
    (firstDot dualParameter + exterior dualParameter) ^ 2 = firstDot dualParameter ^ 2 := by
  refine ⟨dualNumber_model.1, ?_⟩
  apply DotTranslation.square
  · exact dualNumber_model.2.1
  · simpa only [add_comm] using
      (exterior_anticommutes dualParameter (TrivSqZeroExt.inr_mul_inr ℚ 1 1)).1

private abbrev R := TrivSqZeroExt ℚ ℚ
example (m : ℕ) :
    DotTranslation.braidPolynomial
      (firstDot dualParameter + exterior dualParameter) 1
      (firstDot dualParameter + exterior dualParameter) m =
    DotTranslation.braidPolynomial (firstDot dualParameter) 1
      (firstDot dualParameter) m := by
  apply DotTranslation.braidPolynomial_translate
  · exact dualNumber_model.2.1
  · simpa only [add_comm] using
      (exterior_anticommutes dualParameter (TrivSqZeroExt.inr_mul_inr ℚ 1 1)).1
  · simpa only [add_comm] using
      (exterior_anticommutes dualParameter (TrivSqZeroExt.inr_mul_inr ℚ 1 1)).1
  · simp

private abbrev Z : SingleObj R := PUnit.unit
private def d : End Z := TrivSqZeroExt.inr 1

-- The positive odd-height moment statement has a nonzero exterior witness.
example : d ≠ 0 ∧
    (𝟙 Z ≫ (((0 : End Z) + d) ^ 1) ≫ 𝟙 Z : Z ⟶ Z) =
      (𝟙 Z ≫ ((0 : End Z) ^ 1) ≫ 𝟙 Z) + (show Z ⟶ Z from d) := by
  constructor
  · change (TrivSqZeroExt.inr (1 : ℚ) : R) ≠ 0
    intro h
    have hs := congrArg TrivSqZeroExt.snd h
    norm_num at hs
  · have h := OddMath.SKM.OddDotTranslation.odd_moment_shift
      (0 : End Z) d (show Z ⟶ Z from d) (𝟙 Z) (𝟙 Z) 0
      (show d * d = 0 from TrivSqZeroExt.inr_mul_inr ℚ 1 1)
      (by simp) (by simp) (by simp)
    exact h

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

-- At actual source height three, the odd row-one correction leaves the
-- last (row-two) coordinate unchanged for every target exterior coefficient.
example (d₀ : End ((pres D Sc).obj (ob D 3 []))) :
    ∀ r ≤ 2,
      ((↑(cs.c 3 ())⁻¹ : ℚ) • etaP cs () 3) ≫
        OddMath.SKM.OddDotTranslation.shiftedCap
          (fun s => cl D Sc 3 [up (), dn ()] [] (epsL () s)) d₀ r =
      if r = 2 then 𝟙 _ else 0 :=
  etaP_shifted_cap_coordinates cs () 3 2 rfl d₀

#print axioms OddMath.OddNilHecke.DotTranslation.square
#print axioms OddMath.OddNilHecke.DotTranslation.even_pow
#print axioms OddMath.OddNilHecke.DotTranslation.odd_pow
#print axioms OddMath.OddNilHecke.DotTranslation.slide
#print axioms OddMath.OddNilHecke.DotTranslation.braidPolynomial_paired
#print axioms OddMath.OddNilHecke.DotTranslation.braidPolynomial_translate
#print axioms OddMath.SKM.OddDotTranslation.shiftedCap_inverse
#print axioms OddMath.SKM.OddDotTranslation.last_column_coordinates
#print axioms OddMath.SKM.OddDotTranslation.odd_moment_shift
#print axioms OddMath.SKM.OddDotTranslation.even_moment_fixed
#print axioms OddMath.SKM.etaP_shifted_cap_coordinates
end NonVacuity.OddDotTranslation
