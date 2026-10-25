import OddMath.SKM.PositiveDotTransport
import OddMath.SKM.MixedCrossingLocalExamples

/-! Full-coefficient source-prefix closure on a concrete two-odd-color datum. -/

noncomputable section
namespace NonVacuity.PositiveDotTransport
open CategoryTheory StringDiagrams Presentation OddMath.SKM

private abbrev D₂ := MixedCrossingLocalExamples.oddDatum
private def sc : Scalars D₂ ℚ where
  t := fun _ _ => 1
  t_self := by intros; rfl
  t_symm_of_d_eq_zero := by intros; rfl
  s := fun _ _ _ _ => 0
  s_symm := by intros; rfl
  s_eq_zero := by intros; rfl
  two_isUnit := by intro _; exact isUnit_iff_ne_zero.mpr (by norm_num)

private def cs : CScalars sc where
  c := fun _ _ => 1
  shift := by intros; simp [sc]

private def p : SYM D₂ ℚ :=
  SYM.delta D₂ ℚ ⟨false, rfl⟩ +
    SYM.delta D₂ ℚ ⟨false, rfl⟩ * SYM.delta D₂ ℚ ⟨true, rfl⟩ + SYM.e D₂ ℚ false 0

/-- An inhomogeneous coefficient with a product of distinct odd generators. -/
theorem finite_full_slide :
    ∃ z : {n : ℕ // 0 < n} →₀ SYM D₂ ℚ,
      lbub true 0 (betaSYM cs (wt D₂ 0 [up true]) p) =
        rbub true 0 (betaSYM cs (wt D₂ 0 []) p) + positiveDotExpansion cs 0 true z :=
  betaSYM_exists_positiveDotExpansion cs 0 true p

/-- Positive dots cannot disappear in composition, including odd coefficients. -/
example {f g : (pres D₂ sc).obj (ob D₂ 0 [up false]) ⟶
    (pres D₂ sc).obj (ob D₂ 0 [up false])}
    (hf : f ∈ dotSlideAtLeast cs 0 (up false) 2)
    (hg : g ∈ dotSlideAtLeast cs 0 (up false) 3) :
    f ≫ g ∈ dotSlideAtLeast cs 0 (up false) 5 :=
  dotSlideAtLeast_comp cs (N := 2) (M := 3) hf hg

#print axioms betaSYM_exists_positiveDotExpansion
#print axioms dotSlideAtLeast_comp
#print axioms finite_full_slide
end NonVacuity.PositiveDotTransport
