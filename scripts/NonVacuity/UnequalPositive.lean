import OddMath

/-! Non-vacuity checks in `NonVacuity.UnequalPositive`.
Conventions are in `scripts/NonVacuity.lean`. -/

open CategoryTheory

noncomputable section

namespace NonVacuity.UnequalPositive
open OddMath.SKM.PositiveFormCoefficientsExamples
example (z : ℤ) :
    (twoWordForm 1 (by norm_num) 0 1).coeff z = 0 :=
  unequal_coeff 1 (by norm_num) (by decide : 0 ≠ 1) z

example : EmptyFamilyComparison 1 (by norm_num) 0 1 :=
  unequal_family 1 (by norm_num) (by decide : 0 ≠ 1)

example (z : ℤ) :
    (twoWordForm (-1) (by norm_num) 0 1).coeff z = 0 :=
  unequal_coeff (-1) (by norm_num) (by decide : 0 ≠ 1) z

example : EmptyFamilyComparison (-1) (by norm_num) 0 1 :=
  unequal_family (-1) (by norm_num) (by decide : 0 ≠ 1)

example (z : ℤ) :
    (twoWordForm 1 (by norm_num) 1 2).coeff z = 0 :=
  unequal_coeff 1 (by norm_num) (by decide : 1 ≠ 2) z

example : EmptyFamilyComparison 1 (by norm_num) 1 2 :=
  unequal_family 1 (by norm_num) (by decide : 1 ≠ 2)

example (z : ℤ) :
    (twoWordForm (-1) (by norm_num) 1 2).coeff z = 0 :=
  unequal_coeff (-1) (by norm_num) (by decide : 1 ≠ 2) z

example : EmptyFamilyComparison (-1) (by norm_num) 1 2 :=
  unequal_family (-1) (by norm_num) (by decide : 1 ≠ 2)

example (z : ℤ) :
    (twoWordForm 1 (by norm_num) 1 0).coeff z = 0 :=
  unequal_coeff 1 (by norm_num) (by decide : 1 ≠ 0) z

example : EmptyFamilyComparison 1 (by norm_num) 1 0 :=
  unequal_family 1 (by norm_num) (by decide : 1 ≠ 0)

example (z : ℤ) :
    (twoWordForm (-1) (by norm_num) 1 0).coeff z = 0 :=
  unequal_coeff (-1) (by norm_num) (by decide : 1 ≠ 0) z

example : EmptyFamilyComparison (-1) (by norm_num) 1 0 :=
  unequal_family (-1) (by norm_num) (by decide : 1 ≠ 0)

example (z : ℤ) :
    (twoWordForm 1 (by norm_num) 2 1).coeff z = 0 :=
  unequal_coeff 1 (by norm_num) (by decide : 2 ≠ 1) z

example : EmptyFamilyComparison 1 (by norm_num) 2 1 :=
  unequal_family 1 (by norm_num) (by decide : 2 ≠ 1)

example (z : ℤ) :
    (twoWordForm (-1) (by norm_num) 2 1).coeff z = 0 :=
  unequal_coeff (-1) (by norm_num) (by decide : 2 ≠ 1) z

example : EmptyFamilyComparison (-1) (by norm_num) 2 1 :=
  unequal_family (-1) (by norm_num) (by decide : 2 ≠ 1)

end NonVacuity.UnequalPositive
