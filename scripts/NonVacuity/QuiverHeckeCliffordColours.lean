import OddMath

open OddMath.QuiverHecke

example (ν : CliffordColours.Word Bool 2) : CliffordColours.e (R := ℚ) ν ≠ 0 :=
  CliffordColours.Examples.projection_ne_zero ν

example (ν : CliffordColours.Word Bool 2) :
    CliffordColours.C (R := ℚ) Bool.not 0 * CliffordColours.e ν =
      CliffordColours.e (CliffordColours.flip Bool.not 0 ν) * CliffordColours.C Bool.not 0 :=
  CliffordColours.C_e Bool.not Bool.not_not 0 ν

example : (∑ ν : CliffordColours.Word Bool 2, CliffordColours.e (R := ZMod 2) ν) = 1 :=
  CliffordColours.sum_e
