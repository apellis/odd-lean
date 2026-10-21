import OddMath

open OddMath.QuiverHecke

example (w : Equiv.Perm (Fin 2)) : CliffordPermutations.perm (R := ℚ) (J := Bool) w ≠ 0 :=
  CliffordPermutations.Examples.perm_ne_zero w

example (ν : CliffordColours.Word Bool 2) :
    CliffordPermutations.perm (R := ℚ) (Equiv.swap (0 : Fin 2) 1) * CliffordColours.e ν =
      CliffordColours.e (ν ∘ Equiv.swap (0 : Fin 2) 1) *
        CliffordPermutations.perm (Equiv.swap (0 : Fin 2) 1) := by
  simpa using CliffordPermutations.perm_e (R := ℚ) (Equiv.swap (0 : Fin 2) 1) ν
