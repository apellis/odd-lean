import OddMath

/-! # KKT coefficient-operator consumers -/

noncomputable section
open OddMath.QuiverHecke.CliffordCoefficients

example (i : Fin 2) : X (R := ℚ) (fun _ => true) i ^ 2 ≠ 0 :=
  Examples.X_sq_ne_zero i

example (i j : Fin 3) (hij : i ≠ j) :
    C (R := ℚ) i * C j = -(C j * C i) := C_anticommute i j hij

example (i : Fin 2) : C (R := ZMod 2) i * C i = 1 := C_sq i

#print axioms OddMath.QuiverHecke.CliffordCoefficients.X_supercommute
#print axioms OddMath.QuiverHecke.CliffordCoefficients.Examples.X_sq_ne_zero
