import OddMath.QuiverHecke.CyclotomicAction.SignedPolynomialTransport

noncomputable section
namespace SignedPolynomialTransportConsumer
open CategoryTheory StringDiagrams OddMath OddMath.QuiverHecke

/-- Odd rank one over a ring with two invertible. -/
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

/-- Odd chain length: the polynomial must be evaluated at the negative dot.
The polynomial deliberately has both parities, so a single overall sign
would be wrong. -/
example :
    Polynomial.aeval (dotE datum scalars [(), ()] 0)
        (Polynomial.X ^ 3 + Polynomial.X ^ 2 + 1 : Polynomial ℚ) ≫
        moveHom datum scalars () [] [()] =
      moveHom datum scalars () [] [()] ≫
        Polynomial.aeval (-dotE datum scalars [(), ()] 1)
          (Polynomial.X ^ 3 + Polynomial.X ^ 2 + 1 : Polynomial ℚ) := by
  simpa [wordSumParity, datum, SKM.zsign] using
    polynomial_comp_moveHom datum scalars () [] [()]
      (Polynomial.X ^ 3 + Polynomial.X ^ 2 + 1 : Polynomial ℚ)

/-- A spectator polynomial sees the parity of the entire chain. -/
example (f : Polynomial ℚ) :=
  polynomial_mem_comp_moveHom datum scalars () () [()] [()] [] f

/-- Two odd crossings cancel the moving-dot sign. -/
example (f : Polynomial ℚ) :
    Polynomial.aeval (dotE datum scalars [(), (), ()] 0) f ≫
        moveHom datum scalars () [] [(), ()] =
      moveHom datum scalars () [] [(), ()] ≫
        Polynomial.aeval (dotE datum scalars [(), (), ()] 2) f := by
  simpa [wordSumParity, datum, SKM.zsign] using
    polynomial_comp_moveHom datum scalars () [] [(), ()] f

/-- Empty chain, constant polynomial and exponent zero are retained. -/
example := polynomial_comp_moveHom datum scalars () [] [] (1 : Polynomial ℚ)
example := dot_pow_comp_moveHom datum scalars () [()] [(), ()] 0

#print axioms dot_pow_comp_moveHom
#print axioms polynomial_comp_moveHom
#print axioms polynomial_mem_comp_moveHom
end SignedPolynomialTransportConsumer
