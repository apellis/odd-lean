import OddMath.SKM.BWWPureCoefficients
import NonVacuity.BWWScalars

/-! # Pure coefficients of Brundan–Wang–Webster parameters

On the datum of `NonVacuity.BWWScalars`, the Brundan–Ellis parameters `u³ + uv² + v³` have
their pure coefficients in every ideal, so `Qᵢⱼ(x, 0)` is a unit for every unit `x` of a
`ℚ`-algebra, and `Qᵢⱼ(x, y)` has the unit-plus-remainder forms for commuting `x`, `y`.
-/

noncomputable section
namespace NonVacuity.BWWPureCoefficients
open OddMath OddMath.SKM NonVacuity.BWWScalars

theorem pureIn : scalars.toBWW.PureIn (⊥ : Ideal ℚ) := BWWScalars.PureIn.of_toBWW scalars ⊥

example {R : Type} [Ring R] [Algebra ℚ R] {x : R} (hx : IsUnit x) :
    IsUnit ((scalars.toBWW.t true false : ℚ) • x ^ datum.dn true false +
      ∑ p ∈ Finset.range (datum.dn true false), scalars.toBWW.c true false p 0 • x ^ p) :=
  BWWScalars.isUnit_lowerPoly (N := 1) (pow_one _) pureIn (by decide) hx

example {R : Type} [Ring R] [Algebra ℚ R] {x y : R} (hx : IsUnit x) (hxy : Commute x y) :
    ∃ U Rr Rl : R, IsUnit U ∧
      ∑ p ∈ Finset.range (datum.dn true false + 1),
        ∑ q ∈ Finset.range (datum.dn false true + 1),
          scalars.toBWW.c true false p q • (x ^ p * y ^ q) = U + Rr * y ∧
      ∑ p ∈ Finset.range (datum.dn true false + 1),
        ∑ q ∈ Finset.range (datum.dn false true + 1),
          scalars.toBWW.c true false p q • (x ^ p * y ^ q) = U + y * Rl :=
  BWWScalars.exists_isUnit_quad_remainders (N := 1) (pow_one _) pureIn (by decide) hx 1
    fun p => by rw [one_pow, one_smul]; exact (hxy.pow_left p).eq

end NonVacuity.BWWPureCoefficients
