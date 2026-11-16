/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.BWWGradedParameters
import OddMath.Algebra.BoxPolynomialUnits

/-!
# Pure coefficients of Brundan–Wang–Webster parameters in an ideal

J. Brundan, W. Wang, B. Webster, arXiv:2505.22929v2, §2.2. For `i ≠ j`,

    Qᵢⱼ(u, 0) = tᵢⱼ u^{dᵢⱼ} + Σ_{p<dᵢⱼ} cᵢⱼ(p, 0) u^p.

The Brundan–Ellis parameters have no lower terms here, and several invertibility arguments
for distinct colours use that `Qᵢⱼ(u, 0)` is a unit times `u^{dᵢⱼ}`. For Brundan–Wang–Webster
parameters the lower coefficients have positive coefficient degree
(`coefficientDegree_pos_of_pure`). Over a base whose positive-degree part lies in a nilpotent
ideal `J` (a truncated Rees base), `Qᵢⱼ(u, 0)` is therefore a unit whenever `u` is.

* `BWWScalars.PureIn Sc J`: every coefficient `cᵢⱼ(p, 0)`, `p < dᵢⱼ`, lies in `J`. By
  `c_symm` this covers every pure coefficient below the corners, including the constant
  term and the pure terms in `v`.
* `BWWScalars.PureIn.of_gradedHomogeneous`: graded-homogeneous parameters satisfy `PureIn` for
  any ideal containing the positive-degree parts.
* `BWWScalars.PureIn.of_toBWW`: parameters without pure terms satisfy `PureIn` for every ideal.
* `BWWScalars.isUnit_lowerPoly`: `Qᵢⱼ(u, 0)` is a unit for `u` a unit and `J` nilpotent.
* `BWWScalars.exists_isUnit_quad_remainders`: `Qᵢⱼ(u, v) = U + R v = U + v R'` with `U` a unit,
  the form used by the distinct-colour mixed crossing arguments.
-/

namespace OddMath.SKM

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
variable {k : Type w} [CommRing k]

namespace BWWScalars

/-- The coefficients of `Qᵢⱼ(u, 0)` below the leading term lie in `J`. By `c_symm`, this is
the condition that every pure coefficient below the corners lies in `J`. -/
def PureIn (Sc : BWWScalars D k) (J : Ideal k) : Prop :=
  ∀ (i j : I) (p : ℕ), i ≠ j → p < D.dn i j → Sc.c i j p 0 ∈ J

/-- Parameters without pure terms below the corners (`ScalarData.NoPure`, as in BE2) have no
lower terms in `Qᵢⱼ(u, 0)`. -/
theorem PureIn.of_toBWW (Sc : Scalars D k) (hn : Sc.NoPure) (J : Ideal k) :
    Sc.toBWW.PureIn J := by
  intro i j p hij hp
  have hji : D.dn j i ≠ 0 := fun h =>
    absurd ((ScalarData.dn_eq_zero_iff (D := D) i j).mpr h) (by omega)
  rw [ScalarData.toBWW_c_of_lt Sc hij hp (Nat.pos_of_ne_zero hji),
    hn i j p 0 hij hp (Nat.pos_of_ne_zero hji) (Or.inr rfl)]
  exact J.zero_mem

/-- **The distinct-colour quadratic with a unit leading part.** For a unit `x` and the pure
coefficients in a nilpotent ideal, `Qᵢⱼ(x, y) = U + R y = U + y R'` with `U = Qᵢⱼ(x, 0)` a unit.
The left form uses the signed slide `x^p y = ε^p (y x^p)`. -/
theorem exists_isUnit_quad_remainders {Sc : BWWScalars D k} {J : Ideal k} {N : ℕ}
    (hJ : J ^ N = ⊥) (hpure : Sc.PureIn J) {i j : I} (hij : i ≠ j) {R : Type*} [Ring R]
    [Algebra k R] {x y : R} (hx : IsUnit x) (ε : k)
    (hslide : ∀ p : ℕ, x ^ p * y = ε ^ p • (y * x ^ p)) :
    ∃ U Rr Rl : R, IsUnit U ∧
      ∑ p ∈ Finset.range (D.dn i j + 1), ∑ q ∈ Finset.range (D.dn j i + 1),
        Sc.c i j p q • (x ^ p * y ^ q) = U + Rr * y ∧
      ∑ p ∈ Finset.range (D.dn i j + 1), ∑ q ∈ Finset.range (D.dn j i + 1),
        Sc.c i j p q • (x ^ p * y ^ q) = U + y * Rl :=
  OddMath.Algebra.exists_isUnit_box_remainders J hJ (Sc.c i j) (D.dn i j) (D.dn j i) (Sc.t i j)
    (Sc.c_corner i j hij) (fun p hp => hpure i j p hij hp) hx ε hslide

end BWWScalars

end OddMath.SKM
