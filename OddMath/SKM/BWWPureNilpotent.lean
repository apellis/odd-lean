/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.BWWPureCoefficients
import OddMath.SKM.BWWBoxSum

/-!
# Pure coefficients in a nilpotent ideal

J. Brundan, W. Wang, B. Webster, arXiv:2505.22929v2, §2.2.

For box parameters `Sc : Scalars D k` (all coefficients `sᵢⱼ^{pq}` with `p < dᵢⱼ`, `q < dⱼᵢ`),
the polynomial `Qᵢⱼ(u, 0) = tᵢⱼ u^{dᵢⱼ} + Σ_{p < dᵢⱼ} sᵢⱼ^{p0} u^p` need not be a unit when `u`
is. It is a unit when the pure coefficients `sᵢⱼ^{p0}` lie in a nilpotent ideal.

* `ScalarData.PureNilpotent`: the pure coefficients lie in a nilpotent ideal.
* `ScalarData.NoPure.pureNilpotent`: Brundan–Ellis parameters (no pure terms) satisfy it with
  the zero ideal.
* `ScalarData.PureNilpotent.exists_isUnit_quad_remainders`: for a unit `x` and a `y` that
  supercommutes with it, `Qᵢⱼ(x, y) = U + R y = U + y R'` with `U` a unit.
-/

noncomputable section

namespace OddMath.SKM

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
variable {k : Type w} [CommRing k]

namespace ScalarData

/-- The pure coefficients `sᵢⱼ^{p0}` (`p < dᵢⱼ`) of the box parameters lie in a nilpotent
ideal. -/
def PureNilpotent (Sc : Scalars D k) : Prop :=
  ∃ (J : Ideal k) (N : ℕ), J ^ N = ⊥ ∧ Sc.toBWW.PureIn J

/-- Parameters without pure terms have their pure coefficients in the zero ideal. -/
theorem NoPure.pureNilpotent {Sc : Scalars D k} (hn : Sc.NoPure) : Sc.PureNilpotent :=
  ⟨⊥, 1, by simp, BWWScalars.PureIn.of_toBWW Sc hn ⊥⟩

/-- **The connected quadratic with a unit leading part.** If the pure coefficients lie in a
nilpotent ideal, `x` is a unit and `x^p y = ε^p (y x^p)`, then
`Qᵢⱼ(x, y) = tᵢⱼ x^{dᵢⱼ} + tⱼᵢ y^{dⱼᵢ} + Σ sᵢⱼ^{pq} x^p y^q` is `U + R y = U + y R'` with `U` a
unit. -/
theorem PureNilpotent.exists_isUnit_quad_remainders {Sc : Scalars D k}
    (hP : Sc.PureNilpotent) {i j : I} (hij : i ≠ j) (hd : D.d i j ≠ 0) {R : Type*} [Ring R]
    [Algebra k R] {x y : R} (hx : IsUnit x) (ε : k)
    (hslide : ∀ p : ℕ, x ^ p * y = ε ^ p • (y * x ^ p)) :
    ∃ U Rr Rl : R, IsUnit U ∧
      (Sc.t i j : k) • x ^ D.dn i j + (Sc.t j i : k) • y ^ D.dn j i +
        ∑ p ∈ Finset.range (D.dn i j), ∑ q ∈ Finset.range (D.dn j i),
          Sc.s i j p q • (x ^ p * y ^ q) = U + Rr * y ∧
      (Sc.t i j : k) • x ^ D.dn i j + (Sc.t j i : k) • y ^ D.dn j i +
        ∑ p ∈ Finset.range (D.dn i j), ∑ q ∈ Finset.range (D.dn j i),
          Sc.s i j p q • (x ^ p * y ^ q) = U + y * Rl := by
  obtain ⟨J, N, hJ, hpure⟩ := hP
  obtain ⟨U, Rr, Rl, hU, h1, h2⟩ :=
    BWWScalars.exists_isUnit_quad_remainders hJ hpure hij hx ε hslide
  rw [sum_box_toBWW Sc hij hd (fun p q => x ^ p * y ^ q)] at h1 h2
  simp only [pow_zero, mul_one, one_mul] at h1 h2
  exact ⟨U, Rr, Rl, hU, h1, h2⟩

end ScalarData

end OddMath.SKM
