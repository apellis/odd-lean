/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.GroundRingNondegeneracy
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Graded coefficient rings and lower-degree parameters

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, §1,
(1.5), (1.6) and the homogeneity condition (1.31); the Nondegeneracy Conjecture of §8.
J. Brundan, W. Wang, B. Webster, arXiv:2505.22929v2, §2.2 (the parameters (2.3) over an
`ℕ`-graded commutative ring) and Theorem 5.6, proof (reduction to the generic graded
parameter ring).

With a symmetrizer `dᵢ` the dot on a strand of colour `i` has degree `2dᵢ`, so the monomial
`u^p v^q` of `Qᵢⱼ` has degree `2dᵢp + 2dⱼq`, and the leading monomial `u^{dᵢⱼ}` has degree
`2dᵢdᵢⱼ`. The *coefficient degree* of `sᵢⱼ^{pq}` is the difference
`2(dᵢdᵢⱼ - dᵢp - dⱼq)` (`coefficientDegree`).

* `Scalars.GradedHomogeneous`: over an `ℕ`-graded commutative ring `k = ⨁ₙ 𝒜 n`, the units
  `tᵢⱼ` lie in degree `0` and every nonzero `sᵢⱼ^{pq}` lies in its coefficient degree, which
  is therefore nonnegative. This is the parameter condition of Brundan–Wang–Webster §2.2,
  restricted to the monomials that occur in Brundan–Ellis (1.6), namely `0 < p < dᵢⱼ`,
  `0 < q < dⱼᵢ`.
* `Scalars.LowerDegree`: over an arbitrary commutative ring, every nonzero `sᵢⱼ^{pq}` has
  nonnegative coefficient degree: `Qᵢⱼ` has no monomial above its leading terms.
* `Scalars.Homogeneous.coefficientDegree_eq_zero`: the homogeneity condition (1.31) says
  exactly that nonzero coefficients have coefficient degree zero.
* `GradedCoefficientNondegeneracy D sy`: the conjecture for graded-homogeneous parameters over
  every `ℕ`-graded commutative ring with `2` invertible. This is the statement targeted after
  the homogeneous case.
* `ReesParameters.scalars`: the Rees family `sᵢⱼ^{pq} h^{deg}` over `k[h]`, graded by the
  degree in `h`; it is graded homogeneous and specializes to the given parameters at `h = 1`.
* `nondegeneracyConjecture_of_lowerDegree`: the graded statement implies the conjecture for
  every lower-degree parameter system over every commutative ring with `2` invertible, in
  particular (`nondegeneracyConjecture_of_homogeneous_of_graded`) for homogeneous parameters.

The converse direction is not available by a filtration argument alone: specializing the
Rees family at `h = 0` gives the homogeneous parameters, but independence over `k[h]` does
not follow from independence at `h = 0` without torsion-freeness of the Hom modules in `h`.
-/

noncomputable section

namespace OddMath.SKM

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}

/-- The coefficient degree `2(dᵢdᵢⱼ - dᵢp - dⱼq)` of `sᵢⱼ^{pq}`: the degree of the leading
monomial `u^{dᵢⱼ}` of `Qᵢⱼ` minus that of `u^p v^q`, with dots of degree `2dᵢ`. -/
def coefficientDegree (sy : Symmetrizer D) (i j : I) (p q : ℕ) : ℤ :=
  2 * (sy.d i * D.d i j - sy.d i * p - sy.d j * q)

theorem coefficientDegree_symm (sy : Symmetrizer D) (i j : I) (p q : ℕ) :
    coefficientDegree sy i j p q = coefficientDegree sy j i q p := by
  have := sy.symm i j
  unfold coefficientDegree
  linear_combination 2 * this

variable {k : Type w} [CommRing k]

/-- The parameter condition over an `ℕ`-graded commutative ring `k = ⨁ₙ 𝒜 n`
(Brundan–Wang–Webster §2.2, on the monomials of Brundan–Ellis (1.6)): the units `tᵢⱼ` have
degree `0`, and each nonzero `sᵢⱼ^{pq}` is homogeneous of its coefficient degree, which is
in particular nonnegative. -/
def Scalars.GradedHomogeneous {σ : Type*} [SetLike σ k] (sy : Symmetrizer D) (𝒜 : ℕ → σ)
    (Sc : Scalars D k) : Prop :=
  (∀ i j, ((Sc.t i j : kˣ) : k) ∈ 𝒜 0) ∧
    ∀ i j (p q : ℕ), 0 < p → (p : ℤ) < D.d i j → 0 < q → (q : ℤ) < D.d j i →
      Sc.s i j p q ≠ 0 → ∃ n : ℕ, (n : ℤ) = coefficientDegree sy i j p q ∧ Sc.s i j p q ∈ 𝒜 n

/-- Lower-degree parameters: every nonzero `sᵢⱼ^{pq}` has nonnegative coefficient degree,
i.e. `dᵢp + dⱼq ≤ dᵢdᵢⱼ`. No grading of `k` is involved. -/
def Scalars.LowerDegree (sy : Symmetrizer D) (Sc : Scalars D k) : Prop :=
  ∀ i j (p q : ℕ), 0 < p → (p : ℤ) < D.d i j → 0 < q → (q : ℤ) < D.d j i →
    Sc.s i j p q ≠ 0 → 0 ≤ coefficientDegree sy i j p q

/-- Under the homogeneity condition (1.31), nonzero coefficients have coefficient degree
zero. -/
theorem Scalars.Homogeneous.coefficientDegree_eq_zero {Sc : Scalars D k} (hh : Sc.Homogeneous)
    (sy : Symmetrizer D) {i j : I} {p q : ℕ} (hp : 0 < p) (hp' : (p : ℤ) < D.d i j)
    (hq : 0 < q) (hq' : (q : ℤ) < D.d j i) (hs : Sc.s i j p q ≠ 0) :
    coefficientDegree sy i j p q = 0 := by
  have h31 := hh i j p q hp hp' hq hq' hs
  have hsy := sy.symm i j
  have hji : D.d j i ≠ 0 := by
    have : (0 : ℤ) < q := by exact_mod_cast hq
    omega
  have key : D.d j i * (sy.d i * D.d i j - sy.d i * p - sy.d j * q) = 0 := by
    linear_combination (-(sy.d i)) * h31 + (q : ℤ) * hsy
  have := (mul_eq_zero.mp key).resolve_left hji
  unfold coefficientDegree
  rw [this, mul_zero]

/-- Homogeneous parameters are lower-degree parameters. -/
theorem Scalars.Homogeneous.lowerDegree {Sc : Scalars D k} (hh : Sc.Homogeneous)
    (sy : Symmetrizer D) : Sc.LowerDegree sy := by
  intro i j p q hp hp' hq hq' hs
  rw [hh.coefficientDegree_eq_zero sy hp hp' hq hq' hs]

variable (D) in
/-- **The graded-coefficient statement.** For every `ℕ`-graded commutative ring `k` in which
`2` is invertible, every graded-homogeneous parameter system and every normalization, the
Nondegeneracy Conjecture holds. -/
def GradedCoefficientNondegeneracy (sy : Symmetrizer D) : Prop :=
  ∀ (k : Type w) [CommRing k] (σ : Type w) [SetLike σ k] [AddSubgroupClass σ k] (𝒜 : ℕ → σ)
    [GradedRing 𝒜], IsUnit (2 : k) → ∀ Sc : Scalars D k, Sc.GradedHomogeneous sy 𝒜 →
      ∀ cs : CScalars Sc, NondegeneracyConjecture cs

namespace ReesParameters

open MvPolynomial

variable (sy : Symmetrizer D) (Sc : Scalars D k)

/-- The Rees parameters over `k[h] = MvPolynomial Unit k`: the units are unchanged and
`sᵢⱼ^{pq}` is replaced by `sᵢⱼ^{pq} h^{deg}`, with `deg` the coefficient degree (truncated
at zero). -/
def scalars : Scalars D (MvPolynomial Unit k) where
  t i j := Units.map (C : k →+* MvPolynomial Unit k).toMonoidHom (Sc.t i j)
  t_self i := by rw [Sc.t_self, map_one]
  t_symm_of_d_eq_zero i j h := by rw [Sc.t_symm_of_d_eq_zero i j h]
  s i j p q := C (Sc.s i j p q) * X () ^ (coefficientDegree sy i j p q).toNat
  s_symm i j p q := by rw [Sc.s_symm, coefficientDegree_symm]
  s_eq_zero i j p q h := by rw [Sc.s_eq_zero i j p q h, map_zero, zero_mul]
  two_isUnit h := by
    convert (Sc.two_isUnit h).map (C : k →+* MvPolynomial Unit k) using 1
    exact (map_ofNat _ 2).symm

/-- The normalization units, transported along the constants. -/
def cScalars {Sc : Scalars D k} (cs : CScalars Sc) : CScalars (scalars sy Sc) where
  c μ i := Units.map (C : k →+* MvPolynomial Unit k).toMonoidHom (cs.c μ i)
  shift μ i j := by
    rw [cs.shift, map_mul]
    rfl

/-- For lower-degree parameters the Rees parameters are graded homogeneous for the grading
of `k[h]` by degree. -/
theorem gradedHomogeneous {Sc : Scalars D k} (hl : Sc.LowerDegree sy) :
    (scalars sy Sc).GradedHomogeneous sy (homogeneousSubmodule Unit k) := by
  refine ⟨fun i j => ?_, fun i j p q hp hp' hq hq' hs => ?_⟩
  · exact (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_C _ _)
  · have hs' : Sc.s i j p q ≠ 0 := by
      intro h0
      exact hs (by simp [scalars, h0])
    refine ⟨(coefficientDegree sy i j p q).toNat,
      Int.toNat_of_nonneg (hl i j p q hp hp' hq hq' hs'), ?_⟩
    exact (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_C_mul_X_pow _ _ _)

/-- Evaluation at `h = 1`. -/
abbrev specialize : MvPolynomial Unit k →+* k := eval fun _ => (1 : k)

/-- Specializing the Rees parameters at `h = 1` recovers the given parameters. -/
theorem scalarChange_specialize :
    ScalarChange.scalars D (specialize (k := k)) (scalars sy Sc) = Sc := by
  apply Scalars.ext_t_s
  · funext i j
    ext
    simp [ScalarChange.scalars, scalars]
  · funext i j p q
    simp [ScalarChange.scalars, scalars]

end ReesParameters

/-- **Reduction to graded coefficients.** The graded-coefficient statement implies the
Nondegeneracy Conjecture for lower-degree parameters over every commutative ring in which `2`
is invertible: apply it to the Rees parameters over `k[h]` and specialize at `h = 1`. -/
theorem nondegeneracyConjecture_of_lowerDegree {sy : Symmetrizer D}
    (hG : GradedCoefficientNondegeneracy.{u, v, w} D sy) (h₂ : IsUnit (2 : k))
    {Sc : Scalars D k} (hl : Sc.LowerDegree sy) (cs : CScalars Sc) :
    NondegeneracyConjecture cs := by
  letI : GradedRing (MvPolynomial.homogeneousSubmodule Unit k) := MvPolynomial.gradedAlgebra
  have h₂' : IsUnit (2 : MvPolynomial Unit k) := by
    convert h₂.map (MvPolynomial.C : k →+* MvPolynomial Unit k) using 1
    exact (map_ofNat _ 2).symm
  have hR := hG (MvPolynomial Unit k) (Submodule k (MvPolynomial Unit k))
    (MvPolynomial.homogeneousSubmodule Unit k) h₂' (ReesParameters.scalars sy Sc)
    (ReesParameters.gradedHomogeneous sy hl) (ReesParameters.cScalars sy cs)
  have hS := nondegeneracyConjecture_scalarChange ReesParameters.specialize hR
  refine nondegeneracyConjecture_congr (ReesParameters.scalarChange_specialize sy Sc) _ cs
    ?_ hS
  intro μ i
  simp [ScalarChange.cScalars, ReesParameters.cScalars]

/-- Consistency with the homogeneous case: the graded-coefficient statement implies the
conjecture for homogeneous parameters. -/
theorem nondegeneracyConjecture_of_homogeneous_of_graded {sy : Symmetrizer D}
    (hG : GradedCoefficientNondegeneracy.{u, v, w} D sy) (h₂ : IsUnit (2 : k))
    {Sc : Scalars D k} (hh : Sc.Homogeneous) (cs : CScalars Sc) :
    NondegeneracyConjecture cs :=
  nondegeneracyConjecture_of_lowerDegree hG h₂ (hh.lowerDegree sy) cs

end OddMath.SKM
