import OddMath.Frontier.OddBialgebraCornerB
import OddMath.Frontier.OddBialgebraCoproduct

/-!
# The coproduct of `K₀(ONH)` from restriction

EKL arXiv:1111.1320v1, §6, pp. 46–47: the restriction functors along `ONH_a ⊗ ONH_b ⊂ ONH_{a+b}`
give the coproduct of the `q`-bialgebra `K₀(ONH)`. Here `a = m+2`, `b = m'+2`.

* `res_divE_exact`: `Res [E^{(a+b)}] = q^{-ab} [E^{(a)} ⊠ E^{(b)}]` in `K₀(ONH_a ⊗ ONH_b)`
  (`K₀(ONH_a ⊗ ONH_b)` is free of rank one on `[E^{(a)} ⊠ E^{(b)}]`, `K0B.basis`).
* `resCoeff m m' : K₀(ONH_{a+b}) → ℤ[q,q⁻¹]`, the `[E^{(a)} ⊠ E^{(b)}]`-coordinate of restriction.
* `coprodK0_coeff_eq_res`: the `ϑ^{(a)} ⊗ ϑ^{(b)}`-coefficient of the coproduct `coprodK0`
  (`OddBialgebraCoproduct`) of any `x ∈ K₀(ONH)` is `resCoeff m m' (x_{a+b})`: the coproduct is
  induced by restriction. For `a = 0` or `b = 0` restriction is the identity and
  `coprodK0_coeff_zero_left`, `coprodK0_coeff_zero_right` give the corresponding components.
-/

noncomputable section
open LaurentPolynomial

namespace OddMath.Frontier.OddBialgebra
open GradedK0 OddCategorification QuantumSl2Plus TwTensor

local notation "L" => LaurentPolynomial ℤ

variable (m m' : ℕ)

/-- **Restriction of `E^{(a+b)}`**: `Res [E^{(a+b)}] = q^{-ab} [E^{(a)} ⊠ E^{(b)}]`. -/
theorem res_divE_exact : res m m' (K0.of (divE (m+2+m'))) =
    (T (-(((m+2) * (m'+2) : ℕ) : ℤ)) : L) • K0.of (boxE m m') := by
  have h := congrArg (K0B.classify m m') (res_divE (m := m) (m' := m'))
  rw [map_smul, map_zero, smul_eq_mul, mul_eq_zero] at h
  rcases h with h | h
  · exact absurd h (qFact_ne_zero _)
  · exact sub_eq_zero.1 ((K0B.classify m m').injective (h.trans (map_zero _).symm))

/-- The `[E^{(a)} ⊠ E^{(b)}]`-coordinate of restriction `K₀(ONH_{a+b}) → K₀(ONH_a ⊗ ONH_b)`. -/
def resCoeff : KONH (m+2+m'+2) →ₗ[L] L :=
  ((K0B.basis m m').coord 0).comp (res m m')

theorem resCoeff_Eclass : resCoeff m m' (Eclass (m+2+m'+2)) =
    T (-(((m+2) * (m'+2) : ℕ) : ℤ)) := by
  show ((K0B.basis m m').coord 0) (res m m' (K0.of (divE (m+2+m')))) = _
  rw [res_divE_exact, map_smul, ← K0B.basis_apply m m' 0, Basis.coord_apply, Basis.repr_self,
    Finsupp.single_eq_same, smul_eq_mul, mul_one]

theorem coprodK0_single (n : ℕ) :
    coprodK0 (DFinsupp.single n (Eclass n)) = coprodVal n := by
  rw [coprodK0, AlgHom.comp_apply, ← eq_6_3_θ, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe,
    AlgEquiv.symm_apply_apply, coprod_θ]

theorem coeffAt_coprodVal (n a b : ℕ) :
    coeffAt (T (-2)) (a, b) (coprodVal n) =
      if a + b = n then (T (-(((a * b : ℕ)) : ℤ)) : L) else 0 := by
  rw [coprodVal, map_sum]
  simp only [map_smul, tw, coeffAt_single, smul_eq_mul, mul_ite, mul_one, mul_zero]
  split_ifs with h
  · rw [Finset.sum_eq_single (a, b)]
    · simp
    · rintro ⟨c, d⟩ _ hne
      rw [if_neg hne]
    · intro hn
      exact absurd (Finset.mem_antidiagonal.2 h) hn
  · refine Finset.sum_eq_zero fun p hp => if_neg fun hpe => h ?_
    rw [Finset.mem_antidiagonal] at hp
    obtain ⟨h1, h2⟩ := Prod.mk.inj hpe
    omega

/-- **The coproduct is induced by restriction**: the coefficient of `ϑ^{(a)} ⊗ ϑ^{(b)}` in
`Δ(x)` is the `[E^{(a)} ⊠ E^{(b)}]`-coordinate of `Res(x_{a+b})`. -/
theorem coprodK0_coeff_eq_res (x : K0ONH) :
    coeffAt (T (-2)) (m+2, m'+2) (coprodK0 x) = resCoeff m m' (x (m+2+m'+2)) := by
  have h : (coeffAt (T (-2)) (m+2, m'+2)).comp coprodK0.toLinearMap =
      (resCoeff m m').comp (DFinsupp.lapply (m+2+m'+2)) := by
    refine basisK0.ext fun n => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply, basisK0_apply,
      coprodK0_single, coeffAt_coprodVal, DFinsupp.lapply_apply]
    by_cases hn : n = m+2+m'+2
    · subst hn
      rw [if_pos (by omega), DFinsupp.single_eq_same, resCoeff_Eclass]
    · rw [if_neg (by omega), DFinsupp.single_eq_of_ne hn, map_zero]
  exact DFunLike.congr_fun h x

/-- For `a = 0` restriction is the identity of `K₀(ONH_n)` and `E^{(0)} ⊠ E^{(n)} = E^{(n)}`: the
coefficient of `ϑ^{(0)} ⊗ ϑ^{(n)}` in `Δ(x)` is the `[E^{(n)}]`-coordinate of `x_n`. -/
theorem coprodK0_coeff_zero_left (n : ℕ) (x : K0ONH) :
    coeffAt (T (-2)) (0, n) (coprodK0 x) = (basisE n).coord 0 (x n) := by
  have h : (coeffAt (T (-2)) (0, n)).comp coprodK0.toLinearMap =
      ((basisE n).coord 0).comp (DFinsupp.lapply n) := by
    refine basisK0.ext fun k => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply, basisK0_apply,
      coprodK0_single, coeffAt_coprodVal, DFinsupp.lapply_apply]
    by_cases hk : k = n
    · subst hk
      rw [if_pos (zero_add k), DFinsupp.single_eq_same, ← basisE_apply k 0, Basis.coord_apply,
        Basis.repr_self, Finsupp.single_eq_same, zero_mul, Nat.cast_zero, neg_zero, T_zero]
    · rw [if_neg (by omega), DFinsupp.single_eq_of_ne hk, map_zero]
  exact DFunLike.congr_fun h x

/-- For `b = 0` restriction is the identity: the coefficient of `ϑ^{(n)} ⊗ ϑ^{(0)}` in `Δ(x)` is the
`[E^{(n)}]`-coordinate of `x_n`. -/
theorem coprodK0_coeff_zero_right (n : ℕ) (x : K0ONH) :
    coeffAt (T (-2)) (n, 0) (coprodK0 x) = (basisE n).coord 0 (x n) := by
  have h : (coeffAt (T (-2)) (n, 0)).comp coprodK0.toLinearMap =
      ((basisE n).coord 0).comp (DFinsupp.lapply n) := by
    refine basisK0.ext fun k => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply, basisK0_apply,
      coprodK0_single, coeffAt_coprodVal, DFinsupp.lapply_apply]
    by_cases hk : k = n
    · subst hk
      rw [if_pos (add_zero k), DFinsupp.single_eq_same, ← basisE_apply k 0, Basis.coord_apply,
        Basis.repr_self, Finsupp.single_eq_same, mul_zero, Nat.cast_zero, neg_zero, T_zero]
    · rw [if_neg (by omega), DFinsupp.single_eq_of_ne hk, map_zero]
  exact DFunLike.congr_fun h x

end OddMath.Frontier.OddBialgebra
