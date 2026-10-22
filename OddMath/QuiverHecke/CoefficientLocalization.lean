/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.PairingRadical
import Mathlib.RingTheory.Localization.Integral

/-!
# `ℚ(q)[π]/(π² - 1)` is a localization of `ℤ[q, q⁻¹, π]/(π² - 1)`

Brundan–Ellis, arXiv:1701.04133v2, §9 uses two coefficient rings: `ℒ = ℤ[q, q⁻¹, π]/(π² - 1)`
(here `LaurentPolynomial Zπ`) and `𝕃 = ℚ(q)[π]/(π² - 1)` (here `Coefficients.Ring`). The proof of
Theorem 11.7 extends scalars from `ℒ` to `𝕃` and uses that this loses nothing on modules without
`ℤ[q, q⁻¹]`-torsion. This file supplies the coefficient facts:

* `Coefficients.ofLaurent_injective`: `ℒ → 𝕃` is injective;
* `Coefficients.isLocalization`: `𝕃` is the localization of `ℒ` at the nonzero elements of
  `ℤ[q, q⁻¹]` (`Coefficients.intDenominators`);
* `Coefficients.qpFact_isUnit`: the `(q_i, π_i)`-factorials are units of `𝕃`, so the divided powers
  `e_i^{(n)} 1_λ`, `f_i^{(n)} 1_λ` of (9.5) are honest quotients.
-/

noncomputable section

open LaurentPolynomial

namespace OddMath.CoveringQuantum.Coefficients

open StringDiagrams

/-- The inclusion `ℤ[q, q⁻¹] → ℚ(q)`. -/
def ratOfInt : LaurentPolynomial ℤ →+* RatFunc ℚ :=
  LaurentPolynomial.eval₂ (Int.castRingHom _) (Units.mk0 RatFunc.X RatFunc.X_ne_zero)

/-- The inclusion `ℤ[q, q⁻¹] → ℤ[q, q⁻¹, π]/(π² - 1)`. -/
def intToLaurent : LaurentPolynomial ℤ →+* LaurentPolynomial Zπ :=
  AddMonoidAlgebra.mapRingHom ℤ (Int.castRingHom Zπ)

theorem intToLaurent_C_mul_T (a : ℤ) (n : ℤ) :
    intToLaurent (C a * T n) = C (a : Zπ) * T n := by
  rw [← single_eq_C_mul_T, ← single_eq_C_mul_T]
  exact AddMonoidAlgebra.mapRingHom_single _ _ _

theorem ratOfInt_toLaurent (f : Polynomial ℤ) :
    ratOfInt (Polynomial.toLaurent f) =
      algebraMap (Polynomial ℚ) (RatFunc ℚ) (f.map (Int.castRingHom ℚ)) := by
  change (ratOfInt.comp Polynomial.toLaurent) f =
    ((algebraMap (Polynomial ℚ) (RatFunc ℚ)).comp (Polynomial.mapRingHom (Int.castRingHom ℚ))) f
  congr 1
  apply Polynomial.ringHom_ext'
  · exact Subsingleton.elim _ _
  · change ratOfInt (Polynomial.toLaurent Polynomial.X) =
      algebraMap (Polynomial ℚ) (RatFunc ℚ) (Polynomial.map (Int.castRingHom ℚ) Polynomial.X)
    rw [Polynomial.toLaurent_X, ratOfInt, eval₂_T, zpow_one, Polynomial.map_X, RatFunc.algebraMap_X]
    rfl

theorem ratOfInt_injective : Function.Injective ratOfInt := by
  rw [injective_iff_map_eq_zero]
  intro p hp
  obtain ⟨n, f, hf⟩ := p.exists_T_pow
  have h0 : ratOfInt (Polynomial.toLaurent f) = 0 := by rw [hf, map_mul, hp, zero_mul]
  rw [ratOfInt_toLaurent] at h0
  have hf0 : f = 0 := by
    have h1 := (IsFractionRing.injective (Polynomial ℚ) (RatFunc ℚ)) (h0.trans (map_zero _).symm)
    exact Polynomial.map_injective _ (RingHom.injective_int (Int.castRingHom ℚ))
      (h1.trans (Polynomial.map_zero _).symm)
  rw [hf0, map_zero] at hf
  have h2 := congrArg (· * T (-(n : ℤ))) hf
  simp only [zero_mul] at h2
  rw [mul_assoc, ← T_add, add_neg_cancel, T_zero, mul_one] at h2
  exact h2.symm

theorem ofLaurent_C_pi : ofLaurent (C Zπ.π) = pi := by
  rw [ofLaurent, eval₂_C, ofZπ_π]

/-- `ℤ[q, q⁻¹] → ℒ → 𝕃` is `ℤ[q, q⁻¹] → ℚ(q) → 𝕃`. -/
theorem ofLaurent_intToLaurent (p : LaurentPolynomial ℤ) :
    ofLaurent (intToLaurent p) = algebraMap (RatFunc ℚ) Ring (ratOfInt p) := by
  induction p using LaurentPolynomial.induction_on' with
  | add p p' hp hp' => rw [map_add, map_add, hp, hp', map_add, map_add]
  | C_mul_T n a =>
    rw [intToLaurent_C_mul_T]
    simp only [map_mul, ofLaurent, ratOfInt, eval₂_T, q, ← map_zpow, Units.coe_map,
      map_intCast, eq_intCast, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]

/-- Every element of `ℒ` is `u + π v` with `u, v ∈ ℤ[q, q⁻¹]`. -/
theorem exists_eq_intToLaurent (r : LaurentPolynomial Zπ) :
    ∃ u v : LaurentPolynomial ℤ, r = intToLaurent u + C Zπ.π * intToLaurent v := by
  induction r using LaurentPolynomial.induction_on' with
  | add p p' hp hp' =>
    obtain ⟨u, v, rfl⟩ := hp
    obtain ⟨u', v', rfl⟩ := hp'
    exact ⟨u + u', v + v', by rw [map_add, map_add]; ring⟩
  | C_mul_T n a =>
    obtain ⟨a, b, rfl⟩ := Zπ.exists_eq_add_mul_π a
    refine ⟨C a * T n, C b * T n, ?_⟩
    rw [intToLaurent_C_mul_T, intToLaurent_C_mul_T, map_add, map_mul]
    ring

theorem ofLaurent_eq (u v : LaurentPolynomial ℤ) :
    ofLaurent (intToLaurent u + C Zπ.π * intToLaurent v) =
      algebraMap (RatFunc ℚ) Ring (ratOfInt u) + algebraMap (RatFunc ℚ) Ring (ratOfInt v) * pi := by
  rw [map_add, map_mul, ofLaurent_intToLaurent, ofLaurent_intToLaurent, ofLaurent_C_pi, mul_comm]

/-- **`ℒ → 𝕃` is injective.** -/
theorem ofLaurent_injective : Function.Injective ofLaurent := by
  rw [injective_iff_map_eq_zero]
  intro r hr
  obtain ⟨u, v, rfl⟩ := exists_eq_intToLaurent r
  rw [ofLaurent_eq] at hr
  have h1 := congrArg (specialize 1 (one_pow 2)) hr
  have h2 := congrArg (specialize (-1) (by norm_num)) hr
  simp only [map_add, map_mul, specialize_pi, map_zero, AlgHom.commutes, Algebra.algebraMap_self,
    RingHom.id_apply] at h1 h2
  have hu : ratOfInt u = 0 := by linear_combination (h1 + h2) / 2
  have hv : ratOfInt v = 0 := by linear_combination (h1 - h2) / 2
  rw [ratOfInt_injective (hu.trans (map_zero _).symm), ratOfInt_injective (hv.trans (map_zero _).symm),
    map_zero, mul_zero, add_zero]

/-- Every rational function is a quotient of elements of `ℤ[q, q⁻¹]`. -/
theorem exists_ratOfInt_mul (c : RatFunc ℚ) :
    ∃ n s : LaurentPolynomial ℤ, ratOfInt s ≠ 0 ∧ c * ratOfInt s = ratOfInt n := by
  obtain ⟨b₁, hb₁, hn⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) c.num
  obtain ⟨b₂, hb₂, hd⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) c.denom
  set n₁ := IsLocalization.integerNormalization (nonZeroDivisors ℤ) c.num
  set d₁ := IsLocalization.integerNormalization (nonZeroDivisors ℤ) c.denom
  have hb₁' : (b₁ : RatFunc ℚ) ≠ 0 := by
    exact_mod_cast nonZeroDivisors.ne_zero hb₁
  have hb₂' : (b₂ : RatFunc ℚ) ≠ 0 := by
    exact_mod_cast nonZeroDivisors.ne_zero hb₂
  have hN : ratOfInt (Polynomial.toLaurent n₁) =
      (b₁ : RatFunc ℚ) * algebraMap (Polynomial ℚ) (RatFunc ℚ) c.num := by
    rw [ratOfInt_toLaurent]
    change algebraMap _ _ (n₁.map (algebraMap ℤ ℚ)) = _
    rw [hn, zsmul_eq_mul, map_mul, map_intCast]
  have hD : ratOfInt (Polynomial.toLaurent d₁) =
      (b₂ : RatFunc ℚ) * algebraMap (Polynomial ℚ) (RatFunc ℚ) c.denom := by
    rw [ratOfInt_toLaurent]
    change algebraMap _ _ (d₁.map (algebraMap ℤ ℚ)) = _
    rw [hd, zsmul_eq_mul, map_mul, map_intCast]
  have hden : algebraMap (Polynomial ℚ) (RatFunc ℚ) c.denom ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (Polynomial ℚ) (RatFunc ℚ))).mpr c.denom_ne_zero
  have hc : c * algebraMap (Polynomial ℚ) (RatFunc ℚ) c.denom =
      algebraMap (Polynomial ℚ) (RatFunc ℚ) c.num := by
    calc c * algebraMap (Polynomial ℚ) (RatFunc ℚ) c.denom
        = algebraMap (Polynomial ℚ) (RatFunc ℚ) c.num / algebraMap (Polynomial ℚ) (RatFunc ℚ) c.denom *
          algebraMap (Polynomial ℚ) (RatFunc ℚ) c.denom := by rw [RatFunc.num_div_denom]
      _ = _ := div_mul_cancel₀ _ hden
  have hC : ∀ b : ℤ, ratOfInt (C b) = b := fun b ↦ by
    change LaurentPolynomial.eval₂ _ _ (C b) = _
    rw [eval₂_C, eq_intCast]
  refine ⟨C b₂ * Polynomial.toLaurent n₁, C b₁ * Polynomial.toLaurent d₁, ?_, ?_⟩
  · rw [map_mul, hD, hC]
    exact mul_ne_zero hb₁' (mul_ne_zero hb₂' hden)
  · rw [map_mul, map_mul, hD, hN, hC, hC]
    linear_combination (b₁ : RatFunc ℚ) * b₂ * hc

/-! ### `𝕃` as a localization of `ℒ` -/

/-- The nonzero elements of `ℤ[q, q⁻¹]`, inside `ℒ`. -/
def intDenominators : Submonoid (LaurentPolynomial Zπ) :=
  ((nonZeroDivisors (RatFunc ℚ)).comap ratOfInt).map intToLaurent

/-- `𝕃` as an `ℒ`-algebra, through `ofLaurent`. -/
instance algebraLaurent : Algebra (LaurentPolynomial Zπ) Ring :=
  @RingHom.toAlgebra (LaurentPolynomial Zπ) Ring _ _ ofLaurent

/-- `ofLaurent` as the algebra map, with the commutative-semiring instance path of `Algebra`. -/
abbrev ofLaurentHom := @algebraMap (LaurentPolynomial Zπ) Coefficients.Ring _ _ algebraLaurent

theorem ofLaurentHom_apply (r : LaurentPolynomial Zπ) : ofLaurentHom r = ofLaurent r := rfl

theorem smul_one_eq_ofLaurent (r : LaurentPolynomial Zπ) : r • (1 : Ring) = ofLaurent r := by
  rw [Algebra.smul_def, mul_one]
  rfl

/-- **`𝕃 = ℚ(q)[π]/(π² - 1)` is the localization of `ℒ = ℤ[q, q⁻¹, π]/(π² - 1)` at the nonzero
elements of `ℤ[q, q⁻¹]`.** -/
theorem isLocalization : IsLocalization (R := LaurentPolynomial Zπ) intDenominators Ring := by
  rw [isLocalization_iff (R := LaurentPolynomial Zπ)]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, p, hp, rfl⟩
    change IsUnit (ofLaurent (intToLaurent p))
    rw [ofLaurent_intToLaurent]
    exact (IsUnit.mk0 _ (nonZeroDivisors.ne_zero (Submonoid.mem_comap.mp hp))).map _
  · intro z
    set a := (specialize 1 (one_pow 2) z + specialize (-1) (by norm_num) z) / 2
    set b := (specialize 1 (one_pow 2) z - specialize (-1) (by norm_num) z) / 2
    have hz : z = algebraMap (RatFunc ℚ) Ring a + algebraMap (RatFunc ℚ) Ring b * pi := by
      rw [eq_iff_specialize_eq]
      simp only [map_add, map_mul, specialize_pi, AlgHom.commutes, Algebra.algebraMap_self,
        RingHom.id_apply, a, b]
      constructor <;> ring
    obtain ⟨na, sa, hsa, ha⟩ := exists_ratOfInt_mul a
    obtain ⟨nb, sb, hsb, hb⟩ := exists_ratOfInt_mul b
    refine ⟨⟨intToLaurent (na * sb) + C Zπ.π * intToLaurent (nb * sa),
      ⟨intToLaurent (sa * sb), sa * sb, ?_, rfl⟩⟩, ?_⟩
    · exact Submonoid.mem_comap.mpr (mem_nonZeroDivisors_of_ne_zero (by
        rw [map_mul]; exact mul_ne_zero hsa hsb))
    · change z * ofLaurent (intToLaurent (sa * sb)) = ofLaurent _
      rw [ofLaurent_eq, ofLaurent_intToLaurent, hz]
      have ha' := congrArg (algebraMap (RatFunc ℚ) Ring) ha
      have hb' := congrArg (algebraMap (RatFunc ℚ) Ring) hb
      simp only [map_mul] at ha' hb' ⊢
      linear_combination algebraMap (RatFunc ℚ) Ring (ratOfInt sb) * ha' +
        algebraMap (RatFunc ℚ) Ring (ratOfInt sa) * pi * hb'
  · intro x y h
    exact ⟨1, by rw [ofLaurent_injective h]⟩

/-! ### Quantum factorials are units of `𝕃` -/

variable {I : Type*} (C : SuperCartanDatum I)

private theorem pow_sub_isUnit (i : I) {m : ℕ} (hm : 0 < m) {ε : Ring} (hε : ε ^ 2 = 1) :
    IsUnit (((C.qi q i : Ringˣ) : Ring) ^ m - ε * (((C.qi q i)⁻¹ : Ringˣ) : Ring) ^ m) := by
  set Q : Ring := ((C.qi q i : Ringˣ) : Ring)
  set Qi : Ring := (((C.qi q i)⁻¹ : Ringˣ) : Ring)
  have hQQ : (Q * Qi) ^ m = 1 := by rw [show Q * Qi = 1 from (C.qi q i).mul_inv, one_pow]
  have hQ : Q ^ (2 * m) = (q : Ring) ^ (C.d i * (2 * m)) := by
    simp only [Q, SuperCartanDatum.qi, Units.val_pow_eq_pow_val, ← pow_mul]
  have hu := one_sub_isUnit ε hε (n := C.d i * (2 * m)) (Nat.mul_pos (C.d_pos i) (by omega))
  rw [← hQ] at hu
  refine isUnit_of_mul_isUnit_left (y := -ε * Q ^ m) ?_
  convert hu using 1
  linear_combination (Q * Qi) ^ m * hε + hQQ

/-- The `(q_i, π_i)`-integers `[n]_{q_i, π_i}`, `n > 0`, are units of `𝕃`. -/
theorem qpNat_isUnit (i : I) {n : ℕ} (hn : 0 < n) : IsUnit (qpNat (C.qi q i) (C.pii pi i) n) := by
  have hε := C.pii_sq pi pi_sq i
  have h := qpNat_mul_sub (q := C.qi q i) (π := C.pii pi i) n
  have hv := pow_sub_isUnit C i hn (ε := C.pii pi i ^ n)
    (by rw [← pow_mul, mul_comm, pow_mul, hε, one_pow])
  rw [← h] at hv
  exact isUnit_of_mul_isUnit_right hv

/-- **The `(q_i, π_i)`-factorials are units of `𝕃`.** -/
theorem qpFact_isUnit (i : I) (n : ℕ) : IsUnit (qpFact (C.qi q i) (C.pii pi i) n) := by
  induction n with
  | zero => exact isUnit_one
  | succ n ih => rw [qpFact_succ]; exact (qpNat_isUnit C i n.succ_pos).mul ih

end OddMath.CoveringQuantum.Coefficients
