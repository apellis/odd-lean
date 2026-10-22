/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CategoricalDividedPowers
import OddMath.QuiverHecke.DividedPowerModules
import OddMath.QuiverHecke.OddNilHeckeGrading
import OddMath.SKM.DividedPowerMultiplicity
import OddMath.CoveringQuantum.Integers
import StringDiagrams.Super.CoveringLaurent

/-!
# Odd categorical divided powers: BE2 Lemma 11.5

Brundan–Ellis, arXiv:1701.04133v2, the divided powers defined before Lemma 11.5 and the
lemma itself, for an odd colour `i` and `n ≥ 2` strands. BE2 defines `E_i^{(n)} 1_λ` as the
summand of `E_i^n 1_λ` cut out by `α_{n,λ}(1_{i^{(n)}})` in degree zero and parity zero, and
Lemma 11.5 asserts `[E_i^n 1_λ] = [n]^!_{q_i,π_i} [E_i^{(n)} 1_λ]`.

The odd splitting of Lemma 11.1 (`DividedPowerDecomposition.oddSplitting`), transported along
`α`, splits `E_i^n 1_λ` into the summands `Q^{2 d_i s} Π^s E_i^{(n)} 1_λ`, one for each EKL
index with shift `s`. Summing the monomials gives
`[E_i^n 1_λ] = q_i^{n(n-1)/2} π^{n(n-1)/2} [n]^!_{q_i,π} [E_i^{(n)} 1_λ]` for the printed
definition (`class_printed_odd`), and `[E_i^n 1_λ] = [n]^!_{q_i,π} [E_i^{(n)} 1_λ]` for the
divided power shifted by `Q^{d_i n(n-1)/2} Π^{n(n-1)/2}` (`class_corrected_odd`). When the
completed hom category has free `K₀` over `ℤ[q^±]` (`UDot.k0_free_laurentInt`), the printed
equation forces `[E_i^{(n)} 1_λ] = 0` (`printed_forces_zero_odd`).

## Main declarations

* `oddProjector`, `oddSummand`, `oddDividedPowerPrinted`, `oddDividedPowerCorrected`.
* `class_summands_odd`, `class_printed_odd`, `class_corrected_odd`, `printed_forces_zero_odd`.
-/

noncomputable section

namespace OddMath.QuiverHecke.CategoricalDividedPowers

open CategoryTheory StringDiagrams GradedSupercategory OddMath.SKM.Summands
open CategoryTheory.Idempotents LaurentPolynomial
open OddMath.Frontier OddMath.SKM.DividedPowerDecomposition OddMath.SKM.DividedPowerIdempotents
open OddMath.QuiverHecke.DividedPowerModules OddMath.CoveringQuantum BoxPartitionCount

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  {k : Type w} [CommRing k] (Sc : SKM.Scalars D k) (sy : SKM.Symmetrizer D)
  (hc : Sc.Homogeneous)

/-! ### `(q, π)`-factorials at `q_i = q^{d_i}` -/

section Coefficients

/-- The unit `q^d` of `Zπ[q^±]`. -/
def qUnitPi (d : ℤ) : (LaurentPolynomial Zπ)ˣ where
  val := T d
  inv := T (-d)
  val_inv := by rw [← T_add, add_neg_cancel, T_zero]
  inv_val := by rw [← T_add, neg_add_cancel, T_zero]

/-- `π ∈ Zπ[q^±]`. -/
abbrev piLP : LaurentPolynomial Zπ := C Zπ.π

theorem piLP_sq : piLP ^ 2 = 1 := by
  rw [piLP, ← map_pow, pow_two Zπ.π, Zπ.π_mul_π, map_one]

theorem val_qUnitPi_inv_zpow (d z : ℤ) :
    (((qUnitPi d)⁻¹ ^ z : (LaurentPolynomial Zπ)ˣ) : LaurentPolynomial Zπ) = T (-(d * z)) := by
  induction z using Int.induction_on with
  | zero => simp
  | succ z ih =>
    rw [zpow_add_one, Units.val_mul, ih]
    change T (-(d * z)) * T (-d) = _
    rw [← T_add]
    congr 1
    ring
  | pred z ih =>
    rw [zpow_sub_one, Units.val_mul, ih, inv_inv]
    change T (-(d * -z)) * T d = _
    rw [← T_add]
    congr 1
    ring

/-- The odd shifts, scaled by `d`, sum to `q^{d C} π^C [n]^!_{q^d,π}`, `C = n(n-1)/2`. -/
theorem sum_T_oddShift_mul (n : ℕ) (d : ℤ) :
    ∑ ℓ : Sq (n + 2), T (2 * d * shift n ℓ) * piLP ^ (shift n ℓ).toNat =
      T (((n + 2).choose 2 : ℤ) * d) * piLP ^ (n + 2).choose 2 *
        qpFact (qUnitPi d) piLP (n + 2) := by
  have h := sum_shift_monomial (qUnitPi d)⁻¹ piLP n
  rw [qpFact_inv piLP_sq] at h
  have h' := congrArg (fun x => T (((n + 2).choose 2 : ℤ) * d) * x) h
  simp only [Finset.mul_sum] at h'
  rw [← mul_assoc] at h'
  rw [← h']
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [val_qUnitPi_inv_zpow, show 2 * d * shift n ℓ = ((n + 2).choose 2 : ℤ) * d +
    -(d * (((n + 2).choose 2 : ℤ) - 2 * shift n ℓ)) by ring, T_add]
  ring

end Coefficients

/-! ### Lemma 11.5 for an odd colour -/

variable (i : I) (hi : D.parity i = 1) (n : ℕ) (ν : X)

/-- `α_{n,ν}(1_{i^{(n)}})` for `n + 2` strands of an odd colour. -/
def oddProjector : upWordHom D Sc sy hc i (n + 2) ν ⟶ upWordHom D Sc sy hc i (n + 2) ν :=
  alphaEnd D Sc sy hc i (n + 2) ν (oddCornerProjector D Sc i hi (n + 2))

theorem oddProjector_idem :
    oddProjector D Sc sy hc i hi n ν ≫ oddProjector D Sc sy hc i hi n ν =
      oddProjector D Sc sy hc i hi n ν := by
  rw [oddProjector, ← alphaEnd_mul, oddCornerProjector_idempotent]

theorem oddProjector_degree : oddProjector D Sc sy hc i hi n ν ∈ degree (R := k) _ _ 0 := by
  have h := oddNilHecke_mem_integerDegree D Sc sy i hi (oppositeProjector_degree n)
  rw [mul_zero] at h
  exact alphaEnd_mem_degree D Sc sy hc i (n + 2) ν h

theorem oddProjector_even :
    oddProjector D Sc sy hc i hi n ν ∈ Supercategory.parity (R := k) _ _ 0 := by
  have h := oddNilHecke_mem_parity D Sc i hi (oppositeProjector_degree n)
  rw [Int.cast_zero] at h
  exact alphaEnd_mem_parity D Sc sy hc i (n + 2) ν h

/-- The summand `Q^m Π^p (E_i^{n+2} 1_ν, α(1_{i^{(n+2)}}))` of the completed hom category. -/
abbrev oddSummand (m : ℤ) (p : ZMod 2) :=
  raw (oddProjector_idem D Sc sy hc i hi n ν) (oddProjector_degree D Sc sy hc i hi n ν)
    (oddProjector_even D Sc sy hc i hi n ν) m p

/-- BE2's divided power `E_i^{(n+2)} 1_ν`: the summand in degree zero and parity zero. -/
abbrev oddDividedPowerPrinted := oddSummand D Sc sy hc i hi n ν 0 0

/-- The divided power shifted by `Q^{d_i C} Π^C`, `C = (n+2)(n+1)/2`. -/
abbrev oddDividedPowerCorrected :=
  oddSummand D Sc sy hc i hi n ν (((n + 2).choose 2 : ℤ) * sy.d i) ((n + 2).choose 2 : ℕ)

/-- The odd splitting of Lemma 11.1 in the same-colour corner. -/
abbrev oddCornerSplitting :=
  oddSplittingMap (A := Corner D Sc i (n + 2)) (oddNilHecke D Sc i hi n)

/-- The categorical splitting: `[E_i^{n+2} 1_ν] = ∑_ℓ [Q^{2 d_i s_ℓ} Π^{s_ℓ} E_i^{(n+2)} 1_ν]`. -/
theorem class_summands_odd :
    K₀.mk (whole (upWordHom D Sc sy hc i (n + 2) ν)) =
      ∑ ℓ : Sq (n + 2), K₀.mk (oddSummand D Sc sy hc i hi n ν (2 * sy.d i * shift n ℓ)
        (shift n ℓ : ZMod 2)) := by
  let S := oddCornerSplitting D Sc i hi n
  refine class_whole _ _ _ (fun ℓ => 2 * sy.d i * shift n ℓ) (fun ℓ => (shift n ℓ : ZMod 2))
    (fun ℓ => alphaEnd D Sc sy hc i (n + 2) ν (S.σ ℓ))
    (fun ℓ => alphaEnd D Sc sy hc i (n + 2) ν (S.lam ℓ)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro ℓ
    exact alphaEnd_mem_degree D Sc sy hc i (n + 2) ν
      (oddNilHecke_mem_integerDegree D Sc sy i hi (sigma_degree n ℓ))
  · intro ℓ
    exact alphaEnd_mem_parity D Sc sy hc i (n + 2) ν
      (oddNilHecke_mem_parity D Sc i hi (sigma_degree n ℓ))
  · intro ℓ
    have h := oddNilHecke_mem_integerDegree D Sc sy i hi (lam_degree n ℓ)
    rw [mul_neg] at h
    exact alphaEnd_mem_degree D Sc sy hc i (n + 2) ν h
  · intro ℓ
    have h := oddNilHecke_mem_parity D Sc i hi (lam_degree n ℓ)
    rw [Int.cast_neg, ZMod.neg_eq_self_mod_two] at h
    exact alphaEnd_mem_parity D Sc sy hc i (n + 2) ν h
  · simp_rw [← alphaEnd_mul]
    rw [← alphaEnd_sum]
    exact (congrArg _ S.sum_eq).trans (alphaEnd_one D Sc sy hc i (n + 2) ν)
  · intro j l
    rw [← alphaEnd_mul]
    have h := S.orth l j
    rw [h]
    by_cases hjl : j = l
    · subst hjl; rw [ite_eq_left rfl, ite_eq_left rfl]; rfl
    · rw [ite_eq_right (Ne.symm hjl), ite_eq_right hjl, alphaEnd_zero]
  · intro j
    rw [oddProjector, ← alphaEnd_mul]
    exact congrArg _ (S.sigma_mul j)
  · intro j
    rw [oddProjector, ← alphaEnd_mul]
    exact congrArg _ (S.mul_lam j)

theorem class_oddSummand (m : ℤ) (s : ℕ) :
    letI := K₀.moduleLaurent k (HomCat D Sc sy hc i (n + 2) ν)
    K₀.mk (oddSummand D Sc sy hc i hi n ν m (s : ZMod 2)) =
      (T m * piLP ^ s) • K₀.mk (oddDividedPowerPrinted D Sc sy hc i hi n ν) := by
  let := K₀.moduleLaurent k (HomCat D Sc sy hc i (n + 2) ν)
  rw [mul_smul]
  have hp : ∀ s : ℕ, piLP ^ s • K₀.mk (oddDividedPowerPrinted D Sc sy hc i hi n ν) =
      K₀.mk (oddSummand D Sc sy hc i hi n ν 0 (s : ZMod 2)) := by
    intro s
    induction s with
    | zero => simp
    | succ s ih =>
      rw [pow_succ' piLP s, mul_smul, ih, class_raw_pi, Nat.cast_succ]
  rw [hp, class_raw_shift, zero_add]

/-- **BE2 Lemma 11.5 for an odd colour, with the printed divided power**:
`[E_i^{n+2} 1_ν] = q_i^C π^C [n+2]^!_{q_i,π} [E_i^{(n+2)} 1_ν]`, `C = (n+2)(n+1)/2`. -/
theorem class_printed_odd :
    letI := K₀.moduleLaurent k (HomCat D Sc sy hc i (n + 2) ν)
    K₀.mk (whole (upWordHom D Sc sy hc i (n + 2) ν)) =
      (T (((n + 2).choose 2 : ℤ) * sy.d i) * piLP ^ (n + 2).choose 2 *
        qpFact (qUnitPi (sy.d i)) piLP (n + 2)) •
        K₀.mk (oddDividedPowerPrinted D Sc sy hc i hi n ν) := by
  let := K₀.moduleLaurent k (HomCat D Sc sy hc i (n + 2) ν)
  rw [class_summands_odd, ← sum_T_oddShift_mul, Finset.sum_smul]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [← class_oddSummand, ← complement_eq_shift, Int.toNat_natCast]
  rfl

theorem class_corrected_shift :
    letI := K₀.moduleLaurent k (HomCat D Sc sy hc i (n + 2) ν)
    K₀.mk (oddDividedPowerCorrected D Sc sy hc i hi n ν) =
      (T (((n + 2).choose 2 : ℤ) * sy.d i) * piLP ^ (n + 2).choose 2) •
        K₀.mk (oddDividedPowerPrinted D Sc sy hc i hi n ν) :=
  class_oddSummand D Sc sy hc i hi n ν _ _

/-- **BE2 Lemma 11.5 for an odd colour, corrected**:
`[E_i^{n+2} 1_ν] = [n+2]^!_{q_i,π} [Q^{d_i C} Π^C E_i^{(n+2)} 1_ν]`. -/
theorem class_corrected_odd :
    letI := K₀.moduleLaurent k (HomCat D Sc sy hc i (n + 2) ν)
    K₀.mk (whole (upWordHom D Sc sy hc i (n + 2) ν)) =
      qpFact (qUnitPi (sy.d i)) piLP (n + 2) •
        K₀.mk (oddDividedPowerCorrected D Sc sy hc i hi n ν) := by
  have hcomm : qpFact (qUnitPi (sy.d i)) piLP (n + 2) *
      (T (((n + 2).choose 2 : ℤ) * sy.d i) * piLP ^ (n + 2).choose 2) =
      T (((n + 2).choose 2 : ℤ) * sy.d i) * piLP ^ (n + 2).choose 2 *
        qpFact (qUnitPi (sy.d i)) piLP (n + 2) := by ring
  let := K₀.moduleLaurent k (HomCat D Sc sy hc i (n + 2) ν)
  rw [class_corrected_shift, ← mul_smul, hcomm, class_printed_odd]

/-! ### The printed normalization fails for odd colours -/

section Obstruction

open StringDiagrams.CoveringLaurent

/-- `q_i = q^d` and `π = ε` in `ℤ[q^±]`: `[m]_{q_i,ε} ≠ 0` for `m ≥ 1`, `d > 0`, `ε = ±1`. -/
theorem qpNat_qUnit_ne_zero {d : ℤ} (hd : 0 < d) {ε : ℤ} {m : ℕ}
    (hm : 1 ≤ m) : qpNat (qUnit d) (C ε : LaurentPolynomial ℤ) m ≠ 0 := by
  intro h
  have h' := qpNat_mul_sub (q := qUnit d) (π := (C ε : LaurentPolynomial ℤ)) m
  rw [h, mul_zero, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, inv_pow,
    ← zpow_natCast, ← zpow_neg, val_qUnit_zpow, val_qUnit_zpow, ← map_pow,
    ← single_eq_C_mul_T] at h'
  rw [eq_comm, sub_eq_zero] at h'
  have hc := congrArg (fun p : LaurentPolynomial ℤ => p.coeff ((m : ℤ) * d)) h'
  have hne : -(m : ℤ) * d ≠ (m : ℤ) * d := by
    have : (0 : ℤ) < m := by exact_mod_cast hm
    nlinarith
  simp only [T, AddMonoidAlgebra.coeff_single, Finsupp.single_apply, hne, ↓reduceIte] at hc
  exact one_ne_zero hc

theorem qpFact_qUnit_ne_zero' {d : ℤ} (hd : 0 < d) (ε : ℤ) (m : ℕ) :
    qpFact (qUnit d) (C ε : LaurentPolynomial ℤ) m ≠ 0 := by
  induction m with
  | zero => simp
  | succ m ih => rw [qpFact_succ]; exact mul_ne_zero (qpNat_qUnit_ne_zero hd (by omega)) ih

theorem T_mul_C_sub_one_ne_zero {m : ℤ} (hm : m ≠ 0) {ε : ℤ} (hε : ε ≠ 0) :
    (T m * C ε - 1 : LaurentPolynomial ℤ) ≠ 0 := by
  intro h
  rw [mul_comm, ← single_eq_C_mul_T, ← T_zero, sub_eq_zero] at h
  have hc := congrArg (fun p : LaurentPolynomial ℤ => p.coeff m) h
  simp only [T, AddMonoidAlgebra.coeff_single, Finsupp.single_apply, hm.symm, ↓reduceIte] at hc
  exact hε hc

theorem eval_T (ε : ℤ) (hε : ε * ε = 1) (d : ℤ) : CoveringLaurent.eval ε hε (T d) = T d := by
  rw [CoveringLaurent.eval, T, AddMonoidAlgebra.mapRingHom_single, map_one]
  rfl

theorem eval_qUnitPi (ε : ℤ) (hε : ε * ε = 1) (d : ℤ) :
    Units.map (CoveringLaurent.eval ε hε).toMonoidHom (qUnitPi d) = qUnit d := by
  apply Units.ext
  change CoveringLaurent.eval ε hε (T d) = _
  rw [eval_T, qUnit, Categorification.KLR.val_qUnitLP_zpow]

/-- Both specializations of the defect `(q_i^C π^C - 1) [n]^!_{q_i,π}` are nonzero. -/
theorem eval_defect_ne_zero (ε : ℤ) (hε : ε * ε = 1) {C2 : ℕ} {d : ℤ} (hC : 0 < C2)
    (hd : 0 < d) (m : ℕ) :
    CoveringLaurent.eval ε hε ((T ((C2 : ℤ) * d) * piLP ^ C2 - 1) * qpFact (qUnitPi d) piLP m) ≠ 0 := by
  have hp : CoveringLaurent.eval ε hε piLP = C ε := eval_pi ε hε
  have hf : CoveringLaurent.eval ε hε (qpFact (qUnitPi d) piLP m) = qpFact (qUnit d) (C ε) m :=
    (map_qpFact (q := qUnitPi d) (π := piLP) (CoveringLaurent.eval ε hε) m).trans
      (by rw [eval_qUnitPi, hp])
  rw [map_mul, map_sub, map_mul, map_pow, eval_T, map_one, hf, hp, ← map_pow]
  refine mul_ne_zero (T_mul_C_sub_one_ne_zero (by positivity) ?_) (qpFact_qUnit_ne_zero' hd _ _)
  exact pow_ne_zero _ (fun h0 => by simp [h0] at hε)

/-- In a module over `Zπ[q^±]` that is free over `ℤ[q^±]`, an element whose two
specializations `π = ±1` are nonzero kills only zero. -/
theorem eq_zero_of_smul_eq_zero {M : Type*} [AddCommGroup M] [Module (LaurentPolynomial Zπ) M]
    [Module (LaurentPolynomial ℤ) M]
    (hcomp : ∀ (r : LaurentPolynomial ℤ) (x : M), r • x = inclusion r • x)
    [Module.Free (LaurentPolynomial ℤ) M] {c : LaurentPolynomial Zπ} {x : M} (h : c • x = 0)
    (h₁ : CoveringLaurent.eval 1 (by norm_num) c ≠ 0) (h₂ : CoveringLaurent.eval (-1) (by norm_num) c ≠ 0) : x = 0 := by
  obtain ⟨a, b, rfl⟩ := exists_pair c
  have hN : inclusion (a * a - b * b) =
      (inclusion a - inclusion b * CoveringLaurent.pi) *
        (inclusion a + inclusion b * CoveringLaurent.pi) := by
    rw [map_sub, map_mul, map_mul]
    linear_combination (inclusion b * inclusion b) * pi_sq
  have hx : (a * a - b * b) • x = 0 := by
    rw [hcomp, hN, mul_smul, h, smul_zero]
  have e₁ : CoveringLaurent.eval 1 (by norm_num) (inclusion a + inclusion b * CoveringLaurent.pi) = a + b := by
    simp only [map_add, map_mul, eval_inclusion, eval_pi, map_one, mul_one]
  have e₂ : CoveringLaurent.eval (-1) (by norm_num) (inclusion a + inclusion b * CoveringLaurent.pi) =
      a - b := by
    simp only [map_add, map_mul, eval_inclusion, eval_pi, map_neg, map_one, mul_neg, mul_one,
      sub_eq_add_neg]
  rw [e₁] at h₁
  rw [e₂] at h₂
  have hne : a * a - b * b ≠ 0 := by
    rw [show a * a - b * b = (a + b) * (a - b) by ring]
    exact mul_ne_zero h₁ h₂
  exact (smul_eq_zero.mp hx).resolve_left hne

theorem int_smul_eq (r : LaurentPolynomial ℤ) (x : K₀ (HomCat D Sc sy hc i (n + 2) ν)) :
    (letI := K₀.moduleLaurentInt k (HomCat D Sc sy hc i (n + 2) ν); r • x) =
      (letI := K₀.moduleLaurent k (HomCat D Sc sy hc i (n + 2) ν); inclusion r • x) := rfl

/-- The defect of the printed normalization kills the printed class. -/
theorem defect_smul_printed
    (h : letI := K₀.moduleLaurent k (HomCat D Sc sy hc i (n + 2) ν)
      K₀.mk (whole (upWordHom D Sc sy hc i (n + 2) ν)) =
        qpFact (qUnitPi (sy.d i)) piLP (n + 2) •
          K₀.mk (oddDividedPowerPrinted D Sc sy hc i hi n ν)) :
    letI := K₀.moduleLaurent k (HomCat D Sc sy hc i (n + 2) ν)
    ((T (((n + 2).choose 2 : ℤ) * sy.d i) * piLP ^ (n + 2).choose 2 - 1) *
        qpFact (qUnitPi (sy.d i)) piLP (n + 2)) •
      K₀.mk (oddDividedPowerPrinted D Sc sy hc i hi n ν) = 0 := by
  let := K₀.moduleLaurent k (HomCat D Sc sy hc i (n + 2) ν)
  rw [sub_mul, one_mul, sub_smul, sub_eq_zero]
  exact (class_printed_odd D Sc sy hc i hi n ν).symm.trans h

omit [CommRing k] in
/-- **The printed normalization of Lemma 11.5 fails for odd colours.** Over a field, for finitely
many symmetrizer values in each degree (`UDot.k0_free_laurentInt`), the printed equation
`[E_i^{n+2} 1_ν] = [n+2]^!_{q_i,π} [E_i^{(n+2)} 1_ν]` forces `[E_i^{(n+2)} 1_ν] = 0`. -/
theorem printed_forces_zero_odd {k : Type w} [Field k] {Sc : SKM.Scalars D k}
    (cs : SKM.CScalars Sc) (hc : Sc.Homogeneous) (hf : sy.DegreeLocallyFinite)
    (h : letI := K₀.moduleLaurent k (HomCat D Sc sy hc i (n + 2) ν)
      K₀.mk (whole (upWordHom D Sc sy hc i (n + 2) ν)) =
        qpFact (qUnitPi (sy.d i)) piLP (n + 2) •
          K₀.mk (oddDividedPowerPrinted D Sc sy hc i hi n ν)) :
    K₀.mk (oddDividedPowerPrinted D Sc sy hc i hi n ν) = 0 := by
  let := K₀.moduleLaurent k (HomCat D Sc sy hc i (n + 2) ν)
  let := K₀.moduleLaurentInt k (HomCat D Sc sy hc i (n + 2) ν)
  have hfree : Module.Free (LaurentPolynomial ℤ) (K₀ (HomCat D Sc sy hc i (n + 2) ν)) :=
    SKM.UDot.k0_free_laurentInt sy cs hc hf _ _
  have hC : 0 < (n + 2).choose 2 := Nat.choose_pos (by omega)
  exact eq_zero_of_smul_eq_zero (int_smul_eq D Sc sy hc i n ν)
    (defect_smul_printed D Sc sy hc i hi n ν h)
    (eval_defect_ne_zero 1 (by norm_num) hC (sy.pos i) _)
    (eval_defect_ne_zero (-1) (by norm_num) hC (sy.pos i) _)

end Obstruction

end OddMath.QuiverHecke.CategoricalDividedPowers
