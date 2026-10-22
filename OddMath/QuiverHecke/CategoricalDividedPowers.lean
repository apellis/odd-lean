/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.EvenDividedPower
import OddMath.QuiverHecke.AlgebraMaps
import OddMath.SKM.IdempotentSummands
import OddMath.SKM.LaurentianK0

/-!
# Even categorical divided powers: BE2 Lemma 11.5

Brundan–Ellis, arXiv:1701.04133v2, the divided powers defined before Lemma 11.5 and the
lemma itself, for an even colour `i`. BE2 defines `E_i^{(n)} 1_λ` as the summand of
`E_i^n 1_λ` cut out by `α_{n,λ}(1_{i^{(n)}})` in degree zero, and Lemma 11.5 asserts
`[E_i^n 1_λ] = [n]^!_{q_i} [E_i^{(n)} 1_λ]`.

Transporting the splitting of Lemma 11.1 (`evenCornerSplitting`) along `α` gives
`[E_i^n 1_λ] = q_i^{n(n-1)/2} [n]^!_{q_i} [E_i^{(n)} 1_λ]` for the printed definition
(`class_printed`), and `[E_i^n 1_λ] = [n]^!_{q_i} [E_i^{(n)} 1_λ]` for the divided power
shifted by `Q^{d_i n(n-1)/2}` (`class_corrected`), the shift of `P(i^{(n)})` in (11.3) read in
the opposite direction. When the completed hom category is Krull–Schmidt with free Laurent
`K₀` (`UDot.k0_free_laurentInt`), the printed equation forces `[E_i^{(n)} 1_λ] = 0` for
`n ≥ 2` (`printed_forces_zero`).

## Main declarations

* `upWordHom i n ν`: the 1-morphism `E_i^n 1_ν`; `alphaEnd`, the map on 2-endomorphisms.
* `dividedPowerPrinted`, `dividedPowerCorrected`.
* `class_printed`, `class_corrected`, `printed_forces_zero`.
-/

noncomputable section

namespace OddMath.QuiverHecke.CategoricalDividedPowers

open CategoryTheory StringDiagrams GradedSupercategory OddMath.SKM.Summands
open CategoryTheory.Idempotents LaurentPolynomial
open Categorification Categorification.KLR

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  {k : Type w} [CommRing k] (Sc : SKM.Scalars D k) (sy : SKM.Symmetrizer D)
  (hc : Sc.Homogeneous)

/-- The 1-morphism `E_i^n 1_ν`. -/
def upWordHom (i : I) (n : ℕ) (ν : X) :
    (show SKM.UGr D Sc sy hc from ⟨SKM.wt (X := X) D ν (upWord (List.replicate n i))⟩) ⟶
      (show SKM.UGr D Sc sy hc from ⟨ν⟩) :=
  ⟨SKM.ob D ν (upWord (List.replicate n i)), rfl, SKM.ok_wd D ν _, SKM.ob_endR D ν _⟩

/-- The completed hom category containing `E_i^n 1_ν`. -/
abbrev HomCat (i : I) (n : ℕ) (ν : X) :=
  Karoubi (Mat_ (Base (show SKM.UGr D Sc sy hc from
    ⟨SKM.wt (X := X) D ν (upWord (List.replicate n i))⟩) (show SKM.UGr D Sc sy hc from ⟨ν⟩)))

/-- Equation (11.7) on the same-colour corner: weight labelling at `ν`. -/
def alphaEnd (i : I) (n : ℕ) (ν : X) (c : Corner D Sc i n) :
    upWordHom D Sc sy hc i n ν ⟶ upWordHom D Sc sy hc i n ν :=
  (alpha D Sc ν).map c

theorem alphaEnd_mul (i : I) (n : ℕ) (ν : X) (c c' : Corner D Sc i n) :
    alphaEnd D Sc sy hc i n ν (c * c') =
      alphaEnd D Sc sy hc i n ν c' ≫ alphaEnd D Sc sy hc i n ν c :=
  (alpha D Sc ν).map_comp c' c

theorem alphaEnd_one (i : I) (n : ℕ) (ν : X) :
    alphaEnd D Sc sy hc i n ν 1 = 𝟙 _ :=
  (alpha D Sc ν).map_id _

theorem alphaEnd_zero (i : I) (n : ℕ) (ν : X) :
    alphaEnd D Sc sy hc i n ν 0 = 0 :=
  (alpha D Sc ν).map_zero _ _

theorem alphaEnd_sum (i : I) (n : ℕ) (ν : X) {J : Type*} (s : Finset J)
    (c : J → Corner D Sc i n) :
    alphaEnd D Sc sy hc i n ν (∑ j ∈ s, c j) = ∑ j ∈ s, alphaEnd D Sc sy hc i n ν (c j) :=
  (alpha D Sc ν).map_sum _ _

theorem alphaEnd_mem_degree (i : I) (n : ℕ) (ν : X) {c : Corner D Sc i n} {d : ℤ}
    (h : c ∈ cornerDeg D Sc (gdeg D sy) i n d) :
    alphaEnd D Sc sy hc i n ν c ∈ degree (R := k) _ _ d :=
  alpha_mem_degree D Sc sy ν h

theorem alphaEnd_mem_parity (i : I) (n : ℕ) (ν : X) {c : Corner D Sc i n} {p : ZMod 2}
    (h : c ∈ cornerDeg D Sc (Presentation.parityDeg (sig D)) i n p) :
    alphaEnd D Sc sy hc i n ν c ∈ Supercategory.parity (R := k) _ _ p :=
  alpha_mem_parity D Sc ν h

/-! ### Quantum factorials at `q_i = q^{d_i}` -/

section Coefficients

/-- `ℤ[q^±] → ℤ[q^±]`, `q ↦ q^d`. -/
def scaleHom (d : ℤ) : LaurentPolynomial ℤ →+* LaurentPolynomial ℤ :=
  AddMonoidAlgebra.mapDomainRingHom ℤ (AddMonoidHom.mulRight d)

theorem scaleHom_T (d n : ℤ) : scaleHom d (T n) = T (n * d) := by
  rw [scaleHom, T, AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.mapDomain_single]
  rfl

/-- The unit `q_i = q^d`. -/
abbrev qUnit (d : ℤ) : (LaurentPolynomial ℤ)ˣ := qUnitLP ^ d

theorem val_qUnit_zpow (d z : ℤ) : ((qUnit d ^ z : (LaurentPolynomial ℤ)ˣ) : LaurentPolynomial ℤ) =
    T (z * d) := by
  rw [qUnit, ← zpow_mul, val_qUnitLP_zpow, mul_comm]

theorem scaleHom_qint (d : ℤ) (n : ℕ) :
    scaleHom d (QuantumGroup.qint qUnitLP n) = QuantumGroup.qint (qUnit d) n := by
  rw [qint_qUnitLP, map_sum, QuantumGroup.qint_eq_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [scaleHom_T, val_qUnit_zpow]

theorem scaleHom_qfact (d : ℤ) (n : ℕ) :
    scaleHom d (QuantumGroup.qfact qUnitLP n) = QuantumGroup.qfact (qUnit d) n := by
  induction n with
  | zero => simp [QuantumGroup.qfact]
  | succ n ih => rw [QuantumGroup.qfact_succ, QuantumGroup.qfact_succ, map_mul, ih, scaleHom_qint]

/-- The even shifts, scaled by `d`, sum to `q^{d n(n-1)/2} [n]^!_{q^d}`. -/
theorem sum_T_evenShift_mul (r : ℕ) (d : ℤ) :
    ∑ j : evenIndex r, (T (evenShift r j * d) : LaurentPolynomial ℤ) =
      T ((r.choose 2 : ℤ) * d) * QuantumGroup.qfact (qUnit d) r := by
  have h := congrArg (scaleHom d) (sum_T_evenShift r)
  rw [map_sum, map_mul, scaleHom_T, scaleHom_qfact] at h
  simpa only [scaleHom_T] using h

theorem sum_T_evenShift_mul_sub (r : ℕ) (d : ℤ) :
    ∑ j : evenIndex r, (T (evenShift r j * d - (r.choose 2 : ℤ) * d) : LaurentPolynomial ℤ) =
      QuantumGroup.qfact (qUnit d) r := by
  have h : ∑ j : evenIndex r,
      (T (evenShift r j * d - (r.choose 2 : ℤ) * d) : LaurentPolynomial ℤ) =
      (∑ j : evenIndex r, (T (evenShift r j * d) : LaurentPolynomial ℤ)) *
        T (-((r.choose 2 : ℤ) * d)) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by rw [sub_eq_add_neg, T_add]
  rw [h, sum_T_evenShift_mul, mul_comm (T _), mul_assoc, ← T_add, add_neg_cancel, T_zero,
    mul_one]

private theorem evalOne_qfact (d : ℤ) (r : ℕ) :
    LaurentPolynomial.eval₂ (RingHom.id ℤ) 1 (QuantumGroup.qfact (qUnit d) r) = r.factorial := by
  induction r with
  | zero => simp [QuantumGroup.qfact]
  | succ n ih =>
    rw [QuantumGroup.qfact_succ, map_mul, ih, QuantumGroup.qint_eq_sum, map_sum]
    simp only [val_qUnit_zpow, eval₂_T, one_zpow, Units.val_one, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, mul_one, Nat.factorial_succ]
    push_cast
    ring

theorem qfact_qUnit_ne_zero (d : ℤ) (r : ℕ) : QuantumGroup.qfact (qUnit d) r ≠ 0 := by
  intro h
  have h' := evalOne_qfact d r
  rw [h, map_zero] at h'
  exact (Nat.factorial_ne_zero r) (by exact_mod_cast h'.symm)

theorem T_ne_one {m : ℤ} (hm : m ≠ 0) : (T m : LaurentPolynomial ℤ) ≠ 1 := by
  intro h
  rw [← T_zero] at h
  have h' := congrArg (fun p : LaurentPolynomial ℤ => p.coeff m) h
  simp only [T, AddMonoidAlgebra.coeff_single, Finsupp.single_apply, hm.symm, ite_true,
    ite_false] at h'
  exact one_ne_zero h'

end Coefficients

/-! ### Lemma 11.5 for an even colour -/

variable (i : I) (hi : D.parity i = 0) (r : ℕ) (ν : X)

/-- `α_{r,ν}(1_{i^{(r)}})`. -/
def projector : upWordHom D Sc sy hc i r ν ⟶ upWordHom D Sc sy hc i r ν :=
  alphaEnd D Sc sy hc i r ν (evenCornerProjector D Sc i hi r)

theorem projector_idem :
    projector D Sc sy hc i hi r ν ≫ projector D Sc sy hc i hi r ν =
      projector D Sc sy hc i hi r ν := by
  rw [projector, ← alphaEnd_mul, (evenCornerProjector_idempotent D Sc i hi r).eq]

theorem projector_degree : projector D Sc sy hc i hi r ν ∈ degree (R := k) _ _ 0 :=
  alphaEnd_mem_degree D Sc sy hc i r ν
    (evenNilHecke_demIdem_mem D Sc hi r (gdeg_dot_eq D sy) (gdeg_cross_self_eq D sy))

theorem projector_even :
    projector D Sc sy hc i hi r ν ∈ Supercategory.parity (R := k) _ _ 0 :=
  alphaEnd_mem_parity D Sc sy hc i r ν
    (evenNilHecke_demIdem_mem D Sc hi r (parityDeg_dot_eq hi) (parityDeg_cross_self_eq hi))

/-- The summand `Q^m (E_i^r 1_ν, α(1_{i^{(r)}}))` of the completed hom category. -/
abbrev summand (m : ℤ) :=
  raw (projector_idem D Sc sy hc i hi r ν) (projector_degree D Sc sy hc i hi r ν)
    (projector_even D Sc sy hc i hi r ν) m 0

/-- BE2's divided power `E_i^{(r)} 1_ν`: the degree-zero summand. -/
abbrev dividedPowerPrinted := summand D Sc sy hc i hi r ν 0

/-- The divided power shifted by `Q^{d_i r(r-1)/2}`. -/
abbrev dividedPowerCorrected := summand D Sc sy hc i hi r ν ((r.choose 2 : ℤ) * sy.d i)

/-- The categorical splitting: `[E_i^r 1_ν] = ∑_j [Q^{d_i s_j} E_i^{(r)} 1_ν]`. -/
theorem class_summands :
    K₀.mk (whole (upWordHom D Sc sy hc i r ν)) =
      ∑ j : evenIndex r, K₀.mk (summand D Sc sy hc i hi r ν (evenShift r j * sy.d i)) := by
  have S := evenCornerSplitting D Sc i hi r
  refine class_whole _ _ _ (fun j => evenShift r j * sy.d i) (fun _ => 0)
    (fun j => alphaEnd D Sc sy hc i r ν (evenSigma D Sc i hi r j))
    (fun j => alphaEnd D Sc sy hc i r ν (evenLam D Sc i hi r j)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro j
    have h := evenSigma_mem D Sc i hi (gdeg_dot_eq D sy) (gdeg_cross_self_eq D sy) r j
    rw [smul_eq_mul] at h
    exact alphaEnd_mem_degree D Sc sy hc i r ν h
  · intro j
    have h := evenSigma_mem D Sc i hi (parityDeg_dot_eq hi) (parityDeg_cross_self_eq hi) r j
    rw [smul_zero] at h
    exact alphaEnd_mem_parity D Sc sy hc i r ν h
  · intro j
    have h := evenLam_mem D Sc i hi (gdeg_dot_eq D sy) (gdeg_cross_self_eq D sy) r j
    rw [smul_eq_mul, neg_mul] at h
    exact alphaEnd_mem_degree D Sc sy hc i r ν h
  · intro j
    have h := evenLam_mem D Sc i hi (parityDeg_dot_eq hi) (parityDeg_cross_self_eq hi) r j
    rw [smul_zero] at h
    exact alphaEnd_mem_parity D Sc sy hc i r ν h
  · simp_rw [← alphaEnd_mul]
    rw [← alphaEnd_sum]
    exact ((congrArg _ (evenCornerSplitting D Sc i hi r).sum_eq)).trans
      (alphaEnd_one D Sc sy hc i r ν)
  · intro j l
    rw [← alphaEnd_mul]
    have h := (evenCornerSplitting D Sc i hi r).orth l j
    change evenLam D Sc i hi r l * evenSigma D Sc i hi r j = _ at h
    rw [h]
    by_cases hjl : j = l
    · subst hjl; rw [ite_eq_left rfl, ite_eq_left rfl]; rfl
    · rw [ite_eq_right (Ne.symm hjl), ite_eq_right hjl, alphaEnd_zero]
  · intro j
    rw [projector, ← alphaEnd_mul]
    exact congrArg _ ((evenCornerSplitting D Sc i hi r).sigma_mul j)
  · intro j
    rw [projector, ← alphaEnd_mul]
    exact congrArg _ ((evenCornerSplitting D Sc i hi r).mul_lam j)

/-- **BE2 Lemma 11.5 with the printed divided power**:
`[E_i^r 1_ν] = q_i^{r(r-1)/2} [r]^!_{q_i} [E_i^{(r)} 1_ν]`. -/
theorem class_printed :
    letI := K₀.moduleLaurentInt k (HomCat D Sc sy hc i r ν)
    K₀.mk (whole (upWordHom D Sc sy hc i r ν)) =
      (T ((r.choose 2 : ℤ) * sy.d i) *
        QuantumGroup.qfact (K := LaurentPolynomial ℤ) (qUnit (sy.d i)) r) •
        K₀.mk (dividedPowerPrinted D Sc sy hc i hi r ν) := by
  let := K₀.moduleLaurentInt k (HomCat D Sc sy hc i r ν)
  rw [class_summands, ← sum_T_evenShift_mul, Finset.sum_smul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [class_raw_shift_int, zero_add]

/-- **BE2 Lemma 11.5, corrected**: `[E_i^r 1_ν] = [r]^!_{q_i} [Q^{d_i r(r-1)/2} E_i^{(r)} 1_ν]`. -/
theorem class_corrected :
    letI := K₀.moduleLaurentInt k (HomCat D Sc sy hc i r ν)
    K₀.mk (whole (upWordHom D Sc sy hc i r ν)) =
      QuantumGroup.qfact (K := LaurentPolynomial ℤ) (qUnit (sy.d i)) r •
        K₀.mk (dividedPowerCorrected D Sc sy hc i hi r ν) := by
  let := K₀.moduleLaurentInt k (HomCat D Sc sy hc i r ν)
  rw [class_summands D Sc sy hc i hi r ν, ← sum_T_evenShift_mul_sub, Finset.sum_smul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [class_raw_shift_int]
  congr 2
  ring

omit [CommRing k] in
/-- **The printed normalization of Lemma 11.5 fails.** Over a field, for finitely many
symmetrizer values in each degree (`UDot.k0_free_laurentInt`), the printed equation
`[E_i^r 1_ν] = [r]^!_{q_i} [E_i^{(r)} 1_ν]` with `r ≥ 2` forces `[E_i^{(r)} 1_ν] = 0`, and then
`[E_i^r 1_ν] = 0` by `class_printed`. -/
theorem printed_forces_zero {k : Type w} [Field k] {Sc : SKM.Scalars D k} (cs : SKM.CScalars Sc)
    (hc : Sc.Homogeneous) (hf : sy.DegreeLocallyFinite) (hr : 2 ≤ r)
    (h : letI := K₀.moduleLaurentInt k (HomCat D Sc sy hc i r ν)
      K₀.mk (whole (upWordHom D Sc sy hc i r ν)) =
        QuantumGroup.qfact (K := LaurentPolynomial ℤ) (qUnit (sy.d i)) r •
          K₀.mk (dividedPowerPrinted D Sc sy hc i hi r ν)) :
    K₀.mk (dividedPowerPrinted D Sc sy hc i hi r ν) = 0 := by
  let := K₀.moduleLaurentInt k (HomCat D Sc sy hc i r ν)
  have hfree : Module.Free (LaurentPolynomial ℤ) (K₀ (HomCat D Sc sy hc i r ν)) :=
    SKM.UDot.k0_free_laurentInt sy cs hc hf _ _
  have hp := class_printed D Sc sy hc i hi r ν
  by_contra hx
  have heq := smul_left_injective (LaurentPolynomial ℤ) hx (hp.symm.trans h)
  have hd : (r.choose 2 : ℤ) * sy.d i ≠ 0 := by
    have hC : 0 < r.choose 2 := Nat.choose_pos hr
    have hd := sy.pos i
    positivity
  have h1 : (T ((r.choose 2 : ℤ) * sy.d i) - 1) *
      QuantumGroup.qfact (K := LaurentPolynomial ℤ) (qUnit (sy.d i)) r = 0 := by
    rw [sub_mul, one_mul, sub_eq_zero]
    exact heq
  exact mul_ne_zero (sub_ne_zero.mpr (T_ne_one hd)) (qfact_qUnit_ne_zero _ _) h1

end OddMath.QuiverHecke.CategoricalDividedPowers
