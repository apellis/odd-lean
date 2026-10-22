/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CategoricalDividedPowersOdd
import OddMath.QuiverHecke.AlphaPrime

/-!
# Downward categorical divided powers: BE2 Lemma 11.5 for `F_i^{(n)}`

Brundan–Ellis, arXiv:1701.04133v2, the divided powers `F_i^{(n)} 1_λ` defined before
Lemma 11.5 through `α'_{n,λ} = ω ∘ α_{n,λ}` (11.8), and the second equation of the lemma,
`[F_i^n 1_λ] = [n]^!_{q_i,π_i} [F_i^{(n)} 1_λ]`.

Here `betaEnd` is `α'` on the same-colour corner, written at the weight `-ν` so that the
rightmost weight of `F_i^n` is `-ν` on the nose. Since `α'` has the super-opposite source,
`betaEnd (x * y) = (-1)^{|x||y|} betaEnd x ≫ betaEnd y`; the splitting of Lemma 11.1 is
transported with these signs (`class_whole_down`). The summands are
`Q^{-d_i s_j} F_i^{(n)} 1_λ` for an even colour and `Q^{-2 d_i s} Π^s F_i^{(n)} 1_λ` for an
odd one, and
* even: `[F_i^n 1_λ] = q_i^{-n(n-1)/2} [n]^!_{q_i} [F_i^{(n)} 1_λ]` (`class_printed_down`);
* odd: `[F_i^n 1_λ] = q_i^{-n(n-1)/2} [n]^!_{q_i,π} [F_i^{(n)} 1_λ]` (`class_printed_down_odd`).
So the downward divided power needs the shift `Q^{-d_i n(n-1)/2}` and no parity shift
(`class_corrected_down`, `class_corrected_down_odd`), and the printed normalization forces
`[F_i^{(n)} 1_λ] = 0` for `n ≥ 2` over a field (`printed_forces_zero_down`,
`printed_forces_zero_down_odd`).
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

/-- The 1-morphism `F_i^n 1_{-ν}`, the Chevalley image of `E_i^n 1_ν`. -/
def downWordHom (i : I) (n : ℕ) (ν : X) :
    (show SKM.UGr D Sc sy hc from
      ⟨SKM.wt (X := X) D (-ν) (SKM.flipW (upWord (List.replicate n i)))⟩) ⟶
      (show SKM.UGr D Sc sy hc from ⟨-ν⟩) :=
  ⟨(SKM.chevMap D).obj (SKM.ob D ν (upWord (List.replicate n i))),
    by rw [SKM.chevMap_obj]; rfl,
    by rw [SKM.chevMap_obj]; exact SKM.ok_wd D (-ν) _,
    by rw [SKM.chevMap_obj]; exact SKM.ob_endR D (-ν) _⟩

/-- The completed hom category containing `F_i^n 1_{-ν}`. -/
abbrev HomCatDown (i : I) (n : ℕ) (ν : X) :=
  Karoubi (Mat_ (Base k ((show SKM.UGr D Sc sy hc from
    ⟨SKM.wt (X := X) D (-ν) (SKM.flipW (upWord (List.replicate n i)))⟩)
    ⟶ (show SKM.UGr D Sc sy hc from ⟨-ν⟩))))

/-- Equation (11.8) on the same-colour corner: `α'_{n,-ν} = ω ∘ α_{n,ν}`. -/
def betaEnd (i : I) (n : ℕ) (ν : X) (c : Corner D Sc i n) :
    downWordHom D Sc sy hc i n ν ⟶ downWordHom D Sc sy hc i n ν :=
  (SOp.unsop ((SKM.omega Sc).map ((alpha D Sc ν).map c)) :)

theorem betaEnd_one (i : I) (n : ℕ) (ν : X) : betaEnd D Sc sy hc i n ν 1 = 𝟙 _ := by
  change SOp.unsop ((SKM.omega Sc).map ((alpha D Sc ν).map (𝟙 _))) = _
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  rfl

theorem betaEnd_zero (i : I) (n : ℕ) (ν : X) : betaEnd D Sc sy hc i n ν 0 = 0 := by
  change SOp.unsop ((SKM.omega Sc).map ((alpha D Sc ν).map 0)) = _
  rw [Functor.map_zero, Functor.map_zero]
  rfl

theorem betaEnd_add (i : I) (n : ℕ) (ν : X) (c c' : Corner D Sc i n) :
    betaEnd D Sc sy hc i n ν (c + c') =
      betaEnd D Sc sy hc i n ν c + betaEnd D Sc sy hc i n ν c' := by
  change SOp.unsop ((SKM.omega Sc).map ((alpha D Sc ν).map (c + c'))) = _
  rw [Functor.map_add, Functor.map_add]
  rfl

theorem betaEnd_smul (i : I) (n : ℕ) (ν : X) (r : k) (c : Corner D Sc i n) :
    betaEnd D Sc sy hc i n ν (r • c) = r • betaEnd D Sc sy hc i n ν c := by
  change SOp.unsop ((SKM.omega Sc).map ((alpha D Sc ν).map (r • c))) = _
  rw [Functor.map_smul, Functor.map_smul]
  rfl

theorem betaEnd_sum (i : I) (n : ℕ) (ν : X) {J : Type*} (s : Finset J) (c : J → Corner D Sc i n) :
    betaEnd D Sc sy hc i n ν (∑ j ∈ s, c j) = ∑ j ∈ s, betaEnd D Sc sy hc i n ν (c j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using betaEnd_zero D Sc sy hc i n ν
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, betaEnd_add, ih]

theorem betaEnd_mem_parity (i : I) (n : ℕ) (ν : X) {c : Corner D Sc i n} {p : ZMod 2}
    (h : c ∈ cornerDeg D Sc (Presentation.parityDeg (sig D)) i n p) :
    betaEnd D Sc sy hc i n ν c ∈ Supercategory.parity (R := k) _ _ p :=
  SOp.mem_parity_iff.mp (SKM.omega_mem (alpha_mem_parity D Sc ν h))

theorem betaEnd_mem_degree (i : I) (n : ℕ) (ν : X) {c : Corner D Sc i n} {d : ℤ}
    (h : c ∈ cornerDeg D Sc (gdeg D sy) i n d) :
    betaEnd D Sc sy hc i n ν c ∈ degree (R := k) _ _ d :=
  SKM.omega_mem_gdeg sy (alpha_mem_degree D Sc sy ν h)

/-- The super-opposite composition law of `α'`. -/
theorem betaEnd_comp (i : I) (n : ℕ) (ν : X) {c c' : Corner D Sc i n} {p q : ZMod 2}
    (h : c ∈ cornerDeg D Sc (Presentation.parityDeg (sig D)) i n p)
    (h' : c' ∈ cornerDeg D Sc (Presentation.parityDeg (sig D)) i n q) :
    betaEnd D Sc sy hc i n ν c ≫ betaEnd D Sc sy hc i n ν c' =
      Supercategory.sign k (p * q) • betaEnd D Sc sy hc i n ν (c * c') := by
  have e : betaEnd D Sc sy hc i n ν (c * c') =
      Supercategory.sign k (q * p) •
        (betaEnd D Sc sy hc i n ν c ≫ betaEnd D Sc sy hc i n ν c') := by
    change SOp.unsop ((SKM.omega Sc).map ((alpha D Sc ν).map (c' ≫ c))) = _
    rw [Functor.map_comp, Functor.map_comp]
    exact SOp.comp_of_mem (SKM.omega_mem (alpha_mem_parity D Sc ν h'))
      (SKM.omega_mem (alpha_mem_parity D Sc ν h))
  rw [e, mul_comm q p, Supercategory.sign_smul_sign_smul]

attribute [irreducible] betaEnd

/-! ### Transporting a splitting along `α'` -/

section Transport

private theorem zmod2_mul_self (p : ZMod 2) : p * p = p := by fin_cases p <;> rfl

variable (i : I) (n : ℕ) (ν : X) {e : Corner D Sc i n} (he : e * e = e)
  (hed : e ∈ cornerDeg D Sc (gdeg D sy) i n 0)
  (hep : e ∈ cornerDeg D Sc (Presentation.parityDeg (sig D)) i n 0)

include he hep in
theorem betaEnd_idem :
    betaEnd D Sc sy hc i n ν e ≫ betaEnd D Sc sy hc i n ν e = betaEnd D Sc sy hc i n ν e := by
  rw [betaEnd_comp D Sc sy hc i n ν hep hep, mul_zero, Supercategory.sign_zero, one_smul, he]

/-- The summand `Q^m Π^p (F_i^n 1_{-ν}, α'(e))`. -/
abbrev downSummand (m : ℤ) (p : ZMod 2) :=
  raw (betaEnd_idem D Sc sy hc i n ν he hep) (betaEnd_mem_degree D Sc sy hc i n ν hed)
    (betaEnd_mem_parity D Sc sy hc i n ν hep) m p

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  (S : OddMath.Frontier.Categorification.Splitting (1 : Corner D Sc i n) e ι)
  (m : ι → ℤ) (par : ι → ZMod 2)
  (hσd : ∀ j, S.σ j ∈ cornerDeg D Sc (gdeg D sy) i n (m j))
  (hσp : ∀ j, S.σ j ∈ cornerDeg D Sc (Presentation.parityDeg (sig D)) i n (par j))
  (hld : ∀ j, S.lam j ∈ cornerDeg D Sc (gdeg D sy) i n (-m j))
  (hlp : ∀ j, S.lam j ∈ cornerDeg D Sc (Presentation.parityDeg (sig D)) i n (par j))

include hσd hσp hld hlp in
/-- **The downward categorical splitting.** A splitting `1 = ∑ σ_j λ_j` of the corner with
`deg σ_j = m_j` gives `[F_i^n 1_{-ν}] = ∑_j [Q^{-m_j} Π^{p_j} (F_i^n 1_{-ν}, α'(e))]`. -/
theorem class_whole_down :
    K₀.mk (whole (downWordHom D Sc sy hc i n ν)) =
      ∑ j, K₀.mk (downSummand D Sc sy hc i n ν he hed hep (-m j) (par j)) := by
  refine class_whole _ _ _ (fun j => -m j) par (fun j => betaEnd D Sc sy hc i n ν (S.lam j))
    (fun j => Supercategory.sign k (par j) • betaEnd D Sc sy hc i n ν (S.σ j))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro j
    exact betaEnd_mem_degree D Sc sy hc i n ν (hld j)
  · intro j
    exact betaEnd_mem_parity D Sc sy hc i n ν (hlp j)
  · intro j
    rw [neg_neg]
    exact Submodule.smul_mem _ _ (betaEnd_mem_degree D Sc sy hc i n ν (hσd j))
  · intro j
    exact Submodule.smul_mem _ _ (betaEnd_mem_parity D Sc sy hc i n ν (hσp j))
  · have h : ∀ j, (Supercategory.sign k (par j) • betaEnd D Sc sy hc i n ν (S.σ j)) ≫
        betaEnd D Sc sy hc i n ν (S.lam j) = betaEnd D Sc sy hc i n ν (S.σ j * S.lam j) := by
      intro j
      rw [Linear.smul_comp, betaEnd_comp D Sc sy hc i n ν (hσp j) (hlp j), smul_smul,
        zmod2_mul_self, Supercategory.sign_mul_self, one_smul]
    simp_rw [h]
    rw [← betaEnd_sum, S.sum_eq, betaEnd_one]
  · intro j l
    rw [Linear.comp_smul, betaEnd_comp D Sc sy hc i n ν (hlp j) (hσp l), S.orth j l]
    by_cases hjl : j = l
    · subst hjl
      rw [ite_eq_left rfl, ite_eq_left rfl, smul_smul, zmod2_mul_self,
        Supercategory.sign_mul_self, one_smul]
    · rw [ite_eq_right hjl, ite_eq_right hjl, betaEnd_zero, smul_zero, smul_zero]
  · intro j
    rw [betaEnd_comp D Sc sy hc i n ν hep (hlp j), zero_mul, Supercategory.sign_zero, one_smul,
      S.mul_lam]
  · intro j
    rw [Linear.smul_comp, betaEnd_comp D Sc sy hc i n ν (hσp j) hep, mul_zero,
      Supercategory.sign_zero, one_smul, S.sigma_mul]

end Transport

/-! ### Coefficients -/

section Coefficients

theorem qint_inv' {K : Type*} [CommRing K] (t : Kˣ) (r : ℕ) :
    Categorification.QuantumGroup.qint t⁻¹ r = Categorification.QuantumGroup.qint t r := by
  rw [Categorification.QuantumGroup.qint_eq_sum, Categorification.QuantumGroup.qint_eq_sum,
    ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  have hc : ((r - 1 - j : ℕ) : ℤ) = r - 1 - j := by omega
  rw [inv_zpow', hc]
  congr 2
  ring

theorem qfact_inv' {K : Type*} [CommRing K] (t : Kˣ) (r : ℕ) :
    Categorification.QuantumGroup.qfact t⁻¹ r = Categorification.QuantumGroup.qfact t r := by
  simp only [Categorification.QuantumGroup.qfact, qint_inv']

theorem qfact_qUnit_neg (d : ℤ) (r : ℕ) :
    Categorification.QuantumGroup.qfact (K := LaurentPolynomial ℤ) (qUnit (-d)) r =
      Categorification.QuantumGroup.qfact (K := LaurentPolynomial ℤ) (qUnit d) r := by
  have h : qUnit (-d) = (qUnit d)⁻¹ := zpow_neg _ _
  rw [h, qfact_inv']

/-- The even shifts, scaled by `-d`, sum to `q^{-d n(n-1)/2} [n]^!_{q^d}`. -/
theorem sum_T_evenShift_down (r : ℕ) (d : ℤ) :
    ∑ j : evenIndex r, (T (-(evenShift r j * d)) : LaurentPolynomial ℤ) =
      T (-((r.choose 2 : ℤ) * d)) * Categorification.QuantumGroup.qfact (qUnit d) r := by
  have h := sum_T_evenShift_mul r (-d)
  rw [qfact_qUnit_neg] at h
  simpa only [mul_neg] using h

theorem val_qUnitPi_zpow (d z : ℤ) :
    ((qUnitPi d ^ z : (LaurentPolynomial Zπ)ˣ) : LaurentPolynomial Zπ) = T (d * z) := by
  rw [← inv_inv (qUnitPi d), inv_zpow', val_qUnitPi_inv_zpow]
  congr 1
  ring

/-- The odd shifts, negated and scaled by `d`, sum to `q^{-d C} [n]^!_{q^d,π}`. -/
theorem sum_T_oddShift_down (n : ℕ) (d : ℤ) :
    ∑ ℓ : Sq (n + 2), T (-(2 * d * shift n ℓ)) * piLP ^ (shift n ℓ).toNat =
      T (-(((n + 2).choose 2 : ℤ) * d)) * qpFact (qUnitPi d) piLP (n + 2) := by
  rw [← sum_shift_monomial (qUnitPi d) piLP n, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [val_qUnitPi_zpow, show -(2 * d * shift n ℓ) = -(((n + 2).choose 2 : ℤ) * d) +
    d * (((n + 2).choose 2 : ℤ) - 2 * shift n ℓ) by ring, T_add]
  ring

end Coefficients

/-! ### Lemma 11.5 for `F_i^{(n)}`, even colours -/

section Even

variable (i : I) (hi : D.parity i = 0) (r : ℕ) (ν : X)

/-- The idempotent `α'(1_{i^{(r)}})` cuts out BE2's `F_i^{(r)} 1_{-ν}` (degree and parity zero). -/
abbrev dividedPowerDownPrinted :=
  downSummand D Sc sy hc i r ν (evenCornerProjector_idempotent D Sc i hi r).eq
    (evenNilHecke_demIdem_mem D Sc hi r (gdeg_dot_eq D sy) (gdeg_cross_self_eq D sy))
    (evenNilHecke_demIdem_mem D Sc hi r (parityDeg_dot_eq hi) (parityDeg_cross_self_eq hi)) 0 0

/-- The downward divided power shifted by `Q^{-d_i r(r-1)/2}`. -/
abbrev dividedPowerDownCorrected :=
  downSummand D Sc sy hc i r ν (evenCornerProjector_idempotent D Sc i hi r).eq
    (evenNilHecke_demIdem_mem D Sc hi r (gdeg_dot_eq D sy) (gdeg_cross_self_eq D sy))
    (evenNilHecke_demIdem_mem D Sc hi r (parityDeg_dot_eq hi) (parityDeg_cross_self_eq hi))
    (-((r.choose 2 : ℤ) * sy.d i)) 0

theorem class_summands_down :
    K₀.mk (whole (downWordHom D Sc sy hc i r ν)) =
      ∑ j : evenIndex r, K₀.mk (downSummand D Sc sy hc i r ν
        (evenCornerProjector_idempotent D Sc i hi r).eq
        (evenNilHecke_demIdem_mem D Sc hi r (gdeg_dot_eq D sy) (gdeg_cross_self_eq D sy))
        (evenNilHecke_demIdem_mem D Sc hi r (parityDeg_dot_eq hi) (parityDeg_cross_self_eq hi))
        (-(evenShift r j * sy.d i)) 0) := by
  refine class_whole_down D Sc sy hc i r ν _ _ _ (evenCornerSplitting D Sc i hi r)
    (fun j => evenShift r j * sy.d i) (fun _ => 0) ?_ ?_ ?_ ?_
  · intro j
    have h := evenSigma_mem D Sc i hi (gdeg_dot_eq D sy) (gdeg_cross_self_eq D sy) r j
    rwa [smul_eq_mul] at h
  · intro j
    have h := evenSigma_mem D Sc i hi (parityDeg_dot_eq hi) (parityDeg_cross_self_eq hi) r j
    rwa [smul_zero] at h
  · intro j
    have h := evenLam_mem D Sc i hi (gdeg_dot_eq D sy) (gdeg_cross_self_eq D sy) r j
    rwa [smul_eq_mul, neg_mul] at h
  · intro j
    have h := evenLam_mem D Sc i hi (parityDeg_dot_eq hi) (parityDeg_cross_self_eq hi) r j
    rwa [smul_zero] at h

/-- **BE2 Lemma 11.5 for `F_i^{(r)}` with the printed divided power** (even colour):
`[F_i^r 1_{-ν}] = q_i^{-r(r-1)/2} [r]^!_{q_i} [F_i^{(r)} 1_{-ν}]`. -/
theorem class_printed_down :
    letI := K₀.moduleLaurentInt k (HomCatDown D Sc sy hc i r ν)
    K₀.mk (whole (downWordHom D Sc sy hc i r ν)) =
      (T (-((r.choose 2 : ℤ) * sy.d i)) *
        Categorification.QuantumGroup.qfact (K := LaurentPolynomial ℤ) (qUnit (sy.d i)) r) •
        K₀.mk (dividedPowerDownPrinted D Sc sy hc i hi r ν) := by
  let := K₀.moduleLaurentInt k (HomCatDown D Sc sy hc i r ν)
  rw [class_summands_down, ← sum_T_evenShift_down, Finset.sum_smul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [class_raw_shift_int, zero_add]

/-- **BE2 Lemma 11.5 for `F_i^{(r)}`, corrected** (even colour):
`[F_i^r 1_{-ν}] = [r]^!_{q_i} [Q^{-d_i r(r-1)/2} F_i^{(r)} 1_{-ν}]`. -/
theorem class_corrected_down :
    letI := K₀.moduleLaurentInt k (HomCatDown D Sc sy hc i r ν)
    K₀.mk (whole (downWordHom D Sc sy hc i r ν)) =
      Categorification.QuantumGroup.qfact (K := LaurentPolynomial ℤ) (qUnit (sy.d i)) r •
        K₀.mk (dividedPowerDownCorrected D Sc sy hc i hi r ν) := by
  have hcomm : Categorification.QuantumGroup.qfact (K := LaurentPolynomial ℤ) (qUnit (sy.d i)) r *
      T (-((r.choose 2 : ℤ) * sy.d i)) = T (-((r.choose 2 : ℤ) * sy.d i)) *
        Categorification.QuantumGroup.qfact (K := LaurentPolynomial ℤ) (qUnit (sy.d i)) r :=
    mul_comm _ _
  let := K₀.moduleLaurentInt k (HomCatDown D Sc sy hc i r ν)
  have hs := class_raw_shift_int'
    (betaEnd_idem D Sc sy hc i r ν (evenCornerProjector_idempotent D Sc i hi r).eq
      (evenNilHecke_demIdem_mem D Sc hi r (parityDeg_dot_eq hi) (parityDeg_cross_self_eq hi)))
    (betaEnd_mem_degree D Sc sy hc i r ν
      (evenNilHecke_demIdem_mem D Sc hi r (gdeg_dot_eq D sy) (gdeg_cross_self_eq D sy)))
    (betaEnd_mem_parity D Sc sy hc i r ν
      (evenNilHecke_demIdem_mem D Sc hi r (parityDeg_dot_eq hi) (parityDeg_cross_self_eq hi)))
    (zero_add (-((r.choose 2 : ℤ) * sy.d i))) 0
  rw [← hs, ← mul_smul, hcomm, class_printed_down D Sc sy hc i hi r ν]

omit [CommRing k] in
/-- **The printed normalization fails for `F_i^{(r)}`** (even colour, `r ≥ 2`, over a field
with locally finite symmetrizer). -/
theorem printed_forces_zero_down {k : Type w} [Field k] {Sc : SKM.Scalars D k}
    (cs : SKM.CScalars Sc) (hc : Sc.Homogeneous) (hf : sy.DegreeLocallyFinite) (hr : 2 ≤ r)
    (h : letI := K₀.moduleLaurentInt k (HomCatDown D Sc sy hc i r ν)
      K₀.mk (whole (downWordHom D Sc sy hc i r ν)) =
        Categorification.QuantumGroup.qfact (K := LaurentPolynomial ℤ) (qUnit (sy.d i)) r •
          K₀.mk (dividedPowerDownPrinted D Sc sy hc i hi r ν)) :
    K₀.mk (dividedPowerDownPrinted D Sc sy hc i hi r ν) = 0 := by
  let := K₀.moduleLaurentInt k (HomCatDown D Sc sy hc i r ν)
  have hfree : Module.Free (LaurentPolynomial ℤ) (K₀ (HomCatDown D Sc sy hc i r ν)) :=
    SKM.UDot.k0_free_laurentInt sy cs hc hf _ _
  have hp := class_printed_down D Sc sy hc i hi r ν
  by_contra hx
  have heq := smul_left_injective (LaurentPolynomial ℤ) hx (hp.symm.trans h)
  have hd : -((r.choose 2 : ℤ) * sy.d i) ≠ 0 := by
    have hC : 0 < r.choose 2 := Nat.choose_pos hr
    have hd := sy.pos i
    have : 0 < (r.choose 2 : ℤ) * sy.d i := by positivity
    omega
  have h1 : (T (-((r.choose 2 : ℤ) * sy.d i)) - 1) *
      Categorification.QuantumGroup.qfact (K := LaurentPolynomial ℤ) (qUnit (sy.d i)) r = 0 := by
    rw [sub_mul, one_mul, sub_eq_zero]
    exact heq
  exact mul_ne_zero (sub_ne_zero.mpr (T_ne_one hd)) (qfact_qUnit_ne_zero _ _) h1

end Even

/-! ### Lemma 11.5 for `F_i^{(n)}`, odd colours -/

section Odd

variable (i : I) (hi : D.parity i = 1) (n : ℕ) (ν : X)

/-- `1_{i^{(n+2)}}` in the same-colour corner, as the image of the EKL projector. -/
abbrev oddE : Corner D Sc i (n + 2) := oddNilHecke D Sc i hi n (oppositeProjector n)

theorem oddE_idem : oddE D Sc i hi n * oddE D Sc i hi n = oddE D Sc i hi n := by
  rw [oddE, ← map_mul, (oppositeProjector_idempotent n).eq]

theorem oddE_mem_degree : oddE D Sc i hi n ∈ cornerDeg D Sc (gdeg D sy) i (n + 2) 0 := by
  have h := oddNilHecke_mem_integerDegree D Sc sy i hi (oppositeProjector_degree n)
  rwa [mul_zero] at h

theorem oddE_mem_parity :
    oddE D Sc i hi n ∈ cornerDeg D Sc (Presentation.parityDeg (sig D)) i (n + 2) 0 := by
  have h := oddNilHecke_mem_parity D Sc i hi (oppositeProjector_degree n)
  rwa [Int.cast_zero] at h

/-- The summand `Q^m Π^p (F_i^{n+2} 1_{-ν}, α'(1_{i^{(n+2)}}))`. -/
abbrev oddDownSummand (m : ℤ) (p : ZMod 2) :=
  downSummand D Sc sy hc i (n + 2) ν (oddE_idem D Sc i hi n) (oddE_mem_degree D Sc sy i hi n)
    (oddE_mem_parity D Sc i hi n) m p

/-- BE2's `F_i^{(n+2)} 1_{-ν}` for an odd colour. -/
abbrev oddDividedPowerDownPrinted := oddDownSummand D Sc sy hc i hi n ν 0 0

/-- The downward odd divided power shifted by `Q^{-d_i C}`; no parity shift is needed. -/
abbrev oddDividedPowerDownCorrected :=
  oddDownSummand D Sc sy hc i hi n ν (-(((n + 2).choose 2 : ℤ) * sy.d i)) 0

theorem class_summands_down_odd :
    K₀.mk (whole (downWordHom D Sc sy hc i (n + 2) ν)) =
      ∑ ℓ : Sq (n + 2), K₀.mk (oddDownSummand D Sc sy hc i hi n ν (-(2 * sy.d i * shift n ℓ))
        (shift n ℓ : ZMod 2)) := by
  refine class_whole_down D Sc sy hc i (n + 2) ν _ _ _ (oddCornerSplitting D Sc i hi n)
    (fun ℓ => 2 * sy.d i * shift n ℓ) (fun ℓ => (shift n ℓ : ZMod 2)) ?_ ?_ ?_ ?_
  · intro ℓ
    exact oddNilHecke_mem_integerDegree D Sc sy i hi (sigma_degree n ℓ)
  · intro ℓ
    exact oddNilHecke_mem_parity D Sc i hi (sigma_degree n ℓ)
  · intro ℓ
    have h := oddNilHecke_mem_integerDegree D Sc sy i hi (lam_degree n ℓ)
    rwa [mul_neg] at h
  · intro ℓ
    have h := oddNilHecke_mem_parity D Sc i hi (lam_degree n ℓ)
    rwa [Int.cast_neg, ZMod.neg_eq_self_mod_two] at h

theorem class_oddDownSummand (m : ℤ) (s : ℕ) :
    letI := K₀.moduleLaurent k (HomCatDown D Sc sy hc i (n + 2) ν)
    K₀.mk (oddDownSummand D Sc sy hc i hi n ν m (s : ZMod 2)) =
      (T m * piLP ^ s) • K₀.mk (oddDividedPowerDownPrinted D Sc sy hc i hi n ν) :=
  class_raw_eq
    (betaEnd_idem D Sc sy hc i (n + 2) ν (oddE_idem D Sc i hi n) (oddE_mem_parity D Sc i hi n))
    (betaEnd_mem_degree D Sc sy hc i (n + 2) ν (oddE_mem_degree D Sc sy i hi n))
    (betaEnd_mem_parity D Sc sy hc i (n + 2) ν (oddE_mem_parity D Sc i hi n)) m s

/-- **BE2 Lemma 11.5 for `F_i^{(n+2)}` with the printed divided power** (odd colour):
`[F_i^{n+2} 1_{-ν}] = q_i^{-C} [n+2]^!_{q_i,π} [F_i^{(n+2)} 1_{-ν}]`, `C = (n+2)(n+1)/2`. -/
theorem class_printed_down_odd :
    letI := K₀.moduleLaurent k (HomCatDown D Sc sy hc i (n + 2) ν)
    K₀.mk (whole (downWordHom D Sc sy hc i (n + 2) ν)) =
      (T (-(((n + 2).choose 2 : ℤ) * sy.d i)) * qpFact (qUnitPi (sy.d i)) piLP (n + 2)) •
        K₀.mk (oddDividedPowerDownPrinted D Sc sy hc i hi n ν) := by
  let := K₀.moduleLaurent k (HomCatDown D Sc sy hc i (n + 2) ν)
  rw [class_summands_down_odd D Sc sy hc i hi n ν, ← sum_T_oddShift_down, Finset.sum_smul]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [← class_oddDownSummand, ← complement_eq_shift, Int.toNat_natCast]
  rfl

/-- **BE2 Lemma 11.5 for `F_i^{(n+2)}`, corrected** (odd colour):
`[F_i^{n+2} 1_{-ν}] = [n+2]^!_{q_i,π} [Q^{-d_i C} F_i^{(n+2)} 1_{-ν}]`. -/
theorem class_corrected_down_odd :
    letI := K₀.moduleLaurent k (HomCatDown D Sc sy hc i (n + 2) ν)
    K₀.mk (whole (downWordHom D Sc sy hc i (n + 2) ν)) =
      qpFact (qUnitPi (sy.d i)) piLP (n + 2) •
        K₀.mk (oddDividedPowerDownCorrected D Sc sy hc i hi n ν) := by
  have hcomm : qpFact (qUnitPi (sy.d i)) piLP (n + 2) * T (-(((n + 2).choose 2 : ℤ) * sy.d i)) =
      T (-(((n + 2).choose 2 : ℤ) * sy.d i)) * qpFact (qUnitPi (sy.d i)) piLP (n + 2) := by ring
  let := K₀.moduleLaurent k (HomCatDown D Sc sy hc i (n + 2) ν)
  have hs := class_raw_shift'
    (betaEnd_idem D Sc sy hc i (n + 2) ν (oddE_idem D Sc i hi n) (oddE_mem_parity D Sc i hi n))
    (betaEnd_mem_degree D Sc sy hc i (n + 2) ν (oddE_mem_degree D Sc sy i hi n))
    (betaEnd_mem_parity D Sc sy hc i (n + 2) ν (oddE_mem_parity D Sc i hi n))
    (zero_add (-(((n + 2).choose 2 : ℤ) * sy.d i))) 0
  rw [← hs, ← mul_smul, hcomm, class_printed_down_odd D Sc sy hc i hi n ν]

omit [CommRing k] in
theorem defect_smul_of_eq {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] {a b : R}
    {x y : M} (h₁ : y = (a * b) • x) (h₂ : y = b • x) : ((a - 1) * b) • x = 0 := by
  rw [sub_mul, one_mul, sub_smul, ← h₁, ← h₂, sub_self]

theorem eval_defect_down_ne_zero (ε : ℤ) (hε : ε * ε = 1) {m d : ℤ} (hm : m ≠ 0)
    (hd : 0 < d) (r : ℕ) :
    CoveringLaurent.eval ε hε ((T m - 1) * qpFact (qUnitPi d) piLP r) ≠ 0 := by
  have hp : CoveringLaurent.eval ε hε piLP = C ε := CoveringLaurent.eval_pi ε hε
  have hf : CoveringLaurent.eval ε hε (qpFact (qUnitPi d) piLP r) = qpFact (qUnit d) (C ε) r :=
    (map_qpFact (q := qUnitPi d) (π := piLP) (CoveringLaurent.eval ε hε) r).trans
      (by rw [eval_qUnitPi, hp])
  rw [map_mul, map_sub, eval_T, map_one, hf]
  exact mul_ne_zero (sub_ne_zero.mpr (T_ne_one hm)) (qpFact_qUnit_ne_zero' hd _ _)

/-- The defect of the printed downward normalization kills the printed class. -/
theorem defect_smul_printed_down
    (h : letI := K₀.moduleLaurent k (HomCatDown D Sc sy hc i (n + 2) ν)
      K₀.mk (whole (downWordHom D Sc sy hc i (n + 2) ν)) =
        qpFact (qUnitPi (sy.d i)) piLP (n + 2) •
          K₀.mk (oddDividedPowerDownPrinted D Sc sy hc i hi n ν)) :
    letI := K₀.moduleLaurent k (HomCatDown D Sc sy hc i (n + 2) ν)
    ((T (-(((n + 2).choose 2 : ℤ) * sy.d i)) - 1) * qpFact (qUnitPi (sy.d i)) piLP (n + 2)) •
      K₀.mk (oddDividedPowerDownPrinted D Sc sy hc i hi n ν) = 0 := by
  let := K₀.moduleLaurent k (HomCatDown D Sc sy hc i (n + 2) ν)
  exact defect_smul_of_eq (class_printed_down_odd D Sc sy hc i hi n ν) h

theorem int_smul_eq_down (r : LaurentPolynomial ℤ)
    (x : K₀ (HomCatDown D Sc sy hc i (n + 2) ν)) :
    (letI := K₀.moduleLaurentInt k (HomCatDown D Sc sy hc i (n + 2) ν); r • x) =
      (letI := K₀.moduleLaurent k (HomCatDown D Sc sy hc i (n + 2) ν);
        CoveringLaurent.inclusion r • x) := rfl

omit [CommRing k] in
/-- **The printed normalization fails for `F_i^{(n+2)}`** (odd colour, over a field with
locally finite symmetrizer). -/
theorem printed_forces_zero_down_odd {k : Type w} [Field k] {Sc : SKM.Scalars D k}
    (cs : SKM.CScalars Sc) (hc : Sc.Homogeneous) (hf : sy.DegreeLocallyFinite)
    (h : letI := K₀.moduleLaurent k (HomCatDown D Sc sy hc i (n + 2) ν)
      K₀.mk (whole (downWordHom D Sc sy hc i (n + 2) ν)) =
        qpFact (qUnitPi (sy.d i)) piLP (n + 2) •
          K₀.mk (oddDividedPowerDownPrinted D Sc sy hc i hi n ν)) :
    K₀.mk (oddDividedPowerDownPrinted D Sc sy hc i hi n ν) = 0 := by
  let := K₀.moduleLaurent k (HomCatDown D Sc sy hc i (n + 2) ν)
  let := K₀.moduleLaurentInt k (HomCatDown D Sc sy hc i (n + 2) ν)
  have hfree : Module.Free (LaurentPolynomial ℤ) (K₀ (HomCatDown D Sc sy hc i (n + 2) ν)) :=
    SKM.UDot.k0_free_laurentInt sy cs hc hf _ _
  have hm : -(((n + 2).choose 2 : ℤ) * sy.d i) ≠ 0 := by
    have hC : 0 < (n + 2).choose 2 := Nat.choose_pos (by omega)
    have hd := sy.pos i
    have : 0 < ((n + 2).choose 2 : ℤ) * sy.d i := by positivity
    omega
  have hcx := defect_smul_printed_down D Sc sy hc i hi n ν h
  exact eq_zero_of_smul_eq_zero (int_smul_eq_down D Sc sy hc i n ν) hcx
    (eval_defect_down_ne_zero 1 (by norm_num) hm (sy.pos i) _)
    (eval_defect_down_ne_zero (-1) (by norm_num) hm (sy.pos i) _)

end Odd

end OddMath.QuiverHecke.CategoricalDividedPowers
