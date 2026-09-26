import OddMath.Frontier.EKRestGram7
import OddMath.Frontier.EKPrimitives

/-! # `f_n = ±m_n`: true for `n = 1` and `n` even, false for `n = 7`

EK arXiv:1107.5610v2, §3.2, p. 25: "Note that `f_n = ±m_n`, so the `f_{2k}` are primitive
as well (the sign is the same as the coefficient of `h_n` in the expansion of `e_n` in the
h-basis)."

Integral q = -1, in the radical quotient `Q`; `m_n = EKPrimitives.mRow n`, `f_n` the one-row
member of `EKDualBases.fBasis`.

* `f_eq_smul_m`: for `n = 1` and every even `n ≥ 2`, `f_n = c_n m_n` with
  `c_n = [h_n] e_n = -(-1)^{C(n+1,2)}` (`e_coefficient`), a sign.
* `f_three`, `f_five`: `f₃ = m₃`, `f₅ = m₅`.
* `f_seven_ne`: **false for `n = 7`**: `f₇ ≠ c • m₇` for every integer `c`. Indeed
  `(e₇, m₇) = 5` (`e7_m7`), i.e. the coefficient of `h₇` in `e₇` is `5`, while `(e₇, f₇) = 1`.
  So the claim is proved for `n = 1`, every even `n`, and `n = 3, 5`, and fails for `n = 7`;
  larger odd `n` are not treated here.
-/

noncomputable section
set_option maxRecDepth 100000
open scoped BigOperators DualNumber

namespace OddMath.Frontier.EKRest
open EKRadicalQuotient EKAppendixData DegreeShapes EKDualBases EKIntegralBases
open EKPrimitives (Phi phi mRow rowShape rowShape_rows eq_rowShape pairing_mRow)

theorem e_mem (n : ℕ) : EKElementaryQuotient.e n ∈ degreePiece n := by
  rw [degreePiece_eq_hPartition_span]; exact elementary_mem_hPiece n

theorem counit_e {n : ℕ} (hn : 0 < n) : quotientCounit (EKElementaryQuotient.e n) = 0 :=
  EKPrimitives.counit_degree_pos hn (e_mem n)

/-- A product of at least two dual numbers with vanishing real part is zero. -/
theorem dual_prod_zero (l : List ℤ[ε]) (hl : ∀ x ∈ l, x.fst = 0) (h2 : 2 ≤ l.length) :
    l.prod = 0 := by
  match l, h2 with
  | a :: b :: t, _ =>
    have ha : a = DualNumber.eps * (a.snd : ℤ[ε]) := by
      ext
      · simp [hl a (by simp)]
      · simp
    have hb : b = DualNumber.eps * (b.snd : ℤ[ε]) := by
      ext
      · simp [hl b (by simp)]
      · simp
    rw [List.prod_cons, List.prod_cons, ← mul_assoc, ha, hb]
    have : DualNumber.eps * (a.snd : ℤ[ε]) * (DualNumber.eps * (b.snd : ℤ[ε])) = 0 := by
      rw [mul_comm DualNumber.eps (a.snd : ℤ[ε]), mul_assoc, ← mul_assoc DualNumber.eps,
        DualNumber.eps_mul_eps, zero_mul, mul_zero]
    rw [this, zero_mul]

theorem phi_ePartition_long (n : ℕ) (hn : n = 1 ∨ Even n) (μ : YoungDiagram)
    (hl : 2 ≤ μ.rowLens.length) : phi n hn (EKPartitionSpanning.ePartition μ) = 0 := by
  rw [EKPrimitives.phi_apply, EKPartitionSpanning.ePartition, map_list_prod, List.map_map,
    dual_prod_zero]
  · rfl
  · intro x hx
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
    simp only [Function.comp_apply, EKPrimitives.Phi_fst]
    exact counit_e (μ.pos_of_mem_rowLens k hk)
  · simpa using hl

theorem pi_hWord_list (α : List ℕ) :
    pi (CompleteElementary.hWord α) = (α.map EKElementaryQuotient.h).prod := by
  simp only [CompleteElementary.hWord, map_list_prod, List.map_map]
  rfl

/-- The coefficient `c_n = (e_n, m_n) = -(-1)^{C(n+1,2)}` (`n = 1` or `n` even). -/
theorem phi_e (n : ℕ) (hpos : 0 < n) (hn : n = 1 ∨ Even n) :
    phi n hn (EKElementaryQuotient.e n) = -(-1) ^ ((n + 1).choose 2) := by
  rw [EKPrimitives.phi_apply, EKElementaryQuotient.e,
    CompleteElementary.elementary_composition_expansion, map_mul pi, map_sum pi, map_mul (Phi n hn),
    map_sum (Phi n hn), map_pow, map_pow, map_neg, map_neg, map_one, map_one]
  have hterm : ∀ α ∈ CompleteElementary.compositions n,
      Phi n hn (pi ((-1 : CompleteElementary.A) ^ α.length * CompleteElementary.hWord α)) =
        if α = [n] then -DualNumber.eps else 0 := by
    intro α hα
    obtain ⟨hp, hs⟩ := CompleteElementary.composition_sound n α hα
    rw [map_mul, map_mul, map_pow, map_pow, map_neg, map_neg, map_one, map_one,
      pi_hWord_list, EKPrimitives.Phi_word n hn α hp]
    have hne : α ≠ [] := by rintro rfl; simp at hs; omega
    by_cases h1 : α = [n]
    · subst h1; simp
    · simp [hne, h1]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq']
  rw [if_pos ((CompleteElementary.mem_compositions_iff n [n]).mpr ⟨by simp [hpos], by simp⟩)]
  simp

/-- EK p. 25: `c_n` is the coefficient of `h_n` in the h-basis expansion of `e_n`. -/
theorem e_coefficient (n : ℕ) (hpos : 0 < n) (hn : n = 1 ∨ Even n) :
    (degreeHBasis n).repr ⟨EKElementaryQuotient.e n, e_mem n⟩ (rowShape n) =
      -(-1) ^ ((n + 1).choose 2) := by
  rw [EKPrimitives.hrepr_eq_pairing]
  exact (pairing_mRow n hn hpos _).trans (phi_e n hpos hn)

theorem ePartition_row {n : ℕ} (hpos : 0 < n) :
    EKPartitionSpanning.ePartition (rowShape n).val = EKElementaryQuotient.e n := by
  simp [EKPartitionSpanning.ePartition, rowShape_rows hpos]

/-- **EK p. 25, `n = 1` and `n` even:** `f_n = c_n m_n`, `c_n = [h_n]e_n = -(-1)^{C(n+1,2)}`. -/
theorem f_eq_smul_m (n : ℕ) (hpos : 0 < n) (hn : n = 1 ∨ Even n) :
    fBasis n (rowShape n) = (-(-1) ^ ((n + 1).choose 2) : ℤ) • mRow n := by
  symm
  apply f_unique
  intro ν
  rw [Submodule.coe_smul, map_zsmul, smul_eq_mul, pairing_mRow n hn hpos]
  rcases EKPrimitives.shape_cases hpos ν with h1 | h2
  · rw [eq_rowShape hpos ν h1, if_pos rfl, ePartition_row hpos, phi_e n hpos hn]
    rw [neg_mul_neg, ← pow_add, ← two_mul, pow_mul]
    simp
  · rw [phi_ePartition_long n hn _ h2, mul_zero, if_neg]
    intro he
    rw [he, rowShape_rows hpos] at h2
    simp at h2

/-- Hence `f_{2k}` is primitive (EK p. 25). -/
theorem f_primitive (n : ℕ) (hpos : 0 < n) (hn : n = 1 ∨ Even n) :
    EKPrimitives.IsPrimitive (fBasis n (rowShape n)).val := by
  rw [f_eq_smul_m n hpos hn, Submodule.coe_smul]
  exact EKPrimitives.smul_primitive (EKPrimitives.mRow_primitive n hn hpos) _

/-! ## Odd degrees: `n = 3` holds, `n = 7` fails -/

theorem rowShape_three : rowShape 3 = hshapes3 2 := Subtype.ext rfl

/-- `f₃ = m₃`. -/
theorem f_three : fBasis 3 (rowShape 3) = mRow 3 := by
  rw [mRow, rowShape_three, fExp3_3, mExp3_3]

/-- The e/h matrix `M` of (3.2) in degree 5 (printed order of `EKAppendixData.hshapes5`). -/
def gramM5 : Matrix (Fin 7) (Fin 7) ℤ := !![
  0, 0, 2, 0, 2, 1, 1;
  0, 1, -2, 1, 1, -1, 0;
  2, -2, -1, 0, -1, 0, 0;
  0, 1, 0, 1, 0, 0, 0;
  2, 1, -1, 0, 0, 0, 0;
  1, -1, 0, 0, 0, 0, 0;
  1, 0, 0, 0, 0, 0, 0]

theorem gramM_table5 : ∀ i j, M 5 (hshapes5 i) (hshapes5 j) = gramM5 i j :=
  M_table hshapes5 pl5 hs5 gramM5 (by decide +kernel)

theorem rowShape_five' : rowShape 5 = hshapes5 6 := Subtype.ext rfl

/-- `f₅ = m₅` (both equal `h₁₁₁₁₁ + h₂₁₁₁ + 3h₂₂₁ - h₃₁₁ - 3h₃₂ - 9h₄₁ + 9h₅`). -/
theorem f_five : fBasis 5 (rowShape 5) = mRow 5 := by
  rw [mRow, rowShape_five',
    f_of_table hshapes5 exhaust5 inj5 gramM5 gramM_table5 ![1, 1, 3, -1, -3, -9, 9] 6
      (by decide),
    m_of_table hshapes5 exhaust5 inj5 printedGram5 gram_table5 ![1, 1, 3, -1, -3, -9, 9] 6
      (by decide)]

/-- The h-expansion of `m₇` (last row of the inverse of `gram7`). -/
def m7coeff : Fin 15 → ℤ := ![5, 5, 12, 11, -5, -1, -11, -7, -25, -22, -29, 17, 51, 65, -65]

theorem rowShape_seven : rowShape 7 = hshapes7 14 := Subtype.ext rfl

theorem m_seven : mRow 7 = ∑ l, m7coeff l • degreeHBasis 7 (hshapes7 l) := by
  rw [mRow, rowShape_seven]
  exact m_of_table hshapes7 exhaust7 inj7 gram7 gram_table7 m7coeff 14 (by decide)

/-- `(h_μ, e₇) = δ_{μ,(1⁷)}` on the fifteen partitions (EK (2.8)). -/
theorem h_e7 : ∀ l : Fin 15, quotientPairing (hP (pl7 l)) (EKElementaryQuotient.e 7) =
    if l = 0 then 1 else 0 := by
  have : ∀ l : Fin 15, fastEval (pl7 l) (List.replicate (pl7 l).length false) [7] [true] =
      if l = 0 then 1 else 0 := by decide +kernel
  intro l
  rw [← this l, hP, show EKElementaryQuotient.e 7 = ([7].map (col true)).prod by simp [col]]
  rw [show ((pl7 l).map EKElementaryQuotient.h) = (pl7 l).map (col false) by simp [col]]
  exact pairing_const false true _ _

/-- `(e₇, m₇) = 5`: the coefficient of `h₇` in the h-expansion of `e₇` is `5`. -/
theorem e7_m7 : quotientPairing (EKElementaryQuotient.e 7) (mRow 7).val = 5 := by
  rw [quotientPairing_symm]
  change quotientPairing ((mBasis 7 (rowShape 7) : degreePiece 7) : Q) _ = 5
  rw [mBasis_val hshapes7 pl7 hs7 _ m7coeff m_seven, map_sum, LinearMap.sum_apply]
  simp only [map_zsmul, LinearMap.smul_apply, smul_eq_mul, h_e7]
  simp [Fin.sum_univ_succ, m7coeff]

/-- **EK p. 25, "`f_n = ±m_n`", is false for `n = 7`:** `f₇` is not an integer multiple
of `m₇`. -/
theorem f_seven_ne (c : ℤ) : fBasis 7 (rowShape 7) ≠ c • mRow 7 := by
  intro h
  have h1 := e_f 7 (rowShape 7) (rowShape 7)
  rw [if_pos rfl, h, Submodule.coe_smul, map_zsmul, smul_eq_mul,
    ePartition_row (by decide), e7_m7] at h1
  omega

end OddMath.Frontier.EKRest
