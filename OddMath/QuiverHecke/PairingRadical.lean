/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CategoricalPairing
import OddMath.CoveringQuantum.Coefficients.Splitting

/-!
# Relations among classes of words lie in the radical of the form

Let `Q` be a covering root datum (Brundan–Ellis, arXiv:1701.04133v2, §9) and `H` its quiver
Hecke supercategory over a field. A finite combination `∑ c_t [t]` of classes of words in
`K₀(Ḣ_{q,π})`, with coefficients `c_t ∈ ℤπ[q, q⁻¹]`, that vanishes gives an element
`∑ c_t θ_t` of the free algebra over `ℚ(q)[π]/(π² - 1)` in the radical of the form
(`mem_radical_of_wordSum_eq_zero`). This is the injectivity argument of Hill–Wang,
arXiv:1202.2769v2, Proposition 6.8, used in BE2 Theorem 11.3 (Khovanov–Lauda,
arXiv:0803.4121v2, Proposition 3.4, in the even case): pairing with the class of a word `s`
is linear and computes `(θ_s, θ_t)` (`pairing_word_eq_form`), and an element of
`ℚ(q)[π]/(π² - 1)` is determined by its Laurent expansions at `π = ±1`.

## Main definitions

* `Coefficients.ofZπ : Zπ →+* ℚ(q)[π]/(π² - 1)` and
  `Coefficients.ofLaurent : Zπ[q, q⁻¹] →+* ℚ(q)[π]/(π² - 1)`, the inclusions of coefficients.
* `QuiverHecke.evalSeries σ : Zπ((q)) →+* ℚ((q))`, coefficientwise evaluation at `π = σ`.
-/

noncomputable section

open scoped LaurentSeries RatFunc

namespace OddMath.CoveringQuantum.Coefficients

open StringDiagrams

/-- The inclusion `Zπ → ℚ(q)[π]/(π² - 1)`, `π ↦ π`. -/
def ofZπ : Zπ →+* Ring :=
  Ideal.Quotient.lift _ (Polynomial.eval₂RingHom (Int.castRingHom Ring) pi) (by
    intro a ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    simp [pi_sq])

@[simp] theorem ofZπ_π : ofZπ Zπ.π = pi := by
  simp [ofZπ, Zπ.π]

/-- The inclusion `Zπ[q, q⁻¹] → ℚ(q)[π]/(π² - 1)`. -/
def ofLaurent : LaurentPolynomial Zπ →+* Ring := LaurentPolynomial.eval₂ ofZπ q

theorem specialize_congr {ε ε' : RatFunc ℚ} (hε : ε ^ 2 = 1) (hε' : ε' ^ 2 = 1) (h : ε = ε') :
    specialize ε hε = specialize ε' hε' := by
  subst h; rfl

/-- An element of `ℚ(q)[π]/(π² - 1)` whose Laurent expansions at `π = 1` and `π = -1` vanish is
zero. -/
theorem eq_zero_of_signLaurent (x : Ring)
    (h : ∀ (σ : ℤ) (hσ : (σ : ℚ) ^ 2 = 1), signLaurent (σ : ℚ) hσ x = 0) : x = 0 := by
  have hs : ∀ (σ : ℤ) (hσ : (σ : ℚ) ^ 2 = 1) (hσ' : (RatFunc.C (σ : ℚ)) ^ 2 = 1),
      specialize (RatFunc.C (σ : ℚ)) hσ' x = 0 := by
    intro σ hσ hσ'
    apply (algebraMap (RatFunc ℚ) (LaurentSeries ℚ)).injective
    rw [map_zero]
    exact h σ hσ
  rw [eq_iff_specialize_eq, map_zero, map_zero]
  constructor
  · rw [specialize_congr _ (by simp) (by simp : (1 : RatFunc ℚ) = RatFunc.C ((1 : ℤ) : ℚ))]
    exact hs 1 (by norm_num) _
  · rw [specialize_congr _ (by simp)
      (by simp : (-1 : RatFunc ℚ) = RatFunc.C ((-1 : ℤ) : ℚ))]
    exact hs (-1) (by norm_num) _

end OddMath.CoveringQuantum.Coefficients

namespace OddMath.QuiverHecke

open CategoryTheory StringDiagrams CoveringQuantum Module

/-- Coefficientwise evaluation `Zπ((q)) → ℚ((q))` at `π = σ`. -/
def evalSeries (σ : ℤ) (hσ : σ * σ = 1) : LaurentSeries Zπ →+* LaurentSeries ℚ where
  toFun x := x.map ((Int.castRingHom ℚ).comp (Zπ.eval σ hσ))
  map_one' := HahnSeries.map_one ((Int.castRingHom ℚ).comp (Zπ.eval σ hσ)).toMonoidWithZeroHom
  map_mul' _ _ := HahnSeries.map_mul ((Int.castRingHom ℚ).comp (Zπ.eval σ hσ)).toNonUnitalRingHom
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp

@[simp] theorem coeff_evalSeries (σ : ℤ) (hσ : σ * σ = 1) (x : LaurentSeries Zπ) (z : ℤ) :
    (evalSeries σ hσ x).coeff z = (Zπ.eval σ hσ (x.coeff z) : ℚ) := rfl

theorem sq_eq_one_of_mul_self {σ : ℤ} (hσ : σ * σ = 1) : (σ : ℚ) ^ 2 = 1 := by
  rw [pow_two]; exact_mod_cast hσ

/-- Expanding a Laurent polynomial and evaluating at `π = σ` is the same as including it in
`ℚ(q)[π]/(π² - 1)` and expanding at `π = σ`. -/
theorem evalSeries_laurentToSeries (σ : ℤ) (hσ : σ * σ = 1) (r : LaurentPolynomial Zπ) :
    evalSeries σ hσ (laurentToSeries r) =
      signLaurent (σ : ℚ) (sq_eq_one_of_mul_self hσ) (Coefficients.ofLaurent r) := by
  set f : LaurentPolynomial Zπ →+* LaurentSeries ℚ := (evalSeries σ hσ).comp laurentToSeries
  set g : LaurentPolynomial Zπ →+* LaurentSeries ℚ :=
    (signLaurent (σ : ℚ) (sq_eq_one_of_mul_self hσ)).comp Coefficients.ofLaurent
  change f r = g r
  have hC : f.comp LaurentPolynomial.C = g.comp LaurentPolynomial.C := by
    apply Ideal.Quotient.ringHom_ext
    apply Polynomial.ringHom_ext'
    · exact RingHom.ext_int _ _
    · change f (LaurentPolynomial.C Zπ.π) = g (LaurentPolynomial.C Zπ.π)
      simp only [f, g, RingHom.comp_apply, laurentToSeries_C, Coefficients.ofLaurent,
        LaurentPolynomial.eval₂_C, Coefficients.ofZπ_π, signLaurent_pi]
      change HahnSeries.map (HahnSeries.C Zπ.π) ((Int.castRingHom ℚ).comp (Zπ.eval σ hσ)) = _
      rw [HahnSeries.map_C]
      simp [Zπ.eval_π]
  have hT1 : f (LaurentPolynomial.T 1) = g (LaurentPolynomial.T 1) := by
    simp only [f, g, RingHom.comp_apply, laurentToSeries_T_one, Coefficients.ofLaurent,
      LaurentPolynomial.eval₂_T, signLaurent_q_zpow]
    ext z
    simp [HahnSeries.coeff_single]
  have hT2 : f (LaurentPolynomial.T (-1)) = g (LaurentPolynomial.T (-1)) := by
    simp only [f, g, RingHom.comp_apply, laurentToSeries_T_neg_one, Coefficients.ofLaurent,
      LaurentPolynomial.eval₂_T, signLaurent_q_zpow]
    ext z
    simp [HahnSeries.coeff_single]
  have hT : ∀ n : ℤ, f (LaurentPolynomial.T n) = g (LaurentPolynomial.T n) := by
    intro n
    obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
    · have e := LaurentPolynomial.T_pow (R := Zπ) 1 m
      rw [mul_one] at e
      rw [← e, map_pow, map_pow, hT1]
    · have e := LaurentPolynomial.T_pow (R := Zπ) (-1) m
      rw [mul_neg_one] at e
      rw [← e, map_pow, map_pow, hT2]
  induction r using LaurentPolynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, hp, hq]
  | C_mul_T n a =>
    rw [map_mul, map_mul, hT n]
    exact congrArg (· * g (LaurentPolynomial.T n)) (RingHom.congr_fun hC a)

variable {I X : Type*} [AddCommGroup X] [DecidableEq I] {K : Type*} [Field K]

/-- The pairing of words, evaluated at `π = σ`, is the Laurent expansion of the form at
`π = σ`. -/
theorem evalSeries_pairing_word (Q : RootDatum I X) (Sc : SKM.Scalars Q.toSKM K)
    (hc : Sc.Homogeneous) (σ : ℤ) (hσ : σ * σ = 1) (t t' : List I) :
    evalSeries σ hσ (GSKar.pairing K (homBoundedBelow Q.toSKM Q.skmSymmetrizer Sc hc)
        (GSKar.of K (hObj Q.toSKM Sc Q.skmSymmetrizer hc t) 0 0)
        (K₀.mk (GSKar.of K (hObj Q.toSKM Sc Q.skmSymmetrizer hc t') 0 0))) =
      signLaurent (σ : ℚ) (sq_eq_one_of_mul_self hσ)
        (Q.toSuperCartanDatum.form Coefficients.q Coefficients.pi
          (PreF.monomial Coefficients.Ring t) (PreF.monomial Coefficients.Ring t')) := by
  ext z
  rw [coeff_evalSeries]
  exact pairing_word_eq_form Q Sc hc σ hσ t t' z

/-- **Relations among words lie in the radical** (BE2 Theorem 11.3; Hill–Wang,
arXiv:1202.2769v2, Proposition 6.8): if `∑ c_t [t] = 0` in `K₀(Ḣ_{q,π})` with
`c_t ∈ ℤπ[q, q⁻¹]`, then `∑ c_t θ_t` lies in the radical of the form on the free algebra over
`ℚ(q)[π]/(π² - 1)`. -/
theorem mem_radical_of_wordSum_eq_zero (Q : RootDatum I X) (Sc : SKM.Scalars Q.toSKM K)
    (hc : Sc.Homogeneous) (c : List I →₀ LaurentPolynomial Zπ)
    (h : letI := GSKar.moduleLaurent K (HGr Q.toSKM Sc Q.skmSymmetrizer hc)
      (c.sum fun t r => r • K₀.mk (GSKar.of K (hObj Q.toSKM Sc Q.skmSymmetrizer hc t) 0 0)) = 0) :
    (c.sum fun t r => Coefficients.ofLaurent r • PreF.monomial Coefficients.Ring t) ∈
      PreF.radical (Q.toSuperCartanDatum.chi Coefficients.q Coefficients.pi)
        (Q.toSuperCartanDatum.norm Coefficients.q Coefficients.pi) := by
  let := GSKar.moduleLaurent K (HGr Q.toSKM Sc Q.skmSymmetrizer hc)
  set C := Q.toSuperCartanDatum
  set x := c.sum fun t r => Coefficients.ofLaurent r • PreF.monomial Coefficients.Ring t
  have hs : ∀ s : List I, C.form Coefficients.q Coefficients.pi
      (PreF.monomial Coefficients.Ring s) x = 0 := by
    intro s
    apply Coefficients.eq_zero_of_signLaurent
    intro σ hσ'
    have hσ : σ * σ = 1 := by
      have : ((σ * σ : ℤ) : ℚ) = 1 := by push_cast; rw [← pow_two]; exact hσ'
      exact_mod_cast this
    have h0 := congrArg (fun y => evalSeries σ hσ (GSKar.pairing K
      (homBoundedBelow Q.toSKM Q.skmSymmetrizer Sc hc)
      (GSKar.of K (hObj Q.toSKM Sc Q.skmSymmetrizer hc s) 0 0) y)) h
    simp only [map_zero] at h0
    rw [← h0]
    simp only [x, Finsupp.sum, map_sum, LinearMap.map_smul, smul_eq_mul, map_mul,
      GSKar.pairing_smul, evalSeries_laurentToSeries, evalSeries_pairing_word]
    rfl
  rw [PreF.mem_radical_iff]
  intro y
  have hy : y ∈ Submodule.span Coefficients.Ring (Set.range (PreF.monomial Coefficients.Ring)) := by
    rw [PreF.span_monomial]; trivial
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨s, rfl⟩ := hy
    rw [← SuperCartanDatum.form, SuperCartanDatum.form_comm]
    exact hs s
  | zero => simp
  | add a b _ _ ha hb => rw [map_add, ha, hb, add_zero]
  | smul r a _ ha => rw [map_smul, ha, smul_zero]

end OddMath.QuiverHecke
