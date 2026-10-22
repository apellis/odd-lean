/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.GradedDimensionForm
import OddMath.QuiverHecke.HomDimension
import StringDiagrams.Super.GSKarPairing

/-!
# The categorical pairing of words is the form

For a covering root datum `Q` (Brundan–Ellis, arXiv:1701.04133v2, §9) and words `t, t'`, the
graded dimension pairing on `K₀` of the graded super Karoubi envelope of the quiver Hecke
supercategory `H` (string-diagrams-lean `GSKar.pairing`) takes the classes of the words to
`gdim HOM_H(t, t') = ∑ₙ (dim HOM(t, t')ₙ,₀ + dim HOM(t, t')ₙ,₁ π) qⁿ`. At `π = σ = ±1` its
coefficients are those of the form `(θ_t, θ_{t'})` on the free algebra (`pairing_word_eq_form`):
the categorical and algebraic forms agree on words. This is the comparison of forms in
Hill–Wang, arXiv:1202.2769v2, Proposition 6.8, used in BE2 Theorem 11.3 (Khovanov–Lauda,
arXiv:0803.4121v2, Proposition 3.4, in the even case).
-/

noncomputable section

namespace OddMath.QuiverHecke

open CategoryTheory StringDiagrams CoveringQuantum Module

variable {I X : Type*} [AddCommGroup X] [DecidableEq I] {K : Type*} [Field K]

omit [DecidableEq I] in
/-- The number of normal forms of degree `n` and parity `p`, as a filter of the normal forms of
degree `n`. -/
theorem card_par_deg {D : SKM.Datum I X} (sy : SKM.Symmetrizer D) (t t' : List I) (n : ℤ)
    (p : ZMod 2) :
    Nat.card {i : NFIdx t t' | i.par D = p ∧ i.deg D sy = n} =
      ((finite_deg_eq D sy t t' n).toFinset.filter fun i => i.par D = p).card := by
  rw [Nat.card_eq_card_finite_toFinset (finite_par_deg D sy t t' n p)]
  congr 1
  ext i
  simp [and_comm]

/-- **The categorical pairing of words is the form** (BE2 Theorem 11.3; Hill–Wang,
arXiv:1202.2769v2, Proposition 6.8): for `σ = ±1`, the coefficient of `q^z` in the graded
dimension pairing `([t], [t'])` on `K₀(Ḣ_{q,π})`, evaluated at `π = σ`, is the coefficient of
`q^z` in the Laurent expansion of `(θ_t, θ_{t'})` at `π = σ`. -/
theorem pairing_word_eq_form (Q : RootDatum I X) (Sc : SKM.Scalars Q.toSKM K)
    (hc : Sc.Homogeneous) (σ : ℤ) (hσ : σ * σ = 1) (t t' : List I) (z : ℤ) :
    ((Zπ.eval σ hσ ((GSKar.pairing K (homBoundedBelow Q.toSKM Q.skmSymmetrizer Sc hc)
        (GSKar.of K (hObj Q.toSKM Sc Q.skmSymmetrizer hc t) 0 0)
        (K₀.mk (GSKar.of K (hObj Q.toSKM Sc Q.skmSymmetrizer hc t') 0 0))).coeff z) : ℤ) : ℚ) =
      (signLaurent (σ : ℚ) (by rw [pow_two]; exact_mod_cast hσ)
        (Q.toSuperCartanDatum.form Coefficients.q Coefficients.pi
          (PreF.monomial Coefficients.Ring t) (PreF.monomial Coefficients.Ring t'))).coeff z := by
  rw [coeff_form_eq_sum_fiber, GSKar.coeff_pairing, GSKar.superCoeff_of]
  change ((Zπ.eval σ hσ ((finrank K (homPiece Q.toSKM Sc Q.skmSymmetrizer hc t t' z 0) : Zπ) +
    (finrank K (homPiece Q.toSKM Sc Q.skmSymmetrizer hc t t' z 1) : Zπ) * Zπ.π) : ℤ) : ℚ) = _
  rw [finrank_homPiece, finrank_homPiece, card_par_deg, card_par_deg, map_add, map_mul,
    map_natCast, map_natCast, Zπ.eval_π,
    ← Finset.sum_filter_add_sum_filter_not _ fun i => i.par Q.toSKM = 0]
  have h01 : ∀ a : ZMod 2, ¬ a = 0 ↔ a = 1 := by decide
  simp only [h01]
  set S := (finite_deg_eq Q.toSKM Q.skmSymmetrizer t t' z).toFinset
  have e0 : ∑ i ∈ S with i.par Q.toSKM = 0, (σ : ℚ) ^ (i.par Q.toSKM).val =
      (S.filter fun i => i.par Q.toSKM = 0).card := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    exact Finset.sum_congr rfl fun i hi => by rw [(Finset.mem_filter.1 hi).2]; simp
  have e1 : ∑ i ∈ S with i.par Q.toSKM = 1, (σ : ℚ) ^ (i.par Q.toSKM).val =
      (S.filter fun i => i.par Q.toSKM = 1).card * σ := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i hi => by
      rw [(Finset.mem_filter.1 hi).2, show (1 : ZMod 2).val = 1 from rfl]; simp
  rw [e0, e1]
  push_cast
  rfl
