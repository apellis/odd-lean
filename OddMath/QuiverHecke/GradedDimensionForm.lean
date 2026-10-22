/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CrossingDegree
import OddMath.CoveringQuantum.UDot.PositiveWordCoefficients
import OddMath.SKM.PositiveDecoratedCoefficients

/-!
# Graded dimensions of `Hom_H(t, t')` and the form on `f`

For a covering root datum `Q` (Brundan–Ellis, arXiv:1701.04133v2, §9) and words `t, t'`, the
normal forms `x^l ψ_w : t → t'` of the quiver Hecke supercategory `H` of `Q` count the Laurent
coefficients of the form `(θ_t, θ_{t'})` on the free algebra (BE2 §10; Lusztig's form,
normalized by `(θ_i, θ_i) = (1 - π_i q_i²)⁻¹`): after specializing `π` to `σ = ±1`, the
coefficient of `q^z` in `(θ_t, θ_{t'})` is `∑ σ^{par(x^l ψ_w)}` over the normal forms of degree `z`
(`coeff_form_eq_sum_fiber`). Since the normal forms are a basis of `Hom_H(t, t')`
(`QuiverHecke.basisNF`), this is the statement that the graded superdimension of `Hom_H(t, t')`
is `(θ_t, θ_{t'})`: the categorical pairing of words in `K₀(Ḣ_{q,π})` is the algebraic form.
This is the input to the injectivity argument of Hill–Wang, arXiv:1202.2769v2, Proposition 6.8,
used in BE2 Theorem 11.3 (as Khovanov–Lauda, arXiv:0803.4121v2, Proposition 3.4, in the even
case).

No bar-consistency or finiteness assumption on the colours is needed.
-/

noncomputable section

namespace OddMath.QuiverHecke

open Categorification.TypeA CoveringQuantum

variable {I X : Type*} [AddCommGroup X] [DecidableEq I]

/-- A sum over the inversions of `w`, as a double sum over pairs of strands. -/
theorem sum_invSet_eq {M : Type*} [AddCommMonoid M] {n : ℕ} (w : Equiv.Perm (Fin n))
    (f : Fin n → Fin n → M) :
    ∑ p ∈ invSet n w, f p.1 p.2 = ∑ r, ∑ s with r < s ∧ w s < w r, f r s := by
  rw [invSet, Finset.sum_filter, Fintype.sum_prod_type]
  simp only [Finset.sum_filter]

/-- **The graded superdimension of `Hom_H(t, t')` is the form `(θ_t, θ_{t'})`** (BE2 §§10–11;
Hill–Wang, arXiv:1202.2769v2, Proposition 6.8): for `σ = ±1`, the coefficient of `q^z` in the
Laurent expansion of `(θ_t, θ_{t'})` at `π = σ` is the sum of `σ^{par}` over the normal forms
`x^l ψ_w : t → t'` of degree `z`. -/
theorem coeff_form_eq_sum_fiber (Q : RootDatum I X) (σ : ℚ) (hσ : σ ^ 2 = 1)
    (t t' : List I) (z : ℤ) :
    (signLaurent σ hσ (Q.toSuperCartanDatum.form Coefficients.q Coefficients.pi
      (PreF.monomial Coefficients.Ring t) (PreF.monomial Coefficients.Ring t'))).coeff z =
      ∑ i ∈ (finite_deg_eq Q.toSKM Q.skmSymmetrizer t t' z).toFinset,
        σ ^ (i.par Q.toSKM).val := by
  classical
  rw [sum_fiber_nf]
  by_cases hlen : t'.length = t.length
  swap
  · -- unequal lengths: both sides vanish
    have hl : ∀ w : Equiv.Perm (Fin t.length), ¬ t' = List.ofFn fun a => t.get (w⁻¹ a) :=
      fun w h => hlen (by rw [h, List.length_ofFn])
    rw [Finset.filter_false_of_mem (fun w _ => hl w), Finset.sum_empty]
    rw [PreF.form_monomial_eq_zero _ _ t _ _ (PreF.monomial_mem_weightSpace t'), map_zero,
      HahnSeries.coeff_zero]
    intro hw
    have hp : t.Perm t' := List.perm_iff_count.mpr (fun i => by
      simpa only [← PreF.wordWeight_apply] using congrArg (fun ν : I →₀ ℕ => ν i) hw)
    exact hlen hp.length_eq.symm
  set C := Q.toSuperCartanDatum
  let a : Fin t.length → I := t.get
  let b : Fin t.length → I := fun r => t'.get (Fin.cast hlen.symm r)
  have ht : t = List.ofFn a := (List.ofFn_get t).symm
  have ht' : t' = List.ofFn b := by
    apply List.ext_get (by simp [hlen])
    intro n h₁ h₂
    simp [b]
  have hcond : ∀ w : Equiv.Perm (Fin t.length),
      (t' = List.ofFn fun r => t.get (w⁻¹ r)) ↔ ∀ r, a r = b (w r) := by
    intro w
    rw [ht', List.ofFn_inj]
    constructor
    · intro h r
      have := congrFun h (w r)
      simp only [Equiv.Perm.inv_def, Equiv.symm_apply_apply] at this
      exact this.symm
    · intro h
      funext r
      have := h (w⁻¹ r)
      simp only [Equiv.Perm.inv_def, Equiv.apply_symm_apply] at this
      exact this.symm
  conv_lhs => rw [ht, ht']
  rw [SuperCartanDatum.form, PreF.form_monomial_permutations]
  simp only [map_mul, map_sum, apply_ite, map_zero, Finset.mul_sum, HahnSeries.coeff_sum]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro w _
  by_cases hw : ∀ r, a r = b (w r)
  · rw [ite_eq_left hw, ite_eq_left ((hcond w).2 hw),
      signLaurent_norms, PreF.inversionWeight, signLaurent_crossings,
      mul_comm, shifted_series_coeff]
    obtain ⟨hf, hsum⟩ := SKM.shifted_counts_coeff C σ hσ a
      (∑ r, ∑ s with r < s ∧ w s < w r, -C.dot (a r) (a s)) z
      (∑ r, ∑ s with r < s ∧ w s < w r, C.parity (a r) * C.parity (a s))
    rw [← hsum]
    have hκ : crossDeg Q.toSKM Q.skmSymmetrizer t w =
        ∑ r, ∑ s with r < s ∧ w s < w r, -C.dot (a r) (a s) := by
      rw [crossDeg, sum_invSet_eq w (fun r s => gdeg Q.toSKM Q.skmSymmetrizer
        (.cross (t.get r) (t.get s)))]
      simp only [gdeg, RootDatum.skm_crossing_weight]
      rfl
    have hε : crossPar Q.toSKM t w =
        ∑ r, ∑ s with r < s ∧ w s < w r, C.parity (a r) * C.parity (a s) := by
      rw [crossPar, sum_invSet_eq w (fun r s => (Shape.cross (t.get r) (t.get s)).parity
        Q.toSKM)]
      rfl
    have hset : (finite_dotDeg_eq Q.toSKM Q.skmSymmetrizer t
        (z - crossDeg Q.toSKM Q.skmSymmetrizer t w)).toFinset = hf.toFinset := by
      have key : ∀ c : Fin t.length → ℕ, dotDeg Q.toSKM Q.skmSymmetrizer t c =
          ((∑ r, 2 * C.d (a r) * c r : ℕ) : ℤ) := by
        intro c
        simp only [dotDeg, gdeg, RootDatum.skmSymmetrizer_d, nsmul_eq_mul]
        push_cast
        exact Finset.sum_congr rfl fun r _ => by ring
      ext c
      simp only [Set.Finite.mem_toFinset]
      change dotDeg Q.toSKM Q.skmSymmetrizer t c = _ ↔ _ + _ = z
      rw [key, hκ]
      constructor <;> intro h <;> linarith
    rw [hset, hε]
    apply Finset.sum_congr rfl
    intro c _
    congr 3
    simp only [dotPar, nsmul_eq_mul, Shape.parity, RootDatum.toSKM_parity]
    rfl
  · rw [ite_eq_right hw, ite_eq_right (fun h => hw ((hcond w).1 h)), mul_zero,
      HahnSeries.coeff_zero]
