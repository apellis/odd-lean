/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.CoveringQuantum.UDot.TensorGram.SignSpanning
import OddMath.CoveringQuantum.UDot.TensorGram.MixedNormalized

/-!
# Triangular expansion of matched normal words in the negative fiber

We fix a finite set `W` of words of length at most `L` given by
`SignSpanning.exists_signSpanning`: in the negative fiber (the image of the central idempotent
`Coefficients.negativeIdempotent`, i.e. the specialization `π ↦ -1`), the image of every word
of length at most `L` in the Serre presentation is a `ℚ(q)`-combination of the images of the
words of `W` of the same weight.

On the tensor product of a highest and a lowest integrable quotient, a matched normal word
`F_a 1 E_b` with `a, b ∈ W` acts on the tensor of the highest and the lowest vector by a unit
times the leading tensor `F_a v_Λ ⊗ E_b v_Μ`, up to tensors of words shorter in both factors
(`GenericVerma.NativeLeading.normalWord_leading`). In the negative fiber this becomes a
triangular expansion in the leading tensors of the pairs of words of `W`, with respect to the
total length, with unit diagonal coefficients. This is an input of the nondegeneracy of the form
on `U̇` at `π = -1` (Brundan–Ellis, arXiv:1701.04133v2, Theorem 10.1) without the
bar-consistency hypothesis (10.2). The argument is ours.
-/

noncomputable section
namespace OddMath.CoveringQuantum.UDot.SignExpansion
open PreF Coefficients TensorProduct GenericVerma MixedGram SignSpanning MixedNormalized

/-! ### The negative fiber -/

/-- The negative fiber is the specialization `π ↦ -1`. -/
@[simp] theorem sgn_negativeIdempotent : sgn negativeIdempotent = 1 := by
  simpa [split] using congrArg Prod.snd split_negativeIdempotent

/-- The bar involution specializes to the bar involution of `ℚ(q)`. -/
theorem sgn_bar (r : Coefficients.Ring) : sgn (bar r) = ratBar (sgn r) := by
  have h : (sgn : Coefficients.Ring →ₐ[RatFunc ℚ] RatFunc ℚ).toRingHom.comp bar =
      ratBar.comp (sgn : Coefficients.Ring →ₐ[RatFunc ℚ] RatFunc ℚ).toRingHom := by
    apply AdjoinRoot.ringHom_ext
    · ext c
      change sgn (bar (algebraMap (RatFunc ℚ) Coefficients.Ring c)) =
        ratBar (sgn (algebraMap (RatFunc ℚ) Coefficients.Ring c))
      rw [bar_algebraMap, AlgHom.commutes, AlgHom.commutes]
      rfl
    · change sgn (bar pi) = ratBar (sgn pi)
      rw [bar_pi, specialize_pi, map_neg, map_one]
  exact congrArg (fun f : Coefficients.Ring →+* RatFunc ℚ ↦ f r) h

theorem sgn_algebraMap (c : RatFunc ℚ) :
    sgn (algebraMap (RatFunc ℚ) Coefficients.Ring c) = c :=
  AlgHom.commutes _ c

/-- Scalars act on the negative fiber through their specialization at `π = -1`. -/
theorem negativeIdempotent_smul_smul {M : Type*} [AddCommMonoid M] [Module Coefficients.Ring M]
    (r : Coefficients.Ring) (z : M) :
    negativeIdempotent • r • z =
      algebraMap (RatFunc ℚ) Coefficients.Ring (sgn r) • negativeIdempotent • z := by
  rw [smul_smul, smul_smul, mul_comm (algebraMap _ _ _), negativeIdempotent_retract]

/-- The negative fiber of a pure tensor is the tensor of the negative fibers. -/
theorem negativeIdempotent_smul_tmul {M N : Type*} [AddCommMonoid M] [Module Coefficients.Ring M]
    [AddCommMonoid N] [Module Coefficients.Ring N] (x : M) (y : N) :
    negativeIdempotent • (x ⊗ₜ[Coefficients.Ring] y) =
      (negativeIdempotent • x) ⊗ₜ[Coefficients.Ring] (negativeIdempotent • y) := by
  rw [smul_tmul_smul, negativeIdempotent_mul_self]

/-- A bilinear form is determined on the negative fiber by its specialization at `π = -1`. -/
theorem sgn_bilin {M : Type*} [AddCommMonoid M] [Module Coefficients.Ring M]
    (B : LinearMap.BilinForm Coefficients.Ring M) (x y : M) :
    sgn (B (negativeIdempotent • x) (negativeIdempotent • y)) = sgn (B x y) := by
  simp only [LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul, map_mul,
    sgn_negativeIdempotent, one_mul]

/-! ### Spanning words of bounded length -/

variable {I X : Type*} [AddCommGroup X] [DecidableEq I]
variable (D : RootDatum I X)

/-- The specialized Gram matrix of the half form on a finite set of words. -/
def wordGram (W : Finset (List I)) : Matrix W W (RatFunc ℚ) :=
  Matrix.of fun a b ↦ sgn (D.form Coefficients.q pi (monomial Coefficients.Ring a.1)
    (monomial Coefficients.Ring b.1))

/-- The spanning property of a finite set of words of length at most `L`. -/
def Spans (L : ℕ) (W : Finset (List I)) : Prop :=
  ∀ a : List I, a.length ≤ L → ∃ c : List I → RatFunc ℚ,
    (∀ w, c w ≠ 0 → w ∈ W ∧ wordWeight w = wordWeight a) ∧
    negativeIdempotent • D.toSerreF Coefficients.q pi (monomial Coefficients.Ring a) =
      ∑ w ∈ W, algebraMap (RatFunc ℚ) Coefficients.Ring (c w) •
        negativeIdempotent • D.toSerreF Coefficients.q pi (monomial Coefficients.Ring w)

omit [DecidableEq I] in
theorem length_eq_of_wordWeight_eq {a b : List I} (h : wordWeight a = wordWeight b) :
    a.length = b.length := by
  rw [← BarDerivatives.wordWeight_sum, ← BarDerivatives.wordWeight_sum, h]

/-- **Spanning words of bounded length at `π = -1`.** There is a finite set of words of length
at most `L` with invertible specialized Gram matrix, spanning the negative fiber of the image of
every word of length at most `L` by words of the same weight. -/
theorem exists_spans [Finite I] (L : ℕ) :
    ∃ W : Finset (List I), (∀ w ∈ W, w.length ≤ L) ∧ (wordGram D W).det ≠ 0 ∧ Spans D L W := by
  classical
  let S : Finset (List I) := (List.finite_length_le I L).toFinset
  have hS : ∀ a, a ∈ S ↔ a.length ≤ L := fun a ↦ by simp [S]
  obtain ⟨W', hdet, hspan⟩ := exists_signSpanning D.toSuperCartanDatum S fun a ha b hb ↦
    (hS b).2 ((length_eq_of_wordWeight_eq hb).trans_le ((hS a).1 ha))
  let W := W'.map (Function.Embedding.subtype (· ∈ S))
  have hW : ∀ w, w ∈ W ↔ ∃ h : w ∈ S, ⟨w, h⟩ ∈ W' := fun w ↦ by
    simp [W, Finset.mem_map]
  refine ⟨W, fun w hw ↦ (hS w).1 ((hW w).1 hw).1, ?_, fun a ha ↦ ?_⟩
  · let e : W' ≃ W := Equiv.ofBijective
      (fun x ↦ ⟨x.1.1, (hW _).2 ⟨x.1.2, x.2⟩⟩)
      ⟨fun x y hxy ↦ by
          have h := congrArg Subtype.val hxy
          exact Subtype.ext (Subtype.ext h),
        fun w ↦ ⟨⟨⟨w.1, ((hW w.1).1 w.2).1⟩, ((hW w.1).1 w.2).2⟩, rfl⟩⟩
    rw [← Matrix.det_submatrix_equiv_self e]
    convert hdet using 2
    ext x y
    rfl
  · obtain ⟨c, hc, hsum⟩ := hspan ⟨a, (hS a).2 ha⟩
    refine ⟨fun v ↦ if h : v ∈ S then c ⟨v, h⟩ else 0, fun w hw ↦ ?_, ?_⟩
    · by_cases h : w ∈ S
      · simp only [h, ↓reduceDIte] at hw
        exact ⟨(hW w).2 ⟨h, (hc _ hw).1⟩, (hc _ hw).2⟩
      · simp [h] at hw
    · rw [hsum, Finset.sum_map]
      refine Finset.sum_congr rfl fun w _ ↦ ?_
      simp [w.2]

variable [DecidableEq X] (Λ Μ : X)

theorem spans_project {L : ℕ} {W : Finset (List I)} (hW : Spans D L W) (a : List I)
    (ha : a.length ≤ L) : ∃ c : List I → RatFunc ℚ,
      (∀ w, c w ≠ 0 → w ∈ W ∧ wordWeight w = wordWeight a) ∧
      negativeIdempotent • project D Λ (monomial Coefficients.Ring a) =
        ∑ w ∈ W, algebraMap (RatFunc ℚ) Coefficients.Ring (c w) •
          negativeIdempotent • project D Λ (monomial Coefficients.Ring w) := by
  obtain ⟨c, hc, h⟩ := hW a ha
  refine ⟨c, hc, ?_⟩
  have h' := congrArg (toIntegrable D Λ) h
  simpa only [map_smul, map_sum, project] using h'

/-! ### Expansion in leading tensors -/

/-- Pairs of words of `W`. -/
abbrev Pair (W : Finset (List I)) := W × W

/-- The total length of a pair of words. -/
def height {W : Finset (List I)} (t : Pair W) : ℕ := t.1.1.length + t.2.1.length

/-- Tensors of shorter words expand in the negative fiber in leading tensors of pairs of words of
`W` that are shorter in both factors. -/
theorem lower_expansion {L : ℕ} {W : Finset (List I)} (hW : Spans D L W) {m n : ℕ}
    (hm : m ≤ L + 1) (hn : n ≤ L + 1) {z : IntegrableQuotient D Λ ⊗[Coefficients.Ring]
      IntegrableQuotient D Μ} (hz : z ∈ NativeLeading.lowerBidegree D Λ Μ m n) :
    ∃ c : Pair W → RatFunc ℚ, (∀ w, c w ≠ 0 → w.1.1.length < m ∧ w.2.1.length < n) ∧
      negativeIdempotent • z = ∑ w : Pair W, algebraMap (RatFunc ℚ) Coefficients.Ring (c w) •
        negativeIdempotent • leadingTensor D Λ Μ w.1.1 w.2.1 := by
  classical
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨a, b, ha, hb, rfl⟩ := hz
    obtain ⟨c₁, hc₁, h₁⟩ := spans_project D Λ hW a (by omega)
    obtain ⟨c₂, hc₂, h₂⟩ := spans_project D Μ hW b (by omega)
    refine ⟨fun w ↦ c₁ w.1.1 * c₂ w.2.1, fun w hw ↦ ?_, ?_⟩
    · have h₁' := (hc₁ _ (left_ne_zero_of_mul hw)).2
      have h₂' := (hc₂ _ (right_ne_zero_of_mul hw)).2
      rw [length_eq_of_wordWeight_eq h₁', length_eq_of_wordWeight_eq h₂']
      exact ⟨ha, hb⟩
    · rw [negativeIdempotent_smul_tmul, h₁, h₂, sum_tmul, Fintype.sum_prod_type,
        ← Finset.sum_coe_sort W]
      refine Finset.sum_congr rfl fun w₁ _ ↦ ?_
      rw [tmul_sum, ← Finset.sum_coe_sort W]
      refine Finset.sum_congr rfl fun w₂ _ ↦ ?_
      rw [smul_tmul_smul, map_mul, leadingTensor, negativeIdempotent_smul_tmul]
  | zero => exact ⟨0, by simp, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, hc, hx⟩ := hx
    obtain ⟨c', hc', hy⟩ := hy
    refine ⟨c + c', fun w hw ↦ ?_, ?_⟩
    · by_cases h : c w = 0
      · exact hc' w (by simpa [h] using hw)
      · exact hc w h
    · rw [smul_add, hx, hy, ← Finset.sum_add_distrib]
      simp only [Pi.add_apply, map_add, add_smul]
  | smul r x _ hx =>
    obtain ⟨c, hc, hx⟩ := hx
    refine ⟨fun w ↦ sgn r * c w, fun w hw ↦ hc w (right_ne_zero_of_mul hw), ?_⟩
    rw [negativeIdempotent_smul_smul, hx, Finset.smul_sum]
    simp only [map_mul, mul_smul]

/-- **Triangular expansion.** In the negative fiber, a scalar multiple of the action of a matched
normal word with words of `W` on the tensor of the highest and the lowest vector is a
combination of leading tensors of pairs of words of `W`: the diagonal coefficient is the
specialization of the scalar times the leading unit, and the other coefficients vanish unless
both words are shorter. -/
theorem normalWord_expansion {L : ℕ} {W : Finset (List I)} (hW : Spans D L W)
    (hWL : ∀ w ∈ W, w.length ≤ L) (s : Bool) (κ : Coefficients.Ring) (t : Pair W) :
    ∃ P : Pair W → RatFunc ℚ,
      P t = sgn (κ * NativeLeading.leadingScalar D Λ Μ s t.1.1 t.2.1) ∧
      (∀ w, w ≠ t → P w ≠ 0 → w.1.1.length < t.1.1.length ∧ w.2.1.length < t.2.1.length) ∧
      negativeIdempotent • κ • tensorRepresentation D Λ Μ s
          (normalWord D Coefficients.q pi t.1.1 t.2.1 (Λ - Μ))
          (toIntegrable D Λ 1 ⊗ₜ[Coefficients.Ring] toIntegrable D Μ 1) =
        ∑ w : Pair W, algebraMap (RatFunc ℚ) Coefficients.Ring (P w) •
          negativeIdempotent • leadingTensor D Λ Μ w.1.1 w.2.1 := by
  classical
  obtain ⟨-, r, hr, he⟩ := NativeLeading.normalWord_leading D Λ Μ s t.1.1 t.2.1
  have ht₁ := hWL _ t.1.2
  have ht₂ := hWL _ t.2.2
  obtain ⟨c, hc, hce⟩ := lower_expansion D Λ Μ hW (by omega) (by omega) hr
  refine ⟨fun w ↦ (if w = t then sgn (κ * NativeLeading.leadingScalar D Λ Μ s t.1.1 t.2.1)
    else 0) + sgn κ * c w, ?_, fun w hwt hw ↦ ?_, ?_⟩
  · have : c t = 0 := by
      by_contra h
      exact lt_irrefl _ (hc t h).1
    simp [this]
  · simp only [hwt, ite_false, zero_add] at hw
    exact hc w (right_ne_zero_of_mul hw)
  · rw [he, smul_add, smul_smul, smul_add, negativeIdempotent_smul_smul, negativeIdempotent_smul_smul, hce,
      Finset.smul_sum]
    simp only [map_add, add_smul, Finset.sum_add_distrib, map_mul, mul_smul,
      apply_ite (algebraMap (RatFunc ℚ) Coefficients.Ring), ite_smul, map_zero, zero_smul,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rfl

end OddMath.CoveringQuantum.UDot.SignExpansion
