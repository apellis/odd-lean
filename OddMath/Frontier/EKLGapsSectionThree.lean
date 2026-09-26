import OddMath.Frontier.OnhReflection
import OddMath.Frontier.OmissionCanonical
import OddMath.Frontier.ThickRelations
import OddMath.Frontier.ThickDots
import OddMath.Frontier.ShuffleLemma

/-! # EKL: the proof of the OWL, (3.49), Remark 3.4, Definition 4.10 and (4.26)

EKL = Ellis–Khovanov–Lauda, *The odd nilHecke algebra and its diagrammatics*,
arXiv:1111.1320v1. Rank `a = n+2`; products act rightmost first; indices are 0-based.

* Proof of Lemma 2.18 (OWL), p. 17: the reordering `D'_a = (∂_{a-1}⋯∂_1)(∂_{a-1}⋯∂_2)⋯∂_{a-1}`
  (`OmissionCanonical.word`, block form `OmissionCanonical.word_blocks`) satisfies
  `D'_a = (-1)^{C(a,4)} D_a` (`owl_Dprime_sign`), not `(-1)^{C(a,3)} D_a`: the printed sign fails
  at `a = 3` (`owl_Dprime_printed_false`) and holds iff `C(a,3) ≡ C(a,4) (mod 2)`
  (`owl_Dprime_printed_iff`). The "Explicitly, `D_a = …`" line fails at `a = 4`
  (`owl_explicit_false`, `owl_explicit_iff`).
* (3.49), p. 30: the printed right side omits `x_{a-1}`; `ψσ(x^{δ_a})` is not a multiple of any
  monomial without `x_{a-1}`, for every `a ≥ 3` (`eq_3_49_printed_false`); the correct form is
  `OnhReflection.eq_3_49`.
* Remark 3.4, p. 25: the reflection of (3.28) in a horizontal axis, `∂̄_2 ∂_1 ∂_2 = ∂_1 ∂_2 ∂̄_1`
  (1-based), is false in `ONH_3` (`remark_3_4_reflection`).
* Definition 4.10, p. 37: the two expressions for `ŝ_α` agree (`def_4_10`), via
  `ψσ(x^E) = x^{E ∘ rev}` (`reverse_sigma_dotMonomial`).
* (4.26), p. 35: the printed identity (with or without the stray tilde) is false
  (`eq_4_26_printed_false`, `eq_4_26_printed_tilde_false`); corrected: `eq_4_26`.
-/

namespace OddMath.Frontier.EKLGaps
open NilHeckeAction NilCoxeterWords NilHeckeRightBasis OnhReflection
open ZeroHecke (DElem staircaseElem zeroHecke)
open OddMath.SkewPolynomial (SkewPolynomial monomial generator)
noncomputable section

/-! ### The sign of `D'_a` in the proof of the OWL (Lemma 2.18) -/

/-- The word of `D'_a = (∂_{a-1}⋯∂_1)(∂_{a-1}⋯∂_2)⋯(∂_{a-1}∂_{a-2})∂_{a-1}` (proof of the OWL,
p. 17; `D'_2 = ∂_1`, `D'_a = ∂_{a-1}⋯∂_1 D'_{a-1}` with `D'_{a-1}` on the last `a-1` strands, see
`OmissionCanonical.word_blocks`) is the reversed vertical reflection of the word of `D_a`. -/
theorem owlWord_eq (n : ℕ) :
    OmissionCanonical.word n = ((LongestDivided.wordIn n (n+2) le_rfl).map Fin.rev).reverse := by
  rw [OmissionCanonical.word, List.map_reverse]

/-- `D'_a = ψσ(D_a)`. -/
theorem owl_Dprime_eq_reverse_sigma (n : ℕ) :
    product (OmissionCanonical.word n) = MulOpposite.unop (reverseHom n (sigma n (DElem n))) := by
  rw [reverse_sigma_DElem_word, owlWord_eq]

/-- **The sign relating `D'_a` to `D_a` in the proof of the OWL, corrected**: for every
`a = n+2 ≥ 2`, `D'_a = (-1)^{C(a,4)} D_a`. -/
theorem owl_Dprime_sign (n : ℕ) :
    product (OmissionCanonical.word n) = (-1 : ℤ)^((n+2).choose 4) • DElem n := by
  rw [owl_Dprime_eq_reverse_sigma, reverse_sigma_DElem]

/-- The printed sign `(-1)^{C(a,3)}` is correct exactly when `C(a,3) ≡ C(a,4) (mod 2)`. -/
theorem owl_Dprime_printed_iff (n : ℕ) :
    product (OmissionCanonical.word n) = (-1 : ℤ)^((n+2).choose 3) • DElem n ↔
      (n+2).choose 3 % 2 = (n+2).choose 4 % 2 := by
  rw [owl_Dprime_sign]
  constructor
  · intro h
    have h' := smul_DElem_inj h
    rw [neg_one_pow_eq_pow_mod_two (R := ℤ),
      neg_one_pow_eq_pow_mod_two (R := ℤ) (n := (n+2).choose 3)] at h'
    rcases Nat.mod_two_eq_zero_or_one ((n+2).choose 3) with h3 | h3 <;>
      rcases Nat.mod_two_eq_zero_or_one ((n+2).choose 4) with h4 | h4 <;>
      rw [h3, h4] at h' ⊢ <;> norm_num at h' ⊢
  · intro h
    rw [neg_one_pow_eq_pow_mod_two (R := ℤ) (n := (n+2).choose 3), h,
      ← neg_one_pow_eq_pow_mod_two]

/-- **The printed sign `D'_a = (-1)^{C(a,3)} D_a` in the proof of the OWL is false** at `a = 3`:
there `D'_3 = ∂_2∂_1∂_2 = D_3`, while `C(3,3) = 1`. -/
theorem owl_Dprime_printed_false :
    product (OmissionCanonical.word 1) ≠ (-1 : ℤ)^((1+2).choose 3) • DElem 1 := by
  rw [Ne, owl_Dprime_printed_iff]
  decide

theorem owl_Dprime_printed_false' :
    ¬ ∀ n : ℕ, product (OmissionCanonical.word n) = (-1 : ℤ)^((n+2).choose 3) • DElem n :=
  fun h => owl_Dprime_printed_false (h 1)

/-- The line "Explicitly, `D_a = (∂_{a-1}⋯∂_1)⋯(∂_{a-1}∂_{a-2})∂_{a-1}`" of the proof of the OWL is
false at `a = 4` (the displayed word is `D'_4 = -D_4`); it holds exactly when `C(a,4)` is even. -/
theorem owl_explicit_iff (n : ℕ) :
    DElem n = product (OmissionCanonical.word n) ↔ (n+2).choose 4 % 2 = 0 := by
  rw [owl_Dprime_sign]
  constructor
  · intro h
    have h' := smul_DElem_inj (show (1 : ℤ) • DElem n = _ from (one_smul ℤ (DElem n)).trans h)
    rcases Nat.mod_two_eq_zero_or_one ((n+2).choose 4) with h4 | h4
    · exact h4
    · rw [neg_one_pow_eq_pow_mod_two (R := ℤ), h4] at h'; norm_num at h'
  · intro h
    rw [neg_one_pow_eq_pow_mod_two (R := ℤ), h, pow_zero, one_smul]

theorem owl_explicit_false : DElem 2 ≠ product (OmissionCanonical.word 2) := by
  rw [Ne, owl_explicit_iff]; decide

/-! ### (3.49) -/

/-- `ψσ(x^E) = x^{E ∘ rev}` for every ordered monomial `x^E = x_1^{E_1} ⋯ x_a^{E_a}`. -/
theorem reverse_sigma_dotMonomial (n : ℕ) (E : Fin (n+2) → ℕ) :
    MulOpposite.unop (reverseHom n (sigma n (NilHeckeBasis.dotMonomial E))) =
      NilHeckeBasis.dotMonomial (fun i => E (Fin.rev i)) := by
  have h1 : sigma n (NilHeckeBasis.dotMonomial E) =
      ((List.finRange (n+2)).map fun i => dot n (Fin.rev i) ^ E i).prod := by
    rw [NilHeckeBasis.dotMonomial, map_list_prod, List.map_map]
    congr 1
    apply List.map_congr_left
    intro i _
    simp
  rw [h1, unop_map_list_prod, List.map_map, ← List.map_reverse, List.finRange_reverse,
    List.map_map, NilHeckeBasis.dotMonomial]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply, Fin.rev_rev]
  exact unop_reverse_dot_pow i _

theorem action_dotMonomial_one (n : ℕ) (A : Fin (n+2) → ℕ) :
    action n (NilHeckeBasis.dotMonomial A) 1 = monomial A 1 := by
  rw [NilHeckeBasis.action_dotMonomial, mul_one]

/-- The right side of (3.49) as printed, `x_1^0 x_2^1 ⋯ x_{a-3}^{a-4} x_{a-2}^{a-1} x_a^{a-1}`
(`a = n+2`, 0-based exponent vector): `x_{a-1}` does not occur. -/
def printed349 (n : ℕ) : Fin (n+2) → ℕ := fun i =>
  if i.val = n then 0 else if i.val + 1 = n ∨ i.val = n+1 then n+1 else i.val

/-- **(3.49) as printed is false for every `a ≥ 3`**: `ψσ(x^{δ_a})` is not an integer multiple
of any ordered monomial in which `x_{a-1}` does not occur; in particular not of the printed
`x_1^0 x_2^1 ⋯ x_{a-2}^{a-1} x_a^{a-1}`. The correct form is `OnhReflection.eq_3_49`:
`ψσ(x^{δ_a}) = x_1^0 x_2^1 ⋯ x_{a-1}^{a-2} x_a^{a-1}`. -/
theorem eq_3_49_printed_false (n : ℕ) (E : Fin (n+3) → ℕ) (hE : E ⟨n+1, by omega⟩ = 0) (c : ℤ) :
    MulOpposite.unop (reverseHom (n+1) (sigma (n+1) (staircaseElem (n+1)))) ≠
      c • NilHeckeBasis.dotMonomial E := by
  intro h
  rw [eq_3_49_dotMonomial] at h
  have h2 := congrArg (fun x => action (n+1) x 1) h
  simp only [map_zsmul, LinearMap.smul_apply, action_dotMonomial_one] at h2
  have h3 := congrArg (fun f : SkewPolynomial (n+3) => f (fun i => i.val)) h2
  have hne : E ≠ fun i => i.val := fun e => by
    have := congrFun e ⟨n+1, by omega⟩
    rw [hE] at this
    simp at this
  simp only [monomial, Finsupp.smul_apply, Finsupp.single_eq_same,
    Finsupp.single_eq_of_ne hne, smul_zero] at h3
  exact one_ne_zero h3

theorem eq_3_49_printed_false' (n : ℕ) (c : ℤ) :
    MulOpposite.unop (reverseHom (n+1) (sigma (n+1) (staircaseElem (n+1)))) ≠
      c • NilHeckeBasis.dotMonomial (printed349 (n+1)) :=
  eq_3_49_printed_false n _ (by simp [printed349]) c

/-! ### Remark 3.4 -/

/-- **Remark 3.4: the reflection of (3.28) in a horizontal axis is false** (keeping the 0-Hecke
generator `∂̄_r = x_r ∂_r` as drawn): in `ONH_3`, `∂̄_2 ∂_1 ∂_2 ≠ ∂_1 ∂_2 ∂̄_1` (1-based), while
(3.28) itself, `∂_2 ∂_1 ∂̄_2 = ∂̄_1 ∂_2 ∂_1`, is `ThickRelations.eq_3_28`. On `x_1 x_3` the left
side gives `0` and the right side does not. -/
theorem remark_3_4_reflection :
    zeroHecke 1 1 * crossing 1 0 * crossing 1 1 ≠ crossing 1 0 * crossing 1 1 * zeroHecke 1 0 := by
  intro h
  have e := congrArg (fun x => action 1 x (generator 0 * generator 2 : SkewPolynomial 3)) h
  simp only [ZeroHecke.zeroHecke, map_mul, Module.End.mul_apply, action_crossing_apply,
    action_dot_apply] at e
  simp [AllRankDivided.divided_mul, AllRankDivided.divided_generator, AllRankDivided.s_generator,
    Equiv.swap_apply_def, Fin.ext_iff, AllRankDivided.divided_one,
    ThickDecomposition.skew_mul_zero, ThickDecomposition.skew_zero_mul] at e

/-! ### Definition 4.10 -/

/-- **Definition 4.10, the two forms agree**:
`ŝ_α = (-1)^{χ} D_a(σψ(x^{δ+α}))^{w_0}`, where `σψ(x^{δ+α}) = x_1^{α_a} x_2^{1+α_{a-1}} ⋯
x_a^{a-1+α_1}` (the second form is the definition `ThickDots.dualSchur`). Here the element
`σψ(x^{δ+α}) ∈ ONH_a` acts on `1 ∈ OPol_a`. -/
theorem def_4_10 (n : ℕ) (α : Fin (n+2) → ℕ) :
    ThickDots.dualSchur α = (-1 : ℤ)^(ThickDots.chi α) •
      SignedPermutation.skewAction (LongestElementary.longest (n+2))
        (LongestDivided.D (n+2) (action n (MulOpposite.unop (reverseHom n (sigma n
          (NilHeckeBasis.dotMonomial (fun k => n+1-k.val + α k))))) 1)) := by
  rw [ThickDots.dualSchur, reverse_sigma_dotMonomial, action_dotMonomial_one]
  congr 4
  funext k
  simp only [Fin.val_rev]
  omega

/-! ### (4.26) -/

section Shuffle
open AllRankDivided
variable {n : ℕ} (i : Fin (n+1))

local notation "xl" => generator i.castSucc
local notation "xr" => generator i.succ

/-- The printed (4.26), with the tilde on `x_i^{m+1}` dropped. -/
def Printed_4_26 (m k : ℕ) : Prop :=
  (-1 : ℤ)^m • divided i (xl ^ (m+k) * xr ^ m) - divided i (xl ^ (m+k-1) * xr ^ (m+1)) +
      (-1 : ℤ)^m • divided i (xl ^ (m+1) * xr ^ (m+k-1)) =
    (-1 : ℤ)^m • divided i (xl ^ (m+k) * xr ^ m) -
      (2 : ℤ) • ∑ j ∈ Finset.Icc 1 (k/2), (-1 : ℤ)^(m*(j+1)) •
        divided i (xl ^ (m+k-j) * xr ^ (m+j))

/-- The printed (4.26), literally, with `x̃_i^{m+1}` in the last term of the left side. -/
def Printed_4_26_tilde (m k : ℕ) : Prop :=
  (-1 : ℤ)^m • divided i (xl ^ (m+k) * xr ^ m) - divided i (xl ^ (m+k-1) * xr ^ (m+1)) +
      (-1 : ℤ)^m • divided i (PlacticEvaluation.tildeGenerator i.castSucc ^ (m+1) * xr ^ (m+k-1)) =
    (-1 : ℤ)^m • divided i (xl ^ (m+k) * xr ^ m) -
      (2 : ℤ) • ∑ j ∈ Finset.Icc 1 (k/2), (-1 : ℤ)^(m*(j+1)) •
        divided i (xl ^ (m+k-j) * xr ^ (m+j))

/-- **The printed (4.26) is false** (in every rank and at every position): with Lemma 4.4 it would
give the printed big odd shuffle (4.27), which fails at `m = 0`, `k = 7`
(`ShuffleLemma.big_shuffle_false`). -/
theorem eq_4_26_printed_false : ¬ ∀ m k : ℕ, Odd k → 3 ≤ k → Printed_4_26 i m k :=
  fun H => ShuffleLemma.big_shuffle_false i fun m k hk h3 =>
    (ShuffleLemma.shuffle_odd i m k hk h3).trans (H m k hk h3)

/-- The literal printed (4.26), with the tilde, is false at every position `i` with `i` even in
0-based indexing (there `x̃_i = x_i`), in particular at the first position. -/
theorem eq_4_26_printed_tilde_false (hi : Even i.val) :
    ¬ ∀ m k : ℕ, Odd k → 3 ≤ k → Printed_4_26_tilde i m k := by
  have ht : PlacticEvaluation.tildeGenerator (n := n+2) i.castSucc = xl := by
    rw [PlacticEvaluation.tildeGenerator, Fin.coe_castSucc, hi.neg_one_pow, one_smul]
  intro H
  exact eq_4_26_printed_false i fun m k hk h3 => by
    have := H m k hk h3
    rwa [Printed_4_26_tilde, ht] at this

/-- **(4.26), corrected**, for every odd `k ≥ 3` and every `m`:
`(-1)^m ∂_i(x_i^{m+k} x_{i+1}^m) - ∂_i(x_i^{m+k-1} x_{i+1}^{m+1}) + (-1)^m ∂_i(x_i^{m+1} x_{i+1}^{m+k-1})
= (-1)^m ∂_i(x_i^{m+k} x_{i+1}^m) - 2 Σ_{j=1}^{⌊k/2⌋} (-1)^{C(j,2)+(m+1)(j+1)} ∂_i(x_i^{m+k-j} x_{i+1}^{m+j})`;
both sides equal `∂_i(x_i^m x_{i+1}^{m+k})` (Lemma 4.4 and the corrected (4.27)). -/
theorem eq_4_26 (m k : ℕ) (hk : Odd k) (h3 : 3 ≤ k) :
    (-1 : ℤ)^m • divided i (xl ^ (m+k) * xr ^ m) - divided i (xl ^ (m+k-1) * xr ^ (m+1)) +
        (-1 : ℤ)^m • divided i (xl ^ (m+1) * xr ^ (m+k-1)) =
      (-1 : ℤ)^m • divided i (xl ^ (m+k) * xr ^ m) -
        (2 : ℤ) • ∑ j ∈ Finset.Icc 1 (k/2), (-1 : ℤ)^(j.choose 2 + (m+1)*(j+1)) •
          divided i (xl ^ (m+k-j) * xr ^ (m+j)) :=
  (ShuffleLemma.shuffle_odd i m k hk h3).symm.trans (ShuffleLemma.big_shuffle i m k hk)

end Shuffle

end
end OddMath.Frontier.EKLGaps
