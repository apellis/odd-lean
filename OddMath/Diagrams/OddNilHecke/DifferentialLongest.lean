import OddMath.Diagrams.OddNilHecke.Differential
import OddMath.Frontier.NilCoxeterWords

/-!
# The differential of the longest odd divided difference

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*,
arXiv:1504.01712v2, §2.3 ((2.39), Lemma 2.17) and §3.2 (Lemma 3.4 with its proof (3.13)–(3.15),
Lemma 3.5 with (3.16)–(3.17)).

In the diagrammatic endomorphism algebra of `N` strands (any commutative ring `R`), let
`longest R N k` be the product of crossings along odd-lean's literal word
`LongestDivided.coxeterWord k`, `∂_0 (∂_1 ∂_0) ⋯ (∂_{k-2} ⋯ ∂_0)` in written order; this is
Ellis–Qi's reduced expression (2.39) `∂_{w_0} = ∂_1(∂_2∂_1)⋯(∂_{n-1}⋯∂_1)` on the first `k`
strands, and satisfies their recursion (3.14). Strands are numbered from `0`.

Main results:

* `longest_mul_ψ`: `∂_{w_0} ∂_j = 0` for `j + 1 < k` (a crossing below the longest element
  among its strands vanishes);
* `longest_mul_dn_one` ((3.15)):
  `∂^{(k)} (∂_{k-1} ⋯ ∂_1) = ∂^{(k+1)} x_0 - (-1)^{binom(k+1,2)} x_k ∂^{(k+1)}`;
* `d_longest` (**Ellis–Qi Lemma 3.4**, 0-indexed, for every `k ≤ N`):
  `d(∂_{w_0}) = Σ_{i<k} {i} x_i ∂_{w_0} - (-1)^{binom(k,2)} Σ_{i<k} {k-1-i} ∂_{w_0} x_i`,
  where `{m} = m mod 2`. In Ellis–Qi's 1-indexed notation (3.13) this is
  `Σ_{i=1}^n {i-1} x_i ∂_{w_0} - (-1)^{binom(n,2)} Σ_{i=1}^n {n-i} ∂_{w_0} x_i`;
* `d_staircase` ((3.17)): `d(x^δ) = Σ_{i<k} {k-1-i} x_i x^δ` for
  `x^δ = x_0^{k-1} x_1^{k-2} ⋯ x_{k-2}`;
* `d_idem` (**Ellis–Qi Lemma 3.5**, (3.16)): for `e = (-1)^{binom(k,3)} ∂_{w_0} x^δ`
  (Lemma 2.17 (4)), `d(e) = Σ_{i<k} {i} x_i e`.

The proofs follow Ellis–Qi's: the Leibniz rule reduces `d(∂^{(k+1)})` to `d(∂^{(k)})`, the right
kernel of `∂^{(k)}` kills all but one deletion of a crossing, and (3.15) slides the remaining
term. The statements hold on the first `k ≤ N` strands of `N`; `k = N` is the printed case.
-/

noncomputable section

namespace OddMath.Diagrams.OddNilHecke

open CategoryTheory StringDiagrams
open OddMath.Frontier LongestDivided

variable (R : Type*) [CommRing R] (N : ℕ)

/-! ## Products of crossings along words -/

/-- The product of crossings along a written word (the leftmost letter is drawn on top). -/
def ψw (l : List ℕ) : End ((pres R).obj (strands N)) := (l.map (ψ R N)).prod

@[simp] theorem ψw_nil : ψw R N [] = 1 := rfl

@[simp] theorem ψw_cons (a : ℕ) (l : List ℕ) : ψw R N (a :: l) = ψ R N a * ψw R N l := by
  simp [ψw]

theorem ψw_append (l₁ l₂ : List ℕ) : ψw R N (l₁ ++ l₂) = ψw R N l₁ * ψw R N l₂ := by
  simp [ψw, List.prod_append]

/-- The descending product `ψ_{a+b-1} ⋯ ψ_{a+1} ψ_a`. -/
def dn (a b : ℕ) : End ((pres R).obj (strands N)) := ψw R N (List.range' a b).reverse

@[simp] theorem dn_zero (a : ℕ) : dn R N a 0 = 1 := rfl

theorem dn_succ (a b : ℕ) : dn R N a (b + 1) = ψ R N (a + b) * dn R N a b := by
  simp [dn, List.range'_concat, List.reverse_append]

theorem dn_succ' (a b : ℕ) : dn R N a (b + 1) = dn R N (a + 1) b * ψ R N a := by
  simp [dn, List.range'_succ, List.reverse_cons, ψw_append]

theorem dn_add (a b c : ℕ) : dn R N a (b + c) = dn R N (a + b) c * dn R N a b := by
  induction c with
  | zero => simp
  | succ c ih => rw [← Nat.add_assoc, dn_succ, ih, dn_succ, mul_assoc, Nat.add_assoc]

/-- The literal longest word `∂_0 (∂_1 ∂_0) ⋯ (∂_{k-2} ⋯ ∂_0)` on the first `k` strands. -/
def longest (k : ℕ) : End ((pres R).obj (strands N)) := ψw R N (coxeterWord k)

@[simp] theorem longest_zero : longest R N 0 = 1 := rfl

theorem longest_succ (k : ℕ) : longest R N (k + 1) = longest R N k * dn R N 0 k := by
  simp [longest, coxeterWord, ψw_append, dn, List.range_eq_range']

/-! ## Sign commutations -/

theorem ψ_mul_ψw_far {j : ℕ} {l : List ℕ} (h : ∀ a ∈ l, j + 1 < a ∨ a + 1 < j) :
    ψ R N j * ψw R N l = (-1 : R) ^ l.length • (ψw R N l * ψ R N j) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have hja : ψ R N j * ψ R N a = -(ψ R N a * ψ R N j) :=
      eq_neg_of_add_eq_zero_left (ψ_mul_ψ_add_ψ_mul_ψ R (h a (by simp)))
    rw [ψw_cons, ← mul_assoc, hja, neg_mul, mul_assoc, ih (fun b hb => h b (by simp [hb])),
      mul_smul_comm, List.length_cons, pow_succ, mul_neg_one, neg_smul, mul_assoc]

theorem ψw_mul_ψ_far {j : ℕ} {l : List ℕ} (h : ∀ a ∈ l, j + 1 < a ∨ a + 1 < j) :
    ψw R N l * ψ R N j = (-1 : R) ^ l.length • (ψ R N j * ψw R N l) := by
  rw [ψ_mul_ψw_far R N h, smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul]

theorem x_mul_ψw {i : ℕ} {l : List ℕ} (h : ∀ a ∈ l, i ≠ a ∧ i ≠ a + 1) :
    x R N i * ψw R N l = (-1 : R) ^ l.length • (ψw R N l * x R N i) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have hia : x R N i * ψ R N a = -(ψ R N a * x R N i) :=
      eq_neg_of_add_eq_zero_left
        (x_mul_ψ_add_ψ_mul_x_of_ne R (h a (by simp)).1 (h a (by simp)).2)
    rw [ψw_cons, ← mul_assoc, hia, neg_mul, mul_assoc, ih (fun b hb => h b (by simp [hb])),
      mul_smul_comm, List.length_cons, pow_succ, mul_neg_one, neg_smul, mul_assoc]

theorem mem_range'_reverse {a b c : ℕ} : c ∈ (List.range' a b).reverse ↔ a ≤ c ∧ c < a + b := by
  simp only [List.mem_reverse, List.mem_range'_1]

theorem ψ_mul_dn_far {j a b : ℕ} (h : j + 1 < a ∨ a + b < j) :
    ψ R N j * dn R N a b = (-1 : R) ^ b • (dn R N a b * ψ R N j) := by
  rw [dn, ψ_mul_ψw_far R N (fun c hc => by rw [mem_range'_reverse] at hc; omega)]
  simp

theorem dn_mul_ψ_far {j a b : ℕ} (h : j + 1 < a ∨ a + b < j) :
    dn R N a b * ψ R N j = (-1 : R) ^ b • (ψ R N j * dn R N a b) := by
  rw [dn, ψw_mul_ψ_far R N (fun c hc => by rw [mem_range'_reverse] at hc; omega)]
  simp

theorem x_mul_dn {i a b : ℕ} (h : i < a ∨ a + b < i) :
    x R N i * dn R N a b = (-1 : R) ^ b • (dn R N a b * x R N i) := by
  rw [dn, x_mul_ψw R N (fun c hc => by rw [mem_range'_reverse] at hc; omega)]
  simp

/-! ## The right kernel of the longest element -/

theorem mul_dn_mul_ψ_eq_zero {X : End ((pres R).obj (strands N))} {a b j : ℕ}
    (hX : X * ψ R N j = 0) (ha : j + 1 < a) (Y : End ((pres R).obj (strands N))) :
    X * (dn R N a b * (ψ R N j * Y)) = 0 := by
  rw [← mul_assoc (dn R N a b), dn_mul_ψ_far R N (Or.inl ha), smul_mul_assoc, mul_smul_comm,
    mul_assoc, ← mul_assoc X, hX, zero_mul, smul_zero]

theorem dn_two_mul_ψ (j : ℕ) :
    dn R N 0 (j + 2) * ψ R N (j + 1) = (-1 : R) ^ j • (ψ R N j * dn R N 0 (j + 2)) := by
  have h0 : dn R N 0 (j + 2) = ψ R N (j + 1) * ψ R N j * dn R N 0 j := by
    rw [dn_succ, dn_succ, zero_add, zero_add, mul_assoc]
  rw [h0, mul_assoc, dn_mul_ψ_far R N (Or.inr (by omega)), mul_smul_comm, ← mul_assoc,
    ← mul_assoc, ← ψ_braid R N j]
  simp only [mul_assoc]

/-- A crossing below the longest element among its strands vanishes: `∂^{(k)} ∂_j = 0` for
`j + 1 < k`. -/
theorem longest_mul_ψ {k j : ℕ} (hj : j + 1 < k) : longest R N k * ψ R N j = 0 := by
  induction k generalizing j with
  | zero => omega
  | succ k ih =>
    rw [longest_succ]
    rcases j with _ | j
    · obtain ⟨k, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      rw [dn_succ', mul_assoc, mul_assoc, ψ_mul_ψ, mul_zero, mul_zero]
    · have hsplit : dn R N 0 k = dn R N (j + 2) (k - j - 2) * dn R N 0 (j + 2) := by
        conv_lhs => rw [show k = (j + 2) + (k - j - 2) by omega]
        rw [dn_add, zero_add]
      rw [hsplit, mul_assoc, mul_assoc, dn_two_mul_ψ, mul_smul_comm, mul_smul_comm,
        mul_dn_mul_ψ_eq_zero R N (ih (by omega)) (by omega), smul_zero]

/-- The words obtained from the cycle `∂_{k-1} ⋯ ∂_0` by deleting one letter `∂_j` with
`j ≥ 1` are killed by the longest element on `k` strands. -/
theorem longest_mul_dn_mul_dn {k j : ℕ} (hj1 : 1 ≤ j) (hjk : j < k) :
    longest R N k * (dn R N (j + 1) (k - 1 - j) * dn R N 0 j) = 0 := by
  obtain ⟨j, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  rw [dn_succ, zero_add]
  exact mul_dn_mul_ψ_eq_zero R N (longest_mul_ψ R N (by omega)) (by omega) _

/-! ## Sliding a dot through the longest element: Ellis–Qi (3.15) -/

theorem x_mul_longest {k i : ℕ} (hi : k ≤ i) :
    x R N i * longest R N k = (-1 : R) ^ k.choose 2 • (longest R N k * x R N i) := by
  rw [longest, x_mul_ψw R N (fun a ha => by have := coxeterWord_bound ha; omega),
    NilCoxeterWords.coxeterWord_length]

theorem longest_mul_x {k i : ℕ} (hi : k ≤ i) :
    longest R N k * x R N i = (-1 : R) ^ k.choose 2 • (x R N i * longest R N k) := by
  rw [x_mul_longest R N hi, smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul]

/-- The intermediate terms `∂^{(k)} ∂_{k-1} ⋯ ∂_j x_j ∂_{j-1} ⋯ ∂_0` of the proof of (3.15). -/
def slideTerm (k j : ℕ) : End ((pres R).obj (strands N)) :=
  longest R N k * (dn R N j (k - j) * (x R N j * dn R N 0 j))

theorem slideTerm_step {k j : ℕ} (hjk : j < k) (hk : k < N) :
    slideTerm R N k j =
      longest R N k * (dn R N (j + 1) (k - 1 - j) * dn R N 0 j) - slideTerm R N k (j + 1) := by
  have hmix := ψ_mul_x_add_x_mul_ψ R (n := N) (i := j) (by omega)
  have e : ψ R N j * (x R N j * dn R N 0 j) =
      dn R N 0 j - x R N (j + 1) * dn R N 0 (j + 1) := by
    rw [dn_succ, zero_add, ← mul_assoc, eq_sub_of_add_eq hmix, sub_mul, one_mul, mul_assoc]
  rw [slideTerm, slideTerm, show k - j = (k - 1 - j) + 1 by omega, dn_succ', mul_assoc, e,
    mul_sub, mul_sub, show k - (j + 1) = k - 1 - j by omega]

theorem slideTerm_eq {k j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) (hk : k < N) :
    slideTerm R N k j = (-1 : R) ^ (k - j) • slideTerm R N k k := by
  obtain ⟨m, rfl⟩ : ∃ m, k = j + m := ⟨k - j, by omega⟩
  induction m generalizing j with
  | zero => simp
  | succ m ih =>
    rw [slideTerm_step R N (by omega) hk, longest_mul_dn_mul_dn R N hj1 (by omega), zero_sub,
      show j + (m + 1) = (j + 1) + m by omega, ih (by omega) (by omega) (by omega),
      show j + 1 + m - (j + 1) = m by omega, show j + 1 + m - j = m + 1 by omega, pow_succ,
      mul_neg_one, neg_smul]

/-- **Ellis–Qi (3.15)** (0-indexed): for `1 ≤ k < N`,
`∂^{(k)} ∂_{k-1} ⋯ ∂_1 = ∂^{(k+1)} x_0 - (-1)^{binom(k+1,2)} x_k ∂^{(k+1)}`. -/
theorem longest_mul_dn_one {k : ℕ} (hk1 : 1 ≤ k) (hk : k < N) :
    longest R N k * dn R N 1 (k - 1) =
      longest R N (k + 1) * x R N 0 -
        (-1 : R) ^ (k + 1).choose 2 • (x R N k * longest R N (k + 1)) := by
  have h0 := slideTerm_step R N (j := 0) (by omega) hk
  rw [slideTerm_eq R N (le_refl 1) hk1 hk, dn_zero, mul_one] at h0
  have hT0 : slideTerm R N k 0 = longest R N (k + 1) * x R N 0 := by
    rw [slideTerm, dn_zero, mul_one, Nat.sub_zero, ← mul_assoc, ← longest_succ]
  have hTk : slideTerm R N k k =
      (-1 : R) ^ k.choose 2 • (x R N k * longest R N (k + 1)) := by
    rw [slideTerm, Nat.sub_self, dn_zero, one_mul, ← mul_assoc, longest_mul_x R N le_rfl,
      smul_mul_assoc, mul_assoc, ← longest_succ]
  rw [hT0, hTk, zero_add, smul_smul, Nat.sub_zero] at h0
  have hc : (-1 : R) ^ (k + 1).choose 2 = (-1) ^ k * (-1) ^ k.choose 2 := by
    rw [← pow_add, Nat.choose_succ_succ', Nat.choose_one_right]
  rw [hc]
  rw [eq_sub_iff_add_eq] at h0
  rw [← h0]
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [show m + 1 - 1 = m by omega, pow_succ]
  module

/-! ## Derivatives of products of crossings -/

theorem d_one : d R N 1 = 0 := by
  rw [Presentation.derivEnd_apply, End.one_def, Presentation.deriv_id]

/-- The Leibniz rule with a product of crossings as left factor. -/
theorem d_ψw_mul (l : List ℕ) (hl : ∀ a ∈ l, a + 1 < N) (Y : End ((pres R).obj (strands N))) :
    d R N (ψw R N l * Y) = d R N (ψw R N l) * Y + (-1 : R) ^ l.length • (ψw R N l * d R N Y) := by
  induction l with
  | nil =>
    rw [ψw_nil, one_mul, d_one, zero_mul, List.length_nil, pow_zero, one_smul, one_mul, zero_add]
  | cons a l ih =>
    have ha : a + 1 < N := hl a (by simp)
    have ih' := ih (fun b hb => hl b (by simp [hb]))
    rw [ψw_cons, mul_assoc, d_ψ_mul R ha, d_ψ_mul R ha, ih', List.length_cons, pow_succ]
    simp only [mul_add, sub_mul, mul_smul_comm, smul_mul_assoc, mul_assoc]
    module

/-- The derivative of a descending product of crossings: the alternating sum of the words
with one letter deleted (`d(∂_i) = 1`). -/
theorem d_dn (a b : ℕ) (h : a + b < N) :
    d R N (dn R N a b) = ∑ t ∈ Finset.range b,
      (-1 : R) ^ t • (dn R N (a + b - t) t * dn R N a (b - 1 - t)) := by
  induction b with
  | zero => rw [dn_zero, d_one, Finset.sum_range_zero]
  | succ b ih =>
    rw [dn_succ, d_ψ_mul R (by omega), ih (by omega), Finset.sum_range_succ', Finset.mul_sum]
    simp only [pow_zero, one_smul, dn_zero, one_mul, Nat.sub_zero,
      show a + (b + 1) - 0 = a + b + 1 by omega, show b + 1 - 1 - 0 = b by omega]
    rw [sub_eq_add_neg, add_comm, ← Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl fun t ht => ?_
    have ht' : t < b := Finset.mem_range.mp ht
    have hψ : ψ R N (a + b) * dn R N (a + b - t) t = dn R N (a + b - t) (t + 1) := by
      rw [dn_succ, show a + b - t + t = a + b by omega]
    rw [mul_smul_comm, ← mul_assoc, hψ, show a + (b + 1) - (t + 1) = a + b - t by omega,
      show b + 1 - 1 - (t + 1) = b - 1 - t by omega, pow_succ, mul_neg_one, neg_smul]

/-- `∂^{(k)} d(∂_{k-1} ⋯ ∂_0) = (-1)^{k-1} ∂^{(k)} ∂_{k-1} ⋯ ∂_1`: all other deletions are
killed. -/
theorem longest_mul_d_dn {k : ℕ} (hk1 : 1 ≤ k) (hk : k < N) :
    longest R N k * d R N (dn R N 0 k) = (-1 : R) ^ (k - 1) • (longest R N k * dn R N 1 (k - 1)) := by
  rw [d_dn R N 0 k (by omega), Finset.mul_sum, Finset.sum_eq_single (k - 1)]
  · rw [mul_smul_comm, show 0 + k - (k - 1) = 1 by omega, show k - 1 - (k - 1) = 0 by omega,
      dn_zero, mul_one]
  · intro t ht htk
    have ht' : t < k := Finset.mem_range.mp ht
    have := longest_mul_dn_mul_dn R N (k := k) (j := k - 1 - t) (by omega) (by omega)
    rw [show k - 1 - t + 1 = 0 + k - t by omega, show k - 1 - (k - 1 - t) = t by omega] at this
    rw [mul_smul_comm, this, smul_zero]
  · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h

/-- Sliding a dot of the lower factor through the cycle `∂_{k-1} ⋯ ∂_0` below the longest
element. -/
theorem longest_mul_x_mul_dn {k i : ℕ} (hik : i < k) (hk : k < N) :
    longest R N k * (x R N i * dn R N 0 k) =
      (if i = 0 then (-1 : R) ^ (k - 1) • (longest R N k * dn R N 1 (k - 1)) else 0) -
        (-1 : R) ^ (k - 1) • (longest R N (k + 1) * x R N (i + 1)) := by
  have hmix := x_mul_ψ_add_ψ_mul_x R (n := N) (i := i) (by omega)
  have hsplit : dn R N 0 k = dn R N (i + 1) (k - 1 - i) * dn R N 0 (i + 1) := by
    conv_lhs => rw [show k = (i + 1) + (k - 1 - i) by omega]
    rw [dn_add, zero_add]
  have e : x R N i * dn R N 0 (i + 1) =
      dn R N 0 i - (-1 : R) ^ i • (dn R N 0 (i + 1) * x R N (i + 1)) := by
    have hd : ψ R N i * dn R N 0 i = dn R N 0 (i + 1) := by rw [dn_succ, zero_add]
    rw [dn_succ, zero_add, ← mul_assoc, eq_sub_of_add_eq hmix, sub_mul, one_mul, mul_assoc,
      x_mul_dn R N (a := 0) (Or.inr (by omega)), mul_smul_comm, ← mul_assoc, hd]
  rw [hsplit, ← mul_assoc (x R N i), x_mul_dn R N (Or.inl (by omega)), smul_mul_assoc,
    mul_assoc, e, mul_sub, mul_smul_comm, mul_sub, mul_smul_comm, mul_smul_comm, ← mul_assoc,
    ← mul_assoc (dn R N (i + 1) _), ← hsplit, ← mul_assoc (longest R N k), ← longest_succ,
    smul_sub, smul_smul, ← pow_add, show k - 1 - i + i = k - 1 by omega]
  congr 1
  split_ifs with hi
  · subst hi
    rw [show k - 1 - 0 = k - 1 by omega, dn_zero, mul_one]
  · rw [mul_assoc, longest_mul_dn_mul_dn R N (by omega) hik, smul_zero]

/-! ## Ellis–Qi Lemma 3.4 -/

/-- **Ellis–Qi, Lemma 3.4** ((3.13), 0-indexed, the longest element on the first `k ≤ N` strands):

`d(∂_{w_0}) = Σ_{i<k} {i} x_i ∂_{w_0} - (-1)^{binom(k,2)} Σ_{i<k} {k-1-i} ∂_{w_0} x_i`,

where `{m} = m mod 2`. -/
theorem d_longest {k : ℕ} (hk : k ≤ N) :
    d R N (longest R N k) =
      ∑ i ∈ Finset.range k, ((i % 2 : ℕ) : R) • (x R N i * longest R N k) -
        (-1 : R) ^ k.choose 2 •
          ∑ i ∈ Finset.range k, (((k - 1 - i) % 2 : ℕ) : R) • (longest R N k * x R N i) := by
  induction k with
  | zero => rw [longest_zero, d_one, Finset.sum_range_zero, Finset.sum_range_zero, smul_zero,
      sub_zero]
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk1
    · rw [show longest R N (0 + 1) = 1 by rw [longest_succ, longest_zero, dn_zero, one_mul], d_one]
      simp
    have hkN : k < N := by omega
    have hd : d R N (longest R N k * dn R N 0 k) =
        d R N (longest R N k) * dn R N 0 k +
          (-1 : R) ^ k.choose 2 • (longest R N k * d R N (dn R N 0 k)) := by
      have := d_ψw_mul R N (coxeterWord k)
        (fun a ha => by have := coxeterWord_bound ha; omega) (dn R N 0 k)
      rwa [NilCoxeterWords.coxeterWord_length] at this
    set L' := longest R N (k + 1) with hL'
    set B := longest R N k * dn R N 1 (k - 1) with hB
    set u : R := (-1) ^ (k - 1) with hu
    set sgn : R := (-1) ^ k.choose 2 with hsgn
    have hS1 : (∑ i ∈ Finset.range k, ((i % 2 : ℕ) : R) • (x R N i * longest R N k)) *
        dn R N 0 k = ∑ i ∈ Finset.range k, ((i % 2 : ℕ) : R) • (x R N i * L') := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_mul_assoc, mul_assoc, hL', longest_succ]
    have hS2 : (∑ i ∈ Finset.range k, (((k - 1 - i) % 2 : ℕ) : R) • (longest R N k * x R N i)) *
        dn R N 0 k = (((k - 1) % 2 : ℕ) : R) • (u • B) -
          u • ∑ i ∈ Finset.range k, (((k - 1 - i) % 2 : ℕ) : R) • (L' * x R N (i + 1)) := by
      rw [Finset.sum_mul]
      have e : ∀ i ∈ Finset.range k,
          (((k - 1 - i) % 2 : ℕ) : R) • (longest R N k * x R N i) * dn R N 0 k =
            (if i = 0 then (((k - 1 - i) % 2 : ℕ) : R) • (u • B) else 0) -
              u • ((((k - 1 - i) % 2 : ℕ) : R) • (L' * x R N (i + 1))) := by
        intro i hi
        rw [smul_mul_assoc, mul_assoc, longest_mul_x_mul_dn R N (Finset.mem_range.mp hi) hkN,
          smul_sub, smul_comm u, smul_ite, smul_zero]
      rw [Finset.sum_congr rfl e, Finset.sum_sub_distrib, ← Finset.smul_sum,
        Finset.sum_ite_eq' (Finset.range k) 0, if_pos (Finset.mem_range.mpr hk1), Nat.sub_zero]
    have hB' : B = L' * x R N 0 - (-1 : R) ^ (k + 1).choose 2 • (x R N k * L') :=
      longest_mul_dn_one R N hk1 hkN
    conv_lhs => rw [hL', longest_succ]
    rw [hd, ih (by omega), sub_mul, hS1, smul_mul_assoc, hS2, longest_mul_d_dn R N hk1 hkN,
      Finset.sum_range_succ, Finset.sum_range_succ', hB']
    have hsum : ∑ i ∈ Finset.range k, (((k + 1 - 1 - (i + 1)) % 2 : ℕ) : R) • (L' * x R N (i + 1)) =
        ∑ i ∈ Finset.range k, (((k - 1 - i) % 2 : ℕ) : R) • (L' * x R N (i + 1)) :=
      Finset.sum_congr rfl fun i _ => by rw [show k + 1 - 1 - (i + 1) = k - 1 - i by omega]
    rw [hsum]
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    have hq : ((m % 2 : ℕ) : R) = 1 - (((m + 1) % 2 : ℕ) : R) := by
      rw [eq_sub_iff_add_eq, ← Nat.cast_add, show m % 2 + (m + 1) % 2 = 1 by omega, Nat.cast_one]
    have hc : (-1 : R) ^ (m + 1 + 1).choose 2 = -(u * sgn) := by
      rw [hu, hsgn, Nat.choose_succ_succ' (m + 1), Nat.choose_one_right, pow_add,
        show m + 1 - 1 = m by omega, pow_succ]
      ring
    have hu2 : u * u = 1 := by rw [hu, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
    have hs2 : sgn * sgn = 1 := by rw [hsgn, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
    rw [← hu, ← hB, hB', hc, show m + 1 + 1 - 1 - 0 = m + 1 by omega,
      show m + 1 - 1 = m by omega, hq]
    have h4 : sgn * sgn * (u * u) = 1 := by rw [hs2, hu2, one_mul]
    linear_combination (norm := module)
      h4 • ((((m + 1) % 2 : ℕ) : R) • (x R N (m + 1) * L'))

/-! ## Ellis–Qi Lemma 3.5 -/

/-- `d(x_i^a Y) = {a} x_i^{a+1} Y + (-1)^a x_i^a d(Y)`. -/
theorem d_xpow_mul (i a : ℕ) (Y : End ((pres R).obj (strands N))) :
    d R N (x R N i ^ a * Y) =
      ((a % 2 : ℕ) : R) • (x R N i ^ (a + 1) * Y) + (-1 : R) ^ a • (x R N i ^ a * d R N Y) := by
  induction a with
  | zero => simp
  | succ a ih =>
    have hq : (((a + 1) % 2 : ℕ) : R) = 1 - ((a % 2 : ℕ) : R) := by
      rw [eq_sub_iff_add_eq, ← Nat.cast_add, show (a + 1) % 2 + a % 2 = 1 by omega, Nat.cast_one]
    rw [pow_succ', mul_assoc, d_x_mul, ih, hq, show (-1 : R) ^ (a + 1) = -(-1) ^ a by ring]
    simp only [pow_succ', mul_add, mul_smul_comm, ← mul_assoc]
    module

/-- An ordered monomial `x_{l_1}^{a(l_1)} ⋯ x_{l_r}^{a(l_r)}` in distinct dots. -/
def dotMono (a : ℕ → ℕ) (l : List ℕ) : End ((pres R).obj (strands N)) :=
  (l.map fun i => x R N i ^ a i).prod

/-- The differential of an ordered monomial in distinct dots:
`d(x^a) = Σ_i {a_i} x_i x^a`. -/
theorem d_dotMono (a : ℕ → ℕ) (l : List ℕ) (hl : l.Nodup) :
    d R N (dotMono R N a l) = (l.map fun i => ((a i % 2 : ℕ) : R) • (x R N i * dotMono R N a l)).sum := by
  induction l with
  | nil => rw [dotMono, List.map_nil, List.prod_nil, d_one, List.map_nil, List.sum_nil]
  | cons j l ih =>
    obtain ⟨hj, hl⟩ := List.nodup_cons.mp hl
    have hP : dotMono R N a (j :: l) = x R N j ^ a j * dotMono R N a l := by simp [dotMono]
    rw [hP, d_xpow_mul, ih hl, List.map_cons, List.sum_cons, pow_succ', mul_assoc]
    congr 1
    rw [← List.sum_map_mul_left, List.smul_sum, List.map_map]
    congr 1
    refine List.map_congr_left fun i hi => ?_
    have hij : i ≠ j := fun h => hj (h ▸ hi)
    have hc : x R N j ^ a j * x R N i = (-1 : R) ^ a j • (x R N i * x R N j ^ a j) := by
      clear hP ih
      induction a j with
      | zero => simp
      | succ b ihb =>
        have hji : x R N j * x R N i = -(x R N i * x R N j) :=
          eq_neg_of_add_eq_zero_left (x_mul_x_add_x_mul_x R (Ne.symm hij))
        rw [pow_succ', mul_assoc, ihb, mul_smul_comm, ← mul_assoc, hji, neg_mul, pow_succ',
          mul_assoc]
        module
    rw [Function.comp_apply, mul_smul_comm, ← mul_assoc, hc, smul_mul_assoc, mul_assoc,
      smul_comm (((a i % 2 : ℕ) : R)), smul_smul, ← pow_add, ← two_mul, pow_mul, neg_one_sq,
      one_pow, one_smul]

/-- The staircase monomial `x^δ = x_0^{k-1} x_1^{k-2} ⋯ x_{k-2}` on the first `k` strands. -/
def staircase (k : ℕ) : End ((pres R).obj (strands N)) :=
  dotMono R N (fun i => k - 1 - i) (List.range k)

/-- `d(x^δ) = Σ_{i<k} {k-1-i} x_i x^δ` (Ellis–Qi, proof of Lemma 3.5, (3.17)). -/
theorem d_staircase (k : ℕ) :
    d R N (staircase R N k) =
      ∑ i ∈ Finset.range k, (((k - 1 - i) % 2 : ℕ) : R) • (x R N i * staircase R N k) := by
  rw [staircase, d_dotMono R N _ _ List.nodup_range, ← List.sum_toFinset _ List.nodup_range]
  congr 1
  ext i; simp

/-- Ellis–Qi's idempotent `e = (-1)^{binom(k,3)} ∂_{w_0} x^δ` on the first `k` strands
(Ellis–Qi, Lemma 2.17 (4); EKL use the reflected idempotent `x^δ ∂_{w_0}`). Idempotence is not
reproved here. -/
def idem (k : ℕ) : End ((pres R).obj (strands N)) :=
  (-1 : R) ^ k.choose 3 • (longest R N k * staircase R N k)

/-- **Ellis–Qi, Lemma 3.5** ((3.16), 0-indexed): `d(e) = Σ_{i<k} {i} x_i e`. -/
theorem d_idem {k : ℕ} (hk : k ≤ N) :
    d R N (idem R N k) = ∑ i ∈ Finset.range k, ((i % 2 : ℕ) : R) • (x R N i * idem R N k) := by
  have hd : d R N (longest R N k * staircase R N k) =
      d R N (longest R N k) * staircase R N k +
        (-1 : R) ^ k.choose 2 • (longest R N k * d R N (staircase R N k)) := by
    have := d_ψw_mul R N (coxeterWord k)
      (fun a ha => by have := coxeterWord_bound ha; omega) (staircase R N k)
    rwa [NilCoxeterWords.coxeterWord_length] at this
  rw [idem, map_smul, hd, d_longest R N hk, d_staircase, sub_mul]
  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, Finset.smul_sum,
    mul_assoc]
  rw [sub_add_cancel, Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _

end OddMath.Diagrams.OddNilHecke

end
