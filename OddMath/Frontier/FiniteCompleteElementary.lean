import OddMath.Frontier.PlacticEvaluation
import OddMath.Frontier.CompleteChangeOfGenerators

/-! Literal finite-alphabet sums from Ellis 1111.3932v1 §2.1.
The paper label of i : Fin n is i.val + 1. -/
namespace OddMath.Frontier.FiniteCompleteElementary
open OddMath.SkewPolynomial
open PlacticEvaluation
open scoped BigOperators
noncomputable section

/-- Strictly increasing words, in the source's increasing product order. -/
def elementaryPoly (n k : ℕ) : SkewPolynomial n :=
  ∑ f : Fin k → Fin n, if StrictMono f then
    (List.ofFn (fun i => tildeGenerator (f i))).prod else 0

/-- Weakly increasing words; repeated letters are retained. -/
def completePoly (n k : ℕ) : SkewPolynomial n :=
  ∑ f : Fin k → Fin n, if Monotone f then
    (List.ofFn (fun i => tildeGenerator (f i))).prod else 0

@[simp] theorem elementaryPoly_zero (n : ℕ) : elementaryPoly n 0 = 1 := by
  classical
  simp [elementaryPoly, StrictMono]

@[simp] theorem completePoly_zero (n : ℕ) : completePoly n 0 = 1 := by
  classical
  simp [completePoly, Monotone]

/-- Too many distinct letters cannot occur in the finite alphabet. -/
theorem elementaryPoly_eq_zero_of_lt {n k : ℕ} (h : n < k) :
    elementaryPoly n k = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro f _
  have hf : ¬ StrictMono f := by
    intro hf
    have hc := Fintype.card_le_of_injective f hf.injective
    simp only [Fintype.card_fin] at hc
    omega
  simp only [hf, ↓reduceIte]

/-- The specified specialization is a genuine free-algebra lift. -/
def completeEvaluation (n : ℕ) : CompleteElementary.A →+* SkewPolynomial n :=
  (FreeAlgebra.lift ℤ (fun i => completePoly n (i + 1))).toRingHom

@[simp] theorem completeEvaluation_generator (n i : ℕ) :
    completeEvaluation n (FreeAlgebra.ι ℤ i) = completePoly n (i + 1) :=
  FreeAlgebra.lift_ι_apply _ i

@[simp] theorem completeEvaluation_h (n k : ℕ) :
    completeEvaluation n (CompleteElementary.h k) = completePoly n k := by
  cases k with
  | zero => simp
  | succ k => exact completeEvaluation_generator n k

/-- Transport of the universal convolution. Identification with the independently
defined finite-alphabet elementary sum is proved separately below. -/
theorem evaluated_universal_convolution (n m : ℕ) :
    ∑ k : Fin (m + 2), (-1 : ℤ) ^ ((k.val + 1).choose 2) •
      (completeEvaluation n (CompleteElementary.elementary k) *
        completePoly n (m + 1 - k)) = 0 := by
  have hh := congrArg (completeEvaluation n)
    (CompleteElementary.elementary_complete_inverse m)
  simpa only [map_sum, map_mul, CompleteElementary.ekSign, map_pow,
    map_neg, map_one, completeEvaluation_h, map_zero, zsmul_eq_mul,
    Int.cast_pow, Int.cast_neg, Int.cast_one, _root_.mul_assoc] using hh

namespace FiniteWords

abbrev Weak (n k : ℕ) := {f : Fin k → Fin n // Monotone f}
abbrev Strict (n k : ℕ) := {f : Fin k → Fin n // StrictMono f}

/-- Prepending the least letter allows all weak tails, including repetitions. -/
def weakCons {n k : ℕ} (f : Weak (n + 1) k) : Weak (n + 1) (k + 1) :=
  ⟨Fin.cons 0 f.val, by
    intro i j hij
    cases i using Fin.cases with
    | zero => simp
    | succ i =>
      cases j using Fin.cases with
      | zero => simp at hij
      | succ j => simpa using f.property (Fin.succ_le_succ_iff.mp hij)⟩

/-- The positive-letter branch is a shift of the smaller alphabet. -/
def weakShift {n k : ℕ} (f : Weak n k) : Weak (n + 1) k :=
  ⟨fun i => (f.val i).succ, Fin.strictMono_succ.monotone.comp f.property⟩

def strictCons {n k : ℕ} (f : Strict n k) : Strict (n + 1) (k + 1) :=
  ⟨Fin.cons 0 (fun i => (f.val i).succ), by
    intro i j hij
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => exact False.elim (lt_irrefl _ hij)
      | succ j => simp
    | succ i =>
      cases j using Fin.cases with
      | zero => simp at hij
      | succ j => simpa using f.property (Fin.succ_lt_succ_iff.mp hij)⟩

def strictShift {n k : ℕ} (f : Strict n k) : Strict (n + 1) k :=
  ⟨fun i => (f.val i).succ, Fin.strictMono_succ.comp f.property⟩

theorem weak_split_bijective (n k : ℕ) :
    Function.Bijective (Sum.elim (weakCons (n := n) (k := k))
      (weakShift (n := n) (k := k + 1))) := by
  constructor
  · intro a b hab
    cases a with
    | inl a =>
      cases b with
      | inl b =>
        congr 1
        apply Subtype.ext
        funext i
        exact congrArg (fun f => f.val i.succ) hab
      | inr b =>
        have hh := congrArg (fun f => f.val 0) hab
        simp [weakCons, weakShift] at hh
        exact False.elim (Fin.succ_ne_zero _ hh.symm)
    | inr a =>
      cases b with
      | inl b =>
        have hh := congrArg (fun f => f.val 0) hab
        simp [weakCons, weakShift] at hh
      | inr b =>
        congr 1
        apply Subtype.ext
        funext i
        exact Fin.succ_injective n (congrArg (fun f => f.val i) hab)
  · intro f
    by_cases hz : f.val 0 = 0
    · refine ⟨Sum.inl ⟨fun i => f.val i.succ, f.property.comp Fin.strictMono_succ.monotone⟩, ?_⟩
      apply Subtype.ext
      funext i
      cases i using Fin.cases with
      | zero => exact hz.symm
      | succ i => rfl
    · have hnz : ∀ i, f.val i ≠ 0 := by
        intro i hi
        have hh := f.property (Fin.zero_le i)
        rw [hi] at hh
        exact hz (le_antisymm hh (Fin.zero_le _))
      let g : Fin (k + 1) → Fin n := fun i => (f.val i).pred (hnz i)
      have hg : Monotone g := by
        intro i j hij
        apply Fin.strictMono_succ.le_iff_le.mp
        simpa [g] using f.property hij
      refine ⟨Sum.inr ⟨g, hg⟩, ?_⟩
      apply Subtype.ext
      funext i
      exact Fin.succ_pred _ (hnz i)

theorem strict_split_bijective (n k : ℕ) :
    Function.Bijective (Sum.elim (strictCons (n := n) (k := k))
      (strictShift (n := n) (k := k + 1))) := by
  constructor
  · intro a b hab
    cases a with
    | inl a =>
      cases b with
      | inl b =>
        congr 1
        apply Subtype.ext
        funext i
        exact Fin.succ_injective n (congrArg (fun f => f.val i.succ) hab)
      | inr b =>
        have hh := congrArg (fun f => f.val 0) hab
        simp [strictCons, strictShift] at hh
        exact False.elim (Fin.succ_ne_zero _ hh.symm)
    | inr a =>
      cases b with
      | inl b =>
        have hh := congrArg (fun f => f.val 0) hab
        simp [strictCons, strictShift] at hh
      | inr b =>
        congr 1
        apply Subtype.ext
        funext i
        exact Fin.succ_injective n (congrArg (fun f => f.val i) hab)
  · intro f
    by_cases hz : f.val 0 = 0
    · have hnz : ∀ i : Fin k, f.val i.succ ≠ 0 := by
        intro i
        have hh := f.property (Fin.succ_pos i)
        rw [hz] at hh
        exact ne_of_gt hh
      let g : Fin k → Fin n := fun i => (f.val i.succ).pred (hnz i)
      have hg : StrictMono g := by
        intro i j hij
        apply Fin.strictMono_succ.lt_iff_lt.mp
        simpa [g] using f.property (Fin.succ_lt_succ_iff.mpr hij)
      refine ⟨Sum.inl ⟨g, hg⟩, ?_⟩
      apply Subtype.ext
      funext i
      cases i using Fin.cases with
      | zero => exact hz.symm
      | succ i => exact Fin.succ_pred _ (hnz i)
    · have hnz : ∀ i, f.val i ≠ 0 := by
        intro i hi
        have hh := f.property.monotone (Fin.zero_le i)
        rw [hi] at hh
        exact hz (le_antisymm hh (Fin.zero_le _))
      let g : Fin (k + 1) → Fin n := fun i => (f.val i).pred (hnz i)
      have hg : StrictMono g := by
        intro i j hij
        apply Fin.strictMono_succ.lt_iff_lt.mp
        simpa [g] using f.property hij
      refine ⟨Sum.inr ⟨g, hg⟩, ?_⟩
      apply Subtype.ext
      funext i
      exact Fin.succ_pred _ (hnz i)

variable {R : Type*} [Ring R]

def word {n k : ℕ} (x : Fin n → R) (f : Fin k → Fin n) : R :=
  (List.ofFn (fun i => x (f i))).prod

def weakSum {n : ℕ} (x : Fin n → R) (k : ℕ) : R := by
  classical
  exact ∑ f : Weak n k, word x f.val

def strictSum {n : ℕ} (x : Fin n → R) (k : ℕ) : R := by
  classical
  exact ∑ f : Strict n k, word x f.val

theorem weakSum_eq {n : ℕ} (x : Fin n → R) (k : ℕ) :
    weakSum x k = ∑ f : Fin k → Fin n, if Monotone f then word x f else 0 := by
  classical
  rw [weakSum, ← Finset.sum_filter]
  symm
  exact Finset.sum_subtype _ (by simp) _

theorem strictSum_eq {n : ℕ} (x : Fin n → R) (k : ℕ) :
    strictSum x k = ∑ f : Fin k → Fin n, if StrictMono f then word x f else 0 := by
  classical
  rw [strictSum, ← Finset.sum_filter]
  symm
  exact Finset.sum_subtype _ (by simp) _

@[simp] theorem weakSum_zero {n : ℕ} (x : Fin n → R) : weakSum x 0 = 1 := by
  classical
  simp [weakSum_eq, word, Monotone]

@[simp] theorem strictSum_zero {n : ℕ} (x : Fin n → R) : strictSum x 0 = 1 := by
  classical
  simp [strictSum_eq, word, StrictMono]

@[simp] theorem weakSum_empty (x : Fin 0 → R) (k : ℕ) : weakSum x (k + 1) = 0 := by
  classical
  simp [weakSum_eq]

@[simp] theorem strictSum_empty (x : Fin 0 → R) (k : ℕ) : strictSum x (k + 1) = 0 := by
  classical
  simp [strictSum_eq]

/-- Partition by whether the least letter occurs first. No sorting is assumed. -/
theorem weakSum_succ {n : ℕ} (x : Fin (n + 1) → R) (k : ℕ) :
    weakSum x (k + 1) = x 0 * weakSum x k + weakSum (fun i => x i.succ) (k + 1) := by
  classical
  have hh := Fintype.sum_bijective _ (weak_split_bijective n k)
    (fun f => word x (Sum.elim weakCons weakShift f).val)
    (fun f => word x f.val) (fun _ => rfl)
  rw [Fintype.sum_sum_type] at hh
  simpa [weakSum, word, weakCons, weakShift, List.ofFn_succ, Finset.mul_sum] using hh.symm

theorem strictSum_succ {n : ℕ} (x : Fin (n + 1) → R) (k : ℕ) :
    strictSum x (k + 1) = x 0 * strictSum (fun i => x i.succ) k +
      strictSum (fun i => x i.succ) (k + 1) := by
  classical
  have hh := Fintype.sum_bijective _ (strict_split_bijective n k)
    (fun f => word x (Sum.elim strictCons strictShift f).val)
    (fun f => word x f.val) (fun _ => rfl)
  rw [Fintype.sum_sum_type] at hh
  simpa [strictSum, word, strictCons, strictShift, List.ofFn_succ, Finset.mul_sum] using hh.symm

/-- Move a letter across an arbitrary word of anticommuting letters.
Only off-alphabet commutation is used; no diagonal square relation. -/
theorem mul_word {n k : ℕ} (a : R) (x : Fin n → R)
    (ha : ∀ i, a * x i = -(x i * a)) (f : Fin k → Fin n) :
    a * word x f = (-1 : ℤ) ^ k • (word x f * a) := by
  induction k with
  | zero => simp [word]
  | succ k ih =>
    have hw : word x f = x (f 0) * word x (fun i => f i.succ) := by
      simp [word, List.ofFn_succ]
    rw [hw, ← _root_.mul_assoc, ha, neg_mul, _root_.mul_assoc, ih]
    simp only [pow_succ, mul_neg_one, neg_smul, mul_smul_comm, smul_mul_assoc, _root_.mul_assoc]

theorem mul_strictSum {n : ℕ} (a : R) (x : Fin n → R)
    (ha : ∀ i, a * x i = -(x i * a)) (k : ℕ) :
    a * strictSum x k = (-1 : ℤ) ^ k • (strictSum x k * a) := by
  classical
  simp only [strictSum, Finset.mul_sum, Finset.sum_mul, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro f _
  exact mul_word a x ha f.val

def signedStrict {n : ℕ} (x : Fin n → R) (k : ℕ) : R :=
  (-1 : ℤ) ^ ((k + 1).choose 2) • strictSum x k

@[simp] theorem signedStrict_zero {n : ℕ} (x : Fin n → R) : signedStrict x 0 = 1 := by
  simp [signedStrict]

@[simp] theorem signedStrict_empty (x : Fin 0 → R) (k : ℕ) :
    signedStrict x (k + 1) = 0 := by simp [signedStrict]

theorem sign_step (k : ℕ) :
    (-1 : ℤ) ^ ((k + 2).choose 2) * (-1) ^ k = -((-1) ^ ((k + 1).choose 2)) := by
  have hc : (k + 2).choose 2 = (k + 1) + (k + 1).choose 2 := by
    simpa using Nat.choose_succ_succ (k + 1) 1
  rw [hc, pow_add, pow_succ]
  have hs : (-1 : ℤ) ^ k * (-1) ^ k = 1 := by
    simp [← pow_add, ← two_mul, pow_mul]
  calc
    ((-1 : ℤ) ^ k * -1 * (-1) ^ ((k + 1).choose 2)) * (-1) ^ k =
        -((-1) ^ ((k + 1).choose 2)) * ((-1) ^ k * (-1) ^ k) := by
      simp only [mul_neg_one, neg_mul, mul_neg]
      congr 1
      ac_rfl
    _ = _ := by rw [hs, _root_.mul_one]

/-- The signed strict sum behaves as a descending product of linear factors. -/
theorem signedStrict_succ {n : ℕ} (x : Fin (n + 1) → R)
    (hx : ∀ i : Fin n, x 0 * x i.succ = -(x i.succ * x 0)) (k : ℕ) :
    signedStrict x (k + 1) = signedStrict (fun i => x i.succ) (k + 1) -
      signedStrict (fun i => x i.succ) k * x 0 := by
  rw [signedStrict, strictSum_succ, smul_add,
    mul_strictSum (x 0) (fun i => x i.succ) hx, smul_smul, sign_step]
  simp only [neg_smul, ← smul_mul_assoc, signedStrict, sub_eq_add_neg, neg_mul]
  exact add_comm _ _

/-- Finite-coefficient cancellation of adjacent linear/geometric factors.
This lemma uses only the proved recurrences and keeps every product ordered. -/
theorem convolution_step (e e' h h' : ℕ → R) (a : R)
    (he0 : e 0 = e' 0) (hh0 : h 0 = h' 0)
    (he : ∀ k, e (k + 1) = e' (k + 1) - e' k * a)
    (hh : ∀ k, h (k + 1) = a * h k + h' (k + 1)) (m : ℕ) :
    (∑ k ∈ Finset.range (m + 2), e k * h (m + 1 - k)) =
      ∑ k ∈ Finset.range (m + 2), e' k * h' (m + 1 - k) := by
  have heq : (∑ k ∈ Finset.range (m + 2), e k * h (m + 1 - k)) =
      (∑ k ∈ Finset.range (m + 2), e' k * h (m + 1 - k)) -
        ∑ k ∈ Finset.range (m + 1), e' k * a * h (m - k) := by
    rw [Finset.sum_range_succ', Finset.sum_range_succ' (fun k => e' k * h (m + 1 - k))]
    simp only [he, he0, sub_mul, Finset.sum_sub_distrib, Nat.add_sub_add_right,
      Nat.sub_zero]
    exact sub_add_eq_add_sub _ _ _
  rw [heq]
  rw [Finset.sum_range_succ (fun k => e' k * h (m + 1 - k)),
    Finset.sum_range_succ (fun k => e' k * h' (m + 1 - k))]
  simp only [Nat.sub_self, hh0]
  have hs : (∑ k ∈ Finset.range (m + 1), e' k * h (m + 1 - k)) =
      (∑ k ∈ Finset.range (m + 1), e' k * a * h (m - k)) +
        ∑ k ∈ Finset.range (m + 1), e' k * h' (m + 1 - k) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    have hn : m + 1 - k = (m - k) + 1 := by omega
    rw [hn, hh, _root_.mul_add, _root_.mul_assoc]
  rw [hs]
  rw [add_assoc, add_sub_cancel_left]

/-- The literal finite weak/strict sums are inverses for all finite alphabets. -/
theorem convolution {n : ℕ} (x : Fin n → R)
    (hx : ∀ i j, i ≠ j → x i * x j = -(x j * x i)) (m : ℕ) :
    ∑ k ∈ Finset.range (m + 2), signedStrict x k * weakSum x (m + 1 - k) = 0 := by
  induction n with
  | zero =>
    rw [Finset.sum_range_succ']
    simp
  | succ n ih =>
    rw [convolution_step (signedStrict x) (signedStrict (fun i => x i.succ))
      (weakSum x) (weakSum (fun i => x i.succ)) (x 0)
      (by simp) (by simp) (signedStrict_succ x (fun i => hx 0 i.succ (Fin.succ_ne_zero i).symm))
      (weakSum_succ x)]
    exact ih (fun i => x i.succ) (fun i j hij => hx i.succ j.succ (fun h => hij (Fin.succ_injective n h)))

end FiniteWords

/-- Explicit connection to the independently enumerated strict word sum. -/
theorem elementaryPoly_eq_strictSum (n k : ℕ) :
    elementaryPoly n k = FiniteWords.strictSum (tildeGenerator (n := n)) k := by
  exact (FiniteWords.strictSum_eq _ _).symm

theorem completePoly_eq_weakSum (n k : ℕ) :
    completePoly n k = FiniteWords.weakSum (tildeGenerator (n := n)) k := by
  exact (FiniteWords.weakSum_eq _ _).symm

/-- Ellis §2.1: the genuine finite-alphabet inverse in every positive degree. -/
theorem elementary_complete_inverse (n N : ℕ) (hN : 0 < N) :
    ∑ k ∈ Finset.range (N + 1), (-1 : ℤ) ^ ((k + 1).choose 2) •
      (elementaryPoly n k * completePoly n (N - k)) = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
  simpa only [FiniteWords.signedStrict, smul_mul_assoc,
    ← elementaryPoly_eq_strictSum, ← completePoly_eq_weakSum] using
    FiniteWords.convolution (tildeGenerator (n := n)) tilde_anticommute m

/-- The universal conversion specializes to the independently defined source
polynomials, by ordered-convolution uniqueness rather than a redefinition. -/
theorem completeEvaluation_elementary (n k : ℕ) :
    completeEvaluation n (CompleteElementary.elementary k) = elementaryPoly n k := by
  have heq := CompleteChangeOfGenerators.ordered_convolution_unique
    (fun j => (-1 : ℤ) ^ ((j + 1).choose 2) •
      completeEvaluation n (CompleteElementary.elementary j))
    (fun j => (-1 : ℤ) ^ ((j + 1).choose 2) • elementaryPoly n j)
    (completePoly n) (completePoly_zero n) (by simp)
    (fun m => by simpa only [smul_mul_assoc] using evaluated_universal_convolution n m)
    (fun m => by
      have hh := elementary_complete_inverse n (m + 1) (by omega)
      rw [← Fin.sum_univ_eq_sum_range] at hh
      simpa only [smul_mul_assoc] using hh) k
  have hs : (-1 : ℤ) ^ ((k + 1).choose 2) * (-1) ^ ((k + 1).choose 2) = 1 := by
    simp [← pow_add, ← two_mul, pow_mul]
  have hh := congrArg (fun p => (-1 : ℤ) ^ ((k + 1).choose 2) • p) heq
  simpa only [smul_smul, hs, one_smul] using hh

end
end OddMath.Frontier.FiniteCompleteElementary
