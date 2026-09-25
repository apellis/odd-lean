import OddMath.Frontier.EKMixedPairing
import OddMath.Frontier.CompleteChangeOfGenerators

/-! EK 1107.5610v2 pp14–15, Props 2.9–2.11.
All equalities concern the actual integer radical quotient. -/
noncomputable section
set_option maxHeartbeats 2000000
open scoped BigOperators TensorProduct
namespace OddMath.Frontier.EKQuotientRelations
open CompleteElementary EKFreeCoproduct EKPairingAdjoint EKRadicalQuotient
open EKMixedPairing

private def colorEquiv (c : Bool) : A ≃ₐ[ℤ] A :=
  if c then CompleteChangeOfGenerators.completeElementaryEquiv else AlgEquiv.refl

private theorem colorEquiv_h (c : Bool) (n : ℕ) :
    colorEquiv c (CompleteElementary.h n) = gen c n := by
  cases c
  · rfl
  · exact CompleteChangeOfGenerators.completeToElementary_h n

private theorem colorEquiv_word (c : Bool) (w : W) :
    colorEquiv c (wordBasis w) = word (parts w) (fun _ => c) := by
  rw [← vWord_parts w]
  simp only [vWord, hWord, map_list_prod, List.map_map, List.map_ofFn,
    Function.comp_def, colorEquiv_h, word]

/-- Arbitrary monochromatic words of either color separate the actual Q.
For elementary words this uses the proved free change of generators, not a
presentation or finite-variable faithfulness assumption. Zero parts are allowed. -/
theorem quotient_ext_words (c : Bool) (x y : Q)
    (hh : ∀ r (α : Fin r → ℕ),
      quotientPairing x (pi (word α (fun _ => c))) =
      quotientPairing y (pi (word α (fun _ => c)))) : x = y := by
  apply sub_eq_zero.mp
  apply quotientPairing_nondegenerate_left
  intro z
  obtain ⟨z, rfl⟩ := pi_surjective z
  obtain ⟨z, rfl⟩ := (colorEquiv c).surjective z
  induction z using EKPairingAdjoint.basis_induction wordBasis with
  | hz => simp
  | ha a b ha hb => simp only [map_add, ha, hb, add_zero]
  | hb w r =>
    simp only [map_smul, colorEquiv_word, map_zsmul]
    have he := hh _ (parts w)
    simp only [map_sub, LinearMap.sub_apply, LinearMap.smul_apply, he, sub_self, smul_zero]

/-- Adjointness against an arbitrary residual element, with arbitrary platform
colors. This is the unspecialized recurrence used by the source's cancellation. -/
theorem pairing_word_strip {r : ℕ} (β : Fin r → ℕ) (η : Fin r → Bool)
    (c : Bool) (k : ℕ) (x : A) :
    EKPairingAdjoint.pairing (word β η) (gen c k * x) =
      ∑ u : EKPairingMatrices.Splits β,
        (-1 : ℤ)^EKPairingMatrices.crossCols (EKPairingMatrices.upper u) (EKPairingMatrices.lower u) *
        EKPairingAdjoint.pairing (gen c k) (word (EKPairingMatrices.upper u) η) *
        EKPairingAdjoint.pairing (word (EKPairingMatrices.lower u) η) x := by
  rw [EKPairingAdjoint.pairing_symm, ← adjointness, tensorPairing_symm, coproduct_word]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    tensorPairing_tmul, smul_eq_mul, mul_assoc]
  apply Finset.sum_congr rfl
  intro u _
  rw [EKPairingAdjoint.pairing_symm (word (EKPairingMatrices.upper u) η)]

private theorem sum_splits_succ {c : ℕ} (α : Fin (c+1) → ℕ)
    (f : EKPairingMatrices.Splits α → ℤ) :
    ∑ u, f u = ∑ i : Fin (α 0+1), ∑ u : EKPairingMatrices.Splits (fun j => α j.succ),
      f (Fin.insertNth 0 i u) := by
  rw [← (Fin.insertNthEquiv (fun j => Fin (α j+1)) 0).sum_comp]
  rw [Fintype.sum_prod_type]
  rfl
private theorem sum_splits_zero (α : Fin 0 → ℕ)
    (f : EKPairingMatrices.Splits α → ℤ) :
    ∑ u, f u = f (fun i => Fin.elim0 i) := Fintype.sum_unique f

/-- Explicit two-platform recurrence, valid for all colors, all weights and every
residual free element. All zero-boundary cases are included without underflow. -/
theorem pairing_two_strip (b c d : Bool) (a n k : ℕ) (x : A) :
    EKPairingAdjoint.pairing (gen b a * gen c n) (gen d k * x) =
      ∑ i : Fin (a+1), ∑ j : Fin (n+1),
        (-1 : ℤ)^(j.val*(a-i.val)) *
        (if k = i.val+j.val then cell d b i.val * cell d c j.val else 0) *
        EKPairingAdjoint.pairing (gen b (a-i.val) * gen c (n-j.val)) x := by
  have hh := pairing_word_strip ![a,n] ![b,c] d k x
  simp only [pairing_gen_word, sum_splits_succ, sum_splits_zero] at hh
  simpa [word, List.ofFn_succ, crossCols_succ,
    EKPairingMatrices.upper, EKPairingMatrices.lower, EKPairingMatrices.crossCols,
    Fin.sum_univ_succ, Fin.prod_univ_succ, Fin.insertNth_zero] using hh

private theorem cell_opposite (c : Bool) (n : ℕ) :
    cell (!c) c n = if n ≤ 1 then 1 else 0 := by
  cases c <;> by_cases hn : n ≤ 1 <;>
    simp [cell, hn, Nat.not_lt.mpr, Nat.lt_of_not_ge]

/-- EK (2.13) simultaneously for complete and elementary platforms.
The k=0 summand is retained explicitly; no positivity premise is hidden. -/
theorem pairing_same_strip_succ (c : Bool) (a b k : ℕ) (x : A) :
    EKPairingAdjoint.pairing (gen c (a+1) * gen c (b+1)) (gen (!c) k * x) =
      (if k = 0 then EKPairingAdjoint.pairing (gen c (a+1)*gen c (b+1)) x else 0) +
      (if k = 1 then EKPairingAdjoint.pairing (gen c a*gen c (b+1)) x +
        (-1 : ℤ)^(a+1) * EKPairingAdjoint.pairing (gen c (a+1)*gen c b) x else 0) +
      (if k = 2 then (-1 : ℤ)^a * EKPairingAdjoint.pairing (gen c a*gen c b) x else 0) := by
  rw [pairing_two_strip]
  simp only [cell_opposite]
  simp [Fin.sum_univ_succ, Nat.add_sub_cancel]
  split_ifs <;> ring

theorem pairing_single_strip_succ (c : Bool) (a k : ℕ) (x : A) :
    EKPairingAdjoint.pairing (gen c (a+1)) (gen (!c) k * x) =
      (if k = 0 then EKPairingAdjoint.pairing (gen c (a+1)) x else 0) +
      (if k = 1 then EKPairingAdjoint.pairing (gen c a) x else 0) := by
  have hh := pairing_two_strip c c (!c) (a+1) 0 k x
  simp only [cell_opposite] at hh
  simpa [Fin.sum_univ_succ] using hh

private theorem pairing_two_one (c : Bool) (a b : ℕ) :
    EKPairingAdjoint.pairing (gen c a * gen c b) 1 = if a+b=0 then 1 else 0 := by
  have hh := pairing_gen_word 0 false ![a,b] ![c,c]
  rw [EKPairingAdjoint.pairing_symm] at hh
  simp only [word, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil,
    mul_one, gen_zero, Matrix.cons_val_zero, Matrix.cons_val_succ] at hh
  rw [hh]
  simp only [Fin.sum_univ_succ, Fin.prod_univ_succ, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Fin.sum_univ_zero, Fin.prod_univ_zero, add_zero, mul_one]
  by_cases hab : a+b=0
  · have ha : a=0 := by omega
    have hb : b=0 := by omega
    simp [ha,hb]
  · simp only [if_neg hab, if_neg (Ne.symm hab)]

private theorem sign_same {a b : ℕ} (h : Even (a+b)) :
    (-1 : ℤ)^a = (-1 : ℤ)^b := by
  have hm : a%2=b%2 := by have := Nat.even_iff.mp h; omega
  rw [← Nat.mod_add_div a 2, ← Nat.mod_add_div b 2]
  simp only [pow_add, pow_mul]
  norm_num
  rw [hm]

/-- Simultaneous source cancellation against every opposite-colored word.
This is word induction, so the residual test element is never a finite sample. -/
theorem pairing_same_relations (c : Bool) {r : ℕ} (α : Fin r → ℕ) :
    (∀ a b, Even (a+b) →
      EKPairingAdjoint.pairing (gen c a*gen c b) (word α (fun _ => !c)) =
      EKPairingAdjoint.pairing (gen c b*gen c a) (word α (fun _ => !c))) ∧
    (∀ a b, Even (a+b) →
      EKPairingAdjoint.pairing (gen c a*gen c (b+1)) (word α (fun _ => !c)) +
      (-1 : ℤ)^a * EKPairingAdjoint.pairing (gen c (b+1)*gen c a) (word α (fun _ => !c)) =
      (-1 : ℤ)^a * EKPairingAdjoint.pairing (gen c (a+1)*gen c b) (word α (fun _ => !c)) +
      EKPairingAdjoint.pairing (gen c b*gen c (a+1)) (word α (fun _ => !c))) := by
  induction r with
  | zero =>
    constructor <;> intro a b hab
    · simp only [word_zero, pairing_two_one, Nat.add_comm]
    · simp only [word_zero, pairing_two_one]
      simp
  | succ r ih =>
    obtain ⟨he, ho⟩ := ih (fun i => α i.succ)
    let x := word (fun i => α i.succ) (fun _ => !c)
    have boundary (b : ℕ) (hb : Even b) :
        2 * EKPairingAdjoint.pairing (gen c (b+1)) (gen (!c) (α 0) * x) =
        EKPairingAdjoint.pairing (gen c 1*gen c b) (gen (!c) (α 0) * x) +
        EKPairingAdjoint.pairing (gen c b*gen c 1) (gen (!c) (α 0) * x) := by
      cases b with
      | zero => simp [gen_zero]; ring
      | succ b =>
        have sb : (-1 : ℤ)^(b+1)=1 := hb.neg_one_pow
        have sb' : (-1 : ℤ)^b = -1 := by
          rw [pow_succ, mul_neg_one] at sb; omega
        have h0 := ho 0 (b+1) (by simpa using hb)
        have h1 := he 1 b (by simpa [Nat.add_comm] using hb)
        simp only [gen_zero, one_mul, mul_one, pow_zero, one_mul] at h0
        change 2 * EKPairingAdjoint.pairing (gen c (b+1+1)) _ = _
        rw [pairing_single_strip_succ, pairing_same_strip_succ c 0 b,
          pairing_same_strip_succ c b 0]
        simp only [gen_zero, one_mul, mul_one, pow_zero, pow_one, sb', sb]
        split_ifs <;> dsimp [x] at * <;> omega
    constructor
    · intro a b hab
      cases a with
      | zero => simp
      | succ a =>
        cases b with
        | zero => simp
        | succ b =>
          have hp : Even (a+b) := by rw [Nat.even_iff] at *; omega
          have ss := sign_same hp
          have h0 := he (a+1) (b+1) hab
          have h1 := ho a b hp
          have h2 := he a b hp
          simp only [word_succ, pairing_same_strip_succ, pow_succ, mul_neg_one, ← ss]
          split_ifs <;>
            solve | omega | linear_combination h0 | linear_combination h1 |
              linear_combination (-1 : ℤ)^a*h2
    · intro a b hab
      cases a with
      | zero =>
        simpa [word_succ, x, gen_zero, two_mul] using boundary b (by simpa using hab)
      | succ a =>
        cases b with
        | zero =>
          have ha : Even (a+1) := by simpa using hab
          simpa [word_succ, x, gen_zero, ha.neg_one_pow, two_mul, add_comm] using
            (boundary (a+1) ha).symm
        | succ b =>
          have hp : Even (a+b) := by rw [Nat.even_iff] at *; omega
          have ss := sign_same hp
          have h0 := ho (a+1) (b+1) hab
          have h1 := he a (b+1+1) (by rw [Nat.even_iff] at *; omega)
          have h2 := he (a+1) (b+1) hab
          have h3 := he (a+1+1) b (by rw [Nat.even_iff] at *; omega)
          have h4 := ho a b hp
          rcases neg_one_pow_eq_or ℤ a with hs | hs <;>
            simp only [word_succ, pairing_same_strip_succ, pow_succ, mul_neg_one, ← ss, hs] at * <;>
            split_ifs <;> omega

/-- Actual quotient relation, simultaneously for the two source families. -/
theorem same_even (c : Bool) (a b : ℕ) (hab : Even (a+b)) :
    pi (gen c a) * pi (gen c b) = pi (gen c b) * pi (gen c a) := by
  apply quotient_ext_words (!c)
  intro r α
  simp only [← pi.map_mul, quotientPairing_pi]
  exact (pairing_same_relations c α).1 a b hab

/-- Successor indexing expresses the odd relation without truncated subtraction. -/
theorem same_odd_succ (c : Bool) (a b : ℕ) (hab : Even (a+b)) :
    pi (gen c a) * pi (gen c (b+1)) + (-1 : ℤ)^a • (pi (gen c (b+1))*pi (gen c a)) =
      (-1 : ℤ)^a • (pi (gen c (a+1))*pi (gen c b)) + pi (gen c b)*pi (gen c (a+1)) := by
  apply quotient_ext_words (!c)
  intro r α
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    ← pi.map_mul, quotientPairing_pi, smul_eq_mul]
  exact (pairing_same_relations c α).2 a b hab

theorem complete_even (a b : ℕ) (hab : Even (a+b)) :
    EKElementaryQuotient.h a * EKElementaryQuotient.h b =
      EKElementaryQuotient.h b * EKElementaryQuotient.h a := same_even false a b hab
theorem elementary_even (a b : ℕ) (hab : Even (a+b)) :
    EKElementaryQuotient.e a * EKElementaryQuotient.e b =
      EKElementaryQuotient.e b * EKElementaryQuotient.e a := same_even true a b hab

theorem complete_odd (a b : ℕ) (hb : 0 < b) (hab : Odd (a+b)) :
    EKElementaryQuotient.h a * EKElementaryQuotient.h b +
      (-1 : ℤ)^a • (EKElementaryQuotient.h b * EKElementaryQuotient.h a) =
      (-1 : ℤ)^a • (EKElementaryQuotient.h (a+1) * EKElementaryQuotient.h (b-1)) +
        EKElementaryQuotient.h (b-1) * EKElementaryQuotient.h (a+1) := by
  cases b with
  | zero => omega
  | succ b =>
    have hp : Even (a+b) := by rw [Nat.even_iff]; have := Nat.odd_iff.mp hab; omega
    exact same_odd_succ false a b hp

theorem elementary_odd (a b : ℕ) (hb : 0 < b) (hab : Odd (a+b)) :
    EKElementaryQuotient.e a * EKElementaryQuotient.e b +
      (-1 : ℤ)^a • (EKElementaryQuotient.e b * EKElementaryQuotient.e a) =
      (-1 : ℤ)^a • (EKElementaryQuotient.e (a+1) * EKElementaryQuotient.e (b-1)) +
        EKElementaryQuotient.e (b-1) * EKElementaryQuotient.e (a+1) := by
  cases b with
  | zero => omega
  | succ b =>
    have hp : Even (a+b) := by rw [Nat.even_iff]; have := Nat.odd_iff.mp hab; omega
    exact same_odd_succ true a b hp

theorem same_one_even (c : Bool) (k : ℕ) :
    pi (gen c 1)*pi (gen c (2*k)) + pi (gen c (2*k))*pi (gen c 1) =
      (2 : ℤ) • pi (gen c (2*k+1)) := by
  have hh := same_odd_succ c 0 (2*k) (by simp [even_two_mul])
  simpa only [gen_zero, map_one, one_mul, mul_one, pow_zero, one_smul,
    Nat.zero_add, two_zsmul] using hh.symm

theorem complete_one_even (k : ℕ) :
    EKElementaryQuotient.h 1*EKElementaryQuotient.h (2*k) +
      EKElementaryQuotient.h (2*k)*EKElementaryQuotient.h 1 =
      (2 : ℤ) • EKElementaryQuotient.h (2*k+1) := same_one_even false k
theorem elementary_one_even (k : ℕ) :
    EKElementaryQuotient.e 1*EKElementaryQuotient.e (2*k) +
      EKElementaryQuotient.e (2*k)*EKElementaryQuotient.e 1 =
      (2 : ℤ) • EKElementaryQuotient.e (2*k+1) := same_one_even true k

private theorem sum_fin_match (a k : ℕ) (f : ℕ → ℤ) :
    (∑ i : Fin (a+1), if k = i.val then f i.val else 0) =
      if k ≤ a then f k else 0 := by
  classical
  by_cases hk : k ≤ a
  · rw [if_pos hk, Finset.sum_eq_single (⟨k, by omega⟩ : Fin (a+1))]
    · simp
    · intro i _ hi
      rw [if_neg]
      intro hh
      exact hi (Fin.ext hh.symm)
    · simp
  · rw [if_neg hk]
    apply Finset.sum_eq_zero
    intro i _
    rw [if_neg]
    have := i.isLt
    omega

/-- Correct h-test recurrence underlying EK p15. The printed even-case lines
say e_k, which is not silently adopted here. -/
theorem pairing_he_strip (a b k : ℕ) (x : A) :
    EKPairingAdjoint.pairing (gen false a * gen true (b+1)) (gen false (k+1)*x) =
      (if k+1 ≤ a then EKPairingAdjoint.pairing (gen false (a-(k+1))*gen true (b+1)) x else 0) +
      (if k ≤ a then (-1 : ℤ)^(a-k) *
        EKPairingAdjoint.pairing (gen false (a-k)*gen true b) x else 0) := by
  rw [pairing_two_strip]
  have row (i : Fin (a+1)) :
      (∑ j : Fin (b+1+1), (-1 : ℤ)^(j.val*(a-i.val)) *
        (if k+1 = i.val+j.val then cell false false i.val * cell false true j.val else 0) *
        EKPairingAdjoint.pairing (gen false (a-i.val)*gen true (b+1-j.val)) x) =
      (if k+1=i.val then EKPairingAdjoint.pairing (gen false (a-i.val)*gen true (b+1)) x else 0) +
      (if k=i.val then (-1 : ℤ)^(a-i.val)*
        EKPairingAdjoint.pairing (gen false (a-i.val)*gen true b) x else 0) := by
    simp [Fin.sum_univ_succ, cell, Nat.add_sub_cancel, mul_ite, ite_mul]
  simp_rw [row]
  rw [Finset.sum_add_distrib,
    sum_fin_match a (k+1) (fun j => EKPairingAdjoint.pairing (gen false (a-j)*gen true (b+1)) x),
    sum_fin_match a k (fun j => (-1 : ℤ)^(a-j)*EKPairingAdjoint.pairing (gen false (a-j)*gen true b) x)]

theorem pairing_eh_strip (a b k : ℕ) (x : A) :
    EKPairingAdjoint.pairing (gen true (b+1) * gen false a) (gen false (k+1)*x) =
      (if k+1 ≤ a then (-1 : ℤ)^((k+1)*(b+1))*
        EKPairingAdjoint.pairing (gen true (b+1)*gen false (a-(k+1))) x else 0) +
      (if k ≤ a then (-1 : ℤ)^(k*b) *
        EKPairingAdjoint.pairing (gen true b*gen false (a-k)) x else 0) := by
  rw [pairing_two_strip, Finset.sum_comm]
  have row (i : Fin (a+1)) :
      (∑ j : Fin (b+1+1), (-1 : ℤ)^(i.val*(b+1-j.val)) *
        (if k+1 = j.val+i.val then cell false true j.val * cell false false i.val else 0) *
        EKPairingAdjoint.pairing (gen true (b+1-j.val)*gen false (a-i.val)) x) =
      (if k+1=i.val then (-1 : ℤ)^(i.val*(b+1))*
        EKPairingAdjoint.pairing (gen true (b+1)*gen false (a-i.val)) x else 0) +
      (if k=i.val then (-1 : ℤ)^(i.val*b)*
        EKPairingAdjoint.pairing (gen true b*gen false (a-i.val)) x else 0) := by
    simp [Fin.sum_univ_succ, cell, Nat.add_sub_cancel, mul_ite, ite_mul, Nat.add_comm]
  simp_rw [row]
  rw [Finset.sum_add_distrib,
    sum_fin_match a (k+1) (fun j => (-1 : ℤ)^(j*(b+1))*EKPairingAdjoint.pairing (gen true (b+1)*gen false (a-j)) x),
    sum_fin_match a k (fun j => (-1 : ℤ)^(j*b)*EKPairingAdjoint.pairing (gen true b*gen false (a-j)) x)]

private theorem gen_one_eq : gen true 1 = gen false 1 := by
  simp [gen, elementary, inverseCoeff, ekSign, Fin.sum_univ_succ]

private theorem pairing_same_odd_any (c : Bool) (a b : ℕ) (hab : Even (a+b)) (x : A) :
    EKPairingAdjoint.pairing (gen c a*gen c (b+1)) x +
      (-1 : ℤ)^a * EKPairingAdjoint.pairing (gen c (b+1)*gen c a) x =
      (-1 : ℤ)^a * EKPairingAdjoint.pairing (gen c (a+1)*gen c b) x +
      EKPairingAdjoint.pairing (gen c b*gen c (a+1)) x := by
  have hh := congrArg (fun z => quotientPairing z (pi x)) (same_odd_succ c a b hab)
  simpa only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    ← pi.map_mul, quotientPairing_pi, smul_eq_mul] using hh

private theorem pairing_two_one_colors (c d : Bool) (a b : ℕ) :
    EKPairingAdjoint.pairing (gen c a * gen d b) 1 = if a+b=0 then 1 else 0 := by
  have hh := pairing_gen_word 0 false ![a,b] ![c,d]
  rw [EKPairingAdjoint.pairing_symm] at hh
  simp only [word, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil,
    mul_one, gen_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.sum_univ_succ, Fin.prod_univ_succ, Fin.sum_univ_zero, Fin.prod_univ_zero,
    add_zero] at hh
  rw [hh]
  by_cases hab : a+b=0
  · have ha : a=0 := by omega
    have hb : b=0 := by omega
    simp [ha,hb]
  · simp only [if_neg hab, if_neg (Ne.symm hab)]

theorem pairing_mixed_relations {r : ℕ} (α : Fin r → ℕ) :
    (∀ a b, Even (a+b) →
      EKPairingAdjoint.pairing (gen false a*gen true b) (word α (fun _ => false)) =
      EKPairingAdjoint.pairing (gen true b*gen false a) (word α (fun _ => false))) ∧
    (∀ a b, Even (a+b) →
      EKPairingAdjoint.pairing (gen false a*gen true (b+1)) (word α (fun _ => false)) +
      (-1 : ℤ)^a * EKPairingAdjoint.pairing (gen true (b+1)*gen false a) (word α (fun _ => false)) =
      (-1 : ℤ)^a * EKPairingAdjoint.pairing (gen false (a+1)*gen true b) (word α (fun _ => false)) +
      EKPairingAdjoint.pairing (gen true b*gen false (a+1)) (word α (fun _ => false))) := by
  induction r with
  | zero =>
    constructor <;> intro a b hab
    · simp only [word_zero, pairing_two_one_colors, Nat.add_comm]
    · simp only [word_zero, pairing_two_one_colors]
      simp
  | succ r ih =>
    obtain ⟨he, ho⟩ := ih (fun i => α i.succ)
    constructor
    · intro a b hab
      cases b with
      | zero => simp
      | succ b =>
        rw [word_succ]
        by_cases hk0 : α 0=0
        · simp only [hk0, gen_zero, one_mul]
          exact he a (b+1) hab
        · obtain ⟨k, hk⟩ : ∃ k, α 0=k+1 := ⟨α 0-1, by omega⟩
          rw [hk, pairing_he_strip, pairing_eh_strip]
          by_cases hka : k+1 ≤ a
          · obtain ⟨u, rfl⟩ : ∃u, a=u+k+1 := ⟨a-(k+1), by omega⟩
            have hsub : u+k+1-(k+1)=u := by omega
            have hsub' : u+k+1-k=u+1 := by omega
            simp only [if_pos hka, if_pos (show k ≤ u+k+1 by omega), hsub, hsub']
            rcases Nat.even_or_odd k with hkE | hkO
            · have hp : Even (u+b) := by
                rw [Nat.even_iff] at *; omega
              have hh := ho u b hp
              have ss := sign_same hp
              simp only [pow_add, pow_mul, hkE.neg_one_pow, one_pow, pow_one] at hh ⊢
              rcases neg_one_pow_eq_or ℤ u with hs | hs <;> norm_num [← ss, hs] at hh ⊢ <;> omega
            · have hp : Even (u+(b+1)) := by
                rw [Nat.even_iff] at *; have := Nat.odd_iff.mp hkO; omega
              have h1 := he u (b+1) hp
              have h2 := he (u+1) b (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hp)
              have ss : (-1 : ℤ)^(u+1)=(-1 : ℤ)^b :=
                sign_same (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hp)
              simp only [pow_add, pow_mul, hkO.neg_one_pow, neg_one_sq, one_pow, pow_one] at *
              rw [ss]
              rw [h1,h2]
              norm_num
          · by_cases hka' : k ≤ a
            · have ha : a=k := by omega
              subst a
              simp only [if_neg hka, if_pos hka', Nat.sub_self, pow_zero, one_mul,
                gen_zero, mul_one, zero_add]
              have hs : (-1 : ℤ)^(k*b)=1 := by
                have hh : Even k ∨ Even b := by simp only [Nat.even_iff] at *; omega
                rcases hh with hh | hh
                · simp [pow_mul, hh.neg_one_pow]
                · rw [Nat.mul_comm, pow_mul, hh.neg_one_pow, one_pow]
              rw [hs, one_mul]
            · simp [hka,hka']
    · intro a b hab
      cases a with
      | zero =>
        have hh := pairing_same_odd_any true 0 b hab (word α (fun _ => false))
        simpa only [Nat.zero_add, gen_zero, one_mul, mul_one, pow_zero, one_mul, gen_one_eq] using hh
      | succ a =>
        cases b with
        | zero =>
          have hh := pairing_same_odd_any false (a+1) 0 hab (word α (fun _ => false))
          simpa only [Nat.zero_add, gen_zero, one_mul, mul_one, gen_one_eq] using hh
        | succ b =>
          rw [word_succ]
          by_cases hk0 : α 0=0
          · simp only [hk0, gen_zero, one_mul]
            exact ho (a+1) (b+1) hab
          · obtain ⟨k, hk⟩ : ∃ k, α 0=k+1 := ⟨α 0-1, by omega⟩
            rw [hk, pairing_he_strip, pairing_eh_strip, pairing_he_strip, pairing_eh_strip]
            by_cases hka : k ≤ a
            · obtain ⟨u, rfl⟩ : ∃u, a=u+k := ⟨a-k, by omega⟩
              have hsub : u+k+1-(k+1)=u := by omega
              have hsub' : u+k+1-k=u+1 := by omega
              have hsub'' : u+k+1+1-(k+1)=u+1 := by omega
              have hsub''' : u+k+1+1-k=u+1+1 := by omega
              simp only [if_pos (show k+1 ≤ u+k+1 by omega),
                if_pos (show k ≤ u+k+1 by omega), if_pos (show k+1 ≤ u+k+1+1 by omega),
                if_pos (show k ≤ u+k+1+1 by omega), hsub,hsub',hsub'',hsub''']
              rcases Nat.even_or_odd k with hkE | hkO
              · have hp : Even (u+b) := by
                  rw [Nat.even_iff] at *; omega
                have h1 := he u (b+1+1) (by rw [Nat.even_iff] at *; omega)
                have h2 := he (u+1+1) b (by rw [Nat.even_iff] at *; omega)
                have ss := sign_same hp
                simp only [pow_add, pow_mul, hkE.neg_one_pow, one_pow, pow_one]
                rcases neg_one_pow_eq_or ℤ u with hs | hs <;> norm_num [← ss,hs] <;> omega
              · have hp : Even (u+(b+1)) := by
                  rw [Nat.even_iff] at *; have := Nat.odd_iff.mp hkO; omega
                have h1 := ho u (b+1) hp
                have h2 := ho (u+1) b (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hp)
                have ss := sign_same hp
                simp only [pow_add, pow_mul, hkO.neg_one_pow, pow_one] at h1 h2 ss ⊢
                rcases neg_one_pow_eq_or ℤ u with hs | hs <;>
                  rcases neg_one_pow_eq_or ℤ b with ht | ht <;>
                  norm_num [hs,ht] at h1 h2 ss ⊢ <;> omega
            · have hcases : k=a+1 ∨ k=a+2 ∨ a+2<k := by omega
              rcases hcases with rfl | rfl | hlarge
              · have hp : Even (a+b) := by rw [Nat.even_iff] at *; omega
                have ss := sign_same hp
                simp only [if_neg (show ¬a+1+1 ≤ a+1 by omega),
                  if_pos (show a+1 ≤ a+1 by omega), if_pos (show a+1+1 ≤ a+1+1 by omega),
                  if_pos (show a+1 ≤ a+1+1 by omega), Nat.sub_self,
                  show a+1+1-(a+1)=1 by omega, gen_zero, one_mul, mul_one, pow_zero, pow_one]
                rcases Nat.even_or_odd b with hbE | hbO
                · have hh := ho 0 b (by simpa using hbE)
                  simp only [Nat.zero_add, gen_zero, one_mul, mul_one, pow_zero, one_mul] at hh
                  simp only [pow_add, pow_mul, pow_one, ss, hbE.neg_one_pow, one_pow]
                  norm_num [hbE.neg_one_pow]
                  omega
                · have hh := he 1 b (by rw [Nat.even_iff]; have := Nat.odd_iff.mp hbO; omega)
                  simp only [pow_add, pow_mul, pow_one, ss, hbO.neg_one_pow]
                  norm_num [hbO.neg_one_pow]
                  omega
              · simp only [if_neg (show ¬a+2+1 ≤ a+1 by omega),
                  if_neg (show ¬a+2 ≤ a+1 by omega), if_neg (show ¬a+2+1 ≤ a+1+1 by omega),
                  if_pos (show a+2 ≤ a+1+1 by omega), show a+1+1-(a+2)=0 by omega,
                  gen_zero, one_mul, mul_one, pow_zero, zero_add, mul_zero]
                have ss : (-1 : ℤ)^a = (-1 : ℤ)^b := sign_same (by rw [Nat.even_iff] at *; omega)
                simp only [pow_add, pow_mul, pow_one, ss]
                rcases neg_one_pow_eq_or ℤ b with hs | hs <;> norm_num [hs]
              · simp [show ¬k+1 ≤ a+1 by omega, show ¬k ≤ a+1 by omega,
                  show ¬k+1 ≤ a+1+1 by omega, show ¬k ≤ a+1+1 by omega]

/-- EK Proposition 2.11, equation (2.16), on the actual quotient. -/
theorem mixed_even (a b : ℕ) (hab : Even (a+b)) :
    EKElementaryQuotient.h a * EKElementaryQuotient.e b =
      EKElementaryQuotient.e b * EKElementaryQuotient.h a := by
  apply quotient_ext_words false
  intro r α
  change quotientPairing (pi (gen false a)*pi (gen true b)) _ =
    quotientPairing (pi (gen true b)*pi (gen false a)) _
  simp only [← pi.map_mul, quotientPairing_pi]
  exact (pairing_mixed_relations α).1 a b hab

/-- EK Proposition 2.11, equation (2.17), with explicit positive second index. -/
theorem mixed_odd (a b : ℕ) (hb : 0 < b) (hab : Odd (a+b)) :
    EKElementaryQuotient.h a * EKElementaryQuotient.e b +
      (-1 : ℤ)^a • (EKElementaryQuotient.e b * EKElementaryQuotient.h a) =
      (-1 : ℤ)^a • (EKElementaryQuotient.h (a+1) * EKElementaryQuotient.e (b-1)) +
        EKElementaryQuotient.e (b-1) * EKElementaryQuotient.h (a+1) := by
  cases b with
  | zero => omega
  | succ b =>
    have hp : Even (a+b) := by rw [Nat.even_iff]; have := Nat.odd_iff.mp hab; omega
    apply quotient_ext_words false
    intro r α
    change quotientPairing (pi (gen false a)*pi (gen true (b+1)) +
        (-1 : ℤ)^a • (pi (gen true (b+1))*pi (gen false a))) _ =
      quotientPairing ((-1 : ℤ)^a • (pi (gen false (a+1))*pi (gen true b)) +
        pi (gen true b)*pi (gen false (a+1))) _
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      ← pi.map_mul, quotientPairing_pi, smul_eq_mul]
    exact (pairing_mixed_relations α).2 a b hp

end OddMath.Frontier.EKQuotientRelations
