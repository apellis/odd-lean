import OddMath.Frontier.EKElementaryQuotient
import OddMath.Frontier.EKPlatformBijection

/-! EK 1107.5610v2 (2.10) and Proposition 2.6, integral q=-1.
Top rows precede bottom columns; false is complete/white, true elementary/black.
All algebraic objects below live in the actual free algebra or radical quotient. -/
noncomputable section
open scoped BigOperators TensorProduct
namespace OddMath.Frontier.EKMixedPairing
open CompleteElementary EKFreeCoproduct EKPairingAdjoint EKRadicalQuotient
open EKPairingMatrices

/-- The source platform generator before passing to the radical quotient. -/
def gen (b : Bool) (n : ℕ) : A := if b then elementary n else CompleteElementary.h n
/-- Literal ordered mixed word, before quotienting. -/
def word {r : ℕ} (β : Fin r → ℕ) (η : Fin r → Bool) : A :=
  (List.ofFn (fun i => gen (η i) (β i))).prod
/-- Literal source product in the actual radical quotient. -/
def mixed {r : ℕ} (β : Fin r → ℕ) (η : Fin r → Bool) : Q :=
  (List.ofFn (fun i => if η i then EKElementaryQuotient.e (β i)
    else EKElementaryQuotient.h (β i))).prod

theorem mixed_eq_pi {r : ℕ} (β : Fin r → ℕ) (η : Fin r → Bool) :
    mixed β η = pi (word β η) := by
  simp only [mixed, word, map_list_prod, List.map_ofFn]
  congr 2
  funext i
  simp only [Function.comp_apply]
  cases η i <;> rfl

@[simp] theorem gen_zero (b : Bool) : gen b 0 = 1 := by cases b <;> simp [gen]
@[simp] theorem word_zero (β : Fin 0 → ℕ) (η : Fin 0 → Bool) : word β η = 1 := rfl
@[simp] theorem word_succ {r : ℕ} (β : Fin (r+1) → ℕ) (η : Fin (r+1) → Bool) :
    word β η = gen (η 0) (β 0) * word (fun i => β i.succ) (fun i => η i.succ) := by
  simp [word, List.ofFn_succ]
@[simp] theorem word_singleton (n : ℕ) (b : Bool) :
    word (fun _ : Fin 1 => n) (fun _ => b) = gen b n := by simp

theorem elementary_norm (n : ℕ) :
    EKPairingAdjoint.pairing (elementary n) (elementary n) = (-1 : ℤ)^n.choose 2 := by
  classical
  have hn : elementary n = (-1 : ℤ)^((n+1).choose 2) •
      ∑ α ∈ compositions n, (-1 : ℤ)^α.length • hWord α := by
    simp [elementary_composition_expansion, zsmul_eq_mul]
  conv_lhs => lhs; rw [hn]
  simp only [map_smul, LinearMap.smul_apply, map_sum, LinearMap.sum_apply, smul_eq_mul]
  have hon : List.replicate n 1 ∈ compositions n := by
    rw [mem_compositions_iff]
    simp
  have hs : (∑ α ∈ compositions n, (-1 : ℤ)^α.length *
      EKPairingAdjoint.pairing (hWord α) (elementary n)) = (-1 : ℤ)^n := by
    rw [Finset.sum_eq_single (List.replicate n 1)]
    · rw [EKElementaryQuotient.pairing_hWord_elementary _ (by simp)]
      simp
    · intro α ha hne
      rw [EKElementaryQuotient.pairing_hWord_elementary α (composition_sound n α ha).1]
      rw [if_neg, mul_zero]
      rintro ⟨hs, hall⟩
      apply hne
      have he : α = List.replicate α.length 1 := List.eq_replicate_iff.mpr ⟨rfl, hall⟩
      have hl : α.length = n := by
        have hsum := congrArg List.sum he
        simpa only [List.sum_replicate, smul_eq_mul, mul_one, hs] using hsum.symm
      simpa [hl] using he
    · exact fun h => (h hon).elim
  rw [hs]
  have ht : (n+1).choose 2 = n.choose 2 + n := by
    simpa [Nat.add_comm] using Nat.choose_succ_succ n 1
  rw [ht, pow_add, mul_assoc, ← pow_add, ← two_mul, pow_mul]
  simp

/-- EK (2.10), without a norm or perfectness assumption. -/
theorem quotient_elementary_norm (n : ℕ) :
    quotientPairing (EKElementaryQuotient.e n) (EKElementaryQuotient.e n) =
      (-1 : ℤ)^n.choose 2 := elementary_norm n

open EKElementaryQuotient (weight elementary_weight)

private theorem h_weight (n : ℕ) : CompleteElementary.h n ∈ weight n := by
  cases n with
  | zero => exact Submodule.subset_span ⟨1, rfl, wordBasis_one⟩
  | succ n => exact Submodule.subset_span ⟨FreeMonoid.of n, rfl, wordBasis_of n⟩

theorem gen_weight (b : Bool) (n : ℕ) : gen b n ∈ weight n := by
  cases b
  · exact h_weight n
  · exact elementary_weight n

private theorem weight_mul {m n : ℕ} {a b : A}
    (ha : a ∈ weight m) (hb : b ∈ weight n) : a*b ∈ weight (m+n) := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨u, hu, rfl⟩ := ha
    induction hb using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨v, hv, rfl⟩ := hb
      exact Submodule.subset_span ⟨u*v, by simp [hu,hv], wordBasis_mul u v⟩
    | zero => simp
    | add b c _ _ hb hc => simpa [mul_add] using (weight (m+n)).add_mem hb hc
    | smul r b _ hb => simpa only [mul_smul_comm] using (weight (m+n)).smul_mem r hb
  | zero => simp
  | add a c _ _ ha hc => simpa [add_mul] using (weight (m+n)).add_mem ha hc
  | smul r a _ ha => simpa only [smul_mul_assoc] using (weight (m+n)).smul_mem r ha

theorem word_weight {r : ℕ} (β : Fin r → ℕ) (η : Fin r → Bool) :
    word β η ∈ weight (∑ i, β i) := by
  induction r with
  | zero => simpa using h_weight 0
  | succ r ih =>
    rw [word_succ, Fin.sum_univ_succ]
    exact weight_mul (gen_weight _ _) (ih _ _)

private theorem twist_weight (k : ℕ) {n : ℕ} {a : A} (ha : a ∈ weight n) :
    EKSignedQuotient.twist k a = (-1 : ℤ)^(n*k) • a := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨u, hu, rfl⟩ := ha
    simp [hu]
  | zero => simp
  | add a b _ _ ha hb => simp only [map_add, ha, hb, smul_add]
  | smul r a _ ha => simp only [map_smul, ha, smul_comm r]

private theorem tensorMul_weight (a d : A) {m n : ℕ} {b c : A}
    (hb : b ∈ weight m) (hc : c ∈ weight n) :
    tensorMul (a ⊗ₜ[ℤ] b) (c ⊗ₜ[ℤ] d) =
      (-1 : ℤ)^(m*n) • ((a*c) ⊗ₜ[ℤ] (b*d)) := by
  induction a using EKPairingAdjoint.basis_induction wordBasis with
  | hz => simp
  | ha a a' ha ha' => simp [TensorProduct.add_tmul, add_mul, ha, ha', smul_add]
  | hb u r =>
    simp only [← TensorProduct.smul_tmul', tensorMul_smul_left, smul_mul_assoc]
    rw [← smul_comm r]
    congr 1
    induction hb using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨v, hv, rfl⟩ := hb
      rw [← tensorBasis_apply, EKSignedQuotient.tensorMul_basis_tmul,
        twist_weight _ hc, hv, mul_smul_comm, ← TensorProduct.smul_tmul', Nat.mul_comm]
    | zero => simp
    | add b b' _ _ hb hb' =>
      simp [TensorProduct.tmul_add, add_mul, hb, hb', smul_add]
    | smul s b _ hb =>
      simp only [TensorProduct.tmul_smul, tensorMul_smul_left, hb, smul_mul_assoc]
      rw [← smul_comm s]

theorem coproduct_gen (b : Bool) (n : ℕ) :
    coproduct (gen b n) = ∑ i : Fin (n+1), gen b i ⊗ₜ[ℤ] gen b (n-i) := by
  cases b
  · exact coproduct_h n
  · exact EKElementaryQuotient.coproduct_elementary n

/-- The actual coproduct on arbitrary mixed ordered words. -/
theorem coproduct_word {c : ℕ} (α : Fin c → ℕ) (ε : Fin c → Bool) :
    coproduct (word α ε) = ∑ u : Splits α,
      (-1 : ℤ)^crossCols (upper u) (lower u) •
        (word (upper u) ε ⊗ₜ[ℤ] word (lower u) ε) := by
  induction c with
  | zero => simp [crossCols, tensorOne]
  | succ c ih =>
    rw [word_succ, coproduct_mul, coproduct_gen, ih]
    rw [← (Fin.insertNthEquiv (fun j => Fin (α j + 1)) 0).sum_comp]
    simp only [Fintype.sum_prod_type, tensorMul, map_sum, LinearMap.sum_apply]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro u _
    change tensorMul _ _ = _
    rw [tensorMul_smul_right, tensorMul_weight _ _ (gen_weight _ _) (word_weight _ _)]
    simp only [Fin.insertNthEquiv, Equiv.coe_fn_mk, Fin.insertNth_zero, crossCols_succ,
      Fin.cons_zero, Fin.cons_succ, word_succ, pow_add, smul_smul]
    congr 1
    change (-1 : ℤ)^crossCols (upper u) (lower u) *
      (-1)^((α 0-i.val)*(∑ j, (u j).val)) =
      (-1)^((∑ j, (u j).val)*(α 0-i.val)) * (-1)^crossCols (upper u) (lower u)
    rw [Nat.mul_comm]
    ring

/-- Actual multiplication adjointness, now with arbitrary mixed bottom colors. -/
theorem pairing_word_mul {c : ℕ} (x y : A) (α : Fin c → ℕ) (ε : Fin c → Bool) :
    EKPairingAdjoint.pairing (x*y) (word α ε) =
      ∑ u : Splits α, (-1 : ℤ)^crossCols (upper u) (lower u) *
        EKPairingAdjoint.pairing x (word (upper u) ε) *
        EKPairingAdjoint.pairing y (word (lower u) ε) := by
  rw [← adjointness, coproduct_word]
  simp only [map_sum, map_smul, tensorPairing_tmul, smul_eq_mul, mul_assoc]

/-- Off-weight pairings vanish, for all colors including empty/zero platforms. -/
theorem pairing_word_mismatch {r c : ℕ} (β : Fin r → ℕ) (η : Fin r → Bool)
    (α : Fin c → ℕ) (ε : Fin c → Bool) (hne : (∑ i, β i) ≠ ∑ j, α j) :
    EKPairingAdjoint.pairing (word β η) (word α ε) = 0 :=
  pairing_homogeneous_orthogonal hne (word_weight β η) (word_weight α ε)

/-- Local platform pairing: a mixed-color bundle has at most one strand. -/
def cell (b e : Bool) (n : ℕ) : ℤ :=
  if b ≠ e ∧ 1 < n then 0 else (-1)^ (if b && e then n.choose 2 else 0)

@[simp] theorem cell_zero (b e : Bool) : cell b e 0 = 1 := by cases b <;> cases e <;> simp [cell]

theorem pairing_gen_self (b e : Bool) (n : ℕ) :
    EKPairingAdjoint.pairing (gen b n) (gen e n) = cell b e n := by
  cases b <;> cases e
  · simp [gen, cell]
  · simp only [gen, Bool.false_eq_true, ↓reduceIte]
    rw [EKElementaryQuotient.pairing_h_elementary]
    by_cases hn : n ≤ 1 <;> simp [cell, hn, Nat.not_lt.mpr, Nat.lt_of_not_ge]
  · rw [EKPairingAdjoint.pairing_symm]
    simp only [gen, Bool.false_eq_true, ↓reduceIte]
    rw [EKElementaryQuotient.pairing_h_elementary]
    by_cases hn : n ≤ 1 <;> simp [cell, hn, Nat.not_lt.mpr, Nat.lt_of_not_ge]
  · exact elementary_norm n

theorem pairing_gen (b e : Bool) (m n : ℕ) :
    EKPairingAdjoint.pairing (gen b m) (gen e n) = if m = n then cell b e n else 0 := by
  by_cases h : m = n
  · subst m; simp only [if_pos rfl]; exact pairing_gen_self b e n
  · rw [if_neg h]
    exact pairing_homogeneous_orthogonal h (gen_weight b m) (gen_weight e n)

/-- Pairing a single platform with any mixed word, at equal total weight. -/
theorem pairing_gen_word_total {c : ℕ} (α : Fin c → ℕ) (ε : Fin c → Bool) (b : Bool) :
    EKPairingAdjoint.pairing (gen b (∑ j, α j)) (word α ε) = ∏ j, cell b (ε j) (α j) := by
  classical
  induction c with
  | zero => simpa using pairing_one_one
  | succ c ih =>
    rw [EKPairingAdjoint.pairing_symm, word_succ, ← adjointness, coproduct_gen]
    simp only [map_sum, tensorPairing_tmul]
    let k : Fin ((∑ j, α j)+1) := ⟨α 0, by rw [Fin.sum_univ_succ]; omega⟩
    rw [Finset.sum_eq_single k]
    · have hd : (∑ j, α j) - k.val = ∑ j : Fin c, α j.succ := by
        dsimp [k]; rw [Fin.sum_univ_succ]; omega
      rw [hd, EKPairingAdjoint.pairing_symm (gen (ε 0) (α 0)),
        EKPairingAdjoint.pairing_symm (word _ _)]
      change EKPairingAdjoint.pairing (gen b (α 0)) (gen (ε 0) (α 0)) * _ = _
      rw [pairing_gen_self, ih, Fin.prod_univ_succ]
    · intro i _ hi
      have hne : α 0 ≠ i.val := by
        intro h; apply hi; exact Fin.ext h.symm
      rw [pairing_gen, if_neg hne, zero_mul]
    · simp

theorem pairing_gen_word {c : ℕ} (m : ℕ) (b : Bool)
    (α : Fin c → ℕ) (ε : Fin c → Bool) :
    EKPairingAdjoint.pairing (gen b m) (word α ε) =
      if m = ∑ j, α j then ∏ j, cell b (ε j) (α j) else 0 := by
  by_cases h : m = ∑ j, α j
  · rw [if_pos h, h, pairing_gen_word_total]
  · rw [if_neg h]
    exact pairing_homogeneous_orthogonal h (gen_weight b m) (word_weight α ε)

/-- Matrix summand with forbidden mixed cells given zero weight. -/
def matrixWeight {r c : ℕ} (η : Fin r → Bool) (ε : Fin c → Bool) (M : Raw r c) : ℤ :=
  (-1)^crossing M * ∏ i, ∏ j, cell (η i) (ε j) (M i j)

def matrixSum {r c : ℕ} (β : Fin r → ℕ) (η : Fin r → Bool)
    (α : Fin c → ℕ) (ε : Fin c → Bool) : ℤ :=
  ∑ M : Mat β α, matrixWeight η ε M

private theorem matrixWeight_join {r s c : ℕ} (η : Fin r → Bool) (θ : Fin s → Bool)
    (ε : Fin c → Bool) (U : Raw r c) (V : Raw s c) :
    matrixWeight (Fin.addCases η θ) ε (join U V) =
      (-1 : ℤ)^crossCols (colSum U) (colSum V) * matrixWeight η ε U * matrixWeight θ ε V := by
  simp only [matrixWeight, crossing_join, pow_add, Fin.prod_univ_add,
    Fin.addCases_left, Fin.addCases_right, join_left, join_right]
  ring

/-- Weighted version of the genuine margin-matrix splitting equivalence. -/
theorem matrixSum_convolution {r s c : ℕ} (β : Fin r → ℕ) (η : Fin r → Bool)
    (γ : Fin s → ℕ) (θ : Fin s → Bool) (α : Fin c → ℕ) (ε : Fin c → Bool) :
    matrixSum (Fin.addCases β γ) (Fin.addCases η θ) α ε =
      ∑ u : Splits α, (-1 : ℤ)^crossCols (upper u) (lower u) *
        matrixSum β η (upper u) ε * matrixSum γ θ (lower u) ε := by
  classical
  unfold matrixSum
  rw [← (matrixEquivSplit β γ α).symm.sum_comp (fun M => matrixWeight (Fin.addCases η θ) ε M)]
  change (∑ z : SplitMatrices β γ α, matrixWeight (Fin.addCases η θ) ε (join z.2.1 z.2.2)) = _
  simp only [matrixWeight_join, Fintype.sum_sigma, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl; intro u _
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro U _
  apply Finset.sum_congr rfl; intro V _
  rw [U.property.2, V.property.2]

theorem matrixSum_mismatch {r c : ℕ} (β : Fin r → ℕ) (η : Fin r → Bool)
    (α : Fin c → ℕ) (ε : Fin c → Bool) (hne : (∑ i, β i) ≠ ∑ j, α j) :
    matrixSum β η α ε = 0 := by
  haveI : IsEmpty (Mat β α) := ⟨fun M => hne (total_eq M)⟩
  exact Finset.sum_eq_zero (fun M _ => isEmptyElim M)

private theorem matrixSum_singleton {c : ℕ} (m : ℕ) (b : Bool)
    (α : Fin c → ℕ) (ε : Fin c → Bool) :
    matrixSum (fun _ : Fin 1 => m) (fun _ => b) α ε =
      if m = ∑ j, α j then ∏ j, cell b (ε j) (α j) else 0 := by
  classical
  by_cases h : m = ∑ j, α j
  · rw [if_pos h]
    let M : Mat (fun _ : Fin 1 => m) α := ⟨fun _ j => α j, by
      constructor
      · funext i; exact h.symm
      · funext j; simp [colSum]⟩
    have unique (N : Mat (fun _ : Fin 1 => m) α) : N = M := by
      apply Subtype.ext
      funext i j
      have hh := congrFun N.property.2 j
      simpa [colSum, Fin.sum_univ_one, Subsingleton.elim i (0 : Fin 1)] using hh
    unfold matrixSum
    rw [Finset.sum_eq_single M]
    · simp [M, matrixWeight, crossing]
    · intro N _ hne; exact (hne (unique N)).elim
    · simp
  · rw [if_neg h]
    exact matrixSum_mismatch _ _ _ _ (by simpa using h)

private theorem word_join {r s : ℕ} (β : Fin r → ℕ) (η : Fin r → Bool)
    (γ : Fin s → ℕ) (θ : Fin s → Bool) :
    word (Fin.addCases β γ) (Fin.addCases η θ) = word β η * word γ θ := by
  simp only [word, List.ofFn_add, Fin.addCases_left, Fin.addCases_right, List.prod_append]

private theorem matrixSum_zeroRows {c : ℕ} (β : Fin 0 → ℕ) (η : Fin 0 → Bool)
    (α : Fin c → ℕ) (ε : Fin c → Bool) :
    matrixSum β η α ε = if (∑ j, α j) = 0 then 1 else 0 := by
  classical
  by_cases h : (∑ j, α j) = 0
  · rw [if_pos h]
    have hz (j : Fin c) : α j = 0 := (Finset.sum_eq_zero_iff.mp h) j (Finset.mem_univ j)
    let M : Mat β α := ⟨fun i => Fin.elim0 i, by
      constructor
      · funext i; exact Fin.elim0 i
      · funext j; simp [colSum, hz]⟩
    unfold matrixSum
    rw [Finset.sum_eq_single M]
    · simp [matrixWeight, crossing]
    · intro N _ hne
      exact (hne (Subtype.ext (funext fun i => Fin.elim0 i))).elim
    · simp
  · rw [if_neg h]
    exact matrixSum_mismatch _ _ _ _ (by simpa [eq_comm] using h)

/-- General mixed pairing formula on the actual free algebra. -/
theorem pairing_word_eq_matrixSum {r c : ℕ} (β : Fin r → ℕ) (η : Fin r → Bool)
    (α : Fin c → ℕ) (ε : Fin c → Bool) :
    EKPairingAdjoint.pairing (word β η) (word α ε) = matrixSum β η α ε := by
  classical
  induction r generalizing c with
  | zero =>
    rw [word_zero, matrixSum_zeroRows]
    have hh := pairing_gen_word 0 false α ε
    by_cases hz : (∑ j, α j) = 0
    · have ha (j : Fin c) : α j = 0 := (Finset.sum_eq_zero_iff.mp hz) j (Finset.mem_univ j)
      simpa [gen, hz, ha] using hh
    · simpa [gen, hz, Ne.symm hz] using hh
  | succ r ih =>
    let β' : Fin r → ℕ := fun i => β (Fin.castAdd 1 i)
    let η' : Fin r → Bool := fun i => η (Fin.castAdd 1 i)
    have hb : β = Fin.addCases β' (fun _ : Fin 1 => β (Fin.last r)) := by
      funext i
      refine Fin.addCases ?_ ?_ i
      · intro j; simp [β']
      · intro j
        have hj : Fin.natAdd r j = Fin.last r := Fin.ext (by simp)
        rw [Fin.addCases_right, hj]
    have he : η = Fin.addCases η' (fun _ : Fin 1 => η (Fin.last r)) := by
      funext i
      refine Fin.addCases ?_ ?_ i
      · intro j; simp [η']
      · intro j
        have hj : Fin.natAdd r j = Fin.last r := Fin.ext (by simp)
        rw [Fin.addCases_right, hj]
    rw [hb, he, word_join, word_singleton, pairing_word_mul, matrixSum_convolution]
    apply Finset.sum_congr rfl
    intro u _
    rw [ih, pairing_gen_word, matrixSum_singleton]

/-- EK Proposition 2.6, actual quotient pairing in matrix form.
Zero and empty platforms are allowed; different total weights give an empty sum. -/
theorem quotientPairing_eq_matrixSum {r c : ℕ} (β : Fin r → ℕ) (η : Fin r → Bool)
    (α : Fin c → ℕ) (ε : Fin c → Bool) :
    quotientPairing (mixed β η) (mixed α ε) = matrixSum β η α ε := by
  rw [mixed_eq_pi, mixed_eq_pi, quotientPairing_pi]
  exact pairing_word_eq_matrixSum β η α ε

/-- Exactly the source restriction on oppositely colored platforms. -/
def Admissible {r c : ℕ} (η : Fin r → Bool) (ε : Fin c → Bool) (M : Raw r c) : Prop :=
  ∀ i j, η i ≠ ε j → M i j ≤ 1

/-- Internal longest-permutation signs between black platforms, EK p.13. -/
def blackPairs {r c : ℕ} (η : Fin r → Bool) (ε : Fin c → Bool) (M : Raw r c) : ℕ :=
  ∑ i, ∑ j, if η i && ε j then (M i j).choose 2 else 0

def MixedMatrices {r c : ℕ} (β : Fin r → ℕ) (η : Fin r → Bool)
    (α : Fin c → ℕ) (ε : Fin c → Bool) :=
  {M : Mat β α // Admissible η ε M}

instance {r c : ℕ} (β : Fin r → ℕ) (η : Fin r → Bool)
    (α : Fin c → ℕ) (ε : Fin c → Bool) : Fintype (MixedMatrices β η α ε) :=
  by
  classical
  exact inferInstanceAs (Fintype {M : Mat β α // Admissible η ε M})

private theorem matrixWeight_admissible {r c : ℕ} (η : Fin r → Bool) (ε : Fin c → Bool)
    (M : Raw r c) (h : Admissible η ε M) :
    matrixWeight η ε M = (-1 : ℤ)^(crossing M + blackPairs η ε M) := by
  have hc (i : Fin r) (j : Fin c) : cell (η i) (ε j) (M i j) =
      (-1 : ℤ)^(if η i && ε j then (M i j).choose 2 else 0) := by
    apply if_neg
    rintro ⟨hne, hlt⟩
    have := h i j hne
    omega
  simp only [matrixWeight, hc, Finset.prod_pow_eq_pow_sum, ← pow_add, blackPairs]

private theorem matrixWeight_forbidden {r c : ℕ} (η : Fin r → Bool) (ε : Fin c → Bool)
    (M : Raw r c) (h : ¬ Admissible η ε M) : matrixWeight η ε M = 0 := by
  classical
  simp only [Admissible, not_forall, not_le, _root_.not_imp] at h
  obtain ⟨i,j,hne,hlt⟩ := h
  unfold matrixWeight
  have hc : cell (η i) (ε j) (M i j) = 0 := if_pos ⟨hne,hlt⟩
  have hz : (∏ i, ∏ j, cell (η i) (ε j) (M i j)) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    exact Finset.prod_eq_zero (Finset.mem_univ j) hc
  rw [hz, mul_zero]

/-- Proposition 2.6 in restricted matrix form, with the literal single exponent. -/
theorem quotientPairing_eq_restricted_matrices {r c : ℕ} (β : Fin r → ℕ) (η : Fin r → Bool)
    (α : Fin c → ℕ) (ε : Fin c → Bool) :
    quotientPairing (mixed β η) (mixed α ε) =
      ∑ M : MixedMatrices β η α ε,
        (-1 : ℤ)^(crossing M.val + blackPairs η ε M.val) := by
  classical
  rw [quotientPairing_eq_matrixSum]
  exact Finset.sum_congr_set {M : Mat β α | Admissible η ε M}
    (fun M => matrixWeight η ε M)
    (fun M => (-1 : ℤ)^(crossing M.val + blackPairs η ε M.val))
    (fun M h => matrixWeight_admissible η ε M h)
    (fun M h => matrixWeight_forbidden η ε M h)

/-- Genuine minimal-platform diagrams, restricted by the source color condition.
These are the inherited actual permutations with endpoint maps, not matrices. -/
def MixedDiagrams {r c : ℕ} (β : Fin r → ℕ) (η : Fin r → Bool)
    (α : Fin c → ℕ) (ε : Fin c → Bool) :=
  {D : EKPlatformBijection.Diagrams β α // Admissible η ε D.val.matrix}

/-- Restriction of the already proved genuine diagram equivalence. -/
def mixedDiagramEquiv {r c : ℕ} (β : Fin r → ℕ) (η : Fin r → Bool)
    (α : Fin c → ℕ) (ε : Fin c → Bool) :
    MixedDiagrams β η α ε ≃ MixedMatrices β η α ε where
  toFun D := ⟨EKPlatformBijection.diagramEquiv β α D.val, D.property⟩
  invFun M := ⟨(EKPlatformBijection.diagramEquiv β α).symm M.val, by
    have hh := M.property
    have he := (EKPlatformBijection.diagramEquiv β α).apply_symm_apply M.val
    change Admissible η ε (EKPlatformBijection.diagramEquiv β α
      ((EKPlatformBijection.diagramEquiv β α).symm M.val))
    rw [he]; exact hh⟩
  left_inv D := Subtype.ext ((EKPlatformBijection.diagramEquiv β α).symm_apply_apply D.val)
  right_inv M := Subtype.ext ((EKPlatformBijection.diagramEquiv β α).apply_symm_apply M.val)

instance {r c : ℕ} (β : Fin r → ℕ) (η : Fin r → Bool)
    (α : Fin c → ℕ) (ε : Fin c → Bool) : Fintype (MixedDiagrams β η α ε) :=
  Fintype.ofEquiv (MixedMatrices β η α ε) (mixedDiagramEquiv β η α ε).symm

/-- EK Proposition 2.6, with the actual minimal-permutation inversion length
and black-black internal signs. No degree, positivity, or nonemptiness hypothesis. -/
theorem proposition_2_6 {r c : ℕ} (β : Fin r → ℕ) (η : Fin r → Bool)
    (α : Fin c → ℕ) (ε : Fin c → Bool) :
    quotientPairing (mixed β η) (mixed α ε) =
      ∑ D : MixedDiagrams β η α ε,
        (-1 : ℤ)^(D.val.val.length + blackPairs η ε D.val.val.matrix) := by
  rw [quotientPairing_eq_restricted_matrices]
  symm
  apply Fintype.sum_equiv (mixedDiagramEquiv β η α ε)
  intro D
  change (-1 : ℤ)^(D.val.val.length + blackPairs η ε D.val.val.matrix) =
    (-1 : ℤ)^(crossing D.val.val.matrix + blackPairs η ε D.val.val.matrix)
  rw [D.val.val.crossing_eq_length]

theorem quotientPairing_mismatch {r c : ℕ} (β : Fin r → ℕ) (η : Fin r → Bool)
    (α : Fin c → ℕ) (ε : Fin c → Bool) (hne : (∑ i, β i) ≠ ∑ j, α j) :
    quotientPairing (mixed β η) (mixed α ε) = 0 := by
  rw [quotientPairing_eq_matrixSum]
  exact matrixSum_mismatch β η α ε hne

end OddMath.Frontier.EKMixedPairing
