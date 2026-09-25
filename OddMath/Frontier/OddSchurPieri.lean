import OddMath.Frontier.OddSymmetrizer
import OddMath.Frontier.NilCoxeterWords

/-! EKL1111.1320v1, Lemma 2.25 and Proposition 2.26.
All polynomials are the literal integer skew polynomials; Schur means (2.69).
The helper consumers below are the invalid-summand elimination in (2.70)/(2.71). -/
namespace OddMath.Frontier.OddSchurPieri
open OddMath.SkewPolynomial (SkewPolynomial monomial generator expSingle)
open OddSymmetrizer LongestDivided AllRankDivided
open scoped BigOperators
noncomputable section

/-- The source column, padded with zeros. -/
def column (n k : ℕ) : PartitionExponent n :=
  ⟨fun i => if i.val < k then 1 else 0, by
    intro i j hij
    dsimp
    split_ifs <;> omega⟩

/-- Adding at most one box in each selected row. -/
def increment {N : ℕ} (α : Fin N → ℕ) (I : Finset (Fin N)) : Fin N → ℕ :=
  fun i => α i + if i ∈ I then 1 else 0

/-- Boxes strictly below the selected rows of the ORIGINAL partition. -/
def lowerRows {N : ℕ} (α : Fin N → ℕ) (I : Finset (Fin N)) : ℕ :=
  ∑ i ∈ I, ∑ j ∈ Finset.univ.filter (i < ·), α j

/-- A longest reduced word can end at every simple crossing. -/
theorem longest_ends (n : ℕ) (i : Fin (n+1)) :
    ∃ w : NilCoxeterWords.Word n,
      NilCoxeterWords.Reduced (w ++ [i]) ∧
      NilCoxeterWords.permutation (w ++ [i]) = LongestElementary.longest (n+2) := by
  let p := LongestElementary.longest (n+2)
  have hd : NilCoxeterWords.Descent p i := by
    change (n+2-(i.val+1+1)) < (n+2-(i.val+1))
    have := i.isLt
    omega
  obtain ⟨w, hw, hl⟩ := NilCoxeterWords.exists_reduced (p * NilCoxeterWords.simple i)
  have hp : NilCoxeterWords.permutation (w ++ [i]) = p := by
    simp [hw, NilCoxeterWords.mul_simple_cancel]
  refine ⟨w, ?_, hp⟩
  unfold NilCoxeterWords.Reduced
  rw [hp, List.length_append, List.length_singleton, hl]
  exact NilCoxeterWords.length_descend p i hd

/-- Local vanishing implies vanishing under the actual distinguished source D. -/
theorem D_of_divided_zero {n : ℕ} (i : Fin (n+1)) (f : SkewPolynomial (n+2))
    (hf : divided i f = 0) : D (n+2) f = 0 := by
  obtain ⟨w, hr, hp⟩ := longest_ends n i
  have hz : applyWord (w ++ [i]) f = 0 := by
    rw [applyWord_append, applyWord_cons, applyWord_nil, hf, map_zero]
  have hs := NilCoxeterWords.reduced_operator_signed
    (wordIn n (n+2) le_rfl) (w ++ [i]) (NilCoxeterWords.sourceWord_reduced n) hr
    ((NilCoxeterWords.sourceWord_permutation n).trans hp.symm)
  rcases hs with hs | hs
  · change applyWord _ f = 0
    rw [hs, hz]
  · change applyWord _ f = 0
    rw [hs, LinearMap.neg_apply, hz, neg_zero]

/-- Normal ordering of two coefficient-one monomials, with its actual sign. -/
theorem mono_mul {N : ℕ} (a b : Fin N → ℕ) :
    monomial a 1 * monomial b 1 = OddMath.skewSign a b • monomial (a+b) 1 := by
  change OddMath.SkewPolynomial.mul _ _ = _
  rw [OddMath.SkewPolynomial.mul_monomial, PbwL4.monomial_smul]
  norm_num

theorem sign_sq {N : ℕ} (a b : Fin N → ℕ) :
    OddMath.skewSign a b * OddMath.skewSign a b = 1 := by
  rw [OddMath.skewSign, ← mul_pow]
  norm_num

/-- Only used to assemble a balanced pair with spectator powers. -/
theorem mono_add_mem {N : ℕ} (R : Subring (SkewPolynomial N)) (a b : Fin N → ℕ)
    (ha : monomial a 1 ∈ R) (hb : monomial b 1 ∈ R) : monomial (a+b) 1 ∈ R := by
  have h := R.zsmul_mem (R.mul_mem ha hb) (OddMath.skewSign a b)
  rw [mono_mul, smul_smul, sign_sq, one_smul] at h
  exact h

theorem mono_sum_mem {N : ℕ} (R : Subring (SkewPolynomial N))
    (s : Finset (Fin N)) (a : Fin N → Fin N → ℕ)
    (h : ∀ j ∈ s, monomial (a j) 1 ∈ R) : monomial (∑ j ∈ s, a j) 1 ∈ R := by
  induction s using Finset.induction_on with
  | empty => simpa using R.one_mem
  | @insert j s hj ih =>
    rw [Finset.sum_insert hj]
    exact mono_add_mem R _ _ (h j (by simp)) (ih (fun l hl => h l (by simp [hl])))

/-- Equal adjacent exponents are killed, with arbitrary spectator exponents. -/
theorem divided_equal {n : ℕ} (i : Fin (n+1)) (a : Fin (n+2) → ℕ)
    (ha : a i.castSucc = a i.succ) : divided i (monomial a 1) = 0 := by
  let R := OddSymmetricKernel.singleKernel i
  let b := a i.castSucc
  let q := b • expSingle i.castSucc + b • expSingle i.succ
  have hp : monomial q 1 ∈ R := by
    have h : generator i.castSucc ^ b * generator i.succ ^ b ∈ R := divided_balanced i b
    rw [PbwL4.pow_form, PbwL4.pow_form, mono_mul] at h
    have h' := R.zsmul_mem h
      (OddMath.skewSign (b • expSingle i.castSucc) (b • expSingle i.succ))
    rw [smul_smul, sign_sq, one_smul] at h'
    exact h'
  let s := Finset.univ.filter (fun j => j ≠ i.castSucc ∧ j ≠ i.succ)
  have hs : monomial (∑ j ∈ s, a j • expSingle j) 1 ∈ R := by
    apply mono_sum_mem
    intro j hj
    rw [← PbwL4.pow_form]
    apply R.pow_mem
    change divided i (generator j) = 0
    obtain ⟨h₀,h₁⟩ := (Finset.mem_filter.mp hj).2
    simp [divided_generator, h₀, h₁]
  have he : q + ∑ j ∈ s, a j • expSingle j = a := by
    funext j
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, expSingle]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', s, Finset.mem_filter,
      Finset.mem_univ, true_and, q, Pi.add_apply, Pi.smul_apply, smul_eq_mul, expSingle]
    by_cases h₀ : j = i.castSucc
    · subst j
      simp [b, adjacent_ne i, (adjacent_ne i).symm]
    · by_cases h₁ : j = i.succ
      · subst j
        simp [b, adjacent_ne i, (adjacent_ne i).symm, ha]
      · simp [h₀, h₁, Ne.symm h₀, Ne.symm h₁]
  rw [← he]
  exact mono_add_mem R _ _ hp hs

/-- A nonpartition one-box-per-row increment has an adjacent bad pair. -/
theorem invalid_adjacent {n : ℕ} (α : PartitionExponent n) (I : Finset (Fin (n+2)))
    (h : ¬Antitone (increment α.val I)) :
    ∃ i : Fin (n+1), α.val i.castSucc = α.val i.succ ∧ i.castSucc ∉ I ∧ i.succ ∈ I := by
  have hh : ∃ i : Fin (n+1), increment α.val I i.castSucc < increment α.val I i.succ := by
    by_contra hn
    apply h
    apply Fin.antitone_iff_succ_le.mpr
    intro i
    exact le_of_not_gt (fun hi => hn ⟨i, hi⟩)
  obtain ⟨i, hi⟩ := hh
  have ha := α.property (Fin.castSucc_le_succ i)
  dsimp [increment] at hi
  refine ⟨i, ?_⟩
  by_cases h₀ : i.castSucc ∈ I <;> by_cases h₁ : i.succ ∈ I
  all_goals simp only [h₀, h₁, if_true, if_false] at hi
  all_goals first | omega | exact ⟨by omega, h₀, h₁⟩

/-- Exactly the invalid terms in the source Pieri proof vanish under S. -/
theorem S_invalid {n : ℕ} (α : PartitionExponent n) (I : Finset (Fin (n+2)))
    (h : ¬Antitone (increment α.val I)) :
    S n (monomial (increment α.val I) 1) = 0 := by
  obtain ⟨i, he, h₀, h₁⟩ := invalid_adjacent α I h
  rw [S_apply, staircase, mono_mul, map_smul, map_zsmul]
  have hz : D (n+2) (monomial (increment α.val I + fun j => n+2-1-j.val) 1) = 0 := by
    apply D_of_divided_zero i
    apply divided_equal
    simp only [Pi.add_apply, increment, if_neg h₀, if_pos h₁, Fin.coe_castSucc, Fin.val_succ]
    have := i.isLt
    omega
  rw [hz, map_zero, smul_zero, smul_zero]

/-- Square-free ordered exponent of a subset. -/
def subsetExp {N : ℕ} (I : Finset (Fin N)) : Fin N → ℕ := fun i => if i ∈ I then 1 else 0

def tildeWeight {N : ℕ} (I : Finset (Fin N)) : ℕ := ∑ i ∈ I, i.val

def subsetTilde {N : ℕ} (I : Finset (Fin N)) : SkewPolynomial N :=
  (-1 : ℤ)^tildeWeight I • monomial (subsetExp I) 1

/-- The literal increasing tilde product in coefficient normal form. -/
theorem sorted_tilde {N : ℕ} (w : List (Fin N)) (hw : w.Sorted (· ≤ ·)) :
    (w.map PlacticEvaluation.tildeGenerator).prod =
      (-1 : ℤ)^(w.map Fin.val).sum • monomial (PbwRealization.exponents w) 1 := by
  induction w with
  | nil => simp [PbwRealization.exponents_nil]; rfl
  | cons i w ih =>
    obtain ⟨hi, ht⟩ := List.pairwise_cons.mp hw
    simp only [List.map_cons, List.prod_cons, List.sum_cons, ih ht,
      PlacticEvaluation.tildeGenerator, smul_mul_assoc, mul_smul_comm]
    change _ • (_ • (monomial (expSingle i) 1 * monomial _ 1)) = _
    rw [mono_mul, OddMath.skewSign, PbwRealization.crossingCount_head i w hi,
      pow_zero, one_smul, smul_smul, ← pow_add, PbwRealization.exponents_cons]
    rw [Nat.add_comm]

/-- Strict word and subset normal forms agree, including the tilde sign. -/
theorem strict_tilde {N k : ℕ} (f : Fin k → Fin N) (hf : StrictMono f) :
    (List.ofFn (fun i => PlacticEvaluation.tildeGenerator (f i))).prod =
      subsetTilde (Finset.univ.image f) := by
  classical
  have hw : (List.ofFn f).Sorted (· ≤ ·) := List.pairwise_ofFn.mpr (fun i j hij => (hf hij).le)
  have he : PbwRealization.exponents (List.ofFn f) = subsetExp (Finset.univ.image f) := by
    funext j
    rw [ElementaryGeneration.exponents_ofFn_injective f hf.injective]
    simp [subsetExp, Set.mem_range]
  have hs : ((List.ofFn f).map Fin.val).sum = tildeWeight (Finset.univ.image f) := by
    rw [List.map_ofFn, List.sum_ofFn, tildeWeight,
      Finset.sum_image (fun _ _ _ _ h => hf.injective h)]
    rfl
  have hh := sorted_tilde (List.ofFn f) hw
  rw [he, hs] at hh
  simpa only [List.map_ofFn, Function.comp_def] using hh

/-- Reindex increasing words by actual k-element subsets, not tableaux. -/
theorem sum_strict_subsets {N k : ℕ} {A : Type*} [AddCommMonoid A]
    (F : Finset (Fin N) → A) :
    (∑ f : Fin k → Fin N, if StrictMono f then F (Finset.univ.image f) else 0) =
      ∑ I ∈ Finset.univ.filter (fun I : Finset (Fin N) => I.card = k), F I := by
  classical
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun f _ => Finset.univ.image f)
  · intro f hf
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢
    rw [Finset.card_image_of_injective _ hf.injective, Finset.card_univ, Fintype.card_fin]
  · intro f hf g hg he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf hg
    apply hf.range_inj hg |>.mp
    have hh := congrArg (fun s : Finset (Fin N) => (s : Set (Fin N))) he
    simpa using hh
  · intro I hI
    have hc := (Finset.mem_filter.mp hI).2
    refine ⟨I.orderEmbOfFin hc, ?_, ?_⟩
    · simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
        (I.orderEmbOfFin hc).strictMono
    · apply Finset.coe_injective
      simp
  · intro f _; rfl

/-- Literal elementary polynomials as subset monomials. -/
theorem elementary_subsets (N k : ℕ) :
    FiniteCompleteElementary.elementaryPoly N k =
      ∑ I ∈ Finset.univ.filter (fun I : Finset (Fin N) => I.card = k), subsetTilde I := by
  rw [← sum_strict_subsets subsetTilde]
  unfold FiniteCompleteElementary.elementaryPoly
  apply Finset.sum_congr rfl
  intro f _
  by_cases hf : StrictMono f
  · simp only [hf, if_true, strict_tilde f hf]
  · simp [hf]

/-- An antitone zero-one exponent is an initial column. -/
theorem antitone_subset {N : ℕ} (I : Finset (Fin N)) (h : Antitone (subsetExp I)) :
    subsetExp I = fun j => if j.val < I.card then 1 else 0 := by
  classical
  funext j
  have he : j ∈ I ↔ j.val < I.card := by
    constructor
    · intro hj
      have hs : Finset.Iic j ⊆ I := by
        intro l hl
        have hh := h (Finset.mem_Iic.mp hl)
        simp only [subsetExp, if_pos hj] at hh
        by_contra hn
        simp [hn] at hh
      have hc := Finset.card_le_card hs
      simp only [Fin.card_Iic] at hc
      omega
    · intro hj
      by_contra hn
      have hs : I ⊆ Finset.Iio j := by
        intro l hl
        apply Finset.mem_Iio.mpr
        exact lt_of_not_ge (fun hjl => by
          have hh := h hjl
          simp [subsetExp, hn, hl] at hh)
      have hc := Finset.card_le_card hs
      simp only [Fin.card_Iio] at hc
      omega
  simp only [subsetExp, he]

/-- Initial column subset. -/
def initial (N k : ℕ) : Finset (Fin N) := Finset.univ.filter (fun j => j.val < k)

theorem initial_card (N k : ℕ) (hk : k ≤ N) : (initial N k).card = k := by
  have he : initial N k = Finset.univ.image (Fin.castLE hk) := by
    ext j
    simp only [initial, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hj; exact ⟨⟨j.val,hj⟩, Fin.ext rfl⟩
    · rintro ⟨i,rfl⟩; exact i.isLt
  rw [he, Finset.card_image_of_injective _ (Fin.castLE_injective hk)]
  simp

theorem initial_weight (N k : ℕ) (hk : k ≤ N) : tildeWeight (initial N k) = k.choose 2 := by
  have he : initial N k = Finset.univ.image (Fin.castLE hk) := by
    ext j
    simp only [initial, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hj; exact ⟨⟨j.val,hj⟩, Fin.ext rfl⟩
    · rintro ⟨i,rfl⟩; exact i.isLt
  rw [tildeWeight, he, Finset.sum_image (fun _ _ _ _ h => Fin.castLE_injective hk h)]
  change (∑ j : Fin k, j.val) = k.choose 2
  clear he hk N
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.coe_castSucc, Fin.val_last]
    rw [ih, Nat.choose_succ_succ, Nat.choose_one_right, Nat.add_comm]

/-- EKL Lemma 2.25 (2.70), including the empty column. -/
theorem schur_column (n k : ℕ) (hk : k ≤ n+2) :
    schur n (column n k) = (-1 : ℤ)^k.choose 2 •
      FiniteCompleteElementary.elementaryPoly (n+2) k := by
  classical
  have he : FiniteCompleteElementary.elementaryPoly (n+2) k =
      (-1 : ℤ)^k.choose 2 • schur n (column n k) := by
    rw [← S_eq_self n _ (OddSymmetricKernel.elementary_mem n k), elementary_subsets, map_sum]
    rw [Finset.sum_eq_single (initial (n+2) k)]
    · rw [subsetTilde, map_smul, initial_weight _ _ hk]
      have hx : subsetExp (initial (n+2) k) = (column n k).val := by
        funext j
        simp [subsetExp, initial, column]
      rw [hx]
      rfl
    · intro I hI hne
      have hc := (Finset.mem_filter.mp hI).2
      have hn : ¬Antitone (subsetExp I) := by
        intro hh
        apply hne
        ext j
        have he := congrFun (antitone_subset I hh) j
        rw [hc] at he
        simp only [subsetExp] at he
        simp only [initial, Finset.mem_filter, Finset.mem_univ, true_and]
        split_ifs at he <;> simp_all
      rw [subsetTilde, map_smul]
      have hh := S_invalid (column n 0) I
      have hi : increment (column n 0).val I = subsetExp I := by
        funext j; simp [increment, column, subsetExp]
      rw [hi] at hh
      rw [hh hn, smul_zero]
    · intro hn
      exact (hn (by simp [initial_card _ _ hk])).elim
  rw [he, smul_smul, ← mul_pow]
  norm_num

/-- The staircase exponent, in locked increasing variable order. -/
def deltaExp (N : ℕ) : Fin N → ℕ := fun j => N-1-j.val

theorem delta_sum (N : ℕ) : (∑ j : Fin N, deltaExp N j) = N.choose 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Fin.sum_univ_succ]
    simp only [deltaExp, Fin.val_zero, Nat.sub_zero, Nat.add_sub_cancel, Fin.val_succ]
    have he : (fun j : Fin N => N-(j.val+1)) = deltaExp N := by
      funext j; dsimp [deltaExp]; omega
    rw [he, ih, Nat.choose_succ_succ, Nat.choose_one_right]

/-- Crossing with a square-free right factor counts original lower rows. -/
theorem cross_right_subset {N : ℕ} (a : Fin N → ℕ) (I : Finset (Fin N)) :
    OddMath.crossingCount a (subsetExp I) = lowerRows a I := by
  classical
  simp only [OddMath.crossingCount, subsetExp, Finset.sum_filter,
    mul_ite, mul_one, mul_zero]
  rw [Finset.sum_comm]
  simp only [lowerRows, Finset.sum_filter]
  calc
    _ = ∑ i : Fin N, if i ∈ I then ∑ j : Fin N, if i < j then a j else 0 else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i ∈ I
      · simp only [hi, if_true]
      · simp only [hi, if_false, ite_self, Finset.sum_const_zero]
    _ = _ := by rw [← Finset.sum_filter]; simp

theorem cross_left_subset {N : ℕ} (a : Fin N → ℕ) (I : Finset (Fin N)) :
    OddMath.crossingCount (subsetExp I) a =
      ∑ i ∈ I, ∑ j ∈ Finset.univ.filter (· < i), a j := by
  classical
  simp only [OddMath.crossingCount, subsetExp, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_irrel, Finset.sum_const_zero]
  rw [← Finset.sum_filter]
  simp

/-- Moving a subset through the staircase contributes a constant sign per box. -/
theorem staircase_crossing {N : ℕ} (hN : 0 < N) (I : Finset (Fin N)) :
    tildeWeight I + OddMath.crossingCount (deltaExp N) (subsetExp I) +
      OddMath.crossingCount (subsetExp I) (deltaExp N) =
        I.card * (N-1).choose 2 + 2 * tildeWeight I := by
  classical
  rw [cross_right_subset, cross_left_subset]
  have hrow (i : Fin N) :
      i.val + (∑ j ∈ Finset.univ.filter (i < ·), deltaExp N j) +
        (∑ j ∈ Finset.univ.filter (· < i), deltaExp N j) =
          (N-1).choose 2 + 2*i.val := by
    have hs : (∑ j ∈ Finset.univ.filter (i < ·), deltaExp N j) +
        (∑ j ∈ Finset.univ.filter (· < i), deltaExp N j) + deltaExp N i =
        ∑ j : Fin N, deltaExp N j := by
      calc
        _ = ∑ j : Fin N, ((if i < j then deltaExp N j else 0) +
            (if j < i then deltaExp N j else 0) + (if j = i then deltaExp N j else 0)) := by
          simp [Finset.sum_add_distrib, Finset.sum_filter]
        _ = _ := by
          apply Finset.sum_congr rfl
          intro j _
          rcases lt_trichotomy j i with hj | hj | hj
          · simp [hj, not_lt.mpr hj.le, ne_of_lt hj]
          · subst j; simp
          · simp [hj, not_lt.mpr hj.le, (ne_of_gt hj)]
    have ht : N.choose 2 = (N-1).choose 2 + (N-1) := by
      have he : N = (N-1)+1 := by omega
      conv_lhs => rw [he, Nat.choose_succ_succ, Nat.choose_one_right]
      exact Nat.add_comm _ _
    rw [delta_sum, ht] at hs
    dsimp [deltaExp] at hs ⊢
    have := i.isLt
    omega
  simp only [tildeWeight, lowerRows, ← Finset.sum_add_distrib]
  simp_rw [hrow]
  simp [Finset.sum_add_distrib, Finset.mul_sum, Nat.mul_comm]

theorem staircase_subset {N : ℕ} (hN : 0 < N) (I : Finset (Fin N)) :
    staircase N * subsetTilde I = (-1 : ℤ)^(I.card*(N-1).choose 2) •
      (monomial (subsetExp I) 1 * staircase N) := by
  have hp : ((-1 : ℤ)^tildeWeight I * OddMath.skewSign (deltaExp N) (subsetExp I)) *
      OddMath.skewSign (subsetExp I) (deltaExp N) = (-1 : ℤ)^(I.card*(N-1).choose 2) := by
    simp only [OddMath.skewSign, ← pow_add]
    rw [staircase_crossing hN I, pow_add, pow_mul]
    norm_num
  have he : (-1 : ℤ)^tildeWeight I * OddMath.skewSign (deltaExp N) (subsetExp I) =
      (-1 : ℤ)^(I.card*(N-1).choose 2) * OddMath.skewSign (subsetExp I) (deltaExp N) := by
    rw [← hp, mul_assoc, sign_sq, mul_one]
  change monomial (deltaExp N) 1 * subsetTilde I = _
  rw [subsetTilde, mul_smul_comm, mono_mul, smul_smul]
  change _ = _ • (monomial (subsetExp I) 1 * monomial (deltaExp N) 1)
  rw [mono_mul, smul_smul, he, add_comm]

/-- The source's normal-ordering calculation, including every sign. -/
theorem pieri_normal_order {N : ℕ} (hN : 0 < N) (a : Fin N → ℕ)
    (I : Finset (Fin N)) :
    (monomial a 1 * staircase N) * subsetTilde I =
      (-1 : ℤ)^(I.card*(N-1).choose 2) •
        ((-1 : ℤ)^lowerRows a I • (monomial (increment a I) 1 * staircase N)) := by
  rw [mul_assoc, staircase_subset hN I, mul_smul_comm, ← mul_assoc, mono_mul,
    smul_mul_assoc, OddMath.skewSign, cross_right_subset]
  rfl

/-- Right multiplication by the signed elementary column, transported inside D.
The position of the elementary factor is essential in the noncommutative ring. -/
theorem right_elementary_transport (n k : ℕ) (f : SkewPolynomial (n+2)) :
    S n f * ((-1 : ℤ)^k.choose 2 • FiniteCompleteElementary.elementaryPoly (n+2) k) =
      (-1 : ℤ)^(k*(n+1).choose 2) •
        ((-1 : ℤ)^((n+2).choose 3) •
          SignedPermutation.skewAction (LongestElementary.longest (n+2))
            (D (n+2) ((f * staircase (n+2)) *
              FiniteCompleteElementary.elementaryPoly (n+2) k))) := by
  rw [D_right_kernel n _ _ (OddSymmetricKernel.elementary_mem n k), map_mul,
    LongestElementary.action_elementary]
  simp only [S_apply, pow_add, mul_smul_comm, smul_mul_assoc, smul_smul,
    show n+2-1 = n+1 by omega]
  congr 1
  calc
    _ = ((-1 : ℤ)^(k*(n+1).choose 2) * (-1 : ℤ)^(k*(n+1).choose 2)) *
        ((-1 : ℤ)^((n+2).choose 3) * (-1 : ℤ)^k.choose 2) := by
      rw [← mul_pow]; norm_num; ring
    _ = _ := by ring

/-- The unfiltered right Pieri sum for the literal S-defined polynomials. -/
theorem pieri_all_subsets (n k : ℕ) (hk : k ≤ n+2) (α : PartitionExponent n) :
    schur n α * schur n (column n k) =
      ∑ I ∈ Finset.univ.filter (fun I : Finset (Fin (n+2)) => I.card = k),
        (-1 : ℤ)^lowerRows α.val I • S n (monomial (increment α.val I) 1) := by
  classical
  rw [schur_column n k hk]
  change S n (monomial α.val 1) * _ = _
  rw [right_elementary_transport, elementary_subsets, Finset.mul_sum, map_sum,
    map_sum, Finset.smul_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  have hc := (Finset.mem_filter.mp hI).2
  rw [pieri_normal_order (by omega)]
  simp only [map_zsmul]
  rw [hc]
  simp only [S_apply, smul_smul, show n+2-1 = n+1 by omega]
  have hs : (-1 : ℤ)^(k*(n+1).choose 2) * (-1 : ℤ)^(k*(n+1).choose 2) = 1 := by
    rw [← mul_pow]; norm_num
  congr 1
  calc
    _ = ((-1 : ℤ)^(k*(n+1).choose 2) * (-1 : ℤ)^(k*(n+1).choose 2)) *
        ((-1 : ℤ)^lowerRows α.val I * (-1 : ℤ)^((n+2).choose 3)) := by ring
    _ = _ := by rw [hs, one_mul]

/-- Exact vertical-strip index: subsets of k rows whose increment is a partition. -/
def VerticalStrip (n k : ℕ) (α : PartitionExponent n) :=
  {I : Finset (Fin (n+2)) // I.card = k ∧ Antitone (increment α.val I)}

instance (n k : ℕ) (α : PartitionExponent n) : Fintype (VerticalStrip n k α) := by
  classical
  unfold VerticalStrip
  infer_instance

/-- The partition indexed by a vertical strip; proof terms are erased. -/
def stripPartition {n k : ℕ} {α : PartitionExponent n} (I : VerticalStrip n k α) :
    PartitionExponent n := ⟨increment α.val I.val, I.property.2⟩

/-- EKL Proposition 2.26 (2.71), actual right product and original lower-row signs.
Includes k=0 without extra assumptions; k≥1 is the printed source domain. -/
theorem right_pieri (n k : ℕ) (hk : k ≤ n+2) (α : PartitionExponent n) :
    schur n α * schur n (column n k) =
      ∑ I : VerticalStrip n k α,
        (-1 : ℤ)^lowerRows α.val I.val • schur n (stripPartition I) := by
  classical
  rw [pieri_all_subsets n k hk α]
  change _ = ∑ I : {I : Finset (Fin (n+2)) // I.card = k ∧ Antitone (increment α.val I)},
    (-1 : ℤ)^lowerRows α.val I.val • S n (monomial (increment α.val I.val) 1)
  rw [← Finset.sum_subtype (p := fun I : Finset (Fin (n+2)) =>
      I.card = k ∧ Antitone (increment α.val I)) (Finset.univ.filter
    (fun I : Finset (Fin (n+2)) => I.card = k ∧ Antitone (increment α.val I)))
    (by intro I; simp)
    (fun I => (-1 : ℤ)^lowerRows α.val I • S n (monomial (increment α.val I) 1))]
  rw [Finset.sum_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro I _
  by_cases hc : I.card = k
  · by_cases ha : Antitone (increment α.val I)
    · simp only [hc, ha, and_self, dite_true, if_true]
    · simp only [hc, ha, and_false, dite_false, if_true, if_false]
      rw [S_invalid α I ha, smul_zero]
  · simp only [hc, false_and, dite_false, if_false]

end
end OddMath.Frontier.OddSchurPieri
