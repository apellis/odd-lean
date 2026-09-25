import OddMath.Frontier.OmissionWord

/-! EKL Lemma 2.18, only the frozen descending-block word. -/
namespace OddMath.Frontier.OmissionCanonical
open OddMath.SkewPolynomial (SkewPolynomial)
open NilCoxeterWords OmissionWord LongestDivided
open scoped BigOperators
noncomputable section

/-- The exact selected word, not the source D word. -/
def word (n : ℕ) : Word n := (wordIn n (n+2) le_rfl).reverse.map Fin.rev

theorem permutation_reverse {n : ℕ} (w : Word n) :
    permutation w.reverse = (permutation w)⁻¹ := by
  induction w with
  | nil => simp [permutation]
  | cons i w ih =>
    simp only [List.reverse_cons, permutation_append, permutation_singleton, ih, permutation,
      mul_inv_rev]
    congr 1

theorem simple_reflect {n : ℕ} (i : Fin (n+1)) :
    simple i.rev = LongestElementary.longest (n+2) * simple i *
      LongestElementary.longest (n+2) := by
  have h₁ : (i.castSucc).rev = i.rev.succ := by apply Fin.ext; simp [Fin.val_rev]; omega
  have h₂ : (i.succ).rev = i.rev.castSucc := by apply Fin.ext; simp [Fin.val_rev]
  simp only [simple]
  rw [Equiv.mul_swap_eq_swap_mul]
  simp only [LongestElementary.longest_apply, h₁, h₂, mul_assoc,
    LongestElementary.longest_involutive, mul_one]
  exact Equiv.swap_comm _ _

theorem permutation_reflect {n : ℕ} (w : Word n) :
    permutation (w.map Fin.rev) = LongestElementary.longest (n+2) * permutation w *
      LongestElementary.longest (n+2) := by
  induction w with
  | nil => simp [permutation]
  | cons i w ih =>
    simp only [List.map_cons, permutation, simple_reflect, ih]
    simp only [mul_assoc, ← mul_assoc (LongestElementary.longest (n+2))
      (LongestElementary.longest (n+2)), LongestElementary.longest_involutive, one_mul]

theorem word_permutation (n : ℕ) :
    permutation (word n) = LongestElementary.longest (n+2) := by
  rw [word, permutation_reflect, permutation_reverse, sourceWord_permutation]
  have hi : (LongestElementary.longest (n+2))⁻¹ = LongestElementary.longest (n+2) := by
    apply inv_eq_of_mul_eq_one_right
    exact LongestElementary.longest_involutive _
  rw [hi, LongestElementary.longest_involutive, one_mul]

theorem word_reduced (n : ℕ) : Reduced (word n) := by
  unfold Reduced
  rw [word_permutation, ← sourceWord_permutation n, ← sourceWord_reduced n]
  simp [word]

/-- Inversion length is invariant under actual permutation inversion. -/
theorem length_inverse {n : ℕ} (p : Perm n) : length p⁻¹ = length p := by
  classical
  unfold length
  rw [← Equiv.sum_comp p (fun a => ∑ b : Fin (n+2),
    if a < b ∧ p⁻¹ b < p⁻¹ a then (1 : ℕ) else 0)]
  simp only [Equiv.Perm.inv_apply_self]
  conv_lhs =>
    arg 2
    ext a
    rw [← Equiv.sum_comp p (fun b => if p a < b ∧ p⁻¹ b < a then (1 : ℕ) else 0)]
  simp only [Equiv.Perm.inv_apply_self]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  simp only [and_comm]

theorem reduced_reverse {n : ℕ} (w : Word n) : Reduced w.reverse ↔ Reduced w := by
  simp only [Reduced, List.length_reverse, permutation_reverse, length_inverse]

/-- Contiguous suffixes, not arbitrary subwords, inherit reducedness. -/
theorem reduced_tail {n : ℕ} (i : Fin (n+1)) (w : Word n) (h : Reduced (i::w)) : Reduced w := by
  apply (reduced_reverse w).mp
  have hr := (reduced_reverse (i::w)).mpr h
  rw [List.reverse_cons] at hr
  exact (reduced_prefix _ _ hr).1

theorem reduced_suffix {n : ℕ} (u v : Word n) (h : Reduced (u++v)) : Reduced v := by
  induction u with
  | nil => exact h
  | cons i u ih => exact ih (reduced_tail i _ h)

/-- A descending block k+r-1,...,k on the actual alphabet. -/
def down (n k : ℕ) : (r : ℕ) → k+r ≤ n+1 → Word n
  | 0, _ => []
  | r+1, h => ⟨k+r, by omega⟩ :: down n k r (by omega)

@[simp] theorem down_length (n k r : ℕ) (h : k+r ≤ n+1) :
    (down n k r h).length = r := by
  induction r with
  | zero => rfl
  | succ r ih => simp [down, ih]

theorem down_mem {n k r : ℕ} {h : k+r ≤ n+1} {i : Fin (n+1)}
    (hi : i ∈ down n k r h) : k ≤ i.val ∧ i.val < k+r := by
  induction r with
  | zero => simp [down] at hi
  | succ r ih =>
    simp only [down, List.mem_cons] at hi
    rcases hi with rfl | hi
    · simp
    · have := ih hi; omega

theorem permutation_fix_of_support {n : ℕ} (w : Word n) (x : Fin (n+2))
    (h : ∀ i ∈ w, i.val+1 < x.val) : permutation w x = x := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change simple i (permutation w x) = x
    rw [ih (fun j hj => h j (List.mem_cons_of_mem _ hj))]
    apply simple_apply_other
    · intro he; have hx := congrArg Fin.val he; have := h i (by simp)
      simp only [Fin.coe_castSucc] at hx; omega
    · intro he; have hx := congrArg Fin.val he; have := h i (by simp)
      simp only [Fin.val_succ] at hx; omega

/-- Left descent is the obstruction to prepending to a reduced suffix. -/
theorem no_left_descent {n : ℕ} (i : Fin (n+1)) (w : Word n)
    (h : Reduced (i::w)) : ¬Descent (permutation w)⁻¹ i := by
  have hr := (reduced_reverse (i::w)).mpr h
  rw [List.reverse_cons] at hr
  simpa only [permutation_reverse] using (reduced_prefix _ _ hr).2

theorem erase_append {n : ℕ} (a b : Marked n) : erase (a++b) = erase a ++ erase b := by
  simp [erase]

theorem omission_append {n : ℕ} (a b : Marked n) : omission (a++b) = omission a ++ omission b := by
  induction a with
  | nil => rfl
  | cons x a ih => cases x with | mk i v => cases v <;> simp [omission, ih]

theorem hybrid_append {n : ℕ} (a b : Marked n) (f : SkewPolynomial (n+2)) :
    hybrid (a++b) f = hybrid a (hybrid b f) := by
  induction a with
  | nil => rfl
  | cons x a ih => cases x with | mk i v => cases v <;> simp [hybrid, ih]

def allTrue {n : ℕ} (w : Word n) : Marked n := w.map (fun i => (i,true))

@[simp] theorem omission_allTrue {n : ℕ} (w : Word n) : omission (allTrue w) = [] := by
  induction w with
  | nil => rfl
  | cons i w ih => simpa [allTrue, omission] using ih

/-- Contextual block combinatorics: the all-false terminal longest block forces
    all true marks to the left. The suffix hypothesis is actual permutation descents. -/
theorem block_shape {n k r : ℕ} (h : k+r ≤ n+1) (m : Marked n) (v : Word n)
    (he : erase m = down n k r h)
    (hd : ∀ i : Fin (n+1), k < i.val → Descent (permutation v)⁻¹ i)
    (hr : Reduced (omission m ++ v)) :
    ∃ t : ℕ, ∃ ht : t ≤ r,
      m = allTrue (down n (k+t) (r-t) (by omega)) ++
        allFalse (down n k t (by omega)) := by
  induction r generalizing m with
  | zero =>
    have hm : m = [] := by simpa [erase, down] using he
    subst m
    exact ⟨0, le_rfl, rfl⟩
  | succ r ih =>
    cases m with
    | nil => simp [down] at he
    | cons a m =>
      rcases a with ⟨i,b⟩
      simp only [erase_cons, down, List.cons.injEq] at he
      obtain ⟨rfl, he⟩ := he
      have hrt : Reduced (omission m ++ v) := by
        cases b
        · exact reduced_tail _ _ hr
        · exact hr
      obtain ⟨t, ht, hm⟩ := ih (by omega) m he hrt
      cases b
      · have htr : t = r := by
          by_contra hn
          have hlt : t < r := by omega
          have hred : Reduced (⟨k+r, by omega⟩ :: (down n k t (by omega) ++ v)) := by
            simpa [omission, hm, omission_append] using hr
          have hnleft := no_left_descent _ _ hred
          apply hnleft
          simp only [permutation_append, mul_inv_rev]
          have hfix (x : Fin (n+2)) (hx : k+t < x.val) :
              (permutation (down n k t (by omega)))⁻¹ x = x := by
            rw [← permutation_reverse]
            apply permutation_fix_of_support
            intro j hj
            have hj' := down_mem (List.mem_reverse.mp hj)
            omega
          change (permutation v)⁻¹ ((permutation (down n k t _))⁻¹
            (⟨k+r, by omega⟩ : Fin (n+1)).succ) <
            (permutation v)⁻¹ ((permutation (down n k t _))⁻¹
            (⟨k+r, by omega⟩ : Fin (n+1)).castSucc)
          rw [hfix _ (by simp; omega), hfix _ (by simp; omega)]
          exact hd ⟨k+r, by omega⟩ (by simp; omega)
        subst t
        refine ⟨r+1, le_rfl, ?_⟩
        simpa [allTrue, allFalse, down] using congrArg (List.cons (⟨k+r, by omega⟩,false)) hm
      · refine ⟨t, by omega, ?_⟩
        have heq : r+1-t = (r-t)+1 := by omega
        simp only [heq, down, allTrue, List.map_cons, List.cons_append]
        have hi : (⟨k+t+(r-t), by omega⟩ : Fin (n+1)) = ⟨k+r, by omega⟩ := by
          apply Fin.ext; simp; omega
        rw [hi]
        exact congrArg (List.cons (⟨k+r, by omega⟩,true)) hm

/-- Triangles on the highest r+1 strands; recursion is by whole blocks. -/
def blocks (n : ℕ) : (r : ℕ) → r ≤ n+1 → Word n
  | 0, _ => []
  | r+1, h => down n (n-r) (r+1) (by omega) ++ blocks n r (by omega)

theorem down_values (n k r : ℕ) (h : k+r ≤ n+1) :
    (down n k r h).map Fin.val = (List.range r).map (fun j => k+r-1-j) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    simp only [down, List.map_cons, Fin.val_mk, ih, List.range_succ_eq_map,
      List.map_map, Function.comp_def, List.map_cons, Nat.sub_zero]
    congr 1
    apply List.map_congr_left
    intro j hj
    dsimp
    omega

theorem blocks_values (n r : ℕ) (h : r ≤ n+1) :
    (blocks n r h).map Fin.val = (coxeterWord (r+1)).reverse.map (fun j => n-j) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    simp only [blocks, List.map_append, down_values, ih, coxeterWord,
      List.reverse_append, List.reverse_reverse, List.map_append]
    congr 1
    apply List.map_congr_left
    intro j hj
    congr 1
    omega

theorem word_blocks (n : ℕ) : word n = blocks n (n+1) le_rfl := by
  apply (List.map_inj_right (fun a b => Fin.ext : ∀ a b : Fin (n+1), a.val = b.val → a = b)).mp
  rw [blocks_values]
  change ((wordIn n (n+2) le_rfl).reverse.map Fin.rev).map Fin.val = _
  have hv := wordIn_values n (n+2) le_rfl
  rw [List.map_map]
  calc
    _ = ((wordIn n (n+2) le_rfl).reverse.map Fin.val).map (fun j => n-j) := by
      simp only [List.map_map, Function.comp_def, Fin.val_rev, Nat.add_sub_cancel]
      apply List.map_congr_left
      intro j _
      omega
    _ = _ := by rw [List.map_reverse, hv]

/-- Exact ordinary permutation of a descending block, used only for covariance
    and reducedness; no invariance of the polynomial input is asserted. -/
theorem down_apply {n k r : ℕ} (h : k+r ≤ n+1) (x : Fin (n+2)) :
    (permutation (down n k r h) x).val =
      if x.val = k then k+r else if k < x.val ∧ x.val ≤ k+r then x.val-1 else x.val := by
  induction r with
  | zero => simp [down, permutation]; split_ifs <;> omega
  | succ r ih =>
    simp only [down, permutation, Equiv.Perm.mul_apply, simple, Equiv.swap_apply_def,
      Fin.ext_iff, Fin.coe_castSucc, Fin.val_succ, Fin.val_mk]
    have hp := ih (by omega)
    split_ifs at hp ⊢ <;> (try simp only [Fin.val_succ, Fin.val_mk, Fin.coe_castSucc]) <;> omega

theorem blocks_apply {n r : ℕ} (h : r ≤ n+1) (x : Fin (n+2)) :
    (permutation (blocks n r h) x).val =
      if x.val < n+1-r then x.val else n+1+(n+1-r)-x.val := by
  induction r with
  | zero => simp [blocks, permutation]; split_ifs <;> have := x.isLt <;> omega
  | succ r ih =>
    simp only [blocks, permutation_append, Equiv.Perm.mul_apply, down_apply]
    have hp := ih (by omega)
    have hx := x.isLt
    split_ifs at hp ⊢ <;> omega

theorem blocks_inverse {n r : ℕ} (h : r ≤ n+1) :
    (permutation (blocks n r h))⁻¹ = permutation (blocks n r h) := by
  apply inv_eq_of_mul_eq_one_right
  apply Equiv.ext
  intro x
  apply Fin.ext
  simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
  rw [blocks_apply, blocks_apply]
  have hx := x.isLt
  split_ifs <;> omega

theorem blocks_descents {n r : ℕ} (h : r ≤ n+1) (i : Fin (n+1))
    (hi : n-r < i.val) : Descent (permutation (blocks n r h))⁻¹ i := by
  rw [blocks_inverse]
  change (permutation (blocks n r h) i.succ).val <
    (permutation (blocks n r h) i.castSucc).val
  rw [blocks_apply, blocks_apply]
  simp only [Fin.val_succ, Fin.coe_castSucc]
  have hb := i.isLt
  split_ifs <;> omega

open SignedPermutation NonadjacentDivided in
/-- Actual signed covariance through a whole ordinary word. -/
theorem pair_word_covariance {n : ℕ} (w : Word n) (u v : Fin (n+2)) (huv : u ≠ v)
    (f : SkewPolynomial (n+2)) :
    dividedPair u v huv (skewAction (permutation w) f) =
      (-1 : ℤ)^w.length • skewAction (permutation w)
        (dividedPair ((permutation w)⁻¹ u) ((permutation w)⁻¹ v)
          ((permutation w)⁻¹.injective.ne huv) f) := by
  induction w generalizing u v with
  | nil => simp [permutation]
  | cons i w ih =>
    simp only [permutation, action_mul]
    change dividedPair u v huv (s i.castSucc i.succ (skewAction (permutation w) f)) = _
    rw [covariance _ _ _ _ _ (AllRankDivided.adjacent_ne i), ih]
    simp only [s, map_zsmul, List.length_cons, pow_succ, mul_neg, mul_one,
      neg_smul, map_neg, simple, mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply]

theorem down_append_low (n k r : ℕ) (h : k+(r+1) ≤ n+1) :
    down n k (r+1) h = down n (k+1) r (by omega) ++ [⟨k, by omega⟩] := by
  induction r with
  | zero => rfl
  | succ r ih =>
    simp only [down, List.cons_append]
    congr 1
    · apply Fin.ext; simp; omega
    · exact ih (by omega)

open IntervalAnnihilation AllRankDivided in
/-- Left-end recursion for the inherited ascending operator. -/
theorem ascending_front {n : ℕ} (a r : ℕ) (h : a+(r+1) ≤ n+1)
    (f : SkewPolynomial (n+2)) :
    divided (⟨a, by omega⟩ : Fin (n+1)) (ascending (a+1) r (by omega) f) =
      ascending a (r+1) h f := by
  induction r generalizing f with
  | zero => rfl
  | succ r ih =>
    simp only [ascending_succ]
    have hi : (⟨a+1+r, by omega⟩ : Fin (n+1)) = ⟨a+(r+1), by omega⟩ := by
      apply Fin.ext; simp; omega
    rw [hi]
    exact ih (by omega) _

/-- Inverse of a descending block, as a concrete permutation formula. -/
theorem down_inverse_apply {n k r : ℕ} (h : k+r ≤ n+1) (x : Fin (n+2)) :
    ((permutation (down n k r h))⁻¹ x).val =
      if x.val = k+r then k else if k ≤ x.val ∧ x.val < k+r then x.val+1 else x.val := by
  let y := (permutation (down n k r h))⁻¹ x
  have hy := down_apply h y
  have he : permutation (down n k r h) y = x := Equiv.Perm.apply_inv_self _ _
  rw [he] at hy
  change y.val = _
  split_ifs at hy ⊢ <;> omega

/-- The actual signed permutation left after the false part of a block. -/
def blockPermutation (n r t : ℕ) (hr : r+1 ≤ n+1) (ht : t ≤ r+1) : Perm n :=
  permutation (down n (n-r) t (by omega) ++ blocks n r (by omega))

theorem block_inverse_low (n r t : ℕ) (hr : r+1 ≤ n+1) (ht : t ≤ r) :
    (blockPermutation n r t hr (by omega))⁻¹ (⟨n-r+t, by omega⟩ : Fin (n+2)) =
      ⟨n-r, by omega⟩ := by
  apply Fin.ext
  simp only [blockPermutation, permutation_append, mul_inv_rev, Equiv.Perm.mul_apply,
    blocks_inverse, blocks_apply, down_inverse_apply, Fin.val_mk]
  split_ifs <;> omega

theorem block_inverse_high (n r t : ℕ) (hr : r+1 ≤ n+1) (ht : t ≤ r)
    (x : Fin (n+2)) (hx : n-r+t < x.val) :
    ((blockPermutation n r t hr (by omega))⁻¹ x).val = n+1+(n-r+1)-x.val := by
  simp only [blockPermutation, permutation_append, mul_inv_rev, Equiv.Perm.mul_apply,
    blocks_inverse, blocks_apply, down_inverse_apply]
  split_ifs <;> omega

open SignedPermutation IntervalAnnihilation in
/-- A descending divided run becomes an ascending run under actual reversing
    endpoint covariance. The hypotheses describe only a finite permutation. -/
theorem run_covariance {n : ℕ} (w : Word n) (j q c : ℕ)
    (hj : j+q ≤ n+1) (hc : j+q ≤ c) (hb : c-j ≤ n+1)
    (hp : ∀ x : Fin (n+2), j ≤ x.val → x.val ≤ j+q →
      ((permutation w)⁻¹ x).val = c-x.val)
    (f : SkewPolynomial (n+2)) :
    applyWord (down n j q hj) (skewAction (permutation w) f) =
      ((-1 : ℤ)^w.length)^q • skewAction (permutation w)
        (ascending (c-(j+q)) q (by omega) f) := by
  induction q generalizing f with
  | zero => simp [down, ascending]
  | succ q ih =>
    let i : Fin (n+1) := ⟨j+q, by omega⟩
    let z : Fin (n+1) := ⟨c-(j+q+1), by omega⟩
    have h₁ : (permutation w)⁻¹ i.castSucc = z.succ := by
      apply Fin.ext
      have hh := hp i.castSucc (by simp [i]) (by simp [i])
      simp only [Fin.coe_castSucc, Fin.val_succ] at *
      dsimp [i,z] at *
      omega
    have h₂ : (permutation w)⁻¹ i.succ = z.castSucc := by
      apply Fin.ext
      have hh := hp i.succ (by dsimp [i]; omega) (by dsimp [i]; omega)
      simp only [Fin.coe_castSucc, Fin.val_succ] at *
      dsimp [i,z] at *
      omega
    have cov (g : SkewPolynomial (n+2)) :
        AllRankDivided.divided i (skewAction (permutation w) g) =
          (-1 : ℤ)^w.length • skewAction (permutation w) (AllRankDivided.divided z g) := by
      rw [← NonadjacentDivided.adjacent i, pair_word_covariance]
      simp only [h₁, h₂]
      rw [NonadjacentDivided.symmetric, NonadjacentDivided.adjacent]
    change AllRankDivided.divided i (applyWord (down n j q _) (skewAction (permutation w) f)) = _
    rw [ih (by omega) (by omega) (fun x h₁ h₂ => hp x h₁ (by omega)), map_smul, cov,
      smul_smul, ← pow_succ]
    have hs : c-(j+q) = z.val+1 := by dsimp [z]; omega
    simp only [hs]
    rw [ascending_front]
    rfl

open SignedPermutation NonadjacentDivided IntervalAnnihilation in
/-- Exact block transport followed by the existing actual-kernel interval theorem.
    This is termwise annihilation, not cancellation in a total Leibniz sum. -/
theorem shaped_block_zero (n r t : ℕ) (hr : r+1 ≤ n+1) (ht : t ≤ r)
    (f : SkewPolynomial (n+2)) (hf : f ∈ OddSymmetricKernel.kernelSubring n) :
    applyWord (down n (n-r+t) (r+1-t) (by omega))
      (skewAction (blockPermutation n r t hr (by omega)) f) = 0 := by
  let k := n-r
  let j := k+t
  let u : Fin (n+2) := ⟨k, by dsimp [k]; omega⟩
  let v : Fin (n+2) := ⟨k+(r-t)+1, by dsimp [k]; omega⟩
  let i : Fin (n+1) := ⟨j, by dsimp [j,k]; omega⟩
  let w := down n k t (by dsimp [k]; omega) ++ blocks n r (by omega)
  have h₁ : (permutation w)⁻¹ i.castSucc = u := block_inverse_low n r t hr ht
  have h₂ : (permutation w)⁻¹ i.succ = v := by
    apply Fin.ext
    have hh := block_inverse_high n r t hr ht i.succ (by dsimp [i,j,k]; omega)
    change ((permutation w)⁻¹ i.succ).val = _ at hh
    dsimp [v, i, j, k] at *
    omega
  have huv : u ≠ v := by intro he; have := congrArg Fin.val he; dsimp [u,v] at this; omega
  have cov : AllRankDivided.divided i (skewAction (permutation w) f) =
      (-1 : ℤ)^w.length • skewAction (permutation w) (dividedPair u v huv f) := by
    rw [← adjacent i, pair_word_covariance]
    simp only [h₁, h₂]
  have hlen : r+1-t = (r-t)+1 := by omega
  change applyWord (down n j (r+1-t) _) (skewAction (permutation w) f) = 0
  simp only [hlen]
  rw [down_append_low, applyWord_append]
  change applyWord (down n (j+1) (r-t) _) (AllRankDivided.divided i
    (skewAction (permutation w) f)) = 0
  rw [cov, map_smul]
  have hc : (j+1)+(r-t) ≤ n+1+(k+1) := by dsimp [j,k]; omega
  have hb : n+1+(k+1)-(j+1) ≤ n+1 := by dsimp [j]; omega
  rw [run_covariance w (j+1) (r-t) (n+1+(k+1)) (by dsimp [j,k]; omega) hc hb]
  · have ha : n+1+(k+1)-(j+1+(r-t)) = k+1 := by dsimp [j,k]; omega
    simp only [ha]
    have hz := annihilate_length u (r-t) (by dsimp [u,k]; omega) f hf
    change ascending (k+1) (r-t) _ (dividedPair u v huv f) = 0 at hz
    rw [hz, map_zero, smul_zero, smul_zero]
  · intro x hx _
    exact block_inverse_high n r t hr ht x (by dsimp [j,k] at hx; omega)

@[simp] theorem hybrid_allTrue {n : ℕ} (w : Word n) (f : SkewPolynomial (n+2)) :
    hybrid (allTrue w) f = applyWord w f := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change AllRankDivided.divided i (hybrid (allTrue w) f) = _
    rw [ih, applyWord_cons]

/-- Whole-block induction selects the rightmost non-false block. Reducedness is
    inherited only by contiguous suffixes, never by arbitrary subwords. -/
theorem blocks_zero_or_allFalse (n r : ℕ) (h : r ≤ n+1) (m : Marked n)
    (he : erase m = blocks n r h) (hr : Reduced (omission m)) :
    (∀ f ∈ OddSymmetricKernel.kernelSubring n, hybrid m f = 0) ∨
      m = allFalse (blocks n r h) := by
  induction r generalizing m with
  | zero =>
    have hm : m = [] := by simpa [erase, blocks] using he
    exact Or.inr (by simp [hm, blocks, allFalse])
  | succ r ih =>
    change erase m = down n (n-r) (r+1) _ ++ blocks n r _ at he
    obtain ⟨a,b,hm,ha,hb⟩ := List.map_eq_append_iff.mp he
    subst m
    change erase a = down n (n-r) (r+1) _ at ha
    change erase b = blocks n r _ at hb
    rw [omission_append] at hr
    have hbr := reduced_suffix _ _ hr
    rcases ih (by omega) b hb hbr with hz | hfalse
    · apply Or.inl
      intro f hf
      rw [hybrid_append, hz f hf, hybrid_zero]
    · subst b
      rw [omission_allFalse] at hr
      obtain ⟨t,ht,hshape⟩ := block_shape (by omega) a (blocks n r (by omega)) ha
        (fun i hi => blocks_descents (by omega) i hi) hr
      by_cases hall : t = r+1
      · subst t
        apply Or.inr
        simp only [Nat.sub_self, down, allTrue, List.map_nil, List.nil_append] at hshape
        rw [hshape]
        simp [blocks, allFalse, down]
      · apply Or.inl
        intro f hf
        rw [hybrid_append, hshape, hybrid_append, hybrid_allTrue,
          hybrid_allFalse, hybrid_allFalse, ← SignedPermutation.action_mul,
          ← permutation_append]
        exact shaped_block_zero n r t h (by omega) f hf

/-- EKL1111.1320v1 Lemma 2.18 for exactly the printed descending-block word.
    No OWL or interval-factorization premise remains on this export. -/
theorem trichotomy (n : ℕ) (m : Marked n) (he : erase m = word n) : Trichotomy m := by
  by_cases hr : Reduced (omission m)
  · rcases blocks_zero_or_allFalse n (n+1) le_rfl m (by rwa [← word_blocks]) hr with hz | ha
    · exact Or.inl hz
    · apply Or.inr (Or.inl ((all_false_iff m).mpr ?_))
      simpa only [he, word_blocks] using ha
  · exact Or.inr (Or.inr hr)

/-- Explicit termwise vanishing, with the sole exceptional marking excluded. -/
theorem nonexceptional_term_zero (n : ℕ) (m : Marked n) (he : erase m = word n)
    (hne : m ≠ allFalse (word n)) (f g : SkewPolynomial (n+2))
    (hf : f ∈ OddSymmetricKernel.kernelSubring n) :
    hybrid m f * applyWord (omission m) g = 0 := by
  apply term_zero_of_trichotomy m (trichotomy n m he) _ f g hf
  simpa only [he] using hne

/-- All-false-only generalized Leibniz consumer, for arbitrary kernel f and
    arbitrary polynomial g, deduced from termwise OWL and nonreduced zero. -/
theorem left_kernel (n : ℕ) (f g : SkewPolynomial (n+2))
    (hf : f ∈ OddSymmetricKernel.kernelSubring n) :
    applyWord (word n) (f*g) =
      SignedPermutation.skewAction (LongestElementary.longest (n+2)) f * applyWord (word n) g := by
  exact longest_left_kernel_of_trichotomy (word n) (word_permutation n)
    (fun m hm => trichotomy n m ((mem_markings m (word n)).mp hm)) f g hf

end
end OddMath.Frontier.OmissionCanonical
