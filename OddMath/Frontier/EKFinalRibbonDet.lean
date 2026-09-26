import OddMath.Frontier.EKFinalDetCert
import OddMath.Frontier.EKFinalNSym
import Mathlib.Combinatorics.Colex

/-!
# The Gram determinant through the ribbon basis: certified evaluation

Source: Ellis–Khovanov, arXiv:1107.5610v2, §2.4 (2.33) and §5.2, pp. 39–40.

By (2.33) the Gram matrix of (2.1) in the basis `h̃_α` of (2.31) has entries
`(h̃_β, h̃_α) = Σ_{σ ∈ S_n, C(σ) = α, C(σ⁻¹) = β} q^{ℓ(σ)}`, and its determinant equals the
Gram determinant in the basis `h_α` (`EKRest.det_gramH_eq`).  This file evaluates that
matrix at an integer `q = t` by a single pass over the permutations of `{0, …, n-1}`, with
compositions indexed by the binary masks of their cut sets, and relates the result to
`EKGeneralQNondeg.gram`.

* `gramHt_eval`: entries of the `h̃`-Gram matrix at `q = t` as sums over permutations;
* `cutEquiv`: `Fin 2^{n-1} ≃ Cut n` by binary masks;
* `ribbonLL`: the list matrix built from all permutations; `ribbonLL_spec`;
* `det_gram_eq_ribbon`: `det G_n(t) = det (ribbonLL n t)`;
* `gram_det_eq_of_ribbonCheck`: the certified identity `det G_n(q) = Q(q)` in `ℤ[q]`.
-/

noncomputable section
open scoped BigOperators
open Polynomial

namespace OddMath.Frontier.EKFinal
open EKGeneralQ EKRest

/-! ## Permutations as lists -/

/-- The list `[σ 0, σ 1, …]`. -/
def pl {n : ℕ} (σ : Equiv.Perm (Fin n)) : List ℕ := List.ofFn fun i => (σ i : ℕ)

theorem pl_length {n : ℕ} (σ : Equiv.Perm (Fin n)) : (pl σ).length = n := by simp [pl]

theorem pl_getD {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) : (pl σ).getD i 0 = σ i := by
  simp [pl, List.getD_eq_getElem?_getD]

theorem pl_nodup {n : ℕ} (σ : Equiv.Perm (Fin n)) : (pl σ).Nodup := by
  rw [pl, List.nodup_ofFn]
  intro a b h
  exact σ.injective (Fin.ext h)

theorem mem_pl {n : ℕ} (σ : Equiv.Perm (Fin n)) (v : ℕ) : v ∈ pl σ ↔ v < n := by
  rw [pl, List.mem_ofFn]
  constructor
  · rintro ⟨i, rfl⟩; exact (σ i).isLt
  · intro hv; exact ⟨σ.symm ⟨v, hv⟩, by simp⟩

theorem pl_mem_perms {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    pl σ ∈ List.permutations' (List.range n) := by
  rw [List.mem_permutations']
  rw [List.perm_ext_iff_of_nodup (pl_nodup σ) (List.nodup_range)]
  intro v
  rw [mem_pl, List.mem_range]

theorem pl_injective {n : ℕ} : Function.Injective (pl (n := n)) := by
  intro σ τ h
  ext i
  have := congrArg (fun l => l.getD i 0) h
  simp only [pl_getD] at this
  exact this

theorem perms_nodup (n : ℕ) : (List.permutations' (List.range n)).Nodup :=
  (List.permutations_perm_permutations' _).nodup_iff.mp (List.nodup_permutations _ (List.nodup_range))

theorem exists_pl {n : ℕ} {p : List ℕ} (hp : p ∈ List.permutations' (List.range n)) :
    ∃ σ : Equiv.Perm (Fin n), pl σ = p := by
  rw [List.mem_permutations'] at hp
  have hlen : p.length = n := by rw [hp.length_eq, List.length_range]
  have hmem : ∀ i : Fin n, p[i.val]'(by omega) < n := by
    intro i
    have : p[i.val]'(by omega) ∈ List.range n := hp.subset (List.getElem_mem _)
    simpa using this
  let f : Fin n → Fin n := fun i => ⟨p[i.val]'(by omega), hmem i⟩
  have hf : Function.Injective f := by
    intro a b h
    have h' : p[a.val]'(by omega) = p[b.val]'(by omega) := congrArg Fin.val h
    have hnd : p.Nodup := hp.nodup_iff.mpr (List.nodup_range)
    exact Fin.ext ((List.Nodup.getElem_inj_iff hnd).mp h')
  refine ⟨Equiv.ofBijective f hf.bijective_of_finite, ?_⟩
  apply List.ext_getElem
  · rw [pl_length, hlen]
  · intro i h1 h2
    simp [pl, f]

/-- Sums over `S_n` as sums over the list of permutations of `[0, …, n-1]`. -/
theorem sum_perm_eq_list {n : ℕ} {M : Type*} [AddCommMonoid M] (F : List ℕ → M) :
    ∑ σ : Equiv.Perm (Fin n), F (pl σ) = ((List.permutations' (List.range n)).map F).sum := by
  rw [← List.sum_toFinset _ (perms_nodup n)]
  apply Finset.sum_bij (fun σ _ => pl σ)
  · intro σ _; exact List.mem_toFinset.mpr (pl_mem_perms σ)
  · intro a _ b _ h; exact pl_injective h
  · intro p hp
    obtain ⟨σ, rfl⟩ := exists_pl (List.mem_toFinset.mp hp)
    exact ⟨σ, Finset.mem_univ _, rfl⟩
  · intro σ _; rfl

/-! ## Statistics of permutation lists -/

/-- Descent mask: bit `k` is set iff `p[k+1] < p[k]`. -/
def desL (p : List ℕ) : ℕ :=
  ((List.range (p.length - 1)).map fun k => if p.getD (k + 1) 0 < p.getD k 0 then 2 ^ k else 0).sum

/-- The inverse of a permutation list: the position of each value. -/
def posL (p : List ℕ) : List ℕ := (List.range p.length).map fun v => p.idxOf v

/-- Number of inversions. -/
def invL (p : List ℕ) : ℕ :=
  ((List.range p.length).map fun a => ((List.range p.length).map fun b =>
    if a < b ∧ p.getD b 0 < p.getD a 0 then 1 else 0).sum).sum

/-- The binary mask `Σ_{s ∈ S} 2^{s-1}` of a cut set. -/
def mask {n : ℕ} (S : Finset (Fin n)) : ℕ := ∑ s ∈ S, 2 ^ (s.val - 1)

theorem list_sum_range_fin {M : Type*} [AddCommMonoid M] (m : ℕ) (f : ℕ → M) :
    ((List.range m).map f).sum = ∑ k : Fin m, f k := by
  rw [EKAppendixData.list_sum_range, Fin.sum_univ_eq_sum_range]

theorem desL_pl {n : ℕ} (σ : Equiv.Perm (Fin n)) : desL (pl σ) = mask (Des σ) := by
  rw [desL, mask, Des, Finset.sum_filter, pl_length, list_sum_range_fin]
  cases n with
  | zero => simp
  | succ m =>
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, lt_irrefl, false_and, if_false, zero_add, Nat.add_sub_cancel]
    apply Finset.sum_congr rfl
    intro k _
    have h1 : (pl σ).getD (k.val + 1) 0 = σ k.succ := pl_getD σ k.succ
    have h2 : (pl σ).getD k.val 0 = σ k.castSucc := pl_getD σ k.castSucc
    have hp : pred' k.succ = k.castSucc := by ext; simp [pred']
    rw [h1, h2, hp]
    simp only [Fin.val_succ, Nat.succ_pos', true_and, Nat.add_sub_cancel, Fin.lt_def]

theorem posL_pl {n : ℕ} (σ : Equiv.Perm (Fin n)) : posL (pl σ) = pl σ⁻¹ := by
  apply List.ext_getElem
  · simp [posL, pl_length]
  · intro v h1 h2
    simp only [posL, List.getElem_map, List.getElem_range]
    have hv : v < n := by simpa [posL, pl_length] using h1
    have hpos : (σ⁻¹ ⟨v, hv⟩ : ℕ) < (pl σ).length := by rw [pl_length]; exact (σ⁻¹ ⟨v, hv⟩).isLt
    have hval : (pl σ)[(σ⁻¹ ⟨v, hv⟩ : ℕ)] = v := by simp [pl]
    have := List.idxOf_getElem (pl_nodup σ) _ hpos
    rw [hval] at this
    rw [this]
    simp [pl]

theorem invL_pl {n : ℕ} (σ : Equiv.Perm (Fin n)) : invL (pl σ) = EKPlatformBijection.inversions σ := by
  rw [invL, EKPlatformBijection.inversions, pl_length, list_sum_range_fin]
  apply Finset.sum_congr rfl
  intro a _
  rw [list_sum_range_fin]
  apply Finset.sum_congr rfl
  intro b _
  rw [pl_getD, pl_getD]
  simp only [Fin.lt_def]

/-! ## Cut sets and binary masks -/

/-- The cut set with binary mask `i`. -/
def cutOfMask (n i : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun s => 0 < s.val ∧ s.val - 1 ∈ i.bitIndices

theorem cutOfMask_pos (n i : ℕ) : ∀ s ∈ cutOfMask n i, 0 < s.val := by
  intro s hs
  simp only [cutOfMask, Finset.mem_filter] at hs
  exact hs.2.1

theorem sum_range_two_pow (m : ℕ) : ∑ b ∈ Finset.range m, 2 ^ b + 1 = 2 ^ m := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, add_right_comm, ih]; ring

theorem geom_two_lt (m : ℕ) (T : Finset ℕ) (hT : ∀ b ∈ T, b < m) : ∑ b ∈ T, 2 ^ b < 2 ^ m := by
  have h1 : ∑ b ∈ T, 2 ^ b ≤ ∑ b ∈ Finset.range m, 2 ^ b :=
    Finset.sum_le_sum_of_subset (fun b hb => Finset.mem_range.mpr (hT b hb))
  have h2 := sum_range_two_pow m
  omega

theorem mask_eq_image {n : ℕ} (S : Finset (Fin n)) (hS : ∀ s ∈ S, 0 < s.val) :
    mask S = ∑ b ∈ S.image (fun s => s.val - 1), 2 ^ b := by
  rw [mask, Finset.sum_image]
  intro s hs t ht h
  have := hS s hs
  have := hS t ht
  exact Fin.ext (by omega)

theorem mask_lt {n : ℕ} (S : Finset (Fin n)) (hS : ∀ s ∈ S, 0 < s.val) : mask S < 2 ^ (n - 1) := by
  rw [mask_eq_image S hS]
  apply geom_two_lt
  intro b hb
  simp only [Finset.mem_image] at hb
  obtain ⟨s, hs, rfl⟩ := hb
  have := hS s hs
  have := s.isLt
  omega

theorem cutOfMask_mask {n : ℕ} (S : Finset (Fin n)) (hS : ∀ s ∈ S, 0 < s.val) :
    cutOfMask n (mask S) = S := by
  ext s
  rw [cutOfMask, Finset.mem_filter, mask_eq_image S hS]
  have hbits : ∀ b, b ∈ (∑ b ∈ S.image (fun s : Fin n => s.val - 1), 2 ^ b).bitIndices ↔
      b ∈ S.image (fun s : Fin n => s.val - 1) := by
    intro b
    rw [← List.mem_toFinset, Finset.toFinset_bitIndices_twoPowSum]
  rw [hbits]
  simp only [Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · rintro ⟨hs0, t, ht, hts⟩
    have := hS t ht
    have : t = s := Fin.ext (by omega)
    rwa [← this]
  · intro hs
    exact ⟨hS s hs, s, hs, rfl⟩

theorem mask_cutOfMask {n i : ℕ} (hi : i < 2 ^ (n - 1)) : mask (cutOfMask n i) = i := by
  cases n with
  | zero =>
    have : i = 0 := by simpa using hi
    subst this
    simp [mask, cutOfMask]
  | succ m =>
  have hbnd : ∀ b ∈ i.bitIndices, b + 1 < m + 1 := by
    intro b hb
    have h1 := Nat.two_pow_le_of_mem_bitIndices hb
    have h2 : 2 ^ b < 2 ^ (m + 1 - 1) := lt_of_le_of_lt h1 hi
    have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp h2
    omega
  rw [mask]
  conv_rhs => rw [← Finset.twoPowSum_toFinset_bitIndices i]
  apply Finset.sum_nbij' (fun s => s.val - 1)
    (fun b => if h : b + 1 < m + 1 then (⟨b + 1, h⟩ : Fin (m + 1)) else 0)
  · intro s hs
    simp only [cutOfMask, Finset.mem_filter, Finset.mem_coe] at hs
    simpa using hs.2.2
  · intro b hb
    simp only [Finset.mem_coe, List.mem_toFinset] at hb
    simp only [cutOfMask, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [dif_pos (hbnd _ hb)]
    simpa using hb
  · intro s hs
    simp only [cutOfMask, Finset.mem_filter, Finset.mem_coe] at hs
    have h0 := hs.2.1
    have hlt : s.val - 1 + 1 < m + 1 := by have := s.isLt; omega
    rw [dif_pos hlt]
    ext; simp; omega
  · intro b hb
    simp only [Finset.mem_coe, List.mem_toFinset] at hb
    rw [dif_pos (hbnd _ hb)]
    simp
  · intro s _; rfl

/-- Compositions of `n` (cut sets) indexed by binary masks. -/
def cutEquiv (n : ℕ) : Fin (2 ^ (n - 1)) ≃ Cut n where
  toFun i := ⟨cutOfMask n i, cutOfMask_pos n i⟩
  invFun S := ⟨mask S.1, mask_lt S.1 S.2⟩
  left_inv i := Fin.ext (mask_cutOfMask i.isLt)
  right_inv S := Subtype.ext (cutOfMask_mask S.1 S.2)

theorem mask_eq_iff {n : ℕ} (S : Finset (Fin n)) (hS : ∀ s ∈ S, 0 < s.val) (i : Fin (2 ^ (n - 1))) :
    mask S = i ↔ S = (cutEquiv n i).1 := by
  constructor
  · intro h
    show S = cutOfMask n i
    rw [← h, cutOfMask_mask S hS]
  · intro h
    rw [h]
    exact mask_cutOfMask i.isLt

theorem des_pos {n : ℕ} (σ : Equiv.Perm (Fin n)) : ∀ s ∈ Des σ, 0 < s.val := by
  intro s hs
  simp only [Des, Finset.mem_filter] at hs
  exact hs.2.1

/-! ## The ribbon Gram matrix at `q = t` -/

theorem gramHt_perm (k : Type*) [CommRing k] (q : k) {n : ℕ} (S R : Cut n) :
    gramHt q n S R = ∑ σ : Equiv.Perm (Fin n),
      if Des σ = R.1 ∧ Des σ⁻¹ = S.1 then q ^ EKPlatformBijection.inversions σ else 0 := by
  classical
  rw [gramHt, eq_2_33]

theorem gramHt_NN {n : ℕ} (S R : Cut n) : NN (gramHt (X : ℤ[X]) n S R) := by
  classical
  rw [gramHt_perm]
  intro e
  rw [finset_sum_coeff]
  apply Finset.sum_nonneg
  intro σ _
  split_ifs
  · rw [coeff_X_pow]; split_ifs <;> norm_num
  · simp

theorem eval_gramHt (t : ℤ) {n : ℕ} (S R : Cut n) :
    (gramHt (X : ℤ[X]) n S R).eval t = gramHt t n S R := by
  classical
  rw [gramHt_perm, gramHt_perm, eval_finset_sum]
  apply Finset.sum_congr rfl
  intro σ _
  split_ifs <;> simp

/-- `2^{K e}`, computed by a shift. -/
def tpow (K e : ℕ) : ℤ := ((1 <<< (K * e) : ℕ) : ℤ)

theorem tpow_eq (K e : ℕ) : tpow K e = ((2 : ℤ) ^ K) ^ e := by
  rw [tpow, Nat.shiftLeft_eq, one_mul, ← pow_mul]
  push_cast
  rfl

/-- Add `x` at position `j`. -/
def addAt : ℕ → ℤ → List ℤ → List ℤ
  | _, _, [] => []
  | 0, x, a :: l => (a + x) :: l
  | j + 1, x, a :: l => a :: addAt j x l

/-- Add `x` at entry `(i, j)`. -/
def addAt2 : ℕ → ℕ → ℤ → List (List ℤ) → List (List ℤ)
  | _, _, _, [] => []
  | 0, j, x, r :: M => addAt j x r :: M
  | i + 1, j, x, r :: M => r :: addAt2 i j x M

theorem length_addAt (j : ℕ) (x : ℤ) (l : List ℤ) : (addAt j x l).length = l.length := by
  induction l generalizing j with
  | nil => cases j <;> rfl
  | cons a l ih => cases j <;> simp [addAt, ih]

theorem getD_addAt (j : ℕ) (x : ℤ) (l : List ℤ) (hj : j < l.length) (b : ℕ) :
    (addAt j x l).getD b 0 = l.getD b 0 + if j = b then x else 0 := by
  induction l generalizing j b with
  | nil => simp at hj
  | cons a l ih =>
    cases j with
    | zero => cases b <;> simp [addAt]
    | succ j =>
      cases b with
      | zero => simp [addAt]
      | succ b =>
        simp only [addAt, List.getD_cons_succ]
        rw [ih j (by simpa using hj) b]
        simp

theorem length_addAt2 (i j : ℕ) (x : ℤ) (M : List (List ℤ)) : (addAt2 i j x M).length = M.length := by
  induction M generalizing i with
  | nil => cases i <;> rfl
  | cons r M ih => cases i <;> simp [addAt2, ih]

theorem rows_addAt2 (i j : ℕ) (x : ℤ) (M : List (List ℤ)) (N : ℕ) (hM : ∀ r ∈ M, r.length = N) :
    ∀ r ∈ addAt2 i j x M, r.length = N := by
  induction M generalizing i with
  | nil => cases i <;> simp [addAt2]
  | cons r M ih =>
    cases i with
    | zero =>
      intro r' hr'
      simp only [addAt2, List.mem_cons] at hr'
      rcases hr' with rfl | hr'
      · rw [length_addAt]; exact hM r (by simp)
      · exact hM r' (by simp [hr'])
    | succ i =>
      intro r' hr'
      simp only [addAt2, List.mem_cons] at hr'
      rcases hr' with rfl | hr'
      · exact hM _ (by simp)
      · exact ih i (fun r'' h'' => hM r'' (by simp [h''])) r' hr'

theorem getE_addAt2 (i j : ℕ) (x : ℤ) (M : List (List ℤ)) (N : ℕ) (hM : ∀ r ∈ M, r.length = N)
    (hi : i < M.length) (hj : j < N) (a b : ℕ) :
    getE (addAt2 i j x M) a b = getE M a b + if i = a ∧ j = b then x else 0 := by
  induction M generalizing i a with
  | nil => simp at hi
  | cons r M ih =>
    cases i with
    | zero =>
      cases a with
      | zero =>
        simp only [addAt2, getE, List.getD_cons_zero]
        rw [getD_addAt j x r (by rw [hM r (by simp)]; exact hj)]
        simp
      | succ a => simp [addAt2, getE]
    | succ i =>
      cases a with
      | zero => simp [addAt2, getE]
      | succ a =>
        simp only [addAt2, getE, List.getD_cons_succ] at ih ⊢
        rw [ih i (fun r' h' => hM r' (by simp [h'])) (by simpa using hi) a]
        simp

/-- The zero `N × N` list matrix. -/
def zeroLL (N : ℕ) : List (List ℤ) := List.replicate N (List.replicate N 0)

theorem getE_zeroLL (N a b : ℕ) : getE (zeroLL N) a b = 0 := by
  simp only [getE, zeroLL, List.getD_eq_getElem?_getD, List.getElem?_replicate]
  by_cases ha : a < N
  · rw [if_pos ha]
    simp only [Option.getD_some, List.getElem?_replicate]
    split_ifs <;> rfl
  · rw [if_neg ha]; rfl

theorem getE_foldl (N : ℕ) (r c : List ℕ → ℕ) (w : List ℕ → ℤ) (ps : List (List ℕ))
    (hps : ∀ p ∈ ps, r p < N ∧ c p < N) (M : List (List ℤ)) (hMl : M.length = N)
    (hM : ∀ row ∈ M, row.length = N) (a b : ℕ) :
    getE (ps.foldl (fun M p => addAt2 (r p) (c p) (w p) M) M) a b =
      getE M a b + (ps.map fun p => if r p = a ∧ c p = b then w p else 0).sum := by
  induction ps generalizing M with
  | nil => simp
  | cons p ps ih =>
    rw [List.foldl_cons, ih (fun p' h' => hps p' (by simp [h'])) _
      (by rw [length_addAt2, hMl]) (rows_addAt2 _ _ _ M N hM),
      getE_addAt2 _ _ _ M N hM (by rw [hMl]; exact (hps p (by simp)).1) (hps p (by simp)).2]
    simp only [List.map_cons, List.sum_cons]
    ring

/-- **The ribbon Gram matrix at `q = 2^K`**, built from all permutations: entry
`(mask S, mask R)` is `Σ_{Des σ⁻¹ = S, Des σ = R} (2^K)^{ℓ(σ)}`. -/
def ribbonLL (n K : ℕ) : List (List ℤ) :=
  (List.permutations' (List.range n)).foldl
    (fun M p => addAt2 (desL (posL p)) (desL p) (tpow K (invL p)) M) (zeroLL (2 ^ (n - 1)))

theorem desL_perm_lt {n : ℕ} {p : List ℕ} (hp : p ∈ List.permutations' (List.range n)) :
    desL p < 2 ^ (n - 1) ∧ desL (posL p) < 2 ^ (n - 1) := by
  obtain ⟨σ, rfl⟩ := exists_pl hp
  rw [posL_pl, desL_pl, desL_pl]
  exact ⟨mask_lt _ (des_pos σ), mask_lt _ (des_pos σ⁻¹)⟩

theorem ribbonLL_spec (n K : ℕ) (a b : Fin (2 ^ (n - 1))) :
    getE (ribbonLL n K) a b = gramHt ((2 : ℤ) ^ K) n (cutEquiv n a) (cutEquiv n b) := by
  rw [ribbonLL, getE_foldl (2 ^ (n - 1)) _ _ _ _
    (fun p hp => ⟨(desL_perm_lt hp).2, (desL_perm_lt hp).1⟩) _ (by simp [zeroLL])
    (fun r hr => by simp [zeroLL] at hr; rw [hr]; simp), getE_zeroLL, zero_add,
    ← sum_perm_eq_list, gramHt_perm]
  apply Finset.sum_congr rfl
  intro σ _
  rw [posL_pl, desL_pl, desL_pl, invL_pl, tpow_eq]
  have e1 := mask_eq_iff _ (des_pos σ⁻¹) a
  have e2 := mask_eq_iff _ (des_pos σ) b
  by_cases h : Des σ = ((cutEquiv n) b).1 ∧ Des σ⁻¹ = ((cutEquiv n) a).1
  · rw [if_pos h, if_pos ⟨e1.mpr h.2, e2.mpr h.1⟩]
  · rw [if_neg h, if_neg (fun h' => h ⟨e2.mp h'.2, e1.mp h'.1⟩)]

theorem det_gramHt_ribbon (n K : ℕ) :
    (gramHt ((2 : ℤ) ^ K) n).det = (ofLL (2 ^ (n - 1)) (ribbonLL n K)).det := by
  rw [← Matrix.det_submatrix_equiv_self (cutEquiv n)]
  congr 1
  ext a b
  rw [Matrix.submatrix_apply, ofLL, Matrix.of_apply, ribbonLL_spec]

/-! ## From cut sets to compositions -/

/-- The composition with cut set `S`. -/
def compOfCut {n : ℕ} (hn : 0 < n) (S : Cut n) : Composition n where
  blocks := List.ofFn (EKRest.parts S.1)
  blocks_pos := by
    intro i hi
    rw [List.mem_ofFn] at hi
    obtain ⟨j, rfl⟩ := hi
    exact parts_pos hn S.1 j
  blocks_sum := by rw [List.sum_ofFn, EKRest.parts_sum]

theorem compOfCut_bijective {n : ℕ} (hn : 0 < n) : Function.Bijective (compOfCut hn) := by
  have hinj : Function.Injective (compOfCut hn) := by
    intro S T h
    have h' : List.ofFn (EKRest.parts S.1) = List.ofFn (EKRest.parts T.1) :=
      congrArg Composition.blocks h
    exact Subtype.ext (cut_eq_of_parts S.1 T.1 S.2 T.2 h')
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, ?_⟩
  rw [composition_card, ← Fintype.card_congr (cutEquiv n), Fintype.card_fin]

theorem det_gram_eq_gramHt {k : Type*} [CommRing k] (q : k) {n : ℕ} (hn : 0 < n) :
    (gram q n).det = (gramHt q n).det := by
  rw [← det_gramH_eq, ← Matrix.det_submatrix_equiv_self
    (Equiv.ofBijective _ (compOfCut_bijective hn))]
  congr 1

/-! ## The certified identity -/

/-- `∏_j Σ_i M_{ij}`. -/
def colBound (N : ℕ) (M : List (List ℤ)) : ℤ :=
  ((List.range N).map fun j => ((List.range N).map fun i => getE M i j).sum).prod

/-- The combined check for degree `n` against `Q = prodPow fs`, at `q = 2^K`. -/
def ribbonCheck (n K : ℕ) (fs : List (List ℤ × ℕ)) : Bool :=
  certCheck (2 ^ (n - 1)) (ribbonLL n K) (bareissL (2 ^ (n - 1)) (ribbonLL n K))
      (prodPowEval (2 ^ K) fs) &&
    decide (2 * (colBound (2 ^ (n - 1)) (ribbonLL n 0) + prodPowEval 1 (absFs fs)) < 2 ^ K)

theorem abs_coeff_gram_det_le_ribbon {n : ℕ} (hn : 0 < n) (e : ℕ) :
    |(gram (X : ℤ[X]) n).det.coeff e| ≤ colBound (2 ^ (n - 1)) (ribbonLL n 0) := by
  rw [det_gram_eq_gramHt _ hn]
  refine le_trans (abs_coeff_det_le _ (fun S R => gramHt_NN S R) e) (le_of_eq ?_)
  simp only [eval_gramHt]
  rw [colBound, prod_range_eq, ← (cutEquiv n).prod_comp]
  apply Finset.prod_congr rfl
  intro b _
  rw [list_sum_range_fin, ← (cutEquiv n).sum_comp]
  apply Finset.sum_congr rfl
  intro a _
  rw [ribbonLL_spec, pow_zero]

/-- **Certified Gram determinant** via the ribbon basis. -/
theorem gram_det_eq_of_ribbonCheck {n : ℕ} (hn : 0 < n) (K : ℕ) (fs : List (List ℤ × ℕ))
    (h : ribbonCheck n K fs = true) : (gram (X : ℤ[X]) n).det = prodPow fs := by
  simp only [ribbonCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hc, hb⟩ := h
  apply eq_of_eval_of_bound _ _ (2 ^ K) _ (prodPowEval 1 (absFs fs))
    (abs_coeff_gram_det_le_ribbon hn)
  · intro e
    have := (maj_prodPow fs).le_eval_one e
    rwa [eval_prodPow] at this
  · exact hb
  · rw [eval_gram_det, det_gram_eq_gramHt _ hn, det_gramHt_ribbon, det_of_cert _ _ _ _ hc,
      eval_prodPow]

end OddMath.Frontier.EKFinal
