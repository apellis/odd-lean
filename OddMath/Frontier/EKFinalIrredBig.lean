import OddMath.Frontier.EKFinalIrred

/-!
# EK §5.2: irreducibility of the printed polynomials of degrees 50 and 102

Source: Ellis–Khovanov, arXiv:1107.5610v2, §5.2, p. 40.

The printed degree-50 polynomial (degree 6 of the list) is irreducible modulo `269`, and the
printed degree-102 polynomial (degree 7) is irreducible modulo `89`.  As in `EKFinalIrred`, this
is certified by `irreducible_of_frob`: `α^{p^d} - α` is a unit in `𝔽_p[X]/(f)` for
`1 ≤ d ≤ n/2`, with explicit inverses.  The arithmetic in `𝔽_p[X]/(f)` packs a residue
`Σ cᵢ αⁱ` into the natural number `Σ cᵢ Bⁱ`, `B = 2^48`; one product of residues is one product
of natural numbers followed by a reduction through the table of `α^{n+i}`, `i < n - 1`.
Correctness of the packing is proved here (`mulmodK_spec`): all intermediate coefficients are
below `B`, so no carries occur.

* `f50_irreducible`, `f102_irreducible`: irreducible over `ℚ`;
* `f50_no_root_of_unity`, `f102_no_root_of_unity`: no complex root is a root of unity
  (EK: "(not a root of unity)"), since the values at `1` are `924` and `100320`, which are
  neither `0`, `1`, nor prime.
-/

noncomputable section
open Polynomial

namespace OddMath.Frontier.EKFinal

/-! ## Packing residues into natural numbers -/

section Packed

/-- The packing base. -/
def Bw : ℕ := 2 ^ 48

def packN (l : List ℕ) : ℕ := l.foldr (fun c acc => c + Bw * acc) 0

def unpackN : ℕ → ℕ → List ℕ
  | 0, _ => []
  | k + 1, m => (m % Bw) :: unpackN k (m / Bw)

/-- `Σ cᵢ Xⁱ` in `ℕ[X]`. -/
def ofListN : List ℕ → ℕ[X]
  | [] => 0
  | c :: l => C c + X * ofListN l

theorem packN_eq (l : List ℕ) : packN l = (ofListN l).eval Bw := by
  induction l with
  | nil => simp [packN, ofListN]
  | cons c l ih =>
    simp only [packN, List.foldr_cons, ofListN, eval_add, eval_C, eval_mul, eval_X] at ih ⊢
    rw [ih]

theorem coeff_ofListN (l : List ℕ) (i : ℕ) : (ofListN l).coeff i = l.getD i 0 := by
  induction l generalizing i with
  | nil => simp [ofListN]
  | cons c l ih =>
    cases i with
    | zero => simp [ofListN]
    | succ i => rw [ofListN, coeff_add, coeff_C, coeff_X_mul, ih]; simp

theorem evN_eq_aeval {R : Type*} [CommRing R] (α : R) (l : List ℕ) :
    evN α l = aeval α (ofListN l) := by
  induction l with
  | nil => simp [evN, ofListN]
  | cons c l ih => simp [evN, ofListN, ih]

theorem unpackN_eval (P : ℕ[X]) (K : ℕ) (hc : ∀ i, P.coeff i < Bw)
    (hd : ∀ i, K ≤ i → P.coeff i = 0) : unpackN K (P.eval Bw) = (List.range K).map P.coeff := by
  induction K generalizing P with
  | zero => rfl
  | succ K ih =>
    have hX := X_mul_divX_add P
    have he : P.eval Bw = P.coeff 0 + Bw * (divX P).eval Bw := by
      conv_lhs => rw [← hX]
      simp only [eval_add, eval_mul, eval_X, eval_C]
      ring
    have hB : 0 < Bw := by unfold Bw; positivity
    have hmod : P.eval Bw % Bw = P.coeff 0 := by
      rw [he, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hc 0)]
    have hdiv : P.eval Bw / Bw = (divX P).eval Bw := by
      rw [he, Nat.add_mul_div_left _ _ hB, Nat.div_eq_of_lt (hc 0), zero_add]
    rw [unpackN, hmod, hdiv, ih (divX P) (fun i => by rw [coeff_divX]; exact hc _)
      (fun i hi => by rw [coeff_divX]; exact hd _ (by omega)), List.range_succ_eq_map]
    simp [coeff_divX, Function.comp_def]

theorem evN_range {R : Type*} [CommRing R] (α : R) (f : ℕ → ℕ) (K : ℕ) :
    evN α ((List.range K).map f) = ∑ k ∈ Finset.range K, (f k : R) * α ^ k := by
  induction K with
  | zero => simp [evN]
  | succ K ih =>
    rw [List.range_succ, List.map_append, List.map_singleton, evN_append, ih,
      Finset.sum_range_succ, List.length_map, List.length_range]

theorem aeval_eq_sum_of_coeff {R : Type*} [CommRing R] (α : R) (P : ℕ[X]) (K : ℕ)
    (hd : ∀ i, K ≤ i → P.coeff i = 0) :
    aeval α P = ∑ k ∈ Finset.range K, (P.coeff k : R) * α ^ k := by
  rw [aeval_eq_sum_range' (n := max K (P.natDegree + 1)) (by omega)]
  simp only [nsmul_eq_mul]
  rw [← Finset.sum_range_add_sum_Ico _ (le_max_left K _)]
  rw [Finset.sum_eq_zero (s := Finset.Ico K _) (fun i hi => by
    rw [hd i (Finset.mem_Ico.mp hi).1]; simp), add_zero]

end Packed

/-! ## Products of packed residues -/

section MulK

/-- `Σ hᵢ Pᵢ`. -/
def dotPack : List ℕ → List ℕ → ℕ
  | h :: hs, P :: Ps => h * P + dotPack hs Ps
  | _, _ => 0

/-- Product in `𝔽_p[X]/(f)`, `deg f = n`, given the packed table `PT` of `α^{n+i}`. -/
def mulmodK (p n : ℕ) (PT : List ℕ) (a b : List ℕ) : List ℕ :=
  (unpackN n (packN ((unpackN (2 * n - 1) (packN a * packN b)).take n) +
    dotPack ((unpackN (2 * n - 1) (packN a * packN b)).drop n) PT)).map (· % p)

theorem coeff_ofListN_lt {p : ℕ} (hp0 : 0 < p) (l : List ℕ) (hl : ∀ x ∈ l, x < p) (i : ℕ) :
    (ofListN l).coeff i < p := by
  rw [coeff_ofListN, List.getD_eq_getElem?_getD]
  cases h : l[i]? with
  | none => simpa using hp0
  | some x => simpa using hl x (List.mem_of_getElem? h)

theorem coeff_ofListN_eq_zero (l : List ℕ) (i : ℕ) (hi : l.length ≤ i) : (ofListN l).coeff i = 0 := by
  rw [coeff_ofListN, List.getD_eq_default _ _ hi]

theorem coeff_mul_bound {p n : ℕ} (A B : ℕ[X]) (hA : ∀ i, A.coeff i < p) (hB : ∀ i, B.coeff i < p)
    (hA0 : ∀ i, n ≤ i → A.coeff i = 0) (hB0 : ∀ i, n ≤ i → B.coeff i = 0) (k : ℕ) :
    (A * B).coeff k ≤ 2 * n * p ^ 2 ∧ (2 * n - 1 ≤ k → (A * B).coeff k = 0) := by
  rw [coeff_mul]
  constructor
  · by_cases hk : k < 2 * n
    · calc ∑ x ∈ Finset.antidiagonal k, A.coeff x.1 * B.coeff x.2
          ≤ ∑ _x ∈ Finset.antidiagonal k, p ^ 2 := Finset.sum_le_sum fun x _ => by
            rw [sq]; exact Nat.mul_le_mul (le_of_lt (hA _)) (le_of_lt (hB _))
        _ = (k + 1) * p ^ 2 := by rw [Finset.sum_const, Finset.Nat.card_antidiagonal, smul_eq_mul]
        _ ≤ 2 * n * p ^ 2 := Nat.mul_le_mul_right _ (by omega)
    · rw [Finset.sum_eq_zero]
      · exact Nat.zero_le _
      intro x hx
      rw [Finset.mem_antidiagonal] at hx
      by_cases h1 : n ≤ x.1
      · rw [hA0 _ h1, zero_mul]
      · rw [hB0 _ (by omega), mul_zero]
  · intro hk
    apply Finset.sum_eq_zero
    intro x hx
    rw [Finset.mem_antidiagonal] at hx
    by_cases h1 : n ≤ x.1
    · rw [hA0 _ h1, zero_mul]
    · rw [hB0 _ (by omega), mul_zero]

theorem dotPack_eq (hs : List ℕ) (T : List (List ℕ)) (hlen : hs.length = T.length) :
    dotPack hs (T.map packN) = (∑ i ∈ Finset.range hs.length,
      C (hs.getD i 0) * ofListN (T.getD i [])).eval Bw := by
  induction hs generalizing T with
  | nil => simp [dotPack]
  | cons h hs ih =>
    cases T with
    | nil => simp at hlen
    | cons t T =>
      simp only [List.length_cons, add_left_inj] at hlen
      rw [List.map_cons, dotPack, ih T hlen, List.length_cons, Finset.sum_range_succ', packN_eq]
      simp [eval_finset_sum]
      ring

theorem mulmodK_spec {R : Type*} [CommRing R] (α : R) {p : ℕ} (hp : (p : R) = 0) (hp0 : 0 < p)
    {n : ℕ} (hn : 0 < n) (T : List (List ℕ)) (hTl : T.length = n - 1)
    (hT : ∀ i, i < n - 1 → evN α (T.getD i []) = α ^ (n + i))
    (hTe : ∀ t ∈ T, (∀ x ∈ t, x < p) ∧ t.length ≤ n)
    (hBw : 2 * n * p ^ 2 * (1 + n * p) < Bw)
    (a b : List ℕ) (hal : a.length = n) (hbl : b.length = n) (ha : ∀ x ∈ a, x < p)
    (hb : ∀ x ∈ b, x < p) :
    evN α (mulmodK p n (T.map packN) a b) = evN α a * evN α b ∧
      (mulmodK p n (T.map packN) a b).length = n ∧
      ∀ x ∈ mulmodK p n (T.map packN) a b, x < p := by
  set A := ofListN a
  set B := ofListN b
  set Pm := A * B with hPm
  have hbnd := coeff_mul_bound (n := n) A B (coeff_ofListN_lt hp0 a ha) (coeff_ofListN_lt hp0 b hb)
    (fun i hi => coeff_ofListN_eq_zero a i (by omega))
    (fun i hi => coeff_ofListN_eq_zero b i (by omega))
  have hPmB : ∀ k, Pm.coeff k < Bw := fun k => lt_of_le_of_lt (hbnd k).1 (by
    have : 2 * n * p ^ 2 ≤ 2 * n * p ^ 2 * (1 + n * p) := Nat.le_mul_of_pos_right _ (by positivity)
    omega)
  have hfull : unpackN (2 * n - 1) (packN a * packN b) = (List.range (2 * n - 1)).map Pm.coeff := by
    rw [packN_eq, packN_eq, ← eval_mul]
    exact unpackN_eval Pm _ hPmB (fun i hi => (hbnd i).2 hi)
  have htake : ((List.range (2 * n - 1)).map Pm.coeff).take n = (List.range n).map Pm.coeff := by
    rw [← List.map_take, List.take_range, min_eq_left (by omega)]
  have hdrop : ((List.range (2 * n - 1)).map Pm.coeff).drop n =
      (List.range (n - 1)).map (fun i => Pm.coeff (n + i)) := by
    apply List.ext_getElem
    · simp; omega
    · intro i h1 h2
      simp
  set hs := (List.range (n - 1)).map (fun i => Pm.coeff (n + i)) with hhs
  set Q := ofListN ((List.range n).map Pm.coeff) +
    ∑ i ∈ Finset.range (n - 1), C (hs.getD i 0) * ofListN (T.getD i []) with hQ
  have hhsl : hs.length = n - 1 := by simp [hhs]
  have hQeval : packN ((List.range n).map Pm.coeff) + dotPack hs (T.map packN) = Q.eval Bw := by
    rw [dotPack_eq hs T (by rw [hhsl, hTl]), packN_eq, hhsl, hQ, eval_add]
  have hTget : ∀ i, (∀ x ∈ T.getD i [], x < p) ∧ (T.getD i []).length ≤ n := by
    intro i
    rw [List.getD_eq_getElem?_getD]
    cases h : T[i]? with
    | none => simp
    | some t => simpa using hTe t (List.mem_of_getElem? h)
  have hhsget : ∀ i, hs.getD i 0 ≤ 2 * n * p ^ 2 := by
    intro i
    rw [List.getD_eq_getElem?_getD]
    cases h : hs[i]? with
    | none => simp
    | some x =>
      have := List.mem_of_getElem? h
      simp only [hhs, List.mem_map, List.mem_range] at this
      obtain ⟨j, _, rfl⟩ := this
      exact (hbnd _).1
  have hQc : ∀ j, Q.coeff j ≤ 2 * n * p ^ 2 * (1 + n * p) := by
    intro j
    rw [hQ, coeff_add, finset_sum_coeff]
    have h1 : (ofListN ((List.range n).map Pm.coeff)).coeff j ≤ 2 * n * p ^ 2 := by
      rw [coeff_ofListN, List.getD_eq_getElem?_getD]
      cases h : ((List.range n).map Pm.coeff)[j]? with
      | none => simp
      | some x =>
        have := List.mem_of_getElem? h
        simp only [List.mem_map, List.mem_range] at this
        obtain ⟨k, _, rfl⟩ := this
        exact (hbnd _).1
    have h2 : ∑ i ∈ Finset.range (n - 1), (C (hs.getD i 0) * ofListN (T.getD i [])).coeff j ≤
        (n - 1) * (2 * n * p ^ 2 * p) := by
      calc _ ≤ ∑ _i ∈ Finset.range (n - 1), 2 * n * p ^ 2 * p := Finset.sum_le_sum fun i _ => by
            rw [coeff_C_mul]
            exact Nat.mul_le_mul (hhsget i)
              (le_of_lt (coeff_ofListN_lt hp0 _ (hTget i).1 j))
        _ = _ := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
    have h3 : (n - 1) * (2 * n * p ^ 2 * p) ≤ 2 * n * p ^ 2 * (n * p) := by
      rw [mul_comm (n - 1), mul_assoc (2 * n * p ^ 2), mul_comm p (n - 1)]
      exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega))
    rw [mul_add, mul_one]
    omega
  have hQ0 : ∀ j, n ≤ j → Q.coeff j = 0 := by
    intro j hj
    rw [hQ, coeff_add, finset_sum_coeff, coeff_ofListN_eq_zero _ _ (by simpa using hj), zero_add]
    apply Finset.sum_eq_zero
    intro i _
    rw [coeff_C_mul, coeff_ofListN_eq_zero _ _ (le_trans (hTget i).2 hj), mul_zero]
  have hres : unpackN n (Q.eval Bw) = (List.range n).map Q.coeff :=
    unpackN_eval Q n (fun j => lt_of_le_of_lt (hQc j) hBw) hQ0
  have hmk : mulmodK p n (T.map packN) a b = ((List.range n).map Q.coeff).map (· % p) := by
    rw [mulmodK, hfull, htake, hdrop, hQeval, hres]
  rw [hmk]
  refine ⟨?_, by simp, ?_⟩
  · -- the value
    have hmodev : ∀ l : List ℕ, evN α (l.map (· % p)) = evN α l := by
      intro l
      induction l with
      | nil => rfl
      | cons x l ih => simp only [List.map_cons, evN, ih, cast_mod_eq hp]
    rw [hmodev, evN_range, ← aeval_eq_sum_of_coeff α Q n hQ0, hQ, map_add,
      ← evN_eq_aeval, evN_range, map_sum]
    have hT' : ∀ i ∈ Finset.range (n - 1), aeval α (C (hs.getD i 0) * ofListN (T.getD i [])) =
        (Pm.coeff (n + i) : R) * α ^ (n + i) := by
      intro i hi
      rw [Finset.mem_range] at hi
      rw [map_mul, aeval_C, ← evN_eq_aeval, hT i hi, hhs, List.getD_eq_getElem?_getD]
      simp [List.getElem?_map, List.getElem?_range hi]
    rw [Finset.sum_congr rfl hT', ← Finset.sum_range_add (fun k => (Pm.coeff k : R) * α ^ k),
      show n + (n - 1) = 2 * n - 1 by omega, ← aeval_eq_sum_of_coeff α Pm _ (fun i hi => (hbnd i).2 hi),
      hPm, map_mul, ← evN_eq_aeval, ← evN_eq_aeval]
  · intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨y, _, rfl⟩ := hx
    exact Nat.mod_lt _ hp0

end MulK

/-! ## Powers, the table of `α^{n+i}`, and the certificate check -/

section CheckK

theorem addP_lt {p : ℕ} (hp0 : 0 < p) (a b : List ℕ) (h : a.length = b.length) :
    ∀ x ∈ addP p a b, x < p := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => simp [addP]
    | cons y b => simp at h
  | cons x a ih =>
    cases b with
    | nil => simp at h
    | cons y b =>
      intro z hz
      simp only [addP, List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact Nat.mod_lt _ hp0
      · exact ih b (by simpa using h) z hz

/-- `acc ↦ acc² · a^{bit}` along the bits of an exponent (most significant first). -/
def powBits (p n : ℕ) (PT : List ℕ) (a : List ℕ) : List Bool → List ℕ → List ℕ
  | [], acc => acc
  | b :: bs, acc =>
    powBits p n PT a bs (if b then mulmodK p n PT (mulmodK p n PT acc acc) a
      else mulmodK p n PT acc acc)

/-- The value of a bit list (most significant first). -/
def bitsNum : List Bool → ℕ
  | [] => 0
  | b :: bs => (if b then 2 ^ bs.length else 0) + bitsNum bs

/-- The table `[r, α r, α² r, …]` (`m` entries). -/
def tableL (p : ℕ) (r : List ℕ) : ℕ → List ℕ → List (List ℕ)
  | 0, _ => []
  | m + 1, t => t :: tableL p r m (mulX p r t)

def subXK (p n : ℕ) (s : List ℕ) : List ℕ := addP p s (0 :: (p - 1) :: List.replicate (n - 2) 0)

/-- The certificate check with packed arithmetic. -/
def chkK (p n : ℕ) (PT : List ℕ) (bits : List Bool) : List (List ℕ) → List ℕ → Bool
  | [], _ => true
  | w :: ws, s =>
    (w.length == n && w.all (· < p) &&
      mulmodK p n PT (subXK p n (powBits p n PT s bits (oneP n))) w == oneP n) &&
      chkK p n PT bits ws (powBits p n PT s bits (oneP n))

variable {R : Type*} [CommRing R] (α : R) {p : ℕ} (hp : (p : R) = 0) (hp0 : 0 < p) {n : ℕ}
  (hn : 0 < n) (T : List (List ℕ)) (hTl : T.length = n - 1)
  (hT : ∀ i, i < n - 1 → evN α (T.getD i []) = α ^ (n + i))
  (hTe : ∀ t ∈ T, (∀ x ∈ t, x < p) ∧ t.length ≤ n)
  (hBw : 2 * n * p ^ 2 * (1 + n * p) < Bw)
include hp hp0 hn hTl hT hTe hBw

/-- Residue invariant: length `n`, digits below `p`. -/
def GoodR (p n : ℕ) (a : List ℕ) : Prop := a.length = n ∧ ∀ x ∈ a, x < p

theorem mulmodK_good {a b : List ℕ} (ha : GoodR p n a) (hb : GoodR p n b) :
    evN α (mulmodK p n (T.map packN) a b) = evN α a * evN α b ∧
      GoodR p n (mulmodK p n (T.map packN) a b) := by
  obtain ⟨h1, h2, h3⟩ := mulmodK_spec α hp hp0 hn T hTl hT hTe hBw a b ha.1 hb.1 ha.2 hb.2
  exact ⟨h1, h2, h3⟩

theorem powBits_spec (a : List ℕ) (ha : GoodR p n a) (bits : List Bool) :
    ∀ acc, GoodR p n acc → evN α (powBits p n (T.map packN) a bits acc) =
      evN α acc ^ (2 ^ bits.length) * evN α a ^ bitsNum bits ∧
      GoodR p n (powBits p n (T.map packN) a bits acc) := by
  induction bits with
  | nil => intro acc hacc; simp [powBits, bitsNum, hacc]
  | cons b bs ih =>
    intro acc hacc
    obtain ⟨hsq, hsqg⟩ := mulmodK_good α hp hp0 hn T hTl hT hTe hBw hacc hacc
    by_cases hb : b
    · subst hb
      obtain ⟨hm, hmg⟩ := mulmodK_good α hp hp0 hn T hTl hT hTe hBw hsqg ha
      obtain ⟨hv, hg⟩ := ih _ hmg
      simp only [powBits, if_true] at hv hg ⊢
      refine ⟨?_, hg⟩
      rw [hv, hm, hsq, bitsNum, if_pos rfl, List.length_cons, pow_succ, pow_mul, pow_add]
      ring
    · simp only [Bool.not_eq_true] at hb
      subst hb
      obtain ⟨hv, hg⟩ := ih _ hsqg
      simp only [powBits, Bool.false_eq_true, if_false] at hv hg ⊢
      refine ⟨?_, hg⟩
      rw [hv, hsq, bitsNum, if_neg (by simp), zero_add, List.length_cons, pow_succ, pow_mul]
      ring

omit hp hp0 hTl hT hTe hBw in
theorem oneP_good (hp1 : 1 < p) : GoodR p n (oneP n) := by
  refine ⟨by simp [oneP]; omega, ?_⟩
  intro x hx
  simp only [oneP, List.mem_cons, List.mem_replicate] at hx
  rcases hx with rfl | ⟨-, rfl⟩ <;> omega

theorem chkK_spec (hp1 : 1 < p) (hn2 : 2 ≤ n) (bits : List Bool) (hbits : bitsNum bits = p)
    (ws : List (List ℕ)) :
    ∀ (s : List ℕ) (j : ℕ), evN α s = α ^ (p ^ j) → GoodR p n s →
      chkK p n (T.map packN) bits ws s = true →
      ∀ i < ws.length, IsUnit (α ^ (p ^ (j + i + 1)) - α) := by
  induction ws with
  | nil => intro s j _ _ _ i hi; simp at hi
  | cons w ws ih =>
    intro s j hs hsg h i hi
    simp only [chkK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hwl, hwe⟩, hw⟩, hrest⟩ := h
    obtain ⟨hps, hpg⟩ := powBits_spec α hp hp0 hn T hTl hT hTe hBw s hsg bits (oneP n)
      (oneP_good hn hp1)
    rw [evN_oneP, one_pow, one_mul, hbits] at hps
    have hs' : evN α (powBits p n (T.map packN) s bits (oneP n)) = α ^ (p ^ (j + 1)) := by
      rw [hps, hs, ← pow_mul, pow_succ]
    cases i with
    | zero =>
      have hsub : GoodR p n (subXK p n (powBits p n (T.map packN) s bits (oneP n))) := by
        refine ⟨?_, addP_lt hp0 _ _ ?_⟩
        · rw [subXK, length_addP, hpg.1]; simp; omega
        · rw [hpg.1]; simp; omega
      have := (mulmodK_good α hp hp0 hn T hTl hT hTe hBw hsub ⟨hwl, hwe⟩).1
      rw [hw, evN_oneP, subXK, ← subXP, evN_subXP α hp (by omega), hs'] at this
      exact isUnit_of_mul_eq_one _ _ this.symm
    | succ i =>
      have := ih (powBits p n (T.map packN) s bits (oneP n)) (j + 1) hs' hpg hrest i
        (by simpa using hi)
      rwa [show j + 1 + i + 1 = j + (i + 1) + 1 by ring] at this

end CheckK

/-! ## The criterion with packed arithmetic -/

section Final

theorem tableL_length (p : ℕ) (r : List ℕ) (m : ℕ) (t : List ℕ) : (tableL p r m t).length = m := by
  induction m generalizing t with
  | zero => rfl
  | succ m ih => simp [tableL, ih]

theorem tableL_spec {R : Type*} [CommRing R] (α : R) {p : ℕ} (hp : (p : R) = 0) {n : ℕ}
    (hn : 0 < n) (r : List ℕ) (hr : evN α r = α ^ n) (hrl : r.length = n) (m : ℕ) :
    ∀ (t : List ℕ), t.length = n → ∀ i, i < m →
      evN α ((tableL p r m t).getD i []) = α ^ i * evN α t := by
  induction m with
  | zero => intro t _ i hi; omega
  | succ m ih =>
    intro t ht i hi
    cases i with
    | zero => simp [tableL]
    | succ i =>
      simp only [tableL, List.getD_cons_succ]
      rw [ih (mulX p r t) (length_mulX r hrl t ht hn) i (by omega),
        evN_mulX α hp r hr t ht hn, pow_succ]
      ring

/-- The table check and the certificate check. -/
def bigCheck (p : ℕ) (lower : List ℤ) (bits : List Bool) (ws : List (List ℕ)) : Bool :=
  (tableL p (lower.map (negMod p)) (lower.length - 1) (lower.map (negMod p))).all
      (fun t => t.length == lower.length && t.all (· < p)) &&
    chkK p lower.length
      ((tableL p (lower.map (negMod p)) (lower.length - 1) (lower.map (negMod p))).map packN)
      bits ws (0 :: 1 :: List.replicate (lower.length - 2) 0)

theorem irreducible_of_bigCheck (p : ℕ) [Fact p.Prime] (lower : List ℤ) (bits : List Bool)
    (ws : List (List ℕ)) (hbits : bitsNum bits = p) (hws : lower.length ≤ 2 * ws.length)
    (hn2 : 2 ≤ lower.length)
    (hBw : 2 * lower.length * p ^ 2 * (1 + lower.length * p) < Bw)
    (h : bigCheck p lower bits ws = true) :
    Irreducible ((ofList (lower ++ [1])).map (Int.castRingHom ℚ)) := by
  set n := lower.length with hndef
  set f := ofList (lower ++ [1]) with hfdef
  have hdeg : f.natDegree = n := natDegree_ofList_one lower
  have hmonic : f.Monic := monic_ofList_one lower
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hp0 : 0 < p := by omega
  simp only [bigCheck, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨hTe, hchk⟩ := h
  have hZ : Irreducible f := by
    apply hmonic.irreducible_of_irreducible_map (Int.castRingHom (ZMod p))
    set fb := f.map (Int.castRingHom (ZMod p))
    have hmb : fb.Monic := hmonic.map _
    have hdb : fb.natDegree = n := by rw [hmonic.natDegree_map, hdeg]
    apply irreducible_of_frob fb hmb (by omega)
    intro d hd0 hd
    set α := AdjoinRoot.root fb
    have hp : ((p : ℕ) : AdjoinRoot fb) = 0 := by
      rw [← map_natCast (algebraMap (ZMod p) (AdjoinRoot fb)), ZMod.natCast_self, map_zero]
    have hroot : evZ α (lower ++ [1]) = 0 := by
      rw [← evZ_eq_aeval (S := ZMod p), AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
    have hr : evN α (lower.map (negMod p)) = α ^ n := by
      rw [evN_negMod α hp hp0, hndef]
      rw [evZ_append] at hroot
      simp only [Int.cast_one, one_mul] at hroot
      linear_combination -hroot
    have hrl : (lower.map (negMod p)).length = n := by simp [hndef]
    set T := tableL p (lower.map (negMod p)) (n - 1) (lower.map (negMod p))
    have hTl : T.length = n - 1 := tableL_length _ _ _ _
    have hT : ∀ i, i < n - 1 → evN α (T.getD i []) = α ^ (n + i) := by
      intro i hi
      rw [tableL_spec α hp (by omega) _ hr hrl (n - 1) _ hrl i hi, hr, pow_add, mul_comm]
    have hTe' : ∀ t ∈ T, (∀ x ∈ t, x < p) ∧ t.length ≤ n := by
      intro t ht
      obtain ⟨h1, h2⟩ := hTe t ht
      exact ⟨h2, le_of_eq h1⟩
    have hs0 : evN α (0 :: 1 :: List.replicate (n - 2) 0) = α ^ (p ^ 0) := by
      simp [evN, evN_replicate_zero]
    have hs0g : GoodR p n (0 :: 1 :: List.replicate (n - 2) 0) := by
      refine ⟨by simp only [List.length_cons, List.length_replicate]; omega, ?_⟩
      intro x hx
      simp only [List.mem_cons, List.mem_replicate] at hx
      rcases hx with rfl | rfl | ⟨-, rfl⟩ <;> omega
    have := chkK_spec α hp hp0 (by omega) T hTl hT hTe' hBw hp1 hn2 bits hbits ws _ 0 hs0 hs0g
      hchk (d - 1) (by omega)
    rwa [show 0 + (d - 1) + 1 = d by omega] at this
  exact (IsPrimitive.Int.irreducible_iff_irreducible_map_cast hmonic.isPrimitive).mp hZ

end Final

end OddMath.Frontier.EKFinal
