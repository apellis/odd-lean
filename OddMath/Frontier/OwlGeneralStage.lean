import OddMath.Frontier.OwlGeneralFlip

/-! Stage-wise extension of the Omission Word Lemma (EKL arXiv:1111.1320v1, Lemma 2.18).

Stage `r` concerns words on the top letters `n+1-r, ..., n` whose permutation is the
reversal `rho n r` of the top `r+1` strands (= `permutation (blocks n r)`), and the
relative kernel `RelKernel n r` of the operators `∂_i`, `i ≥ n+1-r`.

* `relOWL_step`: the printed block step (inherited `block_shape`, and relative copies
  of `annihilate_length` / `shaped_block_zero`, whose proofs only use `∂_i`, `i ≥ n-r`)
  prepends the descending chain `n, ..., n-r` to ANY stage-`r` word with the relative
  property, not only to the inherited block word.
* `relOWL_flip`: the signed partial reversal of the top `r+1` variables conjugates
  `s_i ↦ s_{i'}`, `∂_i ↦ ε ∂_{i'}` (`i' = 2n+1-r-i`) for top letters and preserves
  `RelKernel n r`, so it transports the relative property.

At `r = n+1` the relative kernel is the joint kernel and the property is the literal
termwise trichotomy. -/
namespace OddMath.Frontier.OwlGeneralStage
open OddMath.SkewPolynomial (SkewPolynomial generator)
open NilCoxeterWords OmissionWord AllRankDivided OmissionCanonical OwlGeneral LongestDivided
noncomputable section

variable {n : ℕ}

/-! ### Relative kernels and the relative block step -/

/-- Joint kernel of the top operators `∂_i`, `i ≥ n+1-r`. -/
def RelKernel (n r : ℕ) (f : SkewPolynomial (n+2)) : Prop :=
  ∀ i : Fin (n+1), n+1-r ≤ i.val → divided i f = 0

open NonadjacentDivided IntervalAnnihilation in
/-- Copy of `IntervalAnnihilation.annihilate_length`, needing only `∂_i f = 0` for
`i ≥ u`; the inherited proof uses exactly those indices. -/
theorem annihilate_length_rel (u : Fin (n+2)) (k : ℕ) (hv : u.val+k+1 < n+2)
    (f : SkewPolynomial (n+2)) (hf : ∀ i : Fin (n+1), u.val ≤ i.val → divided i f = 0) :
    ascending (u.val+1) k (by omega)
      (dividedPair u ⟨u.val+k+1, hv⟩ (by intro h; have := congrArg Fin.val h; simp only [Fin.val_mk] at this; omega) f) = 0 := by
  induction k with
  | zero =>
    let i : Fin (n+1) := ⟨u.val, by omega⟩
    change dividedPair i.castSucc i.succ _ f = 0
    rw [adjacent]
    exact hf i (by dsimp [i]; omega)
  | succ k ih =>
    let b : Fin (n+2) := ⟨u.val+k+1, by omega⟩
    let c : Fin (n+2) := ⟨u.val+(k+1)+1, hv⟩
    let i : Fin (n+1) := ⟨u.val+k+1, by omega⟩
    have hub : u ≠ b := by intro h; have := congrArg Fin.val h; dsimp [b] at this; omega
    have huc : u ≠ c := by intro h; have := congrArg Fin.val h; dsimp [c] at this; omega
    have hbc : b ≠ c := by intro h; have := congrArg Fin.val h; dsimp [b,c] at this; omega
    have ha : dividedPair b c hbc = AllRankDivided.divided i := by
      convert adjacent i using 1
    have ht := triangle u b c hub huc hbc f
    rw [ha, hf i (by dsimp [i]; omega), map_zero, add_zero] at ht
    have ht' := eq_neg_of_add_eq_zero_left ht
    rw [ascending_succ]
    have hi : (⟨u.val+1+k, by omega⟩ : Fin (n+1)) = i := by
      apply Fin.ext
      dsimp [i]
      omega
    rw [hi]
    change ascending (u.val+1) k _ (AllRankDivided.divided i (dividedPair u c huc f)) = 0
    rw [ht', map_neg]
    apply neg_eq_zero.mpr
    apply ascending_pair_zero _ _ _ u c huc
    · intro j hj hj'
      dsimp [c]
      constructor
      · intro h; have := congrArg Fin.val h; change j.val = u.val at this; omega
      constructor
      · intro h; have := congrArg Fin.val h; change j.val = u.val+(k+1)+1 at this; omega
      constructor
      · intro h; have := congrArg Fin.val h; change j.val+1 = u.val at this; omega
      · intro h; have := congrArg Fin.val h; change j.val+1 = u.val+(k+1)+1 at this; omega
    · exact ih (by omega)

open SignedPermutation NonadjacentDivided IntervalAnnihilation in
/-- Copy of `OmissionCanonical.shaped_block_zero` for the relative kernel `i ≥ n-r`. -/
theorem shaped_block_zero_rel (n r t : ℕ) (hr : r+1 ≤ n+1) (ht : t ≤ r)
    (f : SkewPolynomial (n+2)) (hf : ∀ i : Fin (n+1), n-r ≤ i.val → divided i f = 0) :
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
    have hz := annihilate_length_rel u (r-t) (by dsimp [u,k]; omega) f
      (fun i hi => hf i (by dsimp [u,k] at hi; omega))
    change ascending (k+1) (r-t) _ (dividedPair u v huv f) = 0 at hz
    rw [hz, map_zero, smul_zero, smul_zero]
  · intro x hx _
    exact block_inverse_high n r t hr ht x (by dsimp [j,k] at hx; omega)

/-- Relative termwise property at stage `r`. -/
def RelOWL (n r : ℕ) (v : Word n) : Prop :=
  ∀ m : Marked n, erase m = v → Reduced (omission m) →
    (∀ f, RelKernel n r f → hybrid m f = 0) ∨ m = allFalse v

/-- The printed block step, for an arbitrary stage-`r` word `v`. -/
theorem relOWL_step {r : ℕ} (hr : r+1 ≤ n+1) (v : Word n)
    (hpv : permutation v = permutation (blocks n r (by omega))) (hv : RelOWL n r v) :
    RelOWL n (r+1) (down n (n-r) (r+1) (by omega) ++ v) := by
  intro m he hred
  obtain ⟨a,b,hm,ha,hb⟩ := List.map_eq_append_iff.mp he
  subst m
  change erase a = down n (n-r) (r+1) _ at ha
  change erase b = v at hb
  rw [omission_append] at hred
  have hbr := reduced_suffix _ _ hred
  rcases hv b hb hbr with hz | hfalse
  · apply Or.inl
    intro f hf
    rw [hybrid_append, hz f (fun i hi => hf i (by omega)), hybrid_zero]
  · subst b
    rw [omission_allFalse] at hred
    obtain ⟨t,ht,hshape⟩ := block_shape (by omega) a v ha
      (fun i hi => by rw [hpv]; exact blocks_descents (by omega) i hi) hred
    by_cases hall : t = r+1
    · subst t
      apply Or.inr
      simp only [Nat.sub_self, down, allTrue, List.map_nil, List.nil_append] at hshape
      rw [hshape]
      simp [allFalse, down]
    · apply Or.inl
      intro f hf
      rw [hybrid_append, hshape, hybrid_append, hybrid_allTrue,
        hybrid_allFalse, hybrid_allFalse, ← SignedPermutation.action_mul, hpv,
        ← permutation_append]
      exact shaped_block_zero_rel n r t hr (by omega) f (fun i hi => hf i (by omega))

/-! ### The signed partial reversal of the top strands -/

/-- Reversal of the top `r+1` strands, as the inherited block permutation. -/
def rho (n r : ℕ) (h : r ≤ n+1) : Perm n := permutation (blocks n r h)

theorem rho_val {r : ℕ} (h : r ≤ n+1) (x : Fin (n+2)) :
    (rho n r h x).val = if x.val < n+1-r then x.val else n+1+(n+1-r)-x.val :=
  blocks_apply h x

theorem rho_rho {r : ℕ} (h : r ≤ n+1) : rho n r h * rho n r h = 1 := by
  apply Equiv.ext
  intro x
  apply Fin.ext
  simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
  rw [rho_val, rho_val]
  have := x.isLt
  split_ifs <;> omega

theorem rho_apply_rho {r : ℕ} (h : r ≤ n+1) (x : Fin (n+2)) : rho n r h (rho n r h x) = x := by
  rw [← Equiv.Perm.mul_apply, rho_rho, Equiv.Perm.one_apply]

theorem rho_eq_iff {r : ℕ} (h : r ≤ n+1) (x y : Fin (n+2)) : rho n r h x = y ↔ x = rho n r h y := by
  constructor
  · intro e; rw [← e, rho_apply_rho]
  · intro e; rw [e, rho_apply_rho]

/-- Letter reversal of the top range `i ↦ 2n+1-r-i`; lower letters are fixed. -/
def flipL (n r : ℕ) (i : Fin (n+1)) : Fin (n+1) :=
  if hi : n+1-r ≤ i.val then ⟨n+(n+1-r)-i.val, by omega⟩ else i

theorem flipL_val {r : ℕ} (i : Fin (n+1)) (hi : n+1-r ≤ i.val) :
    (flipL n r i).val = n+(n+1-r)-i.val := by
  simp [flipL, hi]

theorem flipL_range {r : ℕ} (i : Fin (n+1)) (hi : n+1-r ≤ i.val) :
    n+1-r ≤ (flipL n r i).val := by
  rw [flipL_val i hi]; have := i.isLt; omega

theorem flipL_flipL {r : ℕ} (i : Fin (n+1)) (hi : n+1-r ≤ i.val) :
    flipL n r (flipL n r i) = i := by
  apply Fin.ext
  rw [flipL_val _ (flipL_range i hi), flipL_val i hi]
  have := i.isLt; omega

theorem rho_castSucc {r : ℕ} (h : r ≤ n+1) (i : Fin (n+1)) (hi : n+1-r ≤ i.val) :
    rho n r h i.castSucc = (flipL n r i).succ := by
  apply Fin.ext
  rw [rho_val, Fin.val_succ, flipL_val i hi, Fin.coe_castSucc]
  have := i.isLt
  split_ifs <;> omega

theorem rho_succ {r : ℕ} (h : r ≤ n+1) (i : Fin (n+1)) (hi : n+1-r ≤ i.val) :
    rho n r h i.succ = (flipL n r i).castSucc := by
  apply Fin.ext
  rw [rho_val, Fin.val_succ, Fin.coe_castSucc, flipL_val i hi]
  have := i.isLt
  split_ifs <;> omega

theorem rho_mul_swap {r : ℕ} (h : r ≤ n+1) (i : Fin (n+1)) (hi : n+1-r ≤ i.val) :
    rho n r h * Equiv.swap i.castSucc i.succ =
      Equiv.swap (flipL n r i).castSucc (flipL n r i).succ * rho n r h := by
  rw [Equiv.mul_swap_eq_swap_mul, rho_castSucc h i hi, rho_succ h i hi, Equiv.swap_comm]

/-- The signed partial reversal automorphism. -/
def psi (n r : ℕ) (h : r ≤ n+1) : SkewPolynomial (n+2) ≃+* SkewPolynomial (n+2) :=
  SignedPermutation.skewAction (rho n r h)

def epsR (n r : ℕ) (h : r ≤ n+1) : ℤ := SignedPermutation.epsilon (rho n r h)

theorem epsR_sq {r : ℕ} (h : r ≤ n+1) : epsR n r h * epsR n r h = 1 := by
  unfold epsR SignedPermutation.epsilon
  rcases Int.units_eq_one_or (Equiv.Perm.sign (rho n r h)) with e | e <;> simp [e]

theorem psi_psi {r : ℕ} (h : r ≤ n+1) (f : SkewPolynomial (n+2)) : psi n r h (psi n r h f) = f := by
  unfold psi
  rw [← SignedPermutation.action_mul, rho_rho, SignedPermutation.action_one]

theorem psi_generator {r : ℕ} (h : r ≤ n+1) (j : Fin (n+2)) :
    psi n r h (generator j) = epsR n r h • generator (rho n r h j) := by
  unfold psi epsR
  rw [SignedPermutation.action_generator]

theorem psi_s {r : ℕ} (h : r ≤ n+1) (i : Fin (n+1)) (hi : n+1-r ≤ i.val)
    (f : SkewPolynomial (n+2)) : psi n r h (s i f) = s (flipL n r i) (psi n r h f) := by
  unfold psi s
  rw [← SignedPermutation.action_mul, ← SignedPermutation.action_mul, rho_mul_swap h i hi]

/-- The conjugate `ε • ψ ∘ ∂_i ∘ ψ`, bundled as a linear map. -/
def conjDividedR (n r : ℕ) (h : r ≤ n+1) (i : Fin (n+1)) :
    SkewPolynomial (n+2) →ₗ[ℤ] SkewPolynomial (n+2) where
  toFun f := epsR n r h • psi n r h (divided i (psi n r h f))
  map_add' f g := by simp only [map_add, smul_add]
  map_smul' c f := by
    simp only [map_zsmul, RingHom.id_apply]
    rw [smul_comm]

theorem psi_divided {r : ℕ} (h : r ≤ n+1) (i : Fin (n+1)) (hi : n+1-r ≤ i.val)
    (f : SkewPolynomial (n+2)) :
    divided (flipL n r i) (psi n r h f) = epsR n r h • psi n r h (divided i f) := by
  have hD : conjDividedR n r h i = divided (flipL n r i) := by
    apply divided_unique
    · show epsR n r h • psi n r h (divided i (psi n r h 1)) = 0
      rw [map_one, divided_one, map_zero, smul_zero]
    · intro j
      show epsR n r h • psi n r h (divided i (psi n r h (generator j))) = _
      rw [psi_generator, map_zsmul, divided_generator, map_zsmul, smul_smul, epsR_sq, one_smul]
      have hiff : (rho n r h j = i.castSucc ∨ rho n r h j = i.succ) ↔
          (j = (flipL n r i).castSucc ∨ j = (flipL n r i).succ) := by
        rw [rho_eq_iff, rho_eq_iff, rho_castSucc h i hi, rho_succ h i hi]
        exact Or.comm
      by_cases hj : j = (flipL n r i).castSucc ∨ j = (flipL n r i).succ
      · rw [if_pos (hiff.mpr hj), if_pos hj, map_one]
      · rw [if_neg (mt hiff.mp hj), if_neg hj, map_zero]
    · intro f g
      show epsR n r h • psi n r h (divided i (psi n r h (f*g))) =
        epsR n r h • psi n r h (divided i (psi n r h f)) * g +
          s (flipL n r i) f * (epsR n r h • psi n r h (divided i (psi n r h g)))
      rw [map_mul, divided_mul, map_add, map_mul, map_mul, psi_psi, psi_s h i hi, psi_psi,
        smul_add, smul_mul_assoc, mul_smul_comm]
  have := LinearMap.congr_fun hD (psi n r h f)
  rw [← this]
  show epsR n r h • psi n r h (divided i (psi n r h (psi n r h f))) = _
  rw [psi_psi]

theorem psi_relKernel {r : ℕ} (h : r ≤ n+1) {f : SkewPolynomial (n+2)} (hf : RelKernel n r f) :
    RelKernel n r (psi n r h f) := by
  intro j hj
  have e := psi_divided h (flipL n r j) (flipL_range j hj) f
  rw [flipL_flipL j hj] at e
  rw [e, hf _ (flipL_range j hj), map_zero, smul_zero]

/-! ### Transport of the relative property -/

/-- All letters lie in the top range. -/
def InRange (n r : ℕ) (w : Word n) : Prop := ∀ i ∈ w, n+1-r ≤ i.val

def flipMarkedR (n r : ℕ) (m : Marked n) : Marked n := m.map (fun a => (flipL n r a.1, a.2))

theorem erase_flipR {r : ℕ} (m : Marked n) :
    erase (flipMarkedR n r m) = (erase m).map (flipL n r) := by
  simp [flipMarkedR, erase, Function.comp_def]

theorem omission_flipR {r : ℕ} (m : Marked n) :
    omission (flipMarkedR n r m) = (omission m).map (flipL n r) := by
  induction m with
  | nil => rfl
  | cons a m ih =>
      rcases a with ⟨i, b⟩
      cases b <;> simp [flipMarkedR, omission] at ih ⊢ <;> exact ih

theorem map_flipL_flipL {r : ℕ} (w : Word n) (hw : InRange n r w) :
    (w.map (flipL n r)).map (flipL n r) = w := by
  rw [List.map_map]
  conv_rhs => rw [← List.map_id w]
  apply List.map_congr_left
  intro i hi
  exact flipL_flipL i (hw i hi)

theorem inRange_flip {r : ℕ} (w : Word n) (hw : InRange n r w) :
    InRange n r (w.map (flipL n r)) := by
  intro i hi
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
  exact flipL_range j (hw j hj)

theorem flipMarkedR_flipMarkedR {r : ℕ} (m : Marked n)
    (hm : InRange n r (erase m)) : flipMarkedR n r (flipMarkedR n r m) = m := by
  simp only [flipMarkedR, List.map_map]
  conv_rhs => rw [← List.map_id m]
  apply List.map_congr_left
  intro a ha
  have := hm a.1 (List.mem_map.mpr ⟨a, ha, rfl⟩)
  simp [flipL_flipL a.1 this]

theorem hybrid_flipR {r : ℕ} (h : r ≤ n+1) (m : Marked n) (hm : InRange n r (erase m))
    (f : SkewPolynomial (n+2)) :
    ∃ c : ℤ, c * c = 1 ∧ hybrid (flipMarkedR n r m) (psi n r h f) = c • psi n r h (hybrid m f) := by
  induction m with
  | nil => exact ⟨1, by norm_num, by simp [flipMarkedR, hybrid]⟩
  | cons a m ih =>
      rcases a with ⟨i, b⟩
      have hi : n+1-r ≤ i.val := hm i (by simp [erase])
      have hm' : InRange n r (erase m) := fun j hj => hm j (by simp [erase] at hj ⊢; exact Or.inr hj)
      obtain ⟨c, hc, e⟩ := ih hm'
      cases b
      · refine ⟨c, hc, ?_⟩
        simp only [flipMarkedR, List.map_cons, hybrid, if_true, if_false,
          Bool.false_eq_true] at e ⊢
        rw [e, map_zsmul, psi_s h i hi]
      · refine ⟨c * epsR n r h, ?_, ?_⟩
        · calc c * epsR n r h * (c * epsR n r h) = (c * c) * (epsR n r h * epsR n r h) := by ring
            _ = 1 := by rw [hc, epsR_sq, one_mul]
        · simp only [flipMarkedR, List.map_cons, hybrid, if_true, if_false,
            Bool.false_eq_true] at e ⊢
          rw [e, map_zsmul, psi_divided h i hi, smul_smul]

theorem simple_flipL {r : ℕ} (h : r ≤ n+1) (i : Fin (n+1)) (hi : n+1-r ≤ i.val) :
    simple (flipL n r i) = rho n r h * simple i * rho n r h := by
  simp only [simple]
  rw [rho_mul_swap h i hi, mul_assoc, rho_rho, mul_one]

theorem permutation_flipL {r : ℕ} (h : r ≤ n+1) (w : Word n) (hw : InRange n r w) :
    permutation (w.map (flipL n r)) = rho n r h * permutation w * rho n r h := by
  induction w with
  | nil => simp only [List.map_nil, permutation, mul_one, rho_rho]
  | cons i w ih =>
      have hi : n+1-r ≤ i.val := hw i (by simp)
      have hw' : InRange n r w := fun j hj => hw j (by simp [hj])
      simp only [List.map_cons, permutation, ih hw', simple_flipL h i hi]
      calc rho n r h * simple i * rho n r h * (rho n r h * permutation w * rho n r h)
          = rho n r h * simple i * (rho n r h * rho n r h) * permutation w * rho n r h := by
            simp only [mul_assoc]
        _ = _ := by rw [rho_rho, mul_one]; simp only [mul_assoc]

theorem permutation_fix_low {r : ℕ} (w : Word n) (hw : InRange n r w) (x : Fin (n+2))
    (hx : x.val < n+1-r) : permutation w x = x := by
  induction w with
  | nil => rfl
  | cons i w ih =>
      have hi : n+1-r ≤ i.val := hw i (by simp)
      have hw' : InRange n r w := fun j hj => hw j (by simp [hj])
      change simple i (permutation w x) = x
      rw [ih hw', simple]
      apply Equiv.swap_apply_of_ne_of_ne
      · intro e; have := congrArg Fin.val e; simp at this; omega
      · intro e; have := congrArg Fin.val e; simp at this; omega

/-- Inversion number is invariant under conjugation by the top reversal, for
permutations fixing the lower strands. -/
theorem length_conj_rho {r : ℕ} (h : r ≤ n+1) (p : Perm n)
    (hp : ∀ x : Fin (n+2), x.val < n+1-r → p x = x) :
    length (rho n r h * p * rho n r h) = length p := by
  classical
  have hpr : ∀ x : Fin (n+2), n+1-r ≤ x.val → n+1-r ≤ (p x).val := by
    intro x hx
    by_contra hc
    have e := hp (p x) (by omega)
    have := p.injective e
    rw [this] at hc
    omega
  have key : ∀ a b : Fin (n+2),
      (if rho n r h a < rho n r h b ∧
          (rho n r h * p * rho n r h) (rho n r h b) < (rho n r h * p * rho n r h) (rho n r h a)
        then (1 : ℕ) else 0) = (if b < a ∧ p a < p b then 1 else 0) := by
    intro a b
    simp only [Equiv.Perm.mul_apply, rho_apply_rho, Fin.lt_iff_val_lt_val, rho_val]
    have ha := a.isLt; have hb := b.isLt
    have hpa := (p a).isLt; have hpb := (p b).isLt
    by_cases ha' : a.val < n+1-r <;> by_cases hb' : b.val < n+1-r
    · have e1 := hp a ha'; have e2 := hp b hb'
      rw [e1, e2]; split_ifs <;> omega
    · have e1 := hp a ha'; have e2 := hpr b (by omega)
      rw [e1]; split_ifs <;> omega
    · have e1 := hpr a (by omega); have e2 := hp b hb'
      rw [e2]; split_ifs <;> omega
    · have e1 := hpr a (by omega); have e2 := hpr b (by omega)
      split_ifs <;> omega
  unfold length
  have step1 : (∑ a : Fin (n+2), ∑ b : Fin (n+2),
      if a < b ∧ (rho n r h * p * rho n r h) b < (rho n r h * p * rho n r h) a
        then (1 : ℕ) else 0) =
      ∑ a : Fin (n+2), ∑ b : Fin (n+2),
        if rho n r h a < rho n r h b ∧
          (rho n r h * p * rho n r h) (rho n r h b) < (rho n r h * p * rho n r h) (rho n r h a)
        then (1 : ℕ) else 0 :=
    (Equiv.sum_comp (rho n r h) (fun a => ∑ b : Fin (n+2),
        if a < b ∧ (rho n r h * p * rho n r h) b < (rho n r h * p * rho n r h) a
          then (1 : ℕ) else 0)).symm.trans
      (Finset.sum_congr rfl fun a _ => (Equiv.sum_comp (rho n r h) (fun b =>
        if rho n r h a < b ∧
          (rho n r h * p * rho n r h) b < (rho n r h * p * rho n r h) (rho n r h a)
        then (1 : ℕ) else 0)).symm)
  calc _ = _ := step1
    _ = ∑ a : Fin (n+2), ∑ b : Fin (n+2), (if b < a ∧ p a < p b then (1 : ℕ) else 0) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => key a b
    _ = _ := Finset.sum_comm

theorem reduced_flipL {r : ℕ} (h : r ≤ n+1) (w : Word n) (hw : InRange n r w) :
    Reduced (w.map (flipL n r)) ↔ Reduced w := by
  unfold Reduced
  rw [permutation_flipL h w hw, length_conj_rho h _ (permutation_fix_low w hw), List.length_map]

theorem omission_subset (m : Marked n) {i : Fin (n+1)} (hi : i ∈ omission m) : i ∈ erase m := by
  induction m with
  | nil => simp [omission] at hi
  | cons a m ih =>
      rcases a with ⟨j, b⟩
      cases b
      · simp only [omission, Bool.false_eq_true, if_false, List.mem_cons] at hi
        rcases hi with rfl | hi
        · simp
        · simp [ih hi]
      · simp only [omission, if_true] at hi
        simp [ih hi]

/-- The signed partial reversal transports the relative property. -/
theorem relOWL_flip {r : ℕ} (h : r ≤ n+1) (v : Word n) (hvr : InRange n r v)
    (hv : RelOWL n r v) : RelOWL n r (v.map (flipL n r)) := by
  intro m he hred
  have hmr : InRange n r (erase m) := by rw [he]; exact inRange_flip v hvr
  have he' : erase (flipMarkedR n r m) = v := by
    rw [erase_flipR, he, map_flipL_flipL v hvr]
  have hm'r : InRange n r (erase (flipMarkedR n r m)) := by rw [he']; exact hvr
  have hback : flipMarkedR n r (flipMarkedR n r m) = m := flipMarkedR_flipMarkedR m hmr
  have hom : InRange n r (omission (flipMarkedR n r m)) := by
    intro i hi
    apply hm'r i
    exact omission_subset _ hi
  have hred' : Reduced (omission (flipMarkedR n r m)) := by
    rw [← reduced_flipL h _ hom, ← omission_flipR, hback]
    exact hred
  rcases hv _ he' hred' with hz | hf
  · left
    intro g hg
    obtain ⟨c, -, hc⟩ := hybrid_flipR h (flipMarkedR n r m) hm'r (psi n r h g)
    rw [hback, psi_psi] at hc
    rw [hc, hz _ (psi_relKernel h hg), map_zero, smul_zero]
  · right
    rw [← hback, hf]
    simp [flipMarkedR, allFalse, Function.comp_def]

/-! ### The stage family -/

/-- Words built from the empty word by prepending the next descending chain
`n, n-1, ..., n-r` and by the signed partial reversal of the occupied top strands. -/
inductive Stage (n : ℕ) : ℕ → Word n → Prop
  | nil : Stage n 0 []
  | chain (r : ℕ) (hr : r+1 ≤ n+1) {v : Word n} :
      Stage n r v → Stage n (r+1) (down n (n-r) (r+1) (by omega) ++ v)
  | flip {r : ℕ} {v : Word n} : Stage n r v → Stage n r (v.map (flipL n r))

theorem stage_invariant {r : ℕ} {v : Word n} (hs : Stage n r v) :
    ∃ h : r ≤ n+1, InRange n r v ∧ permutation v = rho n r h ∧ RelOWL n r v := by
  induction hs with
  | nil =>
    refine ⟨by omega, fun i hi => by simp at hi, rfl, ?_⟩
    intro m he _
    right
    have : m = [] := by simpa [erase] using he
    simp [this, allFalse]
  | chain r hr hs ih =>
    obtain ⟨h, hin, hp, hrel⟩ := ih
    refine ⟨hr, ?_, ?_, relOWL_step hr _ hp hrel⟩
    · intro i hi
      rcases List.mem_append.mp hi with hi | hi
      · have := down_mem hi; omega
      · have := hin i hi; omega
    · rw [permutation_append, hp, rho, rho]
      change _ = permutation (down n (n-r) (r+1) (by omega) ++ blocks n r (by omega))
      rw [permutation_append]
  | flip hs ih =>
    rename_i r v
    obtain ⟨h, hin, hp, hrel⟩ := ih
    refine ⟨h, inRange_flip v hin, ?_, relOWL_flip h v hin hrel⟩
    rw [permutation_flipL h v hin, hp, rho_rho, one_mul]

theorem stage_length {r : ℕ} {v : Word n} (hs : Stage n r v) :
    ∃ h : r ≤ n+1, v.length = (blocks n r h).length := by
  induction hs with
  | nil => exact ⟨by omega, rfl⟩
  | chain r hr hs ih =>
    obtain ⟨h, hl⟩ := ih
    refine ⟨hr, ?_⟩
    change _ = (down n (n-r) (r+1) (by omega) ++ blocks n r (by omega)).length
    simp only [List.length_append, down_length, hl]
  | flip hs ih =>
    obtain ⟨h, hl⟩ := ih
    exact ⟨h, by rw [List.length_map, hl]⟩

theorem stage_blocks (r : ℕ) (h : r ≤ n+1) : Stage n r (blocks n r h) := by
  induction r with
  | zero => exact Stage.nil
  | succ r ih => exact Stage.chain r h (ih (by omega))

theorem flipL_top (i : Fin (n+1)) : flipL n (n+1) i = i.rev := by
  apply Fin.ext
  rw [flipL_val i (by omega), Fin.val_rev]
  omega

/-- A full-stage word satisfies the literal termwise trichotomy for every marking. -/
theorem owl_of_stage (w : Word n) (hs : Stage n (n+1) w) : OwlBraid.OWLFor w := by
  obtain ⟨_, _, _, hrel⟩ := stage_invariant hs
  intro m hm
  rw [mem_markings] at hm
  by_cases hr : Reduced (omission m)
  · rcases hrel m hm hr with hz | ha
    · left
      intro f hf
      apply hz f
      intro i _
      exact (OddSymmetricKernel.mem_kernelSubring f).mp hf i
    · right; left
      rw [all_false_iff, hm]
      exact ha
  · right; right; exact hr

theorem permutation_of_stage (w : Word n) (hs : Stage n (n+1) w) :
    permutation w = LongestElementary.longest (n+2) := by
  obtain ⟨h, _, hp, _⟩ := stage_invariant hs
  rw [hp, rho, ← word_blocks, word_permutation]

end
end OddMath.Frontier.OwlGeneralStage
