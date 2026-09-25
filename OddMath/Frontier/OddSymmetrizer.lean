import OddMath.Frontier.LongestKernel
import OddMath.Frontier.LongestElementary
import OddMath.Frontier.IntervalAnnihilation

/-! Literal EKL (2.57), (2.64), Corollary 2.22. Fixed-word proof, not OWL. -/
namespace OddMath.Frontier.OddSymmetrizer
open OddMath.SkewPolynomial (SkewPolynomial generator monomial)
open LongestDivided SignedPermutation
noncomputable section

/-- Reversal of an initial segment, fixing the remaining alphabet. -/
def revAt (N k : ℕ) (hk : k ≤ N) (i : Fin N) : Fin N :=
  ⟨if i.val < k then k-1-i.val else i.val, by split <;> have := i.isLt <;> omega⟩

theorem revAt_twice (N k : ℕ) (hk : k ≤ N) (i : Fin N) :
    revAt N k hk (revAt N k hk i) = i := by
  apply Fin.ext
  simp only [revAt]
  split_ifs <;> omega

def revPerm (N k : ℕ) (hk : k ≤ N) : Equiv.Perm (Fin N) :=
  ⟨revAt N k hk, revAt N k hk, revAt_twice N k hk, revAt_twice N k hk⟩

@[simp] theorem revPerm_val (N k : ℕ) (hk : k ≤ N) (i : Fin N) :
    (revPerm N k hk i).val = if i.val < k then k-1-i.val else i.val := rfl

@[simp] theorem revPerm_inv (N k : ℕ) (hk : k ≤ N) :
    (revPerm N k hk)⁻¹ = revPerm N k hk := rfl

theorem revPerm_zero (N : ℕ) : revPerm N 0 (by omega) = 1 := by
  ext i
  simp

theorem revPerm_full (N : ℕ) : revPerm N N le_rfl = LongestElementary.longest N := by
  ext i
  change (if i.val < N then N-1-i.val else i.val) = N-(i.val+1)
  rw [if_pos i.isLt]
  omega

/-- The ascending simple-transposition block as an actual permutation. -/
def rot (N k : ℕ) (hk : k+1 ≤ N) : Equiv.Perm (Fin N) :=
  revPerm N (k+1) hk * revPerm N k (by omega)

theorem rot_val (N k : ℕ) (hk : k+1 ≤ N) (i : Fin N) :
    (rot N k hk i).val = if i.val < k then i.val+1 else if i.val = k then 0 else i.val := by
  simp only [rot, Equiv.Perm.mul_apply, revPerm_val]
  split_ifs <;> omega

theorem rot_zero (N : ℕ) (h : 1 ≤ N) : rot N 0 h = 1 := by
  ext i
  simp only [rot_val, Equiv.Perm.one_apply]
  split_ifs <;> omega

theorem rot_succ (n k : ℕ) (hk : k+2 ≤ n+2) :
    rot (n+2) (k+1) hk = rot (n+2) k (by omega) *
      Equiv.swap (⟨k, by omega⟩ : Fin (n+2)) ⟨k+1, by omega⟩ := by
  apply Equiv.ext
  intro i
  apply Fin.ext
  by_cases h₀ : i = (⟨k, by omega⟩ : Fin (n+2))
  · subst i
    simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left, rot_val, Fin.val_mk]
    split_ifs <;> omega
  by_cases h₁ : i = (⟨k+1, by omega⟩ : Fin (n+2))
  · subst i
    simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_right, rot_val, Fin.val_mk]
    split_ifs <;> omega
  have hv₀ : i.val ≠ k := fun h => h₀ (Fin.ext h)
  have hv₁ : i.val ≠ k+1 := fun h => h₁ (Fin.ext h)
  simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne h₀ h₁, rot_val]
  split_ifs <;> omega

/-- Covariance for a genuine signed permutation; consumed only by the fixed block proof. -/
theorem pair_covariance {n : ℕ} (σ : Equiv.Perm (Fin (n+2)))
    (a b : Fin (n+2)) (hab : a ≠ b) (f : SkewPolynomial (n+2)) :
    NonadjacentDivided.dividedPair a b hab (skewAction σ f) =
      epsilon σ • skewAction σ (NonadjacentDivided.dividedPair
        (σ⁻¹ a) (σ⁻¹ b) (σ⁻¹.injective.ne hab) f) := by
  have hc (g : SkewPolynomial (n+2)) :
      NonadjacentDivided.s a b (skewAction σ g) =
        skewAction σ (NonadjacentDivided.s (σ⁻¹ a) (σ⁻¹ b) g) := by
    have hp : Equiv.swap a b * σ = σ * Equiv.swap (σ⁻¹ a) (σ⁻¹ b) := by
      apply Equiv.ext
      intro i
      simpa only [Equiv.Perm.mul_apply, Equiv.Perm.apply_inv_self] using
        (σ.injective.map_swap (σ⁻¹ a) (σ⁻¹ b) i).symm
    simpa only [NonadjacentDivided.s, action_mul] using
      congrArg (fun p => skewAction p g) hp
  induction f using NonadjacentDivided.polynomial_induction with
  | hconst r => simp only [map_zsmul, map_smul, map_one,
      NonadjacentDivided.divided_one, smul_zero, map_zero]
  | hgen j =>
      rw [action_generator, map_smul, NonadjacentDivided.divided_generator,
        NonadjacentDivided.divided_generator]
      have ha : σ j = a ↔ j = σ⁻¹ a := σ.apply_eq_iff_eq_symm_apply
      have hb : σ j = b ↔ j = σ⁻¹ b := σ.apply_eq_iff_eq_symm_apply
      simp only [ha, hb]
      split_ifs <;> simp
  | hadd f g hf hg => simp only [map_add, hf, hg, smul_add]
  | hmul f g hf hg =>
      simp only [map_mul, NonadjacentDivided.divided_mul, map_add, hf, hg, hc,
        smul_add, smul_mul_assoc, mul_smul_comm]

/-- A disjoint nonadjacent derivative can be moved through the reverse interval. -/
theorem sweep_pair_zero (n p k : ℕ) (hb : p+k ≤ n+1)
    (u v : Fin (n+2)) (huv : u ≠ v)
    (hd : ∀ j : Fin (n+1), p ≤ j.val → j.val < p+k →
      j.castSucc ≠ u ∧ j.castSucc ≠ v ∧ j.succ ≠ u ∧ j.succ ≠ v)
    (f : SkewPolynomial (n+2)) (hf : sweep n p k f = 0) :
    sweep n p k (NonadjacentDivided.dividedPair u v huv f) = 0 := by
  induction k generalizing p f with
  | zero =>
      change f = 0 at hf
      simp only [sweep, LinearMap.id_apply, hf, map_zero]
  | succ k ih =>
      let i : Fin (n+1) := ⟨p, by omega⟩
      obtain ⟨h₁,h₂,h₃,h₄⟩ := hd i (by rfl) (by dsimp [i]; omega)
      have hc (g : SkewPolynomial (n+2)) :
          cross n p (NonadjacentDivided.dividedPair u v huv g) =
            -NonadjacentDivided.dividedPair u v huv (cross n p g) := by
        simp only [cross, dif_pos (show p < n+1 by omega)]
        rw [← NonadjacentDivided.adjacent i]
        exact NonadjacentDivided.anticommutation _ _ _ _ _ huv h₁ h₂ h₃ h₄ g
      change sweep n (p+1) k (cross n p (NonadjacentDivided.dividedPair u v huv f)) = 0
      rw [hc, map_neg]
      apply neg_eq_zero.mpr
      exact ih (p+1) (by omega) (fun j hj hj' => hd j (by omega) (by omega))
        (cross n p f) hf

/-- Mirror of EKL (2.62), proved directly from the same triangle relation.
Consumer: the error tails in the fixed longest-word Leibniz expansion. -/
theorem reverse_interval_zero (n p k : ℕ) (hv : p+k+1 < n+2)
    (f : SkewPolynomial (n+2)) (hf : f ∈ OddSymmetricKernel.kernelSubring n) :
    sweep n p k (NonadjacentDivided.dividedPair
      ⟨p, by omega⟩ ⟨p+k+1, hv⟩ (by intro h; have := congrArg Fin.val h; simp only [Fin.val_mk] at this; omega) f) = 0 := by
  induction k generalizing p with
  | zero =>
      change NonadjacentDivided.dividedPair
        (⟨p, by omega⟩ : Fin (n+1)).castSucc (⟨p, by omega⟩ : Fin (n+1)).succ _ f = 0
      rw [NonadjacentDivided.adjacent (⟨p, by omega⟩ : Fin (n+1))]
      exact hf _
  | succ k ih =>
      let a : Fin (n+2) := ⟨p, by omega⟩
      let b : Fin (n+2) := ⟨p+1, by omega⟩
      let c : Fin (n+2) := ⟨p+(k+1)+1, hv⟩
      have hab : a ≠ b := by intro h; have := congrArg Fin.val h; dsimp [a,b] at this; omega
      have hac : a ≠ c := by intro h; have := congrArg Fin.val h; dsimp [a,c] at this; omega
      have hbc : b ≠ c := by intro h; have := congrArg Fin.val h; dsimp [b,c] at this; omega
      have ha : NonadjacentDivided.dividedPair b a hab.symm = cross n p := by
        rw [NonadjacentDivided.symmetric]
        simp only [cross, dif_pos (show p < n+1 by omega)]
        exact NonadjacentDivided.adjacent ⟨p, by omega⟩
      have ht := IntervalAnnihilation.triangle c b a hbc.symm hac.symm hab.symm f
      rw [ha, NonadjacentDivided.symmetric c a, NonadjacentDivided.symmetric c b] at ht
      have hp : cross n p f = 0 := by
        simp only [cross, dif_pos (show p < n+1 by omega)]
        exact hf _
      rw [hp, map_zero, add_zero] at ht
      change sweep n (p+1) k (cross n p (NonadjacentDivided.dividedPair a c hac f)) = 0
      rw [eq_neg_of_add_eq_zero_left ht, map_neg]
      apply neg_eq_zero.mpr
      apply sweep_pair_zero n (p+1) k (by omega) a c hac
      · intro j hj hj'
        dsimp [a,c]
        repeat' constructor
        all_goals intro h; have := congrArg Fin.val h
        all_goals simp only [Fin.coe_castSucc, Fin.val_succ, Fin.val_mk] at this
        all_goals omega
      · simpa only [b, c, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ih (p+1) (by omega)

/-- Ascending block; consumer of all helpers below is `D_left_kernel`. -/
def up (n k : ℕ) := actNat n (List.range k)

@[simp] theorem up_zero (n : ℕ) (f : SkewPolynomial (n+2)) : up n 0 f = f := rfl

theorem up_succ (n k : ℕ) (f : SkewPolynomial (n+2)) :
    up n (k+1) f = up n k (cross n k f) := by
  simp [up, List.range_succ, actNat_append, actNat]

theorem act_right_killed (n : ℕ) (w : List ℕ) (hw : ∀ i ∈ w, i < n+1)
    (f h : SkewPolynomial (n+2)) (hh : ∀ i ∈ w, cross n i h = 0) :
    actNat n w (f*h) = actNat n w f * h := by
  induction w with
  | nil => rfl
  | cons i w ih =>
      change cross n i (actNat n w (f*h)) = cross n i (actNat n w f) * h
      rw [ih (fun j hj => hw j (by simp [hj])) (fun j hj => hh j (by simp [hj])),
        cross_mul n i (hw i (by simp)), hh i (by simp), mul_zero, add_zero]

theorem up_right_killed (n k : ℕ) (hk : k ≤ n+1)
    (f h : SkewPolynomial (n+2)) (hh : ∀ i < k, cross n i h = 0) :
    up n k (f*h) = up n k f * h :=
  act_right_killed n (List.range k)
    (by intro i hi; have := List.mem_range.mp hi; omega) f h
    (fun i hi => hh i (List.mem_range.mp hi))

/-- A triangular Leibniz expansion: all non-main terms are explicit vanishing tails.
This lemma assumes only those tails, not OWL or any word-reduction conclusion. -/
theorem block_mul (n k : ℕ) (hk : k+1 ≤ n+2) (f h : SkewPolynomial (n+2))
    (hh : ∀ i, i+1 < k → cross n i h = 0)
    (hf : ∀ j (hj : j < k), up n (j+1)
      (skewAction ((rot (n+2) (j+1) (by omega))⁻¹ * rot (n+2) k hk) f) = 0) :
    up n k (f*h) = skewAction (rot (n+2) k hk) f * up n k h := by
  induction k generalizing f h with
  | zero => simp only [up_zero, rot_zero, action_one]
  | succ k ih =>
      have hb : k < n+1 := by omega
      let τ := Equiv.swap (⟨k, by omega⟩ : Fin (n+2)) ⟨k+1, by omega⟩
      have hs (g : SkewPolynomial (n+2)) :
          AllRankDivided.s (⟨k,hb⟩ : Fin (n+1)) g = skewAction τ g := rfl
      have hz : up n (k+1) f = 0 := by
        simpa only [inv_mul_cancel, action_one] using hf k (by omega)
      rw [up_succ, cross_mul n k hb, map_add,
        up_right_killed n k (by omega) _ h (fun i hi => hh i (by omega)), ← up_succ,
        hz, zero_mul, zero_add, hs]
      rw [ih (by omega) (skewAction τ f) (cross n k h)]
      · rw [← action_mul, ← rot_succ, ← up_succ]
      · intro i hi
        rw [LongestKernel.cross_distant n i k (by omega) hb (Or.inl hi),
          hh i (by omega), map_zero, neg_zero]
      · intro j hj
        have ht := hf j (by omega)
        rw [rot_succ n k hk, ← mul_assoc, action_mul] at ht
        exact ht

/-- The exact scalar generated by distant interchanges of triangular blocks. -/
def turnSign : ℕ → ℤ
  | 0 => 1
  | k+1 => turnSign k * (-1 : ℤ)^(coxeterWord k).length

/-- Rewrite ONLY the fixed source longest word. No arbitrary reduced-word law. -/
theorem word_up (n k : ℕ) (hk : k+1 ≤ n+2) (f : SkewPolynomial (n+2)) :
    actNat n (coxeterWord (k+1)) f =
      turnSign k • up n k (actNat n (coxeterWord k) f) := by
  induction k generalizing f with
  | zero => simp [coxeterWord, actNat, turnSign, up]
  | succ k ih =>
      rw [coxeterWord, actNat_append, ih (by omega)]
      change turnSign k • up n k
        (actNat n (coxeterWord k) (LongestKernel.down n (k+1) f)) = _
      rw [LongestKernel.down_succ]
      have hm (g : SkewPolynomial (n+2)) :
          actNat n (coxeterWord k) (cross n k g) =
            (-1 : ℤ)^(coxeterWord k).length • cross n k (actNat n (coxeterWord k) g) := by
        rw [LongestKernel.cross_word n k (coxeterWord k) (by omega)
          (fun j hj => coxeterWord_bound hj), smul_smul, ← mul_pow]
        norm_num
      rw [hm, map_smul, smul_smul, ← up_succ, coxeterWord, actNat_append]
      rfl

/-- Transport an adjacent crossing whose endpoints are reversed by σ. -/
theorem cross_covariance (n i u : ℕ) (hi : i < n+1) (hu : u < n+1)
    (σ : Equiv.Perm (Fin (n+2)))
    (h₀ : σ⁻¹ (⟨i, by omega⟩ : Fin (n+2)) = ⟨u+1, by omega⟩)
    (h₁ : σ⁻¹ (⟨i+1, by omega⟩ : Fin (n+2)) = ⟨u, by omega⟩)
    (f : SkewPolynomial (n+2)) :
    cross n i (skewAction σ f) = epsilon σ • skewAction σ (cross n u f) := by
  simp only [cross, dif_pos hi, dif_pos hu]
  rw [← NonadjacentDivided.adjacent (⟨i,hi⟩ : Fin (n+1)), pair_covariance]
  change epsilon σ • skewAction σ
    (NonadjacentDivided.dividedPair (σ⁻¹ ⟨i, by omega⟩) (σ⁻¹ ⟨i+1, by omega⟩) _ f) = _
  simp only [h₀, h₁]
  rw [NonadjacentDivided.symmetric]
  exact congrArg (fun T : SkewPolynomial (n+2) →ₗ[ℤ] SkewPolynomial (n+2) =>
    epsilon σ • skewAction σ (T f)) (NonadjacentDivided.adjacent (⟨u,hu⟩ : Fin (n+1)))

/-- A reversed interval is the exact conjugate of the ascending prefix. -/
theorem up_covariance (n r t : ℕ) (ht : t < n+2) (hr : r ≤ t)
    (σ : Equiv.Perm (Fin (n+2)))
    (hσ : ∀ i (hi : i ≤ r), σ⁻¹ (⟨i, by omega⟩ : Fin (n+2)) = ⟨t-i, by omega⟩)
    (f : SkewPolynomial (n+2)) :
    up n r (skewAction σ f) =
      (epsilon σ)^r • skewAction σ (sweep n (t-r) r f) := by
  induction r generalizing f with
  | zero => simp only [up_zero, pow_zero, sweep, LinearMap.id_apply, one_smul]
  | succ r ih =>
      have he₀ : t-r = (t-(r+1))+1 := by omega
      have hc := cross_covariance n r (t-(r+1)) (by omega) (by omega) σ
        (by simpa only [he₀] using hσ r (by omega))
        (hσ (r+1) le_rfl) f
      rw [up_succ, hc, map_smul, ih (by omega) (fun i hi => hσ i (by omega)),
        smul_smul, pow_succ', he₀]
      rfl

/-- Every omitted-left Leibniz tail vanishes by the proved reverse interval law. -/
theorem tail_zero (n k j : ℕ) (hk : k+1 ≤ n+2) (hj : j < k)
    (f : SkewPolynomial (n+2)) (hf : f ∈ OddSymmetricKernel.kernelSubring n) :
    up n (j+1) (skewAction
      ((rot (n+2) (j+1) (by omega))⁻¹ * revPerm (n+2) (k+1) hk) f) = 0 := by
  let σ := (rot (n+2) (j+1) (by omega))⁻¹ * revPerm (n+2) (k+1) hk
  have hlo (i : ℕ) (hi : i ≤ j) :
      σ⁻¹ (⟨i, by omega⟩ : Fin (n+2)) = ⟨k-1-i, by omega⟩ := by
    apply Fin.ext
    simp only [σ, mul_inv_rev, inv_inv, revPerm_inv, Equiv.Perm.mul_apply,
      revPerm_val, rot_val, Fin.val_mk]
    split_ifs <;> omega
  have hedge : σ⁻¹ (⟨j+1, by omega⟩ : Fin (n+2)) = ⟨k, by omega⟩ := by
    apply Fin.ext
    simp only [σ, mul_inv_rev, inv_inv, revPerm_inv, Equiv.Perm.mul_apply,
      revPerm_val, rot_val, Fin.val_mk]
    split_ifs <;> omega
  let u : Fin (n+2) := ⟨k-1-j, by omega⟩
  let v : Fin (n+2) := ⟨k, by omega⟩
  have huv : u ≠ v := by intro h; have := congrArg Fin.val h; dsimp [u,v] at this; omega
  have hc : cross n j (skewAction σ f) =
      epsilon σ • skewAction σ (NonadjacentDivided.dividedPair u v huv f) := by
    simp only [cross, dif_pos (show j < n+1 by omega)]
    rw [← NonadjacentDivided.adjacent (⟨j, by omega⟩ : Fin (n+1)), pair_covariance]
    change epsilon σ • skewAction σ
      (NonadjacentDivided.dividedPair (σ⁻¹ ⟨j, by omega⟩) (σ⁻¹ ⟨j+1, by omega⟩) _ f) = _
    simp only [hlo j le_rfl, hedge]
    rfl
  change up n (j+1) (skewAction σ f) = 0
  rw [up_succ, hc, map_smul, up_covariance n j (k-1) (by omega) (by omega) σ hlo]
  have hz : sweep n (k-1-j) j (NonadjacentDivided.dividedPair u v huv f) = 0 := by
    have he : k-1-j+j+1 = k := by omega
    simpa only [he] using reverse_interval_zero n (k-1-j) j (by omega) f hf
  rw [hz, map_zero, smul_zero, smul_zero]

/-- Twisted left linearity for each concrete longest prefix in the fixed alphabet.
The hypotheses are only membership in the actual common kernel. -/
theorem word_left_kernel (n k : ℕ) (hk : k ≤ n+2)
    (f g : SkewPolynomial (n+2)) (hf : f ∈ OddSymmetricKernel.kernelSubring n) :
    actNat n (coxeterWord k) (f*g) =
      skewAction (revPerm (n+2) k hk) f * actNat n (coxeterWord k) g := by
  induction k with
  | zero => simp only [coxeterWord, actNat, LinearMap.id_apply, revPerm_zero, action_one]
  | succ k ih =>
      have hp : rot (n+2) k hk * revPerm (n+2) k (by omega) =
          revPerm (n+2) (k+1) hk := by
        have hh := inv_mul_cancel (revPerm (n+2) k (show k ≤ n+2 by omega))
        simp only [revPerm_inv] at hh
        rw [rot, mul_assoc, hh, mul_one]
      rw [word_up n k hk, ih (by omega), block_mul n k hk]
      · rw [← action_mul, hp, ← mul_smul_comm, ← word_up n k hk]
      · intro i hi
        exact LongestKernel.word_killed n k (by omega) i hi g
      · intro j hj
        rw [← action_mul, mul_assoc, hp]
        exact tail_zero n k j hk hj f hf

/-- EKL (2.64), with the literal source D, no OWL/reduced-word premise. -/
theorem D_left_kernel (n : ℕ) (f g : SkewPolynomial (n+2))
    (hf : f ∈ OddSymmetricKernel.kernelSubring n) :
    D (n+2) (f*g) = skewAction (LongestElementary.longest (n+2)) f * D (n+2) g := by
  simpa only [D_eq_actNat, revPerm_full] using word_left_kernel n (n+2) le_rfl f g hf

/-- Literal EKL (2.57): RIGHT staircase multiplication, then D, then w0.
This is deliberately not `LongestKernel.rightRetraction`. Domain rank is n+2. -/
def S (n : ℕ) : SkewPolynomial (n+2) →ₗ[ℤ] SkewPolynomial (n+2) where
  toFun f := (-1 : ℤ)^((n+2).choose 3) •
    skewAction (LongestElementary.longest (n+2)) (D (n+2) (f * staircase (n+2)))
  map_add' f g := by simp only [add_mul, map_add, smul_add]
  map_smul' z f := by
    simp only [smul_mul_assoc, map_smul, map_zsmul, RingHom.id_apply]
    exact smul_comm _ _ _

@[simp] theorem S_apply (n : ℕ) (f : SkewPolynomial (n+2)) :
    S n f = (-1 : ℤ)^((n+2).choose 3) •
      skewAction (LongestElementary.longest (n+2)) (D (n+2) (f * staircase (n+2))) := rfl

/-- The literal source operator lands in the actual common divided kernel. -/
theorem S_mem_kernel (n : ℕ) (f : SkewPolynomial (n+2)) :
    S n f ∈ OddSymmetricKernel.kernelSubring n :=
  (OddSymmetricKernel.kernelSubring n).zsmul_mem
    (LongestElementary.action_mem_kernel n _ (LongestKernel.D_mem_kernel n _)) _

/-- Correct reading of the argument at printed (2.65): S(f)=f for f in the kernel.
The printed extra staircase in its leftmost S argument is inconsistent with (2.57). -/
theorem S_eq_self (n : ℕ) (f : SkewPolynomial (n+2))
    (hf : f ∈ OddSymmetricKernel.kernelSubring n) : S n f = f := by
  rw [S_apply, D_left_kernel n f _ hf, D_staircase, mul_smul_comm, mul_one,
    map_zsmul, LongestElementary.action_involutive, smul_smul, ← mul_pow]
  norm_num

/-- Corollary 2.22: actual left OΛ-linearity, in the noncommutative order. -/
theorem S_left_kernel (n : ℕ) (f g : SkewPolynomial (n+2))
    (hf : f ∈ OddSymmetricKernel.kernelSubring n) : S n (f*g) = f * S n g := by
  rw [S_apply, mul_assoc, D_left_kernel n f _ hf, map_mul,
    LongestElementary.action_involutive, ← mul_smul_comm]
  rfl

/-- Corollary 2.22: genuine idempotence on every input. -/
theorem S_idempotent (n : ℕ) (f : SkewPolynomial (n+2)) : S n (S n f) = S n f :=
  S_eq_self n _ (S_mem_kernel n f)

/-- Exact image, rather than just inclusion in the source target. -/
theorem S_range_kernel (n : ℕ) (f : SkewPolynomial (n+2)) :
    f ∈ LinearMap.range (S n) ↔ f ∈ OddSymmetricKernel.kernelSubring n := by
  constructor
  · rintro ⟨g, rfl⟩
    exact S_mem_kernel n g
  · intro hf
    exact ⟨f, S_eq_self n f hf⟩

theorem S_image (n : ℕ) : Set.range (S n) =
    (OddSymmetricKernel.kernelSubring n : Set (SkewPolynomial (n+2))) := by
  ext f
  exact S_range_kernel n f

theorem S_fixed_iff (n : ℕ) (f : SkewPolynomial (n+2)) :
    S n f = f ↔ f ∈ OddSymmetricKernel.kernelSubring n := by
  constructor
  · intro h
    rw [← h]
    exact S_mem_kernel n f
  · exact S_eq_self n f

/-- Partitions padded by zeros to the actual finite alphabet, as in EKL §2.3.1. -/
def PartitionExponent (n : ℕ) := {α : Fin (n+2) → ℕ // Antitone α}

/-- EKL Definition 2.24 (2.69), with the untilde ordered monomial.
No tableau comparison or Pieri identification is asserted here. -/
def schur (n : ℕ) (α : PartitionExponent n) : SkewPolynomial (n+2) :=
  S n (monomial α.val 1)

/-- The literal source Schur consumer is odd symmetric for every partition. -/
theorem schur_mem_kernel (n : ℕ) (α : PartitionExponent n) :
    schur n α ∈ OddSymmetricKernel.kernelSubring n := S_mem_kernel n _

theorem schur_fixed (n : ℕ) (α : PartitionExponent n) :
    S n (schur n α) = schur n α := S_idempotent n _

end
end OddMath.Frontier.OddSymmetrizer
