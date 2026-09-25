import OddMath.Frontier.OddSymmetrizer

/-! EKL1111.1320v1 Corollary 2.23, equation (2.66), pp.17–18.
The helpers prove the EXACT reflected-word identity, not an unspecified global
sign. All endomorphisms use the inherited operators on actual skew polynomials.
The only consumer of the interval/triangle helpers is longest covariance. -/
namespace OddMath.Frontier.LongestReversal
open OddMath.SkewPolynomial (SkewPolynomial)
open LongestDivided LongestElementary SignedPermutation
noncomputable section

/-- Ascending written interval; rightmost factor acts first. -/
def up (n p : ℕ) : ℕ → Module.End ℤ (SkewPolynomial (n+2))
  | 0 => 1
  | k+1 => cross n p * up n (p+1) k

/-- Descending written interval. -/
def down (n p : ℕ) : ℕ → Module.End ℤ (SkewPolynomial (n+2))
  | 0 => 1
  | k+1 => down n (p+1) k * cross n p

/-- The literal longest triangle in a consecutive subalphabet. -/
def triangle (n p : ℕ) : ℕ → Module.End ℤ (SkewPolynomial (n+2))
  | 0 => 1
  | k+1 => triangle n p k * down n p k

theorem up_last (n p k : ℕ) :
    up n p (k+1) = up n p k * cross n (p+k) := by
  induction k generalizing p with
  | zero => simp [up]
  | succ k ih =>
      change cross n p * up n (p+1) (k+1) =
        (cross n p * up n (p+1) k) * cross n (p+(k+1))
      rw [ih, mul_assoc]
      simp only [Nat.add_assoc, Nat.add_comm 1 k]

theorem down_last (n p k : ℕ) :
    down n p (k+1) = cross n (p+k) * down n p k := by
  induction k generalizing p with
  | zero => simp [down]
  | succ k ih =>
      change down n (p+1) (k+1) * cross n p =
        cross n (p+(k+1)) * (down n (p+1) k * cross n p)
      rw [ih, mul_assoc]
      simp only [Nat.add_assoc, Nat.add_comm 1 k]

/-- Endomorphism version of the inherited distant anti-commutation. -/
theorem cross_anti (n p q : ℕ) (hp : p < n+1) (hq : q < n+1)
    (hpq : p+1 < q) : cross n p * cross n q = -(cross n q * cross n p) := by
  apply LinearMap.ext
  intro f
  exact LongestKernel.cross_distant n p q hp hq (Or.inl hpq) f

/-- A pair of distant interchanges contributes two minus signs, hence +1. -/
theorem sandwich {R : Type*} [Ring R] (a b x : R) (h : a*b = -(b*a)) :
    a * (b*x*b) * a = b * (a*x*a) * b := by
  have h' : b*a = -(a*b) := by rw [h, neg_neg]
  calc
    _ = (a*b)*x*(b*a) := by simp only [mul_assoc]
    _ = (-(b*a))*x*(-(a*b)) := congrArg₂ (·*·) (congrArg (·*x) h) h'
    _ = _ := by simp only [neg_mul, mul_neg, neg_neg, mul_assoc]

/-- A hill with endpoints p and p+k. -/
def hill (n p : ℕ) : ℕ → Module.End ℤ (SkewPolynomial (n+2))
  | 0 => cross n p
  | k+1 => cross n p * hill n (p+1) k * cross n p

/-- The same reflection written starting from the opposite endpoint. -/
def valley (n p : ℕ) : ℕ → Module.End ℤ (SkewPolynomial (n+2))
  | 0 => cross n p
  | k+1 => cross n (p+k+1) * valley n p k * cross n (p+k+1)

/-- Exact reflection identity: braid has sign +; distant interchanges occur in pairs. -/
theorem hill_valley (n p k : ℕ) (hb : p+k < n+1) : hill n p k = valley n p k := by
  induction k using Nat.twoStepInduction generalizing p with
  | zero => rfl
  | one =>
      simp only [hill, valley, Nat.add_zero]
      apply LinearMap.ext
      intro f
      exact (LongestKernel.cross_braid n p (by omega) f).symm
  | more k ih0 ih1 =>
      rw [hill, ih1 (p+1) (by omega), valley]
      have he : p+1+k+1 = p+(k+1)+1 := by omega
      rw [he, sandwich _ _ _ (cross_anti n p _ (by omega) (by omega) (by omega)),
        ← ih0 (p+1) (by omega)]
      change cross n (p+(k+1)+1) * hill n p (k+1) * cross n (p+(k+1)+1) = _
      rw [ih1 p (by omega)]
      rfl

theorem hill_blocks (n p k : ℕ) : hill n p k = up n p k * down n p (k+1) := by
  induction k generalizing p with
  | zero => simp [hill, up, down]
  | succ k ih => simp only [hill, up, down, ih, mul_assoc]

theorem valley_blocks (n p k : ℕ) :
    valley n p k = down n (p+1) k * up n p (k+1) := by
  induction k with
  | zero => simp [valley, up, down]
  | succ k ih =>
      rw [valley, ih, down_last, up_last n p (k+1)]
      have he : p+1+k = p+k+1 := by omega
      rw [he]
      simp only [mul_assoc, Nat.add_assoc]

/-- The triangular-word rotation carries no unidentified sign. -/
theorem triangle_other (n p k : ℕ) (hb : p+k ≤ n+1) :
    triangle n p (k+1) = triangle n (p+1) k * up n p k := by
  induction k with
  | zero => simp [triangle, up, down]
  | succ k ih =>
      rw [triangle, ih (by omega), mul_assoc, ← hill_blocks,
        hill_valley n p k (by omega), valley_blocks, ← mul_assoc]
      rfl

/-- The helper's descending block is the inherited literal descending word. -/
theorem down_sweep (n p k : ℕ) : down n p k = sweep n p k := by
  induction k generalizing p with
  | zero => rfl
  | succ k ih => rw [down, ih]; rfl

/-- Source correspondence: the triangle at p=0 is the actual (2.36) word. -/
theorem triangle_source (n k : ℕ) : triangle n 0 k = actNat n (coxeterWord k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      apply LinearMap.ext
      intro f
      rw [triangle, Module.End.mul_apply, ih, down_sweep]
      rw [coxeterWord, actNat_append, List.range_eq_range', actNat_reverse_range]

/-- Specialize the inherited genuine signed-permutation covariance. -/
theorem cross_longest (n p q : ℕ) (hpq : p+q=n) (f : SkewPolynomial (n+2)) :
    cross n p (skewAction (longest (n+2)) f) =
      epsilon (longest (n+2)) • skewAction (longest (n+2)) (cross n q f) := by
  apply OddSymmetrizer.cross_covariance n p q (by omega) (by omega)
  · apply Fin.ext
    change n+2-(p+1) = q+1
    omega
  · apply Fin.ext
    change n+2-(p+1+1) = q
    omega

/-- Reverse an interval, retaining one permutation sign per divided difference. -/
theorem down_longest (n p q k : ℕ) (hb : p+q+k=n+1) (f : SkewPolynomial (n+2)) :
    down n p k (skewAction (longest (n+2)) f) =
      epsilon (longest (n+2))^k • skewAction (longest (n+2)) (up n q k f) := by
  induction k generalizing p q f with
  | zero => simp [down, up]
  | succ k ih =>
      rw [down_last, Module.End.mul_apply, ih p (q+1) (by omega), map_smul,
        cross_longest n (p+k) q (by omega), smul_smul, ← pow_succ]
      rfl

/-- All interval ranks, with the EXACT binomial sign exponent before parity reduction. -/
theorem triangle_longest (n p q k : ℕ) (hb : p+q+k=n+2)
    (f : SkewPolynomial (n+2)) :
    triangle n p k (skewAction (longest (n+2)) f) =
      epsilon (longest (n+2))^(k.choose 2) •
        skewAction (longest (n+2)) (triangle n q k f) := by
  induction k generalizing p q f with
  | zero => simp [triangle]
  | succ k ih =>
      rw [triangle, Module.End.mul_apply, down_longest n p q k (by omega), map_smul,
        ih p (q+1) (by omega), smul_smul, ← pow_add]
      rw [Nat.choose_succ_succ, Nat.choose_one_right]
      rw [triangle_other n q k (by omega)]
      rfl

/-- Corollary 2.23 for the genuine nontrivial ranks, in an equivalent direction. -/
theorem D_action (n : ℕ) (f : SkewPolynomial (n+2)) :
    D (n+2) (skewAction (longest (n+2)) f) =
      (-1 : ℤ)^((n+2).choose 2) • skewAction (longest (n+2)) (D (n+2) f) := by
  have h := triangle_longest n 0 0 (n+2) (by omega) f
  rw [triangle_source, ← D_eq_actNat, ← D_eq_actNat, epsilon_longest,
    ← pow_mul, square_sign] at h
  exact h

/-- EKL (2.66), ALL ranks and ALL integer skew polynomials, with the source orientation. -/
theorem action_D (N : ℕ) (f : SkewPolynomial N) :
    skewAction (longest N) (D N f) =
      (-1 : ℤ)^(N.choose 2) • D N (skewAction (longest N) f) := by
  rcases N with _ | _ | n
  · simp [D]
  · simp [D]
  · rw [D_action, smul_smul, ← mul_pow]
    norm_num

/-- The p18 reversed-staircase normalization, deduced for EVERY actual rank.
Here reversal means the inherited signed longest permutation, not word reversal. -/
theorem D_reversed_staircase (N : ℕ) :
    D N (skewAction (longest N) (staircase N)) =
      (-1 : ℤ)^((N+1).choose 3) • (1 : SkewPolynomial N) := by
  rcases N with _ | _ | n
  · rw [staircase_zero, map_one]
    change (1 : SkewPolynomial 0) = (-1 : ℤ)^(Nat.choose 1 3) • 1
    rw [show Nat.choose 1 3 = 0 by decide]
    simp
  · change D 1 (skewAction (longest 1) (staircase 1)) =
      (-1 : ℤ)^(Nat.choose 2 3) • (1 : SkewPolynomial 1)
    rw [staircase_one, map_one, show Nat.choose 2 3 = 0 by decide]
    simp [D]
  · rw [D_action, D_staircase, map_zsmul, map_one, smul_smul, ← pow_add,
        Nat.choose_succ_succ (n+2) 2]

/-- Genuine arbitrary left-kernel product consumer THROUGH (2.66).
The coefficient stays on the LEFT; it is not moved past the general polynomial. -/
theorem action_D_left_kernel (n : ℕ) (f g : SkewPolynomial (n+2))
    (hf : f ∈ OddSymmetricKernel.kernelSubring n) :
    skewAction (longest (n+2)) (D (n+2) (f*g)) =
      f * skewAction (longest (n+2)) (D (n+2) g) := by
  rw [action_D, map_mul, OddSymmetrizer.D_left_kernel n _ _ (action_mem_kernel n f hf),
    action_involutive, ← mul_smul_comm, ← action_D]

end
end OddMath.Frontier.LongestReversal
