import OddMath.Frontier.AllRankDivided
import OddMath.Frontier.OddSymmetricKernel

/-! EKL1111.1320v1 (2.36), (2.40), Lemma 2.10. Literal source word.
All operators below are the inherited quotient/PBW operators, not a normalization oracle. -/
namespace OddMath.Frontier.LongestDivided
open OddMath.SkewPolynomial (SkewPolynomial generator monomial)
open AllRankDivided

/-- The source list, in written (not application) order. -/
def coxeterWord : ℕ → List ℕ
  | 0 => []
  | k+1 => coxeterWord k ++ (List.range k).reverse

theorem coxeterWord_bound {k j : ℕ} (h : j ∈ coxeterWord k) : j+1 < k := by
  induction k with
  | zero => simp [coxeterWord] at h
  | succ k ih =>
      simp only [coxeterWord, List.mem_append, List.mem_reverse, List.mem_range] at h
      rcases h with h | h
      · have := ih h; omega
      · omega

/-- Same literal word embedded in any sufficiently large actual ambient rank. -/
def wordIn (n k : ℕ) (h : k ≤ n+2) : List (Fin (n+1)) :=
  (coxeterWord k).pmap (fun j hj => ⟨j, by have := coxeterWord_bound hj; omega⟩)
    (fun _ hj => hj)

/-- Composition is a right fold: the rightmost written operator acts first. -/
noncomputable def applyWord {n : ℕ} : List (Fin (n+1)) →
    (SkewPolynomial (n+2) →ₗ[ℤ] SkewPolynomial (n+2))
  | [] => LinearMap.id
  | i :: w => (divided i).comp (applyWord w)

@[simp] theorem applyWord_nil {n : ℕ} (f : SkewPolynomial (n+2)) :
    applyWord [] f = f := rfl
@[simp] theorem applyWord_cons {n : ℕ} (i : Fin (n+1)) (w : List (Fin (n+1)))
    (f : SkewPolynomial (n+2)) : applyWord (i::w) f = divided i (applyWord w f) := rfl

theorem applyWord_append {n : ℕ} (u v : List (Fin (n+1)))
    (f : SkewPolynomial (n+2)) : applyWord (u++v) f = applyWord u (applyWord v f) := by
  induction u with
  | nil => rfl
  | cons i u ih => simp only [List.cons_append, applyWord_cons, ih]

/-- The low ranks are the empty-word identity on their ACTUAL polynomial rings. -/
noncomputable def D : (N : ℕ) → SkewPolynomial N →ₗ[ℤ] SkewPolynomial N
  | 0 => LinearMap.id
  | 1 => LinearMap.id
  | n+2 => applyWord (wordIn n (n+2) le_rfl)

/-- UntilDE ordered monomial, coefficient one, exactly source (2.40). -/
noncomputable def staircase (N : ℕ) : SkewPolynomial N :=
  monomial (fun i => N-1-i.val) 1

theorem D_eq_inherited (n : ℕ) :
    D (n+2) = applyWord (wordIn n (n+2) le_rfl) := rfl

theorem applyWord_right_kernel {n : ℕ} (w : List (Fin (n+1)))
    (f g : SkewPolynomial (n+2)) (hg : g ∈ OddSymmetricKernel.kernelSubring n) :
    applyWord w (f*g) = applyWord w f * g := by
  induction w with
  | nil => rfl
  | cons i w ih =>
      rw [applyWord_cons, ih, divided_mul,
        (OddSymmetricKernel.mem_kernelSubring g).mp hg i, mul_zero, add_zero]
      rfl

/-- Right-kernel linearity of source (2.36)/(2.56), derived from twisted Leibniz (2.4).
This proof is independent of staircase normalization. -/
theorem D_right_kernel (n : ℕ) (f g : SkewPolynomial (n+2))
    (hg : g ∈ OddSymmetricKernel.kernelSubring n) : D (n+2) (f*g) = D (n+2) f*g :=
  applyWord_right_kernel _ f g hg

@[simp] theorem staircase_zero : staircase 0 = 1 := by
  change monomial _ 1 = monomial 0 1
  congr 1
  funext i
  exact Fin.elim0 i
@[simp] theorem staircase_one : staircase 1 = 1 := by
  change monomial _ 1 = monomial 0 1
  congr 1
  funext i
  simp


/-- Move a distinct generator through a power with every sign retained. -/
theorem generator_mul_pow {N : ℕ} (i j : Fin N) (h : i ≠ j) (b : ℕ) :
    generator j * generator i ^ b = (-1 : ℤ)^b • (generator i ^ b * generator j) := by
  have hc : generator j * generator i = -(generator i * generator j) :=
    OddMath.SkewPolynomial.generator_anticommute j i h.symm
  induction b with
  | zero => simp
  | succ b ih =>
      rw [pow_succ', ← mul_assoc, hc, neg_mul,
        mul_assoc, ih, mul_smul_comm, ← mul_assoc, ← pow_succ']
      simp [pow_succ, mul_smul]

/-- The balanced adjacent monomial is killed by the genuine operator. -/
theorem divided_balanced {n : ℕ} (i : Fin (n+1)) (b : ℕ) :
    divided i (generator i.castSucc ^ b * generator i.succ ^ b) = 0 := by
  induction b with
  | zero => simp [divided_one]
  | succ b ih =>
      have hp : (generator i.castSucc * generator i.succ) *
          (generator i.castSucc ^ b * generator i.succ ^ b) =
          (-1 : ℤ)^b • (generator i.castSucc ^ (b+1) * generator i.succ ^ (b+1)) := by
        rw [mul_assoc, ← mul_assoc (generator i.succ),
          generator_mul_pow _ _ (adjacent_ne i), smul_mul_assoc,
          mul_smul_comm]
        congr 1
        simp only [pow_succ', mul_assoc]
      have hz : divided i ((generator i.castSucc * generator i.succ) *
          (generator i.castSucc ^ b * generator i.succ ^ b)) = 0 := by
        rw [divided_mul, ih, mul_zero, add_zero]
        simp [divided_mul, divided_generator, s_generator]
      rw [hp, map_smul] at hz
      have hz' := congrArg (fun f : SkewPolynomial (n+2) => (-1 : ℤ)^b • f) hz
      simpa only [smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow,
        one_smul, smul_zero] using hz'

/-- A staircase's adjacent exponents differ by exactly one. -/
theorem divided_step {n : ℕ} (i : Fin (n+1)) (b : ℕ) :
    divided i (generator i.castSucc ^ (b+1) * generator i.succ ^ b) =
      generator i.castSucc ^ b * generator i.succ ^ b := by
  rw [pow_succ', mul_assoc, divided_left_mul, divided_balanced, mul_zero, sub_zero]

/-- Natural-index adapter; only bounded indices occur in the source word. -/
noncomputable def cross (n j : ℕ) : SkewPolynomial (n+2) →ₗ[ℤ] SkewPolynomial (n+2) :=
  if h : j < n+1 then divided ⟨j,h⟩ else 0

noncomputable def letter (n j : ℕ) : SkewPolynomial (n+2) :=
  if h : j < n+2 then generator ⟨j,h⟩ else 0

noncomputable def actNat (n : ℕ) : List ℕ → SkewPolynomial (n+2) →ₗ[ℤ] SkewPolynomial (n+2)
  | [] => LinearMap.id
  | j::w => (cross n j).comp (actNat n w)

theorem cross_mul (n j : ℕ) (hj : j < n+1) (f g : SkewPolynomial (n+2)) :
    cross n j (f*g) = cross n j f*g + s ⟨j,hj⟩ f * cross n j g := by
  simp only [cross, dif_pos hj]
  exact divided_mul _ _ _

theorem cross_letter_spectator (n j p : ℕ) (hj : j < n+1)
    (hp : p < n+2) (hpl : p ≠ j) (hpr : p ≠ j+1) (f : SkewPolynomial (n+2)) :
    cross n j (letter n p * f) = -letter n p * cross n j f := by
  simp only [cross, dif_pos hj, letter, dif_pos hp]
  apply divided_spectator_mul <;> intro h <;>
    have hh := congrArg Fin.val h
  · exact hpl hh
  · exact hpr hh

theorem cross_pow_spectator (n j p : ℕ) (hj : j < n+1)
    (hp : p < n+2) (hpl : p ≠ j) (hpr : p ≠ j+1) (b : ℕ)
    (f : SkewPolynomial (n+2)) :
    cross n j (letter n p ^ b * f) = (-1 : ℤ)^b • (letter n p ^ b * cross n j f) := by
  induction b with
  | zero => simp
  | succ b ih =>
      rw [pow_succ', mul_assoc, cross_letter_spectator n j p hj hp hpl hpr, ih]
      simp only [pow_succ, mul_smul, neg_one_smul, smul_neg, neg_mul,
        mul_smul_comm, mul_neg, mul_assoc, mul_one, neg_smul]

/-- Recursive product of the consecutive descending powers, with no reordering. -/
noncomputable def stairs (n p : ℕ) : ℕ → SkewPolynomial (n+2)
  | 0 => 1
  | k+1 => letter n p ^ k * stairs n (p+1) k

/-- One rightmost source block: increasing application order. -/
noncomputable def sweep (n p : ℕ) : ℕ → SkewPolynomial (n+2) →ₗ[ℤ] SkewPolynomial (n+2)
  | 0 => LinearMap.id
  | k+1 => (sweep n (p+1) k).comp (cross n p)


theorem cross_one (n j : ℕ) : cross n j 1 = 0 := by
  unfold cross
  split
  · exact divided_one _
  · rfl

theorem cross_stairs_tail (n j p k : ℕ) (hj : j < n+1)
    (hjp : j+1 < p) (hb : p+k ≤ n+2) : cross n j (stairs n p k) = 0 := by
  induction k generalizing p with
  | zero => exact cross_one n j
  | succ k ih =>
      rw [stairs, cross_pow_spectator n j p hj (by omega) (by omega) (by omega),
        ih (p+1) (by omega) (by omega)]
      simp

theorem cross_pair_step (n p k : ℕ) (hp : p < n+1) :
    cross n p (letter n p ^ (k+1) * letter n (p+1) ^ k) =
      letter n p ^ k * letter n (p+1) ^ k := by
  have hp0 : p < n+2 := by omega
  have hp1 : p+1 < n+2 := by omega
  simp only [cross, dif_pos hp, letter, dif_pos hp0, dif_pos hp1]
  exact divided_step ⟨p,hp⟩ k

theorem cross_stairs_start (n p k : ℕ) (hb : p+(k+2) ≤ n+2) :
    cross n p (stairs n p (k+2)) = letter n p ^ k * stairs n (p+1) (k+1) := by
  have hp : p < n+1 := by omega
  rw [stairs, stairs, ← mul_assoc, cross_mul n p hp,
    cross_stairs_tail n p (p+1+1) k hp (by omega) (by omega),
    mul_zero, add_zero, cross_pair_step n p k hp, mul_assoc]

theorem sweep_pow_spectator (n q k p b : ℕ) (hpq : p < q)
    (hb : q+k ≤ n+1) (hp : p < n+2) (f : SkewPolynomial (n+2)) :
    sweep n q k (letter n p ^ b * f) =
      (-1 : ℤ)^(b*k) • (letter n p ^ b * sweep n q k f) := by
  induction k generalizing q f with
  | zero => simp [sweep]
  | succ k ih =>
      change sweep n (q+1) k (cross n q (letter n p ^ b * f)) = _
      rw [cross_pow_spectator n q p (by omega) hp (by omega) (by omega), map_smul,
        ih (q+1) (by omega) (by omega) (cross n q f)]
      simp only [smul_smul, ← pow_add, Nat.mul_succ, Nat.add_comm]
      rfl

/-- Exact exponent from the successive spectator prefixes in one source block. -/
def sweepSign : ℕ → ℕ
  | 0 => 0
  | k+1 => k*k + sweepSign k

/-- The all-length block calculation underlying Lemma 2.10. -/
theorem sweep_stairs (n p k : ℕ) (hb : p+(k+1) ≤ n+2) :
    sweep n p k (stairs n p (k+1)) =
      (-1 : ℤ)^(sweepSign k) • stairs n p k := by
  induction k generalizing p with
  | zero => simp [sweep, sweepSign, stairs]
  | succ k ih =>
      change sweep n (p+1) k (cross n p (stairs n p (k+2))) = _
      rw [cross_stairs_start n p k hb,
        sweep_pow_spectator n (p+1) k p k (by omega) (by omega) (by omega),
        ih (p+1) (by omega), mul_smul_comm, smul_smul]
      rw [← pow_add]
      rfl


theorem square_sign (k : ℕ) : (-1 : ℤ)^(k*k) = (-1 : ℤ)^k := by
  rw [pow_mul]
  rcases neg_one_pow_eq_or ℤ k with h | h <;> simp [h]

theorem sweepSign_choose (k : ℕ) : (-1 : ℤ)^(sweepSign k) = (-1 : ℤ)^(k.choose 2) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [sweepSign, pow_add, square_sign, ih, Nat.choose_succ_succ]
      simp [pow_add]

theorem actNat_append (n : ℕ) (u v : List ℕ) (f : SkewPolynomial (n+2)) :
    actNat n (u++v) f = actNat n u (actNat n v f) := by
  induction u with
  | nil => rfl
  | cons j u ih =>
      change cross n j (actNat n (u++v) f) = cross n j (actNat n u (actNat n v f))
      rw [ih]

theorem actNat_reverse_range (n p k : ℕ) (f : SkewPolynomial (n+2)) :
    actNat n (List.range' p k).reverse f = sweep n p k f := by
  induction k generalizing p f with
  | zero => rfl
  | succ k ih =>
      rw [List.range'_succ, List.reverse_cons, actNat_append]
      exact ih (p+1) (cross n p f)

theorem actNat_stairs (n k : ℕ) (hb : k ≤ n+2) :
    actNat n (coxeterWord k) (stairs n 0 k) = (-1 : ℤ)^(k.choose 3) • 1 := by
  induction k with
  | zero => simp [coxeterWord, actNat, stairs]
  | succ k ih =>
      rw [coxeterWord, actNat_append, List.range_eq_range',
        actNat_reverse_range, sweep_stairs n 0 k (by omega), map_smul,
        ih (by omega), smul_smul, sweepSign_choose, ← pow_add]
      rw [Nat.choose_succ_succ]

theorem actNat_map_fin (n : ℕ) (w : List (Fin (n+1))) (f : SkewPolynomial (n+2)) :
    actNat n (w.map Fin.val) f = applyWord w f := by
  induction w with
  | nil => rfl
  | cons i w ih =>
      change cross n i.val (actNat n (w.map Fin.val) f) = divided i (applyWord w f)
      rw [ih]
      simp only [cross, dif_pos i.isLt]

theorem wordIn_values (n k : ℕ) (h : k ≤ n+2) :
    (wordIn n k h).map Fin.val = coxeterWord k := by
  simp only [wordIn, List.map_pmap]
  simp

theorem D_eq_actNat (n : ℕ) (f : SkewPolynomial (n+2)) :
    D (n+2) f = actNat n (coxeterWord (n+2)) f := by
  rw [← wordIn_values n (n+2) le_rfl, actNat_map_fin]
  rfl

/-- The exponent vector of the recursively written, ordered staircase segment. -/
def stairsExp (N p k : ℕ) : Fin N → ℕ :=
  fun j => if p ≤ j.val then p+k-1-j.val else 0

theorem stairsExp_zero (N p : ℕ) : stairsExp N p 0 = 0 := by
  funext j
  dsimp [stairsExp]
  split <;> omega

theorem stairsExp_succ (n p k : ℕ) (hp : p < n+2) :
    stairsExp (n+2) p (k+1) =
      k • OddMath.SkewPolynomial.expSingle (⟨p,hp⟩ : Fin (n+2)) +
        stairsExp (n+2) (p+1) k := by
  funext j
  simp only [stairsExp, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    OddMath.SkewPolynomial.expSingle, Fin.mk.injEq]
  by_cases he : (⟨p,hp⟩ : Fin (n+2)) = j
  · subst j
    simp
  · have hne : p ≠ j.val := by intro h; apply he; exact Fin.ext h
    simp only [he, ↓reduceIte, mul_zero]
    split <;> split <;> omega

theorem stairsExp_cross (n p k : ℕ) (hp : p < n+2) :
    OddMath.crossingCount
      (k • OddMath.SkewPolynomial.expSingle (⟨p,hp⟩ : Fin (n+2)))
      (stairsExp (n+2) (p+1) k) = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j hj
  have hji : j.val < i.val := (Finset.mem_filter.mp hj).2
  by_cases he : (⟨p,hp⟩ : Fin (n+2)) = i
  · subst i
    have hno : ¬ p+1 ≤ j.val := by simp only [Fin.val_mk] at hji; omega
    simp [stairsExp, hno]
  · simp [OddMath.SkewPolynomial.expSingle, he]

/-- This identifies the proof's recursive product with the ACTUAL coefficient-one
ordered monomial; no alternate polynomial carrier or imposed normalization. -/
theorem stairs_monomial (n p k : ℕ) (hb : p+k ≤ n+2) :
    stairs n p k = monomial (stairsExp (n+2) p k) 1 := by
  induction k generalizing p with
  | zero => rw [stairsExp_zero]; rfl
  | succ k ih =>
      have hp : p < n+2 := by omega
      rw [stairs, ih (p+1) (by omega)]
      simp only [letter, dif_pos hp]
      rw [PbwL4.pow_form]
      change OddMath.SkewPolynomial.mul _ _ = _
      rw [OddMath.SkewPolynomial.mul_monomial]
      rw [show OddMath.skewSign
        (k • OddMath.SkewPolynomial.expSingle (⟨p,hp⟩ : Fin (n+2)))
        (stairsExp (n+2) (p+1) k) = 1 by
          rw [OddMath.skewSign, stairsExp_cross n p k hp, pow_zero]]
      rw [← stairsExp_succ n p k hp]
      norm_num

theorem stairs_eq_staircase (n : ℕ) : stairs n 0 (n+2) = staircase (n+2) := by
  rw [stairs_monomial n 0 (n+2) (by omega)]
  unfold staircase
  congr 1
  funext i
  simp [stairsExp]

/-- EKL1111.1320v1 Lemma 2.10, for EVERY rank, with the literal (2.36) word
and untilde ordered staircase (2.40). -/
theorem D_staircase (N : ℕ) : D N (staircase N) = (-1 : ℤ)^(N.choose 3) • (1 : SkewPolynomial N) := by
  rcases N with _ | _ | n
  · simp [D]
  · change staircase 1 = (-1 : ℤ)^(Nat.choose 1 3) • (1 : SkewPolynomial 1)
    rw [staircase_one, show Nat.choose 1 3 = 0 from by decide]
    simp
  · rw [D_eq_actNat, ← stairs_eq_staircase]
    exact actNat_stairs n (n+2) le_rfl

end OddMath.Frontier.LongestDivided



