import OddMath.Frontier.LongestDivided
import OddMath.Frontier.DividedBraid
import OddMath.Frontier.DividedDistant

/-! The actual longest divided difference has exactly the joint kernel as range.
EKL1111.1320v1 (2.37), (2.56): only the longest-word instance is proved here.
Every word helper below is used by `D_killed`; no general reduced-word premise.
The resulting RIGHT retraction is not the source's symmetrizer (2.57). -/
namespace OddMath.Frontier.LongestKernel
open OddMath.SkewPolynomial (SkewPolynomial)
open AllRankDivided LongestDivided

/-- Natural-index form of the inherited square-zero law; consumer `D_killed`. -/
theorem cross_sq (n j : ℕ) (f : SkewPolynomial (n+2)) :
    cross n j (cross n j f) = 0 := by
  unfold cross
  split
  · exact DividedSquareZero.divided_sq_zero _ f
  · rfl

/-- Natural-index form of the inherited signed distant law; consumer `D_killed`. -/
theorem cross_distant (n i j : ℕ) (hi : i < n+1) (hj : j < n+1)
    (hd : i+1<j ∨ j+1<i) (f : SkewPolynomial (n+2)) :
    cross n i (cross n j f) = -cross n j (cross n i f) := by
  simp only [cross, dif_pos hi, dif_pos hj]
  exact DividedDistant.divided_distant_neg ⟨i,hi⟩ ⟨j,hj⟩ hd f

/-- Natural-index braid without any arbitrary-word hypothesis; consumer `D_killed`. -/
theorem cross_braid (n j : ℕ) (hj : j+1 < n+1) (f : SkewPolynomial (n+2)) :
    cross n (j+1) (cross n j (cross n (j+1) f)) =
      cross n j (cross n (j+1) (cross n j f)) := by
  cases n with
  | zero => omega
  | succ n =>
      have hj0 : j < n+1+1 := by omega
      simp only [cross, dif_pos hj, dif_pos hj0]
      exact (DividedBraid.divided_braid (⟨j, by omega⟩ : Fin (n+1)) f).symm

/-- Commuting one distant crossing through a concrete word, including every sign.
Consumer `D_killed`, via the descending-block square and final-crossing step. -/
theorem cross_word (n i : ℕ) (w : List ℕ) (hi : i < n+1)
    (hw : ∀ j ∈ w, j+1 < i) (f : SkewPolynomial (n+2)) :
    cross n i (actNat n w f) = (-1 : ℤ)^w.length • actNat n w (cross n i f) := by
  induction w with
  | nil => simp [actNat]
  | cons j w ih =>
      have hj := hw j (by simp)
      have ht : ∀ a ∈ w, a+1 < i := fun a ha => hw a (by simp [ha])
      change cross n i (cross n j (actNat n w f)) = _
      rw [cross_distant n i j hi (by omega) (Or.inr hj), ih ht]
      simp only [map_smul, List.length_cons, pow_succ, mul_smul, neg_one_smul, smul_neg]
      rfl

/-- One literal descending block in (2.56); consumer `D_killed`. -/
noncomputable def down (n k : ℕ) := actNat n (List.range k).reverse

@[simp] theorem down_zero (n : ℕ) (f : SkewPolynomial (n+2)) : down n 0 f = f := rfl

theorem down_succ (n k : ℕ) (f : SkewPolynomial (n+2)) :
    down n (k+1) f = cross n k (down n k f) := by
  simp [down, List.range_succ, List.reverse_append, actNat]

/-- Distant crossing through a descending block; consumer `D_killed`. -/
theorem cross_down (n i k : ℕ) (hi : i < n+1) (hk : k < i)
    (f : SkewPolynomial (n+2)) :
    cross n i (down n k f) = (-1 : ℤ)^k • down n k (cross n i f) := by
  simpa [down] using cross_word n i (List.range k).reverse hi
    (by intro j hj; simp only [List.mem_reverse, List.mem_range] at hj; omega) f

/-- A doubled descending block vanishes, by a single braid and shorter doubled
block. This is the precise non-reduced-word fact needed by `D_killed`. -/
theorem down_sq (n k : ℕ) (hk : k ≤ n+1) (hpos : 0 < k)
    (f : SkewPolynomial (n+2)) : down n k (down n k f) = 0 := by
  induction k using Nat.twoStepInduction with
  | zero => omega
  | one => simpa [down_succ] using cross_sq n 0 f
  | more k _ ih =>
      have hc := cross_down n (k+1) k (by omega) (by omega)
      have move (g : SkewPolynomial (n+2)) :
          down n k (cross n (k+1) g) =
            (-1 : ℤ)^k • cross n (k+1) (down n k g) := by
        rw [hc, smul_smul, ← mul_pow]
        norm_num
      rw [down_succ n (k+1) (down n (k+2) f), down_succ n k,
        down_succ n (k+1) f, move]
      simp only [map_smul]
      rw [cross_braid n k (by omega)]
      rw [← down_succ n k, ih (by omega) (by omega)]
      simp

/-- Joint annihilation of the actual prefix longest word in a fixed ambient rank.
The new last crossing commutes through the shorter longest prefix and leaves
exactly a doubled descending block. Consumer `D_killed`. -/
theorem word_killed (n k : ℕ) (hk : k ≤ n+2) (i : ℕ) (hi : i+1 < k)
    (f : SkewPolynomial (n+2)) : cross n i (actNat n (coxeterWord k) f) = 0 := by
  induction k using Nat.twoStepInduction generalizing f with
  | zero => omega
  | one => omega
  | more k ih0 ih =>
      by_cases hil : i+1 < k+1
      · rw [coxeterWord, actNat_append]
        exact ih (by omega) hil _
      · have he : i = k := by omega
        subst i
        have hb : ∀ j ∈ coxeterWord k, j+1 < k := fun j hj => coxeterWord_bound hj
        rw [coxeterWord, actNat_append, coxeterWord, actNat_append,
          cross_word n k (coxeterWord k) (by omega) hb]
        change (-1 : ℤ)^(coxeterWord k).length •
          actNat n (coxeterWord k) (cross n k (down n k (down n (k+1) f))) = 0
        rw [← down_succ, down_sq n (k+1) (by omega) (by omega)]
        simp

/-- Every actual simple crossing kills the literal source longest operator. -/
theorem D_killed (n : ℕ) (i : Fin (n+1)) (f : SkewPolynomial (n+2)) :
    divided i (D (n+2) f) = 0 := by
  rw [D_eq_actNat]
  have h := word_killed n (n+2) le_rfl i.val (by omega) f
  simpa only [cross, dif_pos i.isLt] using h

theorem D_mem_kernel (n : ℕ) (f : SkewPolynomial (n+2)) :
    D (n+2) f ∈ OddSymmetricKernel.kernelSubring n := fun i => D_killed n i f

/-- The sign-corrected RIGHT retraction. Multiplication order is intentional:
this is not EKL (2.57), which uses f*staircase and a subsequent w0 action. -/
noncomputable def rightRetraction (n : ℕ) (f : SkewPolynomial (n+2)) :
    SkewPolynomial (n+2) :=
  (-1 : ℤ)^((n+2).choose 3) • D (n+2) (staircase (n+2) * f)

theorem rightRetraction_mem_kernel (n : ℕ) (f : SkewPolynomial (n+2)) :
    rightRetraction n f ∈ OddSymmetricKernel.kernelSubring n := by
  intro i
  rw [rightRetraction, map_smul, D_killed, smul_zero]

theorem rightRetraction_eq_self (n : ℕ) (f : SkewPolynomial (n+2))
    (hf : f ∈ OddSymmetricKernel.kernelSubring n) : rightRetraction n f = f := by
  rw [rightRetraction, D_right_kernel n _ f hf, D_staircase, smul_mul_assoc,
    one_mul, smul_smul, ← mul_pow]
  norm_num

theorem rightRetraction_idempotent (n : ℕ) (f : SkewPolynomial (n+2)) :
    rightRetraction n (rightRetraction n f) = rightRetraction n f :=
  rightRetraction_eq_self n _ (rightRetraction_mem_kernel n f)

/-- Exact linear range iff the actual joint-kernel predicate, with an explicit
integral preimage. This does not assume a basis, a field, or perfectness. -/
theorem D_range_kernel (n : ℕ) (f : SkewPolynomial (n+2)) :
    f ∈ LinearMap.range (D (n+2)) ↔ f ∈ OddSymmetricKernel.kernelSubring n := by
  constructor
  · rintro ⟨g, rfl⟩
    exact D_mem_kernel n g
  · intro hf
    refine ⟨(-1 : ℤ)^((n+2).choose 3) • (staircase (n+2) * f), ?_⟩
    rw [map_smul]
    exact rightRetraction_eq_self n f hf

end OddMath.Frontier.LongestKernel
