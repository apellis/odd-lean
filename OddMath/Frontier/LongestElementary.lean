import OddMath.Frontier.SignedPermutation
import OddMath.Frontier.ElementaryGeneration
import OddMath.Frontier.TableauExtremal
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Algebra.BigOperators.Intervals

/-! EKL 1111.1320v1 Lemma 2.16 (2.55), p.14. Actual order reversal,
signed action, literal elementary sums, and joint-kernel preservation. -/
namespace OddMath.Frontier.LongestElementary
open OddMath.SkewPolynomial
open SignedPermutation PlacticEvaluation FiniteCompleteElementary
open scoped BigOperators
noncomputable section

/-- The longest permutation is actual order reversal, including the empty alphabet. -/
def longest (N : ℕ) : Equiv.Perm (Fin N) :=
  ⟨Fin.rev, Fin.rev, Fin.rev_rev, Fin.rev_rev⟩

@[simp] theorem longest_apply {N : ℕ} (i : Fin N) : longest N i = i.rev := rfl

@[simp] theorem longest_involutive (N : ℕ) : longest N * longest N = 1 := by
  ext i
  simp [Equiv.Perm.mul_apply]

/-- Counting the inversions in reversal, not assigning its sign by definition. -/
theorem epsilon_longest (N : ℕ) : epsilon (longest N) = (-1 : ℤ) ^ N.choose 2 := by
  have hs : Equiv.Perm.sign (longest N) = (-1 : ℤˣ) ^ N.choose 2 := by
    rw [Equiv.Perm.sign_eq_prod_prod_Iio]
    have hi (j : Fin N) :
        (∏ i ∈ Finset.Iio j, if longest N i < longest N j then (1 : ℤˣ) else -1) =
        (-1 : ℤˣ) ^ j.val := by
      have h (i : Fin N) (hij : i ∈ Finset.Iio j) : ¬ longest N i < longest N j := by
        simp only [Finset.mem_Iio] at hij
        simpa using not_lt_of_ge (Fin.rev_le_rev.mpr (le_of_lt hij))
      simp only [Finset.prod_congr rfl (fun i hi => if_neg (h i hi))]
      simp
    simp_rw [hi]
    rw [Finset.prod_pow_eq_pow_sum]
    congr 1
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => i), Finset.sum_range_id, Nat.choose_two_right]
  exact congrArg (fun u : ℤˣ => (u : ℤ)) hs

/-- Reversal acts twice as the identity on actual polynomials. -/
@[simp] theorem action_involutive (N : ℕ) (f : SkewPolynomial N) :
    skewAction (longest N) (skewAction (longest N) f) = f := by
  rw [← action_mul, longest_involutive, action_one]

/-- The tilde correction and global sign combine to the source exponent. -/
theorem action_tilde {N : ℕ} (i : Fin N) :
    skewAction (longest N) (tildeGenerator i) =
      (-1 : ℤ) ^ ((N-1).choose 2) • tildeGenerator i.rev := by
  have hN : 0 < N := i.pos
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
  have hv : i.val + i.rev.val = m := by simp only [Fin.val_rev]; omega
  have hp : (-1 : ℤ) ^ (i.val + (m+1).choose 2) =
      (-1 : ℤ) ^ (m.choose 2 + i.rev.val) := by
    have he : i.val + (m+1).choose 2 = (m.choose 2 + i.rev.val) + 2*i.val := by
      rw [Nat.choose_succ_succ, Nat.choose_one_right]
      change i.val + (m + m.choose 2) = (m.choose 2 + i.rev.val) + 2*i.val
      omega
    rw [he, pow_add, pow_mul]
    norm_num
  simp only [tildeGenerator, map_zsmul, action_generator, epsilon_longest,
    longest_apply, smul_smul, Nat.add_sub_cancel, Nat.succ_sub_one]
  rw [← pow_add, ← pow_add, hp]

/-- Reverse both the positions and the alphabet. -/
def reverseWord {N k : ℕ} (f : Fin k → Fin N) : Fin k → Fin N :=
  fun i => (f i.rev).rev

@[simp] theorem reverseWord_reverseWord {N k : ℕ} (f : Fin k → Fin N) :
    reverseWord (reverseWord f) = f := by
  funext i
  simp [reverseWord]

def reverseWordEquiv (N k : ℕ) : (Fin k → Fin N) ≃ (Fin k → Fin N) :=
  ⟨reverseWord, reverseWord, reverseWord_reverseWord, reverseWord_reverseWord⟩

theorem strictMono_reverseWord {N k : ℕ} {f : Fin k → Fin N} (hf : StrictMono f) :
    StrictMono (reverseWord f) := by
  intro i j hij
  exact Fin.rev_lt_rev.mpr (hf (Fin.rev_lt_rev.mpr hij))

@[simp] theorem strictMono_reverseWord_iff {N k : ℕ} (f : Fin k → Fin N) :
    StrictMono (reverseWord f) ↔ StrictMono f := by
  constructor
  · intro h
    simpa using strictMono_reverseWord h
  · exact strictMono_reverseWord

/-- Scalar distribution in the literal noncommutative word product. -/
theorem prod_map_smul {N : ℕ} (c : ℤ) (l : List (SkewPolynomial N)) :
    (l.map (fun x => c • x)).prod = c ^ l.length • l.prod := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons, ih,
      smul_mul_assoc, mul_smul_comm, smul_smul]
    rw [pow_succ]

/-- Position reversal realizes list reversal; the products are not commuted. -/
theorem ofFn_rev {α : Type*} {k : ℕ} (f : Fin k → α) :
    List.ofFn (fun i => f i.rev) = (List.ofFn f).reverse := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.length_ofFn] at hi
    simp only [List.getElem_reverse, List.length_ofFn, List.getElem_ofFn, Fin.rev]
    congr 1
    apply Fin.ext
    simp only [Fin.val_mk]
    omega

/-- The signed action on an arbitrary word, before any sorting. -/
theorem action_tildeWord {N : ℕ} (l : List (Fin N)) :
    skewAction (longest N) ((l.map tildeGenerator).prod) =
      ((-1 : ℤ) ^ ((N-1).choose 2)) ^ l.length •
        (l.map (fun i => tildeGenerator i.rev)).prod := by
  rw [map_list_prod]
  simp only [List.map_map, Function.comp_def, action_tilde]
  simpa only [List.map_map, Function.comp_def, List.length_map] using
    prod_map_smul ((-1 : ℤ) ^ ((N-1).choose 2)) (l.map (fun i => tildeGenerator i.rev))

/-- Reindex the literal elementary summand; sorting supplies choose(k,2). -/
theorem action_strictWord {N k : ℕ} (f : Fin k → Fin N) (hf : StrictMono f) :
    skewAction (longest N) (List.ofFn (fun i => tildeGenerator (f i))).prod =
      (-1 : ℤ) ^ (k.choose 2 + k*((N-1).choose 2)) •
        (List.ofFn (fun i => tildeGenerator (reverseWord f i))).prod := by
  have hr := TableauExtremal.reverse_tildeProduct
    (⟨reverseWord f, strictMono_reverseWord hf⟩ : FiniteWords.Strict N k)
  have hl : (List.ofFn (reverseWord f)).reverse = List.ofFn (fun i => (f i).rev) := by
    rw [← ofFn_rev]
    simp only [reverseWord, Fin.rev_rev]
  rw [hl, List.map_ofFn] at hr
  have he : (List.ofFn f).map tildeGenerator =
      List.ofFn (fun i => tildeGenerator (f i)) := by rw [List.map_ofFn]; rfl
  rw [← he, action_tildeWord, List.length_ofFn, List.map_ofFn]
  simp only [Function.comp_def] at hr ⊢
  rw [hr, smul_smul, ← pow_mul, ← pow_add]
  congr 2
  exact Nat.add_comm _ _ |>.trans (congrArg (k.choose 2 + ·) (Nat.mul_comm _ _))

/-- EKL Lemma 2.16 (2.55), including all empty and out-of-range cases. -/
theorem action_elementary (N k : ℕ) :
    skewAction (longest N) (elementaryPoly N k) =
      (-1 : ℤ) ^ (k.choose 2 + k*((N-1).choose 2)) • elementaryPoly N k := by
  classical
  unfold elementaryPoly
  rw [map_sum, Finset.smul_sum]
  apply Fintype.sum_equiv (reverseWordEquiv N k)
  intro f
  change skewAction (longest N) (if StrictMono f then _ else 0) =
    _ • (if StrictMono (reverseWord f) then _ else 0)
  by_cases hf : StrictMono f
  · simp only [hf, strictMono_reverseWord_iff, ↓reduceIte]
    exact action_strictWord f hf
  · simp only [hf, strictMono_reverseWord_iff, ↓reduceIte, map_zero, smul_zero]

/-- Generation propagates the proved elementary formula to the actual joint kernel. -/
theorem action_mem_kernel (n : ℕ) (f : SkewPolynomial (n+2))
    (hf : f ∈ OddSymmetricKernel.kernelSubring n) :
    skewAction (longest (n+2)) f ∈ OddSymmetricKernel.kernelSubring n := by
  rw [ElementaryGeneration.kernel_eq_elementaryClosure] at hf ⊢
  induction hf using Subring.closure_induction with
  | mem x hx =>
    obtain ⟨k, hk, hkn, rfl⟩ := hx
    rw [action_elementary]
    apply Subring.zsmul_mem
    exact Subring.subset_closure ⟨k, hk, hkn, rfl⟩
  | zero => simpa using (ElementaryGeneration.elementaryClosure n).zero_mem
  | one => simpa using (ElementaryGeneration.elementaryClosure n).one_mem
  | add x y hx hy ihx ihy =>
    simpa using (ElementaryGeneration.elementaryClosure n).add_mem ihx ihy
  | neg x hx ih => simpa using (ElementaryGeneration.elementaryClosure n).neg_mem ih
  | mul x y hx hy ihx ihy =>
    simpa using (ElementaryGeneration.elementaryClosure n).mul_mem ihx ihy

/-- The source preservation is an iff, not just one inclusion. -/
theorem kernel_mem_iff (n : ℕ) (f : SkewPolynomial (n+2)) :
    skewAction (longest (n+2)) f ∈ OddSymmetricKernel.kernelSubring n ↔
      f ∈ OddSymmetricKernel.kernelSubring n := by
  constructor
  · intro h
    simpa using action_mem_kernel n _ h
  · exact action_mem_kernel n f

/-- Set-level equality stated in the source. -/
theorem kernel_image (n : ℕ) :
    skewAction (longest (n+2)) '' (OddSymmetricKernel.kernelSubring n : Set _) =
      (OddSymmetricKernel.kernelSubring n : Set _) := by
  ext f
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact action_mem_kernel n g hg
  · intro hf
    exact ⟨skewAction (longest (n+2)) f, action_mem_kernel n f hf, action_involutive _ _⟩

end
end OddMath.Frontier.LongestElementary
