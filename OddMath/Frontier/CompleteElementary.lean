import Mathlib.Algebra.FreeAlgebra
import Mathlib.Algebra.BigOperators.Fin

/-!
# Elementary/complete inverse in the free associative algebra

Ellis–Khovanov, arXiv:1107.5610v2, §2.2, (2.5) and (2.6), pp.9–10.
This proves the universal presentation-stage identity, not quotient descent,
a basis theorem, a pairing theorem, or a Hopf-algebra structure.
-/
namespace OddMath.Frontier.CompleteElementary

open scoped BigOperators

/-- Generator `i` represents the positive complete generator `h_(i+1)`. -/
abbrev A := FreeAlgebra ℤ ℕ

/-- The zeroth complete element is the unit, not an extra generator. -/
def h : ℕ → A
  | 0 => 1
  | n + 1 => FreeAlgebra.ι ℤ n

@[simp] theorem h_zero : h 0 = 1 := rfl

/-- EK's sign `(-1)^binom(n+1,2)`, in the actual ambient algebra. -/
def ekSign (n : ℕ) : A := (-1) ^ ((n + 1).choose 2)

@[simp] theorem ekSign_sq (n : ℕ) : ekSign n * ekSign n = 1 := by
  simp [ekSign, ← pow_add, ← two_mul, pow_mul]

/-- Sign-normalized elementary coefficients, recursively inverted on the right. -/
def inverseCoeff : ℕ → A
  | 0 => 1
  | n + 1 => - ∑ k : Fin (n + 1), inverseCoeff k * h (n + 1 - k)
termination_by n => n

/-- The odd elementary elements with precisely the EK normalization. -/
def elementary (n : ℕ) : A := ekSign n * inverseCoeff n

@[simp] theorem elementary_zero : elementary 0 = 1 := by
  simp [elementary, ekSign, inverseCoeff]

@[simp] theorem sign_elementary (n : ℕ) :
    ekSign n * elementary n = inverseCoeff n := by
  rw [elementary, ← mul_assoc, ekSign_sq, one_mul]

/-- Explicit recursive construction of the elementary elements themselves. -/
theorem elementary_succ (n : ℕ) :
    elementary (n + 1) = -ekSign (n + 1) *
      ∑ k : Fin (n + 1), ekSign k * elementary k * h (n + 1 - k) := by
  simp [elementary, inverseCoeff, ← mul_assoc]

/-- EK (2.5), uniformly in every positive degree, with the specified order e*h. -/
theorem elementary_complete_inverse (n : ℕ) :
    ∑ k : Fin (n + 2), ekSign k * elementary k * h (n + 1 - k) = 0 := by
  simp only [sign_elementary]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.coe_castSucc, Fin.val_last, Nat.sub_self, h_zero, mul_one]
  rw [inverseCoeff]
  exact add_neg_cancel _

/-- Finite enumeration by the last positive part; no multiplicities. -/
def compositions : ℕ → Finset (List ℕ)
  | 0 => {[]}
  | n + 1 => Finset.univ.biUnion fun k : Fin (n + 1) =>
      (compositions k).image (fun α => α ++ [n + 1 - k])
termination_by n => n

/-- Every enumerated list has positive parts and the intended total. -/
theorem composition_sound (n : ℕ) (α : List ℕ) (ha : α ∈ compositions n) :
    (∀ a ∈ α, 0 < a) ∧ α.sum = n := by
  induction n using Nat.strong_induction_on generalizing α with
  | h n ih =>
    cases n with
    | zero =>
      simp only [compositions, Finset.mem_singleton] at ha
      subst α
      simp
    | succ n =>
      simp only [compositions, Finset.mem_biUnion, Finset.mem_univ, true_and,
        Finset.mem_image] at ha
      obtain ⟨k, β, hb, rfl⟩ := ha
      obtain ⟨hp, hs⟩ := ih k k.isLt β hb
      constructor
      · intro a ha
        simp only [List.mem_append, List.mem_singleton] at ha
        rcases ha with ha | rfl
        · exact hp a ha
        · omega
      · simp only [List.sum_append, List.sum_singleton, hs]
        omega

/-- Conversely every list of positive parts with total n is enumerated. -/
theorem composition_complete (α : List ℕ) (hp : ∀ a ∈ α, 0 < a) :
    α ∈ compositions α.sum := by
  induction α using List.reverseRecOn with
  | nil => simp [compositions]
  | append_singleton α a ih =>
    have hα : ∀ b ∈ α, 0 < b := fun b hb => hp b (List.mem_append_left _ hb)
    have ha : 0 < a := hp a (by simp)
    have hh := ih hα
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : α.sum + a ≠ 0)
    simp only [List.sum_append, List.sum_singleton]
    rw [hn, compositions]
    apply Finset.mem_biUnion.mpr
    refine ⟨⟨α.sum, by omega⟩, Finset.mem_univ _, ?_⟩
    apply Finset.mem_image.mpr
    refine ⟨α, hh, ?_⟩
    simp only [Fin.val_mk]
    congr 2
    omega

/-- Exact semantic characterization, not just a recursively defined surrogate. -/
theorem mem_compositions_iff (n : ℕ) (α : List ℕ) :
    α ∈ compositions n ↔ (∀ a ∈ α, 0 < a) ∧ α.sum = n := by
  constructor
  · exact composition_sound n α
  · rintro ⟨hp, rfl⟩
    exact composition_complete α hp

/-- Ordered (noncommutative) complete word. -/
def hWord (α : List ℕ) : A := (α.map h).prod

/-- The summand of EK (2.6), before its degree-wide sign. -/
def signedWord (α : List ℕ) : A := (-1) ^ α.length * hWord α

@[simp] theorem signedWord_nil : signedWord [] = 1 := by
  simp [signedWord, hWord]

theorem signedWord_append (α : List ℕ) (a : ℕ) :
    signedWord (α ++ [a]) = -(signedWord α * h a) := by
  simp [signedWord, hWord, List.prod_append, pow_succ, mul_assoc]

/-- Distinct prefix degrees give disjoint snoc families. -/
theorem composition_branches_disjoint (n : ℕ) :
    ((Finset.univ : Finset (Fin (n + 1))) : Set (Fin (n + 1))).PairwiseDisjoint
      (fun k => (compositions k).image (fun α => α ++ [n + 1 - k])) := by
  intro i _ j _ hij
  apply Finset.disjoint_left.mpr
  intro α hi hj
  obtain ⟨β, hb, heq⟩ := Finset.mem_image.mp hi
  obtain ⟨γ, hc, heq'⟩ := Finset.mem_image.mp hj
  have hp : β = γ := List.append_inj_left' (heq.trans heq'.symm) rfl
  have hi' := (composition_sound i β hb).2
  have hj' := (composition_sound j γ hc).2
  rw [hp] at hi'
  apply hij
  apply Fin.ext
  exact hi'.symm.trans hj'

/-- Splitting the finite composition sum by its last positive part. -/
theorem signed_composition_sum_succ (n : ℕ) :
    ∑ α ∈ compositions (n + 1), signedWord α =
      - ∑ k : Fin (n + 1), (∑ α ∈ compositions k, signedWord α) * h (n + 1 - k) := by
  rw [compositions, Finset.sum_biUnion (composition_branches_disjoint n)]
  simp only [Finset.sum_image (fun _ _ _ _ h => List.append_cancel_right h),
    signedWord_append, Finset.sum_neg_distrib, ← Finset.sum_mul]

/-- The inverse coefficients are the signed sum over all compositions. -/
theorem inverseCoeff_composition_expansion (n : ℕ) :
    inverseCoeff n = ∑ α ∈ compositions n, signedWord α := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [inverseCoeff, compositions]
    | succ n =>
      rw [inverseCoeff, signed_composition_sum_succ]
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      rw [ih k k.isLt]

/-- EK (2.6), including the empty composition in degree zero. -/
theorem elementary_composition_expansion (n : ℕ) :
    elementary n = (-1 : A) ^ ((n + 1).choose 2) *
      ∑ α ∈ compositions n, (-1 : A) ^ α.length * hWord α := by
  rw [elementary, inverseCoeff_composition_expansion]
  rfl

/-- EK (2.5) in the usual range-indexed notation. -/
theorem elementary_complete_inverse_range (n : ℕ) (hn : 0 < n) :
    ∑ k ∈ Finset.range (n + 1),
      (-1 : A) ^ ((k + 1).choose 2) * elementary k * h (n - k) = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rw [← Fin.sum_univ_eq_sum_range]
  exact elementary_complete_inverse m

end OddMath.Frontier.CompleteElementary
