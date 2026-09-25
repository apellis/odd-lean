import OddMath.Frontier.StaircaseIndependence

/-! # Integral LEFT staircase decomposition
EKL 1111.1320v1, Proposition 2.13 pp.12–13, left freeness portion with
staircase monomials (2.46). Coefficients really multiply on the LEFT.
The actual integer polynomial reversal fixes generators and reverses products;
it is not a ring automorphism. Schubert identification and graded rank remain open.
-/
namespace OddMath.Frontier.StaircaseLeft
open OddMath.SkewPolynomial (SkewPolynomial monomial generator expSingle)
open ElementaryBranching StaircaseSpanning ElementaryGeneration
open FiniteCompleteElementary PlacticEvaluation
open scoped BigOperators
noncomputable section

/-- The sign of reversing an ordered monomial: equal letters never cross. -/
def reversalSign {N : ℕ} (a : Fin N → ℕ) : ℤ := OddMath.skewSign a a

theorem reversalSign_square {N : ℕ} (a : Fin N → ℕ) :
    reversalSign a * reversalSign a = 1 := skewSign_square a a

theorem reversalSign_add {N : ℕ} (a b : Fin N → ℕ) :
    OddMath.skewSign a b * reversalSign (a+b) =
      reversalSign b * reversalSign a * OddMath.skewSign b a := by
  have hs := skewSign_square a b
  unfold reversalSign
  simp only [OddMath.skewSign, OddMath.crossingCount_add_left,
    OddMath.crossingCount_add_right, pow_add] at *
  calc
    _ = ((-1:ℤ)^OddMath.crossingCount a b * (-1:ℤ)^OddMath.crossingCount a b) *
        ((-1:ℤ)^OddMath.crossingCount b b * (-1:ℤ)^OddMath.crossingCount a a *
          (-1:ℤ)^OddMath.crossingCount b a) := by ring
    _ = _ := by rw [hs, one_mul]

/-- Concrete coefficient-linear reversal on the actual finite-support carrier. -/
def reverse (N : ℕ) : SkewPolynomial N →ₗ[ℤ] SkewPolynomial N :=
  Finsupp.linearCombination ℤ (fun a => monomial a (reversalSign a))

@[simp] theorem reverse_monomial {N : ℕ} (a : Fin N → ℕ) (z : ℤ) :
    reverse N (monomial a z) = monomial a (z * reversalSign a) := by
  rw [reverse, Finsupp.linearCombination_single]
  exact Finsupp.smul_single z a (reversalSign a)

@[simp] theorem reverse_involutive {N : ℕ} (f : SkewPolynomial N) :
    reverse N (reverse N f) = f := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single a z =>
    change reverse N (reverse N (monomial a z)) = monomial a z
    rw [reverse_monomial, reverse_monomial, mul_assoc, reversalSign_square, mul_one]

theorem reverse_injective (N : ℕ) : Function.Injective (reverse N) :=
  Function.LeftInverse.injective reverse_involutive

/-- Product reversal, proved from the literal skew multiplication table. -/
theorem reverse_mul {N : ℕ} (f g : SkewPolynomial N) :
    reverse N (f*g) = reverse N g * reverse N f := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f h hf hh => simp only [add_mul, map_add, mul_add, hf, hh]
  | single a z =>
    induction g using Finsupp.induction_linear with
    | zero => simp
    | add g h hg hh => simp only [mul_add, map_add, add_mul, hg, hh]
    | single b t =>
      change reverse N (monomial a z * monomial b t) =
        reverse N (monomial b t) * reverse N (monomial a z)
      have hm (a b : Fin N → ℕ) (z t : ℤ) :
          monomial a z * monomial b t = monomial (a+b) (z*t*OddMath.skewSign a b) :=
        OddMath.SkewPolynomial.mul_monomial a b z t
      rw [hm, reverse_monomial, reverse_monomial, reverse_monomial, hm]
      rw [add_comm b a]
      congr 1
      calc
        _ = z*t*(OddMath.skewSign a b * reversalSign (a+b)) := by ring
        _ = _ := by rw [reversalSign_add]; ring

@[simp] theorem reverse_one (N : ℕ) : reverse N 1 = 1 := by
  change reverse N (monomial 0 1) = monomial 0 1
  simp [reversalSign, OddMath.skewSign, OddMath.crossingCount]

@[simp] theorem reverse_generator {N : ℕ} (i : Fin N) :
    reverse N (generator i) = generator i := by
  have hz : OddMath.crossingCount (expSingle i) (expSingle i) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    apply Finset.sum_eq_zero
    intro k hk
    have hkj := (Finset.mem_filter.mp hk).2
    by_cases hj : i=j
    · subst j; have hi : i ≠ k := ne_of_gt hkj
      simp [expSingle, hi]
    · simp [expSingle, hj]
  change reverse N (monomial (expSingle i) 1) = monomial (expSingle i) 1
  simp [reversalSign, OddMath.skewSign, hz]

@[simp] theorem reverse_tilde {N : ℕ} (i : Fin N) :
    reverse N (tildeGenerator i) = tildeGenerator i := by
  simp only [tildeGenerator, map_zsmul, reverse_generator]

/-- On actual generator words this is literal word reversal, including repeats. -/
theorem reverse_word {N : ℕ} (w : List (Fin N)) :
    reverse N ((w.map generator).prod) = ((w.reverse.map generator).prod) := by
  induction w with
  | nil => simp
  | cons i w ih => simp [reverse_mul, ih]

/-- Moving a letter past distinct letters pays one minus sign per letter. -/
theorem tilde_word_mul {N : ℕ} (w : List (Fin N)) (i : Fin N) (hi : i ∉ w) :
    (w.map tildeGenerator).prod * tildeGenerator i =
      (-1:ℤ)^w.length • (tildeGenerator i * (w.map tildeGenerator).prod) := by
  induction w with
  | nil => simp
  | cons j w ih =>
    have hij : j ≠ i := by intro h; subst j; exact hi (by simp)
    have hiw : i ∉ w := by intro h; exact hi (by simp [h])
    simp only [List.map_cons, List.prod_cons, List.length_cons]
    rw [mul_assoc, ih hiw, mul_smul_comm, ← mul_assoc, tilde_anticommute j i hij]
    simp only [neg_mul, mul_assoc, pow_succ, mul_neg_one, neg_smul, smul_neg]

/-- Squarefree words, unlike general words, have the uniform binomial sign. -/
theorem reverse_tilde_word {N : ℕ} (w : List (Fin N)) (hw : w.Nodup) :
    reverse N ((w.map tildeGenerator).prod) =
      (-1:ℤ)^(w.length.choose 2) • (w.map tildeGenerator).prod := by
  induction w with
  | nil => simp
  | cons i w ih =>
    have hn := List.nodup_cons.mp hw
    simp only [List.map_cons, List.prod_cons, reverse_mul, reverse_tilde,
      ih hn.2, smul_mul_assoc, tilde_word_mul w i hn.1, smul_smul, List.length_cons]
    rw [Nat.choose_succ_succ, Nat.choose_one_right, pow_add]
    congr 1
    ring

/-- Reversal preserves each elementary generator up to its exact integral unit. -/
theorem reverse_elementary (N k : ℕ) :
    reverse N (elementaryPoly N k) =
      (-1:ℤ)^(k.choose 2) • elementaryPoly N k := by
  classical
  unfold elementaryPoly
  rw [map_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro f _
  by_cases hf : StrictMono f
  · rw [if_pos hf]
    have hn : (List.ofFn f).Nodup := List.nodup_ofFn.mpr hf.injective
    have hh := reverse_tilde_word (List.ofFn f) hn
    simpa only [List.map_ofFn, Function.comp_def, List.length_ofFn] using hh
  · simp only [if_neg hf, map_zero, smul_zero]

/-- Preservation is proved from elementary generators, not from left freeness. -/
theorem reverse_mem_E {N : ℕ} (f : SkewPolynomial N) (hf : f ∈ E N) :
    reverse N f ∈ E N := by
  induction hf using Subring.closure_induction with
  | mem f hf =>
    obtain ⟨k,rfl⟩ := hf
    rw [reverse_elementary]
    exact (E N).zsmul_mem (Subring.subset_closure ⟨k,rfl⟩) _
  | zero => simpa only [map_zero] using (E N).zero_mem
  | one => simpa only [reverse_one] using (E N).one_mem
  | add f g _ _ hf hg => simpa only [map_add] using (E N).add_mem hf hg
  | neg f _ hf => simpa only [map_neg] using (E N).neg_mem hf
  | mul f g _ _ hf hg => simpa only [reverse_mul] using (E N).mul_mem hg hf

/-- Reversal of an actual staircase monomial carries its exponent-dependent sign. -/
theorem reverse_stair {N : ℕ} (a : StairIndex N) :
    reverse N (stairMonomial a) = reversalSign a.val • stairMonomial a := by
  unfold stairMonomial
  rw [reverse_monomial, one_mul]
  exact PbwL4.monomial_smul N a.val (reversalSign a.val)

/-- The coefficient transport, an involution on the actual elementary subring. -/
def twist {N : ℕ} (a : StairIndex N) (c : E N) : E N :=
  ⟨reversalSign a.val • reverse N (c : SkewPolynomial N),
    (E N).zsmul_mem (reverse_mem_E (N := N) (c : SkewPolynomial N) c.property)
      (reversalSign a.val)⟩

@[simp] theorem twist_zero {N : ℕ} (a : StairIndex N) : twist a 0 = 0 := by
  apply Subtype.ext
  change reversalSign a.val • reverse N 0 = 0
  simp

@[simp] theorem twist_involutive {N : ℕ} (a : StairIndex N) (c : E N) :
    twist a (twist a c) = c := by
  apply Subtype.ext
  change reversalSign a.val • reverse N (reversalSign a.val • reverse N c) = c
  rw [map_zsmul, reverse_involutive, smul_smul, reversalSign_square, one_smul]

/-- LEFT coefficients reverse to RIGHT coefficients; no commutation is assumed. -/
theorem reverse_left_sum {N : ℕ} (c : StairIndex N → E N) :
    reverse N (∑ a, (c a : SkewPolynomial N) * stairMonomial a) =
      ∑ a, stairMonomial a * (twist a (c a) : SkewPolynomial N) := by
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [reverse_mul, reverse_stair]
  change (reversalSign a.val • stairMonomial a) * reverse N (c a) =
    stairMonomial a * (reversalSign a.val • reverse N (c a))
  rw [smul_mul_assoc, mul_smul_comm]

theorem reverse_right_sum {N : ℕ} (c : StairIndex N → E N) :
    reverse N (∑ a, stairMonomial a * (c a : SkewPolynomial N)) =
      ∑ a, (twist a (c a) : SkewPolynomial N) * stairMonomial a := by
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [reverse_mul, reverse_stair]
  change reverse N (c a) * (reversalSign a.val • stairMonomial a) =
    (reversalSign a.val • reverse N (c a)) * stairMonomial a
  rw [smul_mul_assoc, mul_smul_comm]

/-- Literal integral LEFT coefficient-zero law, including ranks zero and one. -/
theorem left_coeff_zero (N : ℕ) (c : StairIndex N → E N)
    (hc : (∑ a, (c a : SkewPolynomial N) * stairMonomial a) = 0) :
    ∀ a, c a = 0 := by
  have hr := congrArg (reverse N) hc
  rw [reverse_left_sum, map_zero] at hr
  have hh := StaircaseIndependence.right_coeff_zero N (fun a => twist a (c a)) hr
  intro a
  have ht := congrArg (twist a) (hh a)
  simpa only [twist_involutive, twist_zero] using ht

/-- Literal LEFT coefficient uniqueness, without a freeness premise. -/
theorem left_coeff_unique (N : ℕ) (c b : StairIndex N → E N)
    (h : (∑ a, (c a : SkewPolynomial N) * stairMonomial a) =
      ∑ a, (b a : SkewPolynomial N) * stairMonomial a) : c = b := by
  have hz : (∑ a, ((c a - b a : E N) : SkewPolynomial N) * stairMonomial a) = 0 := by
    change (∑ a, ((c a : SkewPolynomial N) - (b a : SkewPolynomial N)) * stairMonomial a) = 0
    simp only [sub_mul, Finset.sum_sub_distrib, h, sub_self]
  have hh := left_coeff_zero N (fun a => c a - b a) hz
  funext a
  exact sub_eq_zero.mp (hh a)

/-- Every actual integer skew polynomial has unique literal LEFT E coefficients.
The all-N theorem includes N=0 and N=1, without a small-rank kernel API. -/
theorem left_decomposition_unique (N : ℕ) (f : SkewPolynomial N) :
    ∃! c : StairIndex N → E N,
      f = ∑ a, (c a : SkewPolynomial N) * stairMonomial a := by
  obtain ⟨c,hc⟩ := right_span N (reverse N f)
  have hr := congrArg (reverse N) hc
  rw [reverse_involutive, reverse_right_sum] at hr
  refine ⟨(fun a => twist a (c a)), hr, ?_⟩
  intro b hb
  exact left_coeff_unique N b _ (hb.symm.trans hr)

/-- Specialization to the actual joint divided-difference kernel, N=n+2. -/
theorem left_kernel_coeff_zero (n : ℕ)
    (c : StairIndex (n+2) → OddSymmetricKernel.kernelSubring n)
    (hc : (∑ a, (c a : SkewPolynomial (n+2)) * stairMonomial a) = 0) :
    ∀ a, c a = 0 := by
  let b : StairIndex (n+2) → E (n+2) := fun a => ⟨c a,
    (le_of_eq (StaircaseIndependence.E_eq_kernel n).symm) (c a).property⟩
  have hh := left_coeff_zero (n+2) b hc
  intro a
  apply Subtype.ext
  exact congrArg (fun x : E (n+2) => (x : SkewPolynomial (n+2))) (hh a)

theorem left_kernel_coeff_unique (n : ℕ)
    (c b : StairIndex (n+2) → OddSymmetricKernel.kernelSubring n)
    (h : (∑ a, (c a : SkewPolynomial (n+2)) * stairMonomial a) =
      ∑ a, (b a : SkewPolynomial (n+2)) * stairMonomial a) : c = b := by
  have hz : (∑ a, ((c a - b a : OddSymmetricKernel.kernelSubring n) :
      SkewPolynomial (n+2)) * stairMonomial a) = 0 := by
    change (∑ a, ((c a : SkewPolynomial (n+2)) - (b a : SkewPolynomial (n+2))) *
      stairMonomial a) = 0
    simp only [sub_mul, Finset.sum_sub_distrib, h, sub_self]
  have hh := left_kernel_coeff_zero n (fun a => c a - b a) hz
  funext a
  exact sub_eq_zero.mp (hh a)

theorem left_kernel_decomposition_unique (n : ℕ) (f : SkewPolynomial (n+2)) :
    ∃! c : StairIndex (n+2) → OddSymmetricKernel.kernelSubring n,
      f = ∑ a, (c a : SkewPolynomial (n+2)) * stairMonomial a := by
  rw [← StaircaseIndependence.E_eq_kernel]
  exact left_decomposition_unique (n+2) f

end
end OddMath.Frontier.StaircaseLeft
