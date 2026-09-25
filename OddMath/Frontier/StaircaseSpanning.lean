import OddMath.Frontier.ElementaryBranching

/-! EKL 1111.1320v1, Prop. 2.13 (right spanning only), with H_N from (2.46).
Every helper in this file serves `right_span`. No independence/rank claim.
The first-variable elimination keeps elementary coefficients on the RIGHT. -/
namespace OddMath.Frontier.StaircaseSpanning
open OddMath.SkewPolynomial (SkewPolynomial generator monomial expSingle)
open FiniteCompleteElementary ElementaryBranching PlacticEvaluation
open scoped BigOperators
noncomputable section

/-- The literal staircase bounds, including its zero exponent. -/
def StairIndex (N : ℕ) := {a : Fin N → ℕ // ∀ i, a i ≤ N-1-i.val}

instance (N : ℕ) : Fintype (StairIndex N) := by
  classical
  exact Fintype.ofInjective (fun a : StairIndex N =>
    fun i : Fin N => (⟨a.val i, by have h := a.property i; omega⟩ : Fin (N+1)))
    (by intro a b h; apply Subtype.ext; funext i; exact congrArg Fin.val (congrFun h i))

def stairMonomial {N : ℕ} (a : StairIndex N) : SkewPolynomial N := monomial a.val 1

def X (N : ℕ) : SkewPolynomial (N+1) := generator 0

def tailE (N k : ℕ) : SkewPolynomial (N+1) :=
  FiniteWords.strictSum (fun i : Fin N => tildeGenerator i.succ) k

@[simp] theorem tailE_zero (N : ℕ) : tailE N 0 = 1 := by simp [tailE]

theorem tailE_succ (N k : ℕ) :
    tailE N (k+1) = elementaryPoly (N+1) (k+1) - X N * tailE N k := by
  rw [elementaryPoly_eq_strictSum, FiniteWords.strictSum_succ]
  have hx : tildeGenerator (0 : Fin (N+1)) = X N := by simp [tildeGenerator, X]
  rw [hx]
  change tailE N (k+1) = X N * tailE N k + tailE N (k+1) - X N * tailE N k
  abel

/-- Literal finite cancellation, with first-variable powers on the left. -/
theorem tailE_expand (N k : ℕ) :
    tailE N k = ∑ j ∈ Finset.range (k+1), (-1:ℤ)^j •
      (X N ^ j * elementaryPoly (N+1) (k-j)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [tailE_succ, ih]
    conv_rhs => rw [Finset.sum_range_succ']
    simp only [Nat.add_sub_add_right, Nat.sub_zero, pow_zero, one_mul, one_smul]
    have hs : (∑ j ∈ Finset.range (k+1), (-1:ℤ)^(j+1) •
        (X N ^ (j+1) * elementaryPoly (N+1) (k-j))) =
        -(X N * ∑ j ∈ Finset.range (k+1), (-1:ℤ)^j •
          (X N ^ j * elementaryPoly (N+1) (k-j))) := by
      simp only [pow_succ', mul_neg, mul_one, neg_one_mul, neg_smul, Finset.mul_sum,
        mul_smul_comm, mul_assoc, Finset.sum_neg_distrib]
    rw [hs]
    exact sub_eq_neg_add _ _

theorem tailE_oversized (N : ℕ) : tailE N (N+1) = 0 := by
  classical
  unfold tailE FiniteWords.strictSum
  apply Finset.sum_eq_zero
  intro f _
  have h := Fintype.card_le_of_injective f.val f.property.injective
  simp only [Fintype.card_fin] at h
  omega

/-- Actual bounded right span in the first variable. -/
def firstSpan (N : ℕ) : AddSubgroup (SkewPolynomial (N+1)) where
  carrier := {p | ∃ c : Fin (N+1) → E (N+1), p = ∑ j, X N ^ j.val * (c j : SkewPolynomial (N+1))}
  zero_mem' := by
    refine ⟨fun _ => 0, ?_⟩
    simp
  add_mem' := by
    rintro p q ⟨c,rfl⟩ ⟨d,rfl⟩
    refine ⟨fun j => c j + d j, ?_⟩
    simp [mul_add, Finset.sum_add_distrib]
  neg_mem' := by
    rintro p ⟨c,rfl⟩
    refine ⟨fun j => -c j, ?_⟩
    simp [Finset.sum_neg_distrib]

theorem firstSpan_term (N j : ℕ) (hj : j < N+1) (c : E (N+1)) :
    X N ^ j * (c : SkewPolynomial (N+1)) ∈ firstSpan N := by
  classical
  refine ⟨fun i => if i = ⟨j,hj⟩ then c else 0, ?_⟩
  simp only [apply_ite, Subring.coe_zero, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem firstSpan_coeff (N : ℕ) (c : E (N+1)) :
    (c : SkewPolynomial (N+1)) ∈ firstSpan N := by
  simpa using firstSpan_term N 0 (by omega) c

theorem firstSpan_right (N : ℕ) {p : SkewPolynomial (N+1)}
    (hp : p ∈ firstSpan N) (c : E (N+1)) : p * c ∈ firstSpan N := by
  obtain ⟨d,rfl⟩ := hp
  refine ⟨fun j => d j * c, ?_⟩
  simp [Finset.sum_mul, mul_assoc]

/-- The missing monic power reduction is integral, not a rank-count argument. -/
theorem first_power_mem (N : ℕ) : X N ^ (N+1) ∈ firstSpan N := by
  have h := tailE_expand N (N+1)
  rw [tailE_oversized, Finset.sum_range_succ] at h
  simp only [Nat.sub_self, elementaryPoly_zero, mul_one] at h
  have hs : (∑ j ∈ Finset.range (N+1), (-1:ℤ)^j •
      (X N ^ j * elementaryPoly (N+1) (N+1-j))) ∈ firstSpan N := by
    apply (firstSpan N).sum_mem
    intro j hj
    apply (firstSpan N).zsmul_mem
    exact firstSpan_term N j (Finset.mem_range.mp hj)
      ⟨_, Subring.subset_closure ⟨N+1-j,rfl⟩⟩
  have ht : (-1:ℤ)^(N+1) • X N ^ (N+1) ∈ firstSpan N := by
    rw [eq_neg_of_add_eq_zero_right h.symm]
    exact (firstSpan N).neg_mem hs
  have hunit : (-1:ℤ)^(N+1) * (-1:ℤ)^(N+1) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; norm_num
  have hh := (firstSpan N).zsmul_mem ht ((-1:ℤ)^(N+1))
  simpa only [smul_smul, hunit, one_smul] using hh

theorem firstSpan_left_X (N : ℕ) {p : SkewPolynomial (N+1)}
    (hp : p ∈ firstSpan N) : X N * p ∈ firstSpan N := by
  obtain ⟨c,rfl⟩ := hp
  rw [Finset.mul_sum]
  apply (firstSpan N).sum_mem
  intro j _
  rw [← mul_assoc, ← pow_succ']
  by_cases hj : j.val+1 < N+1
  · exact firstSpan_term N _ hj (c j)
  · have he : j.val+1 = N+1 := by omega
    rw [he]
    exact firstSpan_right N (first_power_mem N) (c j)

theorem firstSpan_power (N k : ℕ) : X N ^ k ∈ firstSpan N := by
  induction k with
  | zero => simpa using firstSpan_coeff N 1
  | succ k ih => rw [pow_succ']; exact firstSpan_left_X N ih

theorem tailE_mem_firstSpan (N k : ℕ) : tailE N k ∈ firstSpan N := by
  rw [tailE_expand]
  apply (firstSpan N).sum_mem
  intro j _
  apply (firstSpan N).zsmul_mem
  exact firstSpan_right N (firstSpan_power N j)
    ⟨_, Subring.subset_closure ⟨k-j,rfl⟩⟩

/-- Anticommutation is applied only across the disjoint tail alphabet. -/
theorem tailE_mul_X (N k : ℕ) :
    tailE N k * X N = (-1:ℤ)^k • (X N * tailE N k) := by
  have hx (i : Fin N) : X N * tildeGenerator i.succ =
      -(tildeGenerator i.succ * X N) := by
    simp only [X, tildeGenerator, mul_smul_comm, smul_mul_assoc]
    have hc : generator (0 : Fin (N+1)) * generator i.succ =
        -(generator i.succ * generator 0) :=
      OddMath.SkewPolynomial.generator_anticommute _ _ (Fin.succ_ne_zero i).symm
    rw [hc]
    simp
  have h := FiniteWords.mul_strictSum (X N)
    (fun i : Fin N => tildeGenerator i.succ) hx k
  have hunit : (-1:ℤ)^k * (-1:ℤ)^k = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; norm_num
  have h' := congrArg (fun p => (-1:ℤ)^k • p) h
  simpa only [smul_smul, hunit, one_smul] using h'.symm

theorem tailE_power_mem (N k j : ℕ) : tailE N k * X N ^ j ∈ firstSpan N := by
  induction j with
  | zero => simpa using tailE_mem_firstSpan N k
  | succ j ih =>
    rw [pow_succ', ← mul_assoc, tailE_mul_X, smul_mul_assoc, mul_assoc]
    exact (firstSpan N).zsmul_mem (firstSpan_left_X N ih) _

theorem tailE_left_mem (N k : ℕ) {p : SkewPolynomial (N+1)}
    (hp : p ∈ firstSpan N) : tailE N k * p ∈ firstSpan N := by
  obtain ⟨c,rfl⟩ := hp
  rw [Finset.mul_sum]
  apply (firstSpan N).sum_mem
  intro j _
  rw [← mul_assoc]
  exact firstSpan_right N (tailE_power_mem N k j.val) (c j)

/-- Order-preserving inclusion of the smaller alphabet as the tail. -/
def shift (N : ℕ) : SkewPolynomial N →+* SkewPolynomial (N+1) where
  toFun := VariableEmbedding.embed (Fin.succOrderEmb N)
  map_zero' := VariableEmbedding.embed_zero _
  map_one' := VariableEmbedding.embed_one _
  map_add' := VariableEmbedding.embed_add _
  map_mul' := VariableEmbedding.embed_mul _

@[simp] theorem shift_generator (N : ℕ) (i : Fin N) :
    shift N (generator i) = generator i.succ := by
  change VariableEmbedding.embed (Fin.succOrderEmb N) (monomial (expSingle i) 1) = _
  rw [VariableEmbedding.embed_monomial]
  congr 1
  funext j
  cases j using Fin.cases with
  | zero =>
    rw [VariableEmbedding.expEmbed_not_mem_range]
    · simp [expSingle]
    · rintro ⟨j,hj⟩
      exact Fin.succ_ne_zero j hj
  | succ j =>
    change VariableEmbedding.expEmbed (Fin.succOrderEmb N) (expSingle i)
      (Fin.succOrderEmb N j) = _
    rw [VariableEmbedding.expEmbed_apply]
    simp [expSingle]

@[simp] theorem shift_tilde (N : ℕ) (i : Fin N) :
    shift N (tildeGenerator i) = -tildeGenerator i.succ := by
  simp [tildeGenerator, pow_succ]

/-- The tilde signs are shifted, not silently identified. -/
theorem shift_elementary (N k : ℕ) :
    shift N (elementaryPoly N k) = (-1:ℤ)^k • tailE N k := by
  classical
  rw [elementaryPoly_eq_strictSum]
  simp only [FiniteWords.strictSum, map_sum, tailE, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro f _
  simp only [FiniteWords.word, map_list_prod, List.map_ofFn, Function.comp_def, shift_tilde]
  have hneg : List.ofFn (fun i => -tildeGenerator (f.val i).succ) =
      (List.ofFn (fun i => tildeGenerator (f.val i).succ)).map Neg.neg := by simp [Function.comp_def]
  rw [hneg, List.prod_map_neg]
  simp only [List.length_ofFn, zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one]

/-- The entire actual tail elementary subring preserves the bounded span.
This proves the missing ordered reduction for PRODUCTS, not just generators. -/
theorem shift_E_left_mem (N : ℕ) (e : E N) {p : SkewPolynomial (N+1)}
    (hp : p ∈ firstSpan N) : shift N e * p ∈ firstSpan N := by
  have h : ∀ f ∈ E N, ∀ p ∈ firstSpan N, shift N f * p ∈ firstSpan N := by
    intro f hf
    induction hf using Subring.closure_induction with
    | mem f hf =>
      obtain ⟨k,rfl⟩ := hf
      intro p hp
      rw [shift_elementary, smul_mul_assoc]
      exact (firstSpan N).zsmul_mem (tailE_left_mem N k hp) _
    | zero => intro p _; simpa using (firstSpan N).zero_mem
    | one => intro p hp; simpa using hp
    | add a b _ _ ha hb =>
      intro p hp
      rw [map_add, add_mul]
      exact (firstSpan N).add_mem (ha p hp) (hb p hp)
    | neg a _ ha =>
      intro p hp
      rw [map_neg, neg_mul]
      exact (firstSpan N).neg_mem (ha p hp)
    | mul a b _ _ ha hb =>
      intro p hp
      rw [map_mul, mul_assoc]
      exact ha _ (hb p hp)
  exact h e e.property p hp

theorem shift_E_mem (N : ℕ) (e : E N) : shift N e ∈ firstSpan N := by
  have h := shift_E_left_mem N e (firstSpan_coeff N 1)
  simpa using h

/-- The exact finite-sum right span requested by Prop. 2.13. -/
def rightSpan (N : ℕ) : AddSubgroup (SkewPolynomial N) where
  carrier := {p | ∃ c : StairIndex N → E N, p = ∑ a, stairMonomial a * (c a : SkewPolynomial N)}
  zero_mem' := by
    refine ⟨fun _ => 0, ?_⟩
    simp
  add_mem' := by
    rintro p q ⟨c,rfl⟩ ⟨d,rfl⟩
    refine ⟨fun a => c a + d a, ?_⟩
    simp [mul_add, Finset.sum_add_distrib]
  neg_mem' := by
    rintro p ⟨c,rfl⟩
    refine ⟨fun a => -c a, ?_⟩
    simp [Finset.sum_neg_distrib]

theorem rightSpan_term {N : ℕ} (a : StairIndex N) (c : E N) :
    stairMonomial a * (c : SkewPolynomial N) ∈ rightSpan N := by
  classical
  refine ⟨fun b => if b=a then c else 0, ?_⟩
  simp only [apply_ite, Subring.coe_zero, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- Prepending a bounded first power gives EXACTLY the next staircase. -/
def prependIndex {N : ℕ} (j : Fin (N+1)) (a : StairIndex N) : StairIndex (N+1) :=
  ⟨Fin.cons j.val a.val, by
    intro i
    cases i using Fin.cases with
    | zero => simp only [Fin.cons_zero, Fin.val_zero]; omega
    | succ i =>
      simp only [Fin.cons_succ, Fin.val_succ]
      have h := a.property i
      omega⟩

/-- Exact ordered monomial identity, retaining the crossing sign rather than
assuming that an entire tail polynomial commutes with the first variable. -/
theorem shift_monomial_mul_power (N : ℕ) (a : Fin N → ℕ) (j : ℕ) :
    shift N (monomial a 1) * X N ^ j =
      OddMath.skewSign (VariableEmbedding.expEmbed (Fin.succOrderEmb N) a)
        (j • expSingle (0 : Fin (N+1))) • monomial (Fin.cons j a) 1 := by
  have hs : shift N (monomial a 1) =
      monomial (VariableEmbedding.expEmbed (Fin.succOrderEmb N) a) 1 :=
    VariableEmbedding.embed_monomial _ _ _
  rw [hs, X, OddMath.PbwL4.pow_form]
  change OddMath.SkewPolynomial.mul _ _ = _
  rw [OddMath.SkewPolynomial.mul_monomial]
  have he : VariableEmbedding.expEmbed (Fin.succOrderEmb N) a +
      j • expSingle (0 : Fin (N+1)) = Fin.cons j a := by
    funext i
    cases i using Fin.cases with
    | zero =>
      have hz : VariableEmbedding.expEmbed (Fin.succOrderEmb N) a 0 = 0 := by
        apply VariableEmbedding.expEmbed_not_mem_range
        rintro ⟨i,hi⟩
        exact Fin.succ_ne_zero i hi
      simp [Pi.add_apply, hz, expSingle]
    | succ i =>
      have hi := VariableEmbedding.expEmbed_apply (Fin.succOrderEmb N) a i
      simpa [Pi.add_apply, expSingle] using hi
  rw [he]
  simp [monomial, Finsupp.smul_single]

theorem shift_stair_power_mem (N : ℕ) (a : StairIndex N) (j : Fin (N+1)) (c : E (N+1)) :
    shift N (stairMonomial a) * X N ^ j.val * (c : SkewPolynomial (N+1)) ∈ rightSpan (N+1) := by
  rw [stairMonomial, shift_monomial_mul_power, smul_mul_assoc]
  exact (rightSpan (N+1)).zsmul_mem (rightSpan_term (prependIndex j a) c) _

theorem shift_stair_firstSpan (N : ℕ) (a : StairIndex N) {p : SkewPolynomial (N+1)}
    (hp : p ∈ firstSpan N) : shift N (stairMonomial a) * p ∈ rightSpan (N+1) := by
  obtain ⟨c,rfl⟩ := hp
  rw [Finset.mul_sum]
  apply (rightSpan (N+1)).sum_mem
  intro j _
  rw [← mul_assoc]
  exact shift_stair_power_mem N a j (c j)

/-- All-rank finite integral right spanning. The rank step expands actual
monomials, uses tail-alphabet induction, and applies the bounded power lemma. -/
theorem mem_rightSpan (N : ℕ) (f : SkewPolynomial N) : f ∈ rightSpan N := by
  classical
  induction N with
  | zero =>
    have hmon (a : Fin 0 → ℕ) (c : ℤ) : monomial a c ∈ rightSpan 0 := by
      have ha : a = 0 := Subsingleton.elim _ _
      subst a
      let z : StairIndex 0 := ⟨0, fun i => Fin.elim0 i⟩
      have hz : stairMonomial z = (1 : SkewPolynomial 0) := rfl
      have h := rightSpan_term z (c : E 0)
      rw [hz, one_mul] at h
      have hc : ((c : E 0) : SkewPolynomial 0) = monomial 0 c := by
        change c • (1 : SkewPolynomial 0) = monomial 0 c
        change c • monomial 0 1 = monomial 0 c
        simp [monomial, Finsupp.smul_single]
      rwa [hc] at h
    induction f using Finsupp.induction_linear with
    | zero => exact (rightSpan 0).zero_mem
    | add p q hp hq => exact (rightSpan 0).add_mem hp hq
    | single a c => exact hmon a c
  | succ N ih =>
    have hprod (p : SkewPolynomial N) (k : ℕ) :
        shift N p * X N ^ k ∈ rightSpan (N+1) := by
      obtain ⟨c,hc⟩ := ih p
      rw [hc, map_sum, Finset.sum_mul]
      apply (rightSpan (N+1)).sum_mem
      intro a _
      rw [map_mul, mul_assoc]
      exact shift_stair_firstSpan N a (shift_E_left_mem N (c a) (firstSpan_power N k))
    have hmon (a : Fin (N+1) → ℕ) (c : ℤ) : monomial a c ∈ rightSpan (N+1) := by
      let b : Fin N → ℕ := fun i => a i.succ
      let s : ℤ := OddMath.skewSign (VariableEmbedding.expEmbed (Fin.succOrderEmb N) b)
        (a 0 • expSingle (0 : Fin (N+1)))
      have hs : s*s = 1 := ElementaryGeneration.skewSign_square _ _
      have he : Fin.cons (a 0) b = a := by
        funext i
        cases i using Fin.cases <;> rfl
      have h := hprod (monomial b 1) (a 0)
      rw [shift_monomial_mul_power, he] at h
      change s • monomial a 1 ∈ rightSpan (N+1) at h
      have hh := (rightSpan (N+1)).zsmul_mem h (c*s)
      have heq : (c*s) • s • monomial a 1 = monomial a c := by
        rw [smul_smul, mul_assoc, hs, mul_one]
        simp [monomial, Finsupp.smul_single]
      rwa [heq] at hh
    induction f using Finsupp.induction_linear with
    | zero => exact (rightSpan (N+1)).zero_mem
    | add p q hp hq => exact (rightSpan (N+1)).add_mem hp hq
    | single a c => exact hmon a c

theorem right_span (N : ℕ) (f : SkewPolynomial N) :
    ∃ c : StairIndex N → E N, f = ∑ a, stairMonomial a * (c a : SkewPolynomial N) :=
  mem_rightSpan N f

/-- The actual joint-kernel specialization; coefficient order is unchanged. -/
theorem right_span_kernel (n : ℕ) (f : SkewPolynomial (n+2)) :
    ∃ c : StairIndex (n+2) → OddSymmetricKernel.kernelSubring n,
      f = ∑ a, stairMonomial a * (c a : SkewPolynomial (n+2)) := by
  have he : E (n+2) = OddSymmetricKernel.kernelSubring n :=
    (E_eq_elementaryClosure n).trans (ElementaryGeneration.kernel_eq_elementaryClosure n).symm
  obtain ⟨c,hc⟩ := right_span (n+2) f
  refine ⟨fun a => ⟨c a, he ▸ (c a).property⟩, hc⟩

end
end OddMath.Frontier.StaircaseSpanning
