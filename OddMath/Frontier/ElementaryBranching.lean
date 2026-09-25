import OddMath.Frontier.ElementaryGeneration
import OddMath.Frontier.VariableEmbedding

/-! EKL 1111.1320v1, (2.23), Lemma 2.5 (2.29), Corollary 2.6.
All helpers below discharge the last-variable reduction used by Prop. 2.13.
Products retain source order, with the last tilde variable on the RIGHT.
No module-freeness or small-rank divided-kernel theorem is asserted here. -/
namespace OddMath.Frontier.ElementaryBranching
open OddMath.SkewPolynomial (SkewPolynomial generator expSingle monomial)
open FiniteCompleteElementary PlacticEvaluation
open scoped BigOperators
noncomputable section

/-- The literal order-preserving «prefix» variable inclusion. -/
def «prefix» (N : ℕ) : SkewPolynomial N →+* SkewPolynomial (N+1) where
  toFun := VariableEmbedding.embed Fin.castSuccOrderEmb
  map_zero' := VariableEmbedding.embed_zero _
  map_one' := VariableEmbedding.embed_one _
  map_add' := VariableEmbedding.embed_add _
  map_mul' := VariableEmbedding.embed_mul _

theorem prefix_eq_embed (N : ℕ) (f : SkewPolynomial N) :
    «prefix» N f = VariableEmbedding.embed Fin.castSuccOrderEmb f := rfl

@[simp] theorem prefix_generator (N : ℕ) (i : Fin N) :
    «prefix» N (generator i) = generator i.castSucc := by
  change VariableEmbedding.embed Fin.castSuccOrderEmb (monomial (expSingle i) 1) = _
  rw [VariableEmbedding.embed_monomial]
  congr 1
  funext j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · rw [VariableEmbedding.expEmbed_not_mem_range]
    · simp [expSingle]
    · rintro ⟨j,hj⟩
      exact Fin.castSucc_ne_last j hj
  · change VariableEmbedding.expEmbed Fin.castSuccOrderEmb (expSingle i)
      (Fin.castSuccOrderEmb j) = _
    rw [VariableEmbedding.expEmbed_apply]
    simp [expSingle]

/-- The source variable x-tilde_(N+1)=(-1)^N x_(N+1). -/
def lastTilde (N : ℕ) : SkewPolynomial (N+1) := tildeGenerator (Fin.last N)

@[simp] theorem prefix_tilde (N : ℕ) (i : Fin N) :
    «prefix» N (tildeGenerator i) = tildeGenerator i.castSucc := by
  simp only [tildeGenerator, map_zsmul, prefix_generator]
  rfl

/-- Transport the literal increasing-word sum along the actual «prefix» hom. -/
theorem prefix_elementary (N k : ℕ) :
    «prefix» N (elementaryPoly N k) =
      FiniteWords.strictSum (fun i : Fin N => tildeGenerator i.castSucc) k := by
  classical
  rw [elementaryPoly_eq_strictSum]
  simp only [FiniteWords.strictSum, FiniteWords.word, map_sum, map_list_prod,
    List.map_ofFn, Function.comp_def, prefix_tilde]

/-- Last-letter splitting of the SAME ordered sums; the induction only
reassociates products and never commutes the last factor. -/
theorem strictSum_last {R : Type*} [Ring R] (N k : ℕ) (x : Fin (N+1) → R) :
    FiniteWords.strictSum x (k+1) =
      FiniteWords.strictSum (fun i : Fin N => x i.castSucc) (k+1) +
      FiniteWords.strictSum (fun i : Fin N => x i.castSucc) k * x (Fin.last N) := by
  induction N generalizing k with
  | zero =>
    cases k with
    | zero => simp [FiniteWords.strictSum_succ]
    | succ k => simp [FiniteWords.strictSum_succ]
  | succ N ih =>
    cases k with
    | zero =>
      rw [FiniteWords.strictSum_succ x,
        FiniteWords.strictSum_succ (fun i : Fin (N+1) => x i.castSucc)]
      simp only [FiniteWords.strictSum_zero, mul_one, one_mul]
      rw [ih 0 (fun i => x i.succ)]
      simp [add_assoc, Fin.succ_castSucc]
    | succ k =>
      rw [FiniteWords.strictSum_succ, ih k (fun i => x i.succ),
        ih (k+1) (fun i => x i.succ),
        FiniteWords.strictSum_succ (fun i : Fin (N+1) => x i.castSucc),
        FiniteWords.strictSum_succ (fun i : Fin (N+1) => x i.castSucc)]
      simp only [Fin.succ_castSucc]
      have hzero : (0 : Fin (N+1)).castSucc = (0 : Fin (N+2)) := rfl
      have hlast : (Fin.last N).succ = Fin.last (N+1) := rfl
      rw [hzero, hlast]
      noncomm_ring

/-- EKL (2.23), valid even for the empty «prefix» and oversized degree. -/
theorem elementary_succ (N k : ℕ) :
    elementaryPoly (N+1) (k+1) = «prefix» N (elementaryPoly N (k+1)) +
      «prefix» N (elementaryPoly N k) * lastTilde N := by
  rw [elementaryPoly_eq_strictSum, strictSum_last, prefix_elementary, prefix_elementary]
  rfl

/-- EKL Lemma 2.5, (2.29), with the actual order-preserving inclusion.
Finite cancellation works for every N,k, including zero and oversized k. -/
theorem elementary_remove_last (N k : ℕ) :
    «prefix» N (elementaryPoly N k) =
      ∑ j ∈ Finset.range (k+1), (-1:ℤ)^j •
        (elementaryPoly (N+1) (k-j) * lastTilde N ^ j) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hrec : «prefix» N (elementaryPoly N (k+1)) =
        elementaryPoly (N+1) (k+1) - «prefix» N (elementaryPoly N k) * lastTilde N :=
      eq_sub_of_add_eq (elementary_succ N k).symm
    rw [hrec, ih]
    conv_rhs => rw [Finset.sum_range_succ']
    simp only [Nat.add_sub_add_right, Nat.sub_zero, pow_zero, mul_one, one_smul]
    have hs : (∑ j ∈ Finset.range (k+1), (-1:ℤ)^(j+1) •
          (elementaryPoly (N+1) (k-j) * lastTilde N ^ (j+1))) =
        -((∑ j ∈ Finset.range (k+1), (-1:ℤ)^j •
          (elementaryPoly (N+1) (k-j) * lastTilde N ^ j)) * lastTilde N) := by
      simp only [pow_succ, mul_neg_one, neg_smul, Finset.sum_mul,
        smul_mul_assoc, mul_assoc, Finset.sum_neg_distrib]
    rw [hs]
    exact sub_eq_neg_add _ _

/-- Actual elementary-generated subring, in every alphabet rank. -/
def E (N : ℕ) : Subring (SkewPolynomial N) :=
  Subring.closure (Set.range (elementaryPoly N))

/-- EKL Corollary 2.6 at the elementary-generated level, including rank zero.
The generator adjoined is UNTILDED; scalar -1 converts it to the source tilde. -/
theorem adjoin_last_eq (N : ℕ) :
    Subring.closure ((E (N+1) : Set (SkewPolynomial (N+1))) ∪ {generator (Fin.last N)}) =
    Subring.closure (((E N).map («prefix» N) : Set (SkewPolynomial (N+1))) ∪
      {generator (Fin.last N)}) := by
  let A := Subring.closure ((E (N+1) : Set (SkewPolynomial (N+1))) ∪
    {generator (Fin.last N)})
  let B := Subring.closure (((E N).map («prefix» N) : Set (SkewPolynomial (N+1))) ∪
    {generator (Fin.last N)})
  have hA : generator (Fin.last N) ∈ A := Subring.subset_closure (Or.inr rfl)
  have hB : generator (Fin.last N) ∈ B := Subring.subset_closure (Or.inr rfl)
  have htA : lastTilde N ∈ A := A.zsmul_mem hA ((-1:ℤ)^N)
  have htB : lastTilde N ∈ B := B.zsmul_mem hB ((-1:ℤ)^N)
  have hpB (k : ℕ) : «prefix» N (elementaryPoly N k) ∈ B := by
    apply Subring.subset_closure
    apply Or.inl
    exact ⟨elementaryPoly N k, Subring.subset_closure ⟨k,rfl⟩, rfl⟩
  have heB : E (N+1) ≤ B := by
    apply Subring.closure_le.mpr
    rintro f ⟨k,rfl⟩
    cases k with
    | zero => simpa using B.one_mem
    | succ k => rw [elementary_succ]; exact B.add_mem (hpB _) (B.mul_mem (hpB _) htB)
  have heA (k : ℕ) : elementaryPoly (N+1) k ∈ A :=
    Subring.subset_closure (Or.inl (Subring.subset_closure ⟨k,rfl⟩))
  have hpA : (E N).map («prefix» N) ≤ A := by
    apply Subring.map_le_iff_le_comap.mpr
    apply Subring.closure_le.mpr
    rintro f ⟨k,rfl⟩
    change «prefix» N (elementaryPoly N k) ∈ A
    rw [elementary_remove_last]
    apply A.sum_mem
    intro j _
    exact A.zsmul_mem (A.mul_mem (heA _) (A.pow_mem htA _)) _
  apply le_antisymm
  · apply Subring.closure_le.mpr
    rintro f (hf | hf)
    · exact heB hf
    · obtain rfl := Set.mem_singleton_iff.mp hf
      exact hB
  · apply Subring.closure_le.mpr
    rintro f (hf | hf)
    · exact hpA hf
    · obtain rfl := Set.mem_singleton_iff.mp hf
      exact hA

/-- The range closure differs from the inherited bounded-generator closure
only by e_0=1 and the vanishing oversized elementary polynomials. -/
theorem E_eq_elementaryClosure (n : ℕ) :
    E (n+2) = ElementaryGeneration.elementaryClosure n := by
  apply le_antisymm
  · apply Subring.closure_le.mpr
    rintro f ⟨k,rfl⟩
    by_cases hz : k=0
    · subst k; simpa using (ElementaryGeneration.elementaryClosure n).one_mem
    by_cases hk : k ≤ n+2
    · exact Subring.subset_closure ⟨k,by omega,hk,rfl⟩
    · rw [elementaryPoly_eq_zero_of_lt (by omega)]
      exact (ElementaryGeneration.elementaryClosure n).zero_mem
  · apply Subring.closure_le.mpr
    rintro f ⟨k,_,_,rfl⟩
    exact Subring.subset_closure ⟨k,rfl⟩

/-- Source joint-kernel Corollary 2.6 in the inherited range N>=2.
No rank-zero/one divided-kernel API is silently assumed. -/
theorem kernel_adjoin_last_eq (n : ℕ) :
    Subring.closure ((OddSymmetricKernel.kernelSubring (n+1) : Set (SkewPolynomial (n+3))) ∪
      {generator (Fin.last (n+2))}) =
    Subring.closure (((OddSymmetricKernel.kernelSubring n).map («prefix» (n+2)) :
      Set (SkewPolynomial (n+3))) ∪ {generator (Fin.last (n+2))}) := by
  have h (m : ℕ) : OddSymmetricKernel.kernelSubring m = E (m+2) :=
    (ElementaryGeneration.kernel_eq_elementaryClosure m).trans (E_eq_elementaryClosure m).symm
  rw [h (n+1), h n]
  exact adjoin_last_eq (n+2)

end
end OddMath.Frontier.ElementaryBranching
