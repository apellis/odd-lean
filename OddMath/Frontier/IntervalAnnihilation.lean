import OddMath.Frontier.NonadjacentDivided
import OddMath.Frontier.ElementaryGeneration

/-! EKL 1111.1320v1, Lemma 2.20, pp. 15–16, (2.62).
The interval is ascending in zero-based indices and acts rightmost first.
An alternative proof uses a three-endpoint operator relation, proved here on the
actual integral skew polynomial algebra, rather than assuming (2.63). -/
namespace OddMath.Frontier.IntervalAnnihilation
open OddMath.SkewPolynomial (SkewPolynomial generator)
open NonadjacentDivided
noncomputable section
variable {n : ℕ}

/-- The three-endpoint relation on arbitrary polynomials, not only generators. -/
theorem triangle (a b c : Fin (n+2)) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (f : SkewPolynomial (n+2)) :
    dividedPair b c hbc (dividedPair a c hac f) +
      dividedPair a c hac (dividedPair a b hab f) +
      dividedPair a b hab (dividedPair b c hbc f) = 0 := by
  have cov₁ (g : SkewPolynomial (n+2)) :
      dividedPair b c hbc (s a c g) = -s a c (dividedPair a b hab g) := by
    simpa only [Equiv.swap_apply_of_ne_of_ne hab.symm hbc,
      Equiv.swap_apply_right, symmetric b a hab.symm] using covariance b c a c hbc hac g
  have cov₂ (g : SkewPolynomial (n+2)) :
      dividedPair a c hac (s a b g) = -s a b (dividedPair b c hbc g) := by
    simpa only [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hac.symm hbc.symm]
      using covariance a c a b hac hab g
  have cov₃ (g : SkewPolynomial (n+2)) :
      dividedPair a b hab (s b c g) = -s b c (dividedPair a c hac g) := by
    simpa only [Equiv.swap_apply_of_ne_of_ne hab hac, Equiv.swap_apply_left]
      using covariance a b b c hab hbc g
  have act₁ (g : SkewPolynomial (n+2)) : s b c (s a c g) = s a c (s a b g) := by
    simpa only [Equiv.swap_apply_of_ne_of_ne hab.symm hbc, Equiv.swap_apply_right,
      s, Equiv.swap_comm b a] using action_conjugation b c a c g
  have act₂ (g : SkewPolynomial (n+2)) : s a c (s a b g) = s a b (s b c g) := by
    simpa only [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hac.symm hbc.symm]
      using action_conjugation a c a b g
  induction f using polynomial_induction with
  | hconst r => simp only [map_smul, divided_one, smul_zero, map_zero, add_zero]
  | hgen j =>
    simp only [divided_generator]
    split_ifs <;> simp only [divided_one, map_zero, add_zero]
  | hadd f g hf hg =>
    simp only [map_add]
    calc
      _ = ((dividedPair b c hbc (dividedPair a c hac f) +
        dividedPair a c hac (dividedPair a b hab f) +
        dividedPair a b hab (dividedPair b c hbc f)) +
        (dividedPair b c hbc (dividedPair a c hac g) +
        dividedPair a c hac (dividedPair a b hab g) +
        dividedPair a b hab (dividedPair b c hbc g))) := by abel
      _ = 0 := by rw [hf, hg, add_zero]
  | hmul f g hf hg =>
    simp only [divided_mul, map_add, cov₁, cov₂, cov₃, act₁, act₂]
    calc
      _ = (dividedPair b c hbc (dividedPair a c hac f) +
        dividedPair a c hac (dividedPair a b hab f) +
        dividedPair a b hab (dividedPair b c hbc f)) * g +
        s a b (s b c f) * (dividedPair b c hbc (dividedPair a c hac g) +
        dividedPair a c hac (dividedPair a b hab g) +
        dividedPair a b hab (dividedPair b c hbc g)) := by noncomm_ring
      _ = 0 := by rw [hf, hg, zero_mul, mul_zero, add_zero]

/-- Literal ascending composition ∂a ... ∂(a+k-1); the last acts first. -/
def ascending (a : ℕ) : (k : ℕ) → a+k ≤ n+1 →
    SkewPolynomial (n+2) →ₗ[ℤ] SkewPolynomial (n+2)
  | 0, _ => LinearMap.id
  | k+1, h => (ascending a k (by omega)).comp
      (AllRankDivided.divided ⟨a+k, by omega⟩)

@[simp] theorem ascending_zero (a : ℕ) (h : a+0 ≤ n+1) (f : SkewPolynomial (n+2)) :
    ascending a 0 h f = f := rfl

@[simp] theorem ascending_succ (a k : ℕ) (h : a+(k+1) ≤ n+1)
    (f : SkewPolynomial (n+2)) :
    ascending a (k+1) h f = ascending a k (by omega)
      (AllRankDivided.divided ⟨a+k, by omega⟩ f) := rfl

/-- Move a disjoint pair through an interval, retaining the vanishing conclusion.
No swap-invariance of an odd symmetric polynomial is used. -/
theorem ascending_pair_zero (a k : ℕ) (h : a+k ≤ n+1)
    (u v : Fin (n+2)) (huv : u ≠ v)
    (hd : ∀ i : Fin (n+1), a ≤ i.val → i.val < a+k →
      i.castSucc ≠ u ∧ i.castSucc ≠ v ∧ i.succ ≠ u ∧ i.succ ≠ v)
    (f : SkewPolynomial (n+2)) (hf : ascending a k h f = 0) :
    ascending a k h (dividedPair u v huv f) = 0 := by
  induction k generalizing f with
  | zero =>
    change f = 0 at hf
    simp only [ascending_zero, hf, map_zero]
  | succ k ih =>
    let i : Fin (n+1) := ⟨a+k, by omega⟩
    obtain ⟨h₁,h₂,h₃,h₄⟩ := hd i (by dsimp [i]; omega) (by dsimp [i]; omega)
    have hc : AllRankDivided.divided i (dividedPair u v huv f) =
        -dividedPair u v huv (AllRankDivided.divided i f) := by
      rw [← adjacent i]
      exact anticommutation _ _ _ _ _ huv h₁ h₂ h₃ h₄ f
    change ascending a k _ (AllRankDivided.divided i (dividedPair u v huv f)) = 0
    rw [hc, map_neg]
    apply neg_eq_zero.mpr
    apply ih (by omega) (fun j hj hj' => hd j hj (by omega)) (AllRankDivided.divided i f)
    exact hf

/-- EKL (2.62), with the upper endpoint expressed by the interval length. -/
theorem annihilate_length (u : Fin (n+2)) (k : ℕ) (hv : u.val+k+1 < n+2)
    (f : SkewPolynomial (n+2)) (hf : f ∈ OddSymmetricKernel.kernelSubring n) :
    ascending (u.val+1) k (by omega)
      (dividedPair u ⟨u.val+k+1, hv⟩ (by intro h; have := congrArg Fin.val h; simp only [Fin.val_mk] at this; omega) f) = 0 := by
  induction k with
  | zero =>
    let i : Fin (n+1) := ⟨u.val, by omega⟩
    change dividedPair i.castSucc i.succ _ f = 0
    rw [adjacent]
    exact hf i
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
    rw [ha, hf i, map_zero, add_zero] at ht
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

/-- The assigned interval map: endpoints are zero-based, all interior adjacent
indices are in ascending order, and composition acts rightmost first. -/
def interval (u v : Fin (n+2)) (huv : u < v) :
    SkewPolynomial (n+2) →ₗ[ℤ] SkewPolynomial (n+2) :=
  (ascending (u.val+1) (v.val-(u.val+1)) (by have := v.isLt; omega)).comp
    (dividedPair u v (ne_of_lt huv))

/-- Full kernel theorem, for every rank and every element of the actual kernel. -/
theorem annihilate (u v : Fin (n+2)) (huv : u < v)
    (f : SkewPolynomial (n+2)) (hf : f ∈ OddSymmetricKernel.kernelSubring n) :
    interval u v huv f = 0 := by
  have hval : u.val+(v.val-(u.val+1))+1 = v.val := by
    have : u.val < v.val := huv
    omega
  have h := annihilate_length u (v.val-(u.val+1)) (by rw [hval]; exact v.isLt) f hf
  have he : (⟨u.val+(v.val-(u.val+1))+1, by rw [hval]; exact v.isLt⟩ : Fin (n+2)) = v :=
    Fin.ext hval
  simpa only [interval, LinearMap.comp_apply, he] using h

/-- The empty interval is exactly the inherited adjacent operator. -/
theorem interval_adjacent (i : Fin (n+1)) :
    interval i.castSucc i.succ (by change i.val < i.val+1; omega) =
      AllRankDivided.divided i := by
  have hz : i.succ.val-(i.castSucc.val+1) = 0 := by
    change (i.val+1)-(i.val+1) = 0
    omega
  simp only [interval, hz, ascending, LinearMap.id_comp, adjacent]

/-- All literal elementary generators, in every degree, satisfy (2.62). -/
theorem annihilate_elementary (u v : Fin (n+2)) (huv : u < v) (k : ℕ) :
    interval u v huv (FiniteCompleteElementary.elementaryPoly (n+2) k) = 0 :=
  annihilate u v huv _ (OddSymmetricKernel.elementary_mem n k)

/-- Product closure concerns arbitrary actual kernel elements, with no degree
bound or induction hypotheses on factors. -/
theorem annihilate_product (u v : Fin (n+2)) (huv : u < v)
    (f g : SkewPolynomial (n+2))
    (hf : f ∈ OddSymmetricKernel.kernelSubring n)
    (hg : g ∈ OddSymmetricKernel.kernelSubring n) :
    interval u v huv (f*g) = 0 :=
  annihilate u v huv _ ((OddSymmetricKernel.kernelSubring n).mul_mem hf hg)

/-- Consumer of the installed integral elementary-generation equivalence;
this is the actual generated subring, not a substitute carrier. -/
theorem annihilate_generated (u v : Fin (n+2)) (huv : u < v)
    (f : SkewPolynomial (n+2)) (hf : f ∈ ElementaryGeneration.elementaryClosure n) :
    interval u v huv f = 0 := by
  apply annihilate u v huv f
  rw [ElementaryGeneration.kernel_eq_elementaryClosure]
  exact hf

/-- A general ordered-product consumer, with unrestricted degrees and length. -/
theorem annihilate_elementaryWord (u v : Fin (n+2)) (huv : u < v) (w : List ℕ) :
    interval u v huv (ElementaryGeneration.elementaryWord (n+2) w) = 0 := by
  apply annihilate u v huv
  unfold ElementaryGeneration.elementaryWord
  apply (OddSymmetricKernel.kernelSubring n).list_prod_mem
  intro f hf
  obtain ⟨k, _, rfl⟩ := List.mem_map.mp hf
  exact OddSymmetricKernel.elementary_mem n k

end
end OddMath.Frontier.IntervalAnnihilation
