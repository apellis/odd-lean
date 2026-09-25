import OddMath.Frontier.ThickBubble
import OddMath.Frontier.ProjectorRank
import OddMath.Frontier.BoxPartitionCount

/-! # Decomposition of `e_a ⊗ e_b` into the idempotents `e_α`

EKL arXiv:1111.1320v1, §4.4.1, Theorem 4.16, (4.56)–(4.57), p. 43.  In
`ONH_{a+b} = NilHeckeAction.Presented n` (`a + b = n+2`), for all `a, b`:
`e_a ⊗ e_b = ∑_{α ∈ P(a,b)} e_α` with `e_α = σ_α λ_α` (`ThickBubble.idem`).

The paper deduces this from `ONH_{a+b} ≅ Mat(OΛ_{a+b})` (Cor 2.14).  Here the spanning step is a
graded rank count (`GradedTrace.eq_sum_of_trace`) in the faithful polynomial representation,
graded by monomial degree (`ProjectorRank.Vd`):

* `λ_β σ_α = δ_{αβ} e_{a+b}` (4.54), `(e_a ⊗ e_b) σ_α = σ_α`, `λ_α (e_a ⊗ e_b) = λ_α`;
* `σ_α` has degree `|α| - ab` and `λ_α` degree `ab - |α|`;
* with `C_k = C(k,2)` and `p_k(m)` the number of partitions of `m` with at most `k` parts,
  `tr(e_a ⊗ e_b | V_d) = ∑_{i+j=d} p_a(i - C_a) p_b(j - C_b)`, computed block by block (a block
  of size `≤ 1` carries the identity), and `tr(e_{a+b} | V_m) = p_{a+b}(m - C_{a+b})`;
* `C_{a+b} = C_a + C_b + ab` and `∏_{i ≤ a} (1-q^i)⁻¹ ∏_{i ≤ b} (1-q^i)⁻¹ =
  [a+b choose a]_q ∏_{i ≤ a+b} (1-q^i)⁻¹` (`BoxPartitionCount.sum_pcount_mul`) match the traces
  degree by degree.

Blocks of size `0` or `1` are included; `thm_4_16_right_one`, `thm_4_16_left_one` state the
cases `b = 1`, `a = 1`. -/

namespace OddMath.Frontier.ThickDecomposition
open OddMath.SkewPolynomial (SkewPolynomial monomial generator)
open NilHeckeAction NilCoxeterWords GradedTrace ProjectorRank ThickBubble BoxComplement
open Module LinearMap
noncomputable section

/-! ## Counting -/

/-- `#{partitions of d with at most N parts}`, in the two encodings. -/
theorem card_index (N d : ℕ) :
    Fintype.card (ElementaryBasis.Index N d) = BoxPartitionCount.pcount N d := by
  rw [BoxPartitionCount.pcount, ← Fintype.card_coe]
  exact Fintype.card_congr (Equiv.subtypeEquivRight fun a => by
    rw [BoxPartitionCount.mem_partitions])

/-- For `k ≤ 1` every monomial of degree `i` is a partition. -/
theorem card_expSet_small {k : ℕ} (hk : k ≤ 1) (i : ℕ) :
    (expSet k i).card = BoxPartitionCount.pcount k i := by
  have h := BoxPartitionCount.monomial_count k i
  have hs : BoxPartitionCount.Sq k = {0} := by
    ext l
    simp only [BoxPartitionCount.mem_Sq, Finset.mem_singleton]
    constructor
    · intro _; funext ν; have := ν.isLt; omega
    · intro _ ν; have := ν.isLt; omega
  rw [hs] at h
  simpa [expSet, Finset.filter_singleton] using h

/-- `∑_{i+j=d} p_a(i - C_a) p_b(j - C_b) = ∑_{α ∈ P(a,b)} p_{a+b}(d - C_a - C_b - |α|)`, with
`C_k = C(k,2)` and terms with a negative argument omitted. -/
theorem count_identity (a b d : ℕ) :
    ∑ ij ∈ Finset.antidiagonal d,
      (if a.choose 2 ≤ ij.1 then BoxPartitionCount.pcount a (ij.1 - a.choose 2) else 0) *
        (if b.choose 2 ≤ ij.2 then BoxPartitionCount.pcount b (ij.2 - b.choose 2) else 0) =
      ∑ α ∈ BoxPartitionCount.box a b, if a.choose 2 + b.choose 2 + ∑ i, α i ≤ d then
        BoxPartitionCount.pcount (a+b) (d - a.choose 2 - b.choose 2 - ∑ i, α i) else 0 := by
  set Ca := a.choose 2
  set Cb := b.choose 2
  by_cases hd : Ca + Cb ≤ d
  · obtain ⟨J, rfl⟩ := Nat.exists_eq_add_of_le hd
    have hL : ∑ ij ∈ Finset.antidiagonal (Ca + Cb + J),
        (if Ca ≤ ij.1 then BoxPartitionCount.pcount a (ij.1 - Ca) else 0) *
          (if Cb ≤ ij.2 then BoxPartitionCount.pcount b (ij.2 - Cb) else 0) =
        ∑ ij ∈ Finset.antidiagonal J,
          BoxPartitionCount.pcount a ij.1 * BoxPartitionCount.pcount b ij.2 := by
      rw [← Finset.sum_filter_of_ne (p := fun ij : ℕ × ℕ => Ca ≤ ij.1 ∧ Cb ≤ ij.2)
        (fun ij _ hne => by
          by_contra hc
          refine hne ?_
          by_cases h1 : Ca ≤ ij.1
          · rw [if_neg fun h2 => hc ⟨h1, h2⟩, mul_zero]
          · rw [if_neg h1, zero_mul])]
      refine Finset.sum_nbij' (fun ij => (ij.1 - Ca, ij.2 - Cb)) (fun ij => (ij.1 + Ca, ij.2 + Cb))
        ?_ ?_ ?_ ?_ ?_
      · intro ij hij
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_antidiagonal] at hij ⊢
        omega
      · intro ij hij
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_antidiagonal] at hij ⊢
        omega
      · intro ij hij
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_antidiagonal] at hij
        ext <;> simp <;> omega
      · intro ij _
        simp
      · intro ij hij
        simp only [Finset.mem_filter] at hij
        rw [if_pos hij.2.1, if_pos hij.2.2]
    rw [hL, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => BoxPartitionCount.pcount a i * BoxPartitionCount.pcount b j),
      BoxPartitionCount.sum_pcount_mul, Finset.sum_filter]
    refine Finset.sum_congr rfl fun α _ => ?_
    by_cases hα : ∑ i, α i ≤ J
    · rw [if_pos hα, if_pos (by omega)]
      congr 1
      omega
    · rw [if_neg hα, if_neg (by omega)]
  · rw [Finset.sum_eq_zero, Finset.sum_eq_zero]
    · intro α _
      rw [if_neg (by omega)]
    · intro ij hij
      rw [Finset.mem_antidiagonal] at hij
      by_cases h1 : Ca ≤ ij.1
      · rw [if_neg (show ¬ Cb ≤ ij.2 by omega), mul_zero]
      · rw [if_neg h1, zero_mul]

/-! ## Block operators on a window -/

/-- `e_k` acting on `SkewPolynomial k`; the identity for `k ≤ 1`. -/
def blockOp : (k : ℕ) → SkewPolynomial k →ₗ[ℤ] SkewPolynomial k
  | 0 => LinearMap.id
  | 1 => LinearMap.id
  | m+2 => action m (ZeroHecke.projector m)

theorem hasDegree_blockOp : (k : ℕ) → HasDegree (Vd k) 0 (blockOp k)
  | 0 => hasDegree_id
  | 1 => hasDegree_id
  | _+2 => hasDegree_projector

/-- Diagonal sum of `e_k` on `V_i`: `[C(k,2) ≤ i] p_k(i - C(k,2))`. -/
theorem sum_coeff_blockOp (k i : ℕ) :
    ∑ γ ∈ expSet k i, blockOp k (monomial γ 1) γ =
      ((if k.choose 2 ≤ i then BoxPartitionCount.pcount k (i - k.choose 2) else 0 : ℕ) : ℤ) := by
  match k with
  | 0 | 1 =>
      simp only [blockOp, LinearMap.id_apply, monomial, Finsupp.single_eq_same,
        Finset.sum_const, nsmul_eq_mul, mul_one]
      rw [card_expSet_small (by omega)]
      simp
  | m+2 =>
      rw [← trace_res_eq, trace_projector, card_index]
      split_ifs with h1 h2 h2
      · congr 2
        omega
      · omega
      · omega
      · rfl

/-! ## The operator `e_a ⊗ e_b` on `SkewPolynomial (a+b)` -/

section Blocks
variable {n : ℕ}

/-- A block projector acts on `g · ι(f) · r` through `f`, for spectators `g`, `r`. -/
theorem action_blockE_place {p k : ℕ} (h : p + k ≤ n+2) {g r : SkewPolynomial (n+2)}
    (hg : ∀ i : Fin (n+1), p ≤ i.val → i.val + 1 < p + k → LeftSpect i g)
    (hr : ∀ i : Fin (n+1), p ≤ i.val → i.val + 1 < p + k → RightSpect i r)
    (f : SkewPolynomial k) :
    action n (blockE n p k) (g * place p h f * r) = g * place p h (blockOp k f) * r := by
  match k, h, f with
  | 0, h, f => simp [blockE_zero, blockOp]
  | 1, h, f => simp [blockE_one, blockOp]
  | m+2, h, f =>
      rw [blockE_eq h]
      exact action_window_projector h
        (fun i => hg _ (by simp) (by simp only [OnhWindow.shiftIndex_val]; omega))
        (fun i => hr _ (by simp) (by simp only [OnhWindow.shiftIndex_val]; omega)) f

theorem hasDegree_blockE (p k : ℕ) : HasDegree (Vd (n+2)) 0 (action n (blockE n p k)) :=
  hasDegree_zeroHeckeProduct _

theorem skew_add_mul {N : ℕ} (f g h : SkewPolynomial N) : (f + g) * h = f * h + g * h :=
  OddMath.SkewPolynomial.add_mul f g h

theorem skew_mul_add {N : ℕ} (f g h : SkewPolynomial N) : f * (g + h) = f * g + f * h :=
  OddMath.SkewPolynomial.mul_add f g h

theorem skew_zero_mul {N : ℕ} (f : SkewPolynomial N) : 0 * f = 0 :=
  OddMath.SkewPolynomial.zero_mul f

theorem skew_mul_zero {N : ℕ} (f : SkewPolynomial N) : f * 0 = 0 :=
  OddMath.SkewPolynomial.mul_zero f

variable {a b : ℕ} (hab : a + b = n+2)

/-- The left block `ι_a : SkewPolynomial a → SkewPolynomial (a+b)`. -/
def leftPlace : SkewPolynomial a →+* SkewPolynomial (n+2) := place 0 (by omega)

/-- The right block `ι_b : SkewPolynomial b → SkewPolynomial (a+b)`. -/
def rightPlace : SkewPolynomial b →+* SkewPolynomial (n+2) := place a (by omega)

/-- `(e_a ⊗ e_b)(ι f · ι' g) = ι(e_a f) · ι'(e_b g)`. -/
theorem action_blockE_blockE (f : SkewPolynomial a) (g : SkewPolynomial b) :
    action n (blockE n 0 a * blockE n a b) (leftPlace hab f * rightPlace hab g) =
      leftPlace hab (blockOp a f) * rightPlace hab (blockOp b g) := by
  have hL : ∀ i : Fin (n+1), a ≤ i.val → i.val + 1 < a + b → LeftSpect i (leftPlace hab f) :=
    fun i hi _ => leftSpect_induction (fun j => by
      rw [leftPlace, place_generator]
      refine leftSpect_generator ?_ ?_ <;> intro e <;> have := congrArg Fin.val e <;>
        simp at this <;> omega) f
  have hR : ∀ i : Fin (n+1), 0 ≤ i.val → i.val + 1 < 0 + a →
      RightSpect i (rightPlace hab (blockOp b g)) :=
    fun i _ hi => rightSpect_induction (fun j => by
      rw [rightPlace, place_generator]
      refine rightSpect_generator ?_ ?_ <;> intro e <;> have := congrArg Fin.val e <;>
        simp at this <;> omega) _
  have s2 : action n (blockE n a b) (leftPlace hab f * rightPlace hab g * 1) =
      leftPlace hab f * rightPlace hab (blockOp b g) * 1 :=
    action_blockE_place (by omega) hL (fun _ _ _ F => by rw [mul_one, mul_one]) g
  have s1 : action n (blockE n 0 a) (1 * leftPlace hab f * rightPlace hab (blockOp b g)) =
      1 * leftPlace hab (blockOp a f) * rightPlace hab (blockOp b g) :=
    action_blockE_place (by omega) (fun _ _ _ F => by rw [one_mul, one_mul]) hR f
  rw [action_mul_apply, ← mul_one (leftPlace hab f * rightPlace hab g), s2, mul_one,
    ← one_mul (leftPlace hab f), s1, one_mul]

/-- The exponent vector `γ ⊕ η`. -/
def joinExp (γ : Fin a → ℕ) (η : Fin b → ℕ) : Fin (n+2) → ℕ :=
  VariableEmbedding.expEmbed (shiftEmb 0 (by omega : 0 + a ≤ n+2)) γ +
    VariableEmbedding.expEmbed (shiftEmb a (by omega : a + b ≤ n+2)) η

theorem joinExp_left (γ : Fin a → ℕ) (η : Fin b → ℕ) (j : Fin a) :
    joinExp hab γ η (shiftEmb 0 (by omega) j) = γ j := by
  rw [joinExp, Pi.add_apply, VariableEmbedding.expEmbed_apply,
    expEmbed_eq_zero _ _ _ (Or.inl (by simp)), add_zero]

theorem joinExp_right (γ : Fin a → ℕ) (η : Fin b → ℕ) (j : Fin b) :
    joinExp hab γ η (shiftEmb a (by omega) j) = η j := by
  rw [joinExp, Pi.add_apply, VariableEmbedding.expEmbed_apply,
    expEmbed_eq_zero _ _ _ (Or.inr (by simp)), zero_add]

theorem joinExp_inj {γ γ' : Fin a → ℕ} {η η' : Fin b → ℕ}
    (e : joinExp hab γ η = joinExp hab γ' η') : γ = γ' ∧ η = η' :=
  ⟨funext fun j => by rw [← joinExp_left hab γ η, e, joinExp_left],
    funext fun j => by rw [← joinExp_right hab γ η, e, joinExp_right]⟩

theorem weight_joinExp (γ : Fin a → ℕ) (η : Fin b → ℕ) :
    ∑ t, joinExp hab γ η t = ∑ i, γ i + ∑ i, η i := by
  simp only [joinExp, Pi.add_apply, Finset.sum_add_distrib]
  rw [VariableEmbedding.sum_range _ _ fun t ht => VariableEmbedding.expEmbed_not_mem_range _ _ _ ht,
    VariableEmbedding.sum_range _ _ fun t ht => VariableEmbedding.expEmbed_not_mem_range _ _ _ ht]
  simp only [VariableEmbedding.expEmbed_apply]

theorem crossingCount_joinExp (γ : Fin a → ℕ) (η : Fin b → ℕ) :
    OddMath.crossingCount
      (VariableEmbedding.expEmbed (shiftEmb (N := n+2) 0 (by omega : 0 + a ≤ n+2)) γ)
      (VariableEmbedding.expEmbed (shiftEmb a (by omega : a + b ≤ n+2)) η) = 0 := by
  refine Finset.sum_eq_zero fun t _ => Finset.sum_eq_zero fun u hu => ?_
  have hut : u < t := (Finset.mem_filter.mp hu).2
  rw [Fin.lt_def] at hut
  by_cases ht : t.val < a
  · rw [expEmbed_eq_zero a _ η (t := u) (Or.inl (by omega)), mul_zero]
  · rw [expEmbed_eq_zero 0 _ γ (t := t) (Or.inr (by omega)), zero_mul]

theorem place_mul_place_monomial (γ : Fin a → ℕ) (η : Fin b → ℕ) (c c' : ℤ) :
    leftPlace hab (monomial γ c) * rightPlace hab (monomial η c') =
      monomial (joinExp hab γ η) (c * c') := by
  rw [leftPlace, rightPlace, place_monomial, place_monomial]
  change OddMath.SkewPolynomial.mul _ _ = _
  rw [OddMath.SkewPolynomial.mul_monomial, OddMath.skewSign, crossingCount_joinExp hab, pow_zero,
    mul_one]
  rfl

theorem coeff_place_mul_place (F : SkewPolynomial a) (G : SkewPolynomial b)
    (γ : Fin a → ℕ) (η : Fin b → ℕ) :
    (leftPlace hab F * rightPlace hab G) (joinExp hab γ η) = F γ * G η := by
  classical
  induction F using Finsupp.induction_linear with
  | zero => rw [map_zero, skew_zero_mul]; simp
  | add F F' hF hF' =>
      rw [map_add, skew_add_mul, Finsupp.add_apply, hF, hF', Finsupp.add_apply, add_mul]
  | single γ' c =>
      induction G using Finsupp.induction_linear with
      | zero => rw [map_zero, skew_mul_zero]; simp
      | add G G' hG hG' =>
          rw [map_add, skew_mul_add, Finsupp.add_apply, hG, hG', Finsupp.add_apply, mul_add]
      | single η' c' =>
          rw [show Finsupp.single γ' c = monomial γ' c from rfl,
            show Finsupp.single η' c' = monomial η' c' from rfl, place_mul_place_monomial]
          simp only [monomial, Finsupp.single_apply]
          by_cases hγ : γ' = γ
          · by_cases hη : η' = η
            · simp [hγ, hη]
            · rw [if_neg fun e => hη (joinExp_inj hab e).2, if_neg hη, mul_zero]
          · rw [if_neg fun e => hγ (joinExp_inj hab e).1, if_neg hγ, zero_mul]

/-- Diagonal coefficient of `e_a ⊗ e_b` on `x^{γ ⊕ η}`. -/
theorem coeff_blockE_blockE (γ : Fin a → ℕ) (η : Fin b → ℕ) :
    action n (blockE n 0 a * blockE n a b) (monomial (joinExp hab γ η) 1) (joinExp hab γ η) =
      blockOp a (monomial γ 1) γ * blockOp b (monomial η 1) η := by
  rw [show monomial (joinExp hab γ η) (1 : ℤ) =
      leftPlace hab (monomial γ 1) * rightPlace hab (monomial η 1) by
    rw [place_mul_place_monomial, mul_one], action_blockE_blockE, coeff_place_mul_place]

/-- Restriction of an exponent vector to the left block. -/
def splitLeft (ζ : Fin (n+2) → ℕ) : Fin a → ℕ :=
  fun j => ζ (shiftEmb 0 (by omega : 0 + a ≤ n+2) j)

/-- Restriction of an exponent vector to the right block. -/
def splitRight (ζ : Fin (n+2) → ℕ) : Fin b → ℕ :=
  fun j => ζ (shiftEmb a (by omega : a + b ≤ n+2) j)

theorem splitLeft_joinExp (γ : Fin a → ℕ) (η : Fin b → ℕ) :
    splitLeft hab (joinExp hab γ η) = γ :=
  funext (joinExp_left hab γ η)

theorem splitRight_joinExp (γ : Fin a → ℕ) (η : Fin b → ℕ) :
    splitRight hab (joinExp hab γ η) = η :=
  funext (joinExp_right hab γ η)

theorem joinExp_split (ζ : Fin (n+2) → ℕ) :
    joinExp hab (splitLeft hab ζ) (splitRight hab ζ) = ζ := by
  funext t
  by_cases ht : t.val < a
  · have e : t = shiftEmb (N := n+2) 0 (by omega) (⟨t.val, ht⟩ : Fin a) := Fin.ext (by simp)
    rw [e]
    exact joinExp_left _ _ _ _
  · have e : t = shiftEmb a (by omega) (⟨t.val - a, by omega⟩ : Fin b) :=
      Fin.ext (by simp; omega)
    rw [e]
    exact joinExp_right _ _ _ _

theorem hasDegree_blockE_blockE :
    HasDegree (Vd (n+2)) 0 (action n (blockE n 0 a * blockE n a b)) := by
  simpa using hasDegree_action_mul (hasDegree_blockE (n := n) 0 a) (hasDegree_blockE a b)

include hab in
/-- `tr(e_a ⊗ e_b | V_d) = ∑_{i+j=d} tr(e_a | V_i) · tr(e_b | V_j)`, for blocks of any size. -/
theorem trace_blockE_blockE (d : ℕ) :
    trace ℤ (Vd (n+2) d) ((hasDegree_blockE_blockE (n := n) (a := a) (b := b)).res d d
      (add_zero _)) =
      ∑ ij ∈ Finset.antidiagonal d,
        (∑ γ ∈ expSet a ij.1, blockOp a (monomial γ 1) γ) *
          ∑ η ∈ expSet b ij.2, blockOp b (monomial η 1) η := by
  classical
  let A : (Fin a → ℕ) → ℤ := fun γ => blockOp a (monomial γ 1) γ
  let B : (Fin b → ℕ) → ℤ := fun η => blockOp b (monomial η 1) η
  let S : (Fin (n+2) → ℕ) → (ℕ × ℕ) × ((Fin a → ℕ) × (Fin b → ℕ)) := fun ζ =>
    ((∑ i, splitLeft hab ζ i, ∑ i, splitRight hab ζ i), (splitLeft hab ζ, splitRight hab ζ))
  have hφ : ∀ ζ, action n (blockE n 0 a * blockE n a b) (monomial ζ 1) ζ =
      A (splitLeft hab ζ) * B (splitRight hab ζ) := fun ζ => by
    have hc := coeff_blockE_blockE hab (splitLeft hab ζ) (splitRight hab ζ)
    rwa [joinExp_split hab] at hc
  have hinj : Set.InjOn S (expSet (n+2) d) := fun ζ _ ζ' _ e => by
    simp only [S, Prod.mk.injEq] at e
    rw [← joinExp_split hab ζ, ← joinExp_split hab ζ', e.2.1, e.2.2]
  have hmem : ∀ q : (ℕ × ℕ) × ((Fin a → ℕ) × (Fin b → ℕ)),
      q ∈ (expSet (n+2) d).image S ↔
        q.1 ∈ Finset.antidiagonal d ∧ q.2 ∈ expSet a q.1.1 ×ˢ expSet b q.1.2 := by
    rintro ⟨⟨i, j⟩, γ, η⟩
    simp only [Finset.mem_image, Finset.mem_antidiagonal, Finset.mem_product, mem_expSet, S,
      Prod.mk.injEq, Nat.cast_inj]
    constructor
    · rintro ⟨ζ, hζ, ⟨rfl, rfl⟩, rfl, rfl⟩
      refine ⟨?_, rfl, rfl⟩
      rw [← weight_joinExp hab, joinExp_split hab]
      exact_mod_cast hζ
    · rintro ⟨hij, rfl, rfl⟩
      refine ⟨joinExp hab γ η, ?_, ?_⟩
      · rw [weight_joinExp, hij]
      · simp only [splitLeft_joinExp, splitRight_joinExp, and_self]
  rw [trace_res_eq]
  refine (Finset.sum_congr rfl fun ζ _ => hφ ζ).trans ?_
  calc ∑ ζ ∈ expSet (n+2) d, A (splitLeft hab ζ) * B (splitRight hab ζ)
      = ∑ q ∈ (expSet (n+2) d).image S, A q.2.1 * B q.2.2 := by rw [Finset.sum_image hinj]
    _ = ∑ ij ∈ Finset.antidiagonal d,
          ∑ q ∈ expSet a ij.1 ×ˢ expSet b ij.2, A q.1 * B q.2 :=
        Finset.sum_finset_product (f := fun q => A q.2.1 * B q.2.2) _ (Finset.antidiagonal d)
          (fun ij => expSet a ij.1 ×ˢ expSet b ij.2) hmem
    _ = ∑ ij ∈ Finset.antidiagonal d, (∑ γ ∈ expSet a ij.1, A γ) *
          ∑ η ∈ expSet b ij.2, B η :=
        Finset.sum_congr rfl fun ij _ => by rw [Finset.sum_product, Finset.sum_mul_sum]

end Blocks

/-! ## Degrees of the diagrams `σ_α`, `λ_α` -/

section Degrees
variable {n : ℕ}

theorem hasDegree_of_eq {k k' : ℤ} {T : SkewPolynomial (n+2) →ₗ[ℤ] SkewPolynomial (n+2)}
    (h : HasDegree (Vd (n+2)) k T) (e : k = k') : HasDegree (Vd (n+2)) k' T :=
  e ▸ h

theorem hasDegree_action_smul (z : ℤ) {k : ℤ} {u : Presented n}
    (hu : HasDegree (Vd (n+2)) k (action n u)) : HasDegree (Vd (n+2)) k (action n (z • u)) := by
  rw [map_zsmul]
  exact hasDegree_smul z hu

theorem hasDegree_dot_pow (j : Fin (n+2)) (e : ℕ) :
    HasDegree (Vd (n+2)) (e : ℤ) (action n (dot n j ^ e)) := by
  induction e with
  | zero => simpa using hasDegree_action_one (n := n)
  | succ e ih =>
      rw [pow_succ]
      exact hasDegree_of_eq (hasDegree_action_mul ih (hasDegree_dot j)) (by push_cast; ring)

/-- An ordered block monomial `x^A` has degree `|A|`. -/
theorem hasDegree_blockMono {p k : ℕ} (h : p + k ≤ n+2) (A : Fin k → ℕ) :
    HasDegree (Vd (n+2)) (∑ i, A i : ℕ) (action n (blockMono n p k h A)) := by
  have key : ∀ l : List (Fin k), HasDegree (Vd (n+2)) ((l.map A).sum : ℕ)
      (action n ((l.map fun i => dot n (shiftFin h i) ^ A i).prod)) := by
    intro l
    induction l with
    | nil => simpa using hasDegree_action_one (n := n)
    | cons i l ih =>
        simp only [List.map_cons, List.prod_cons, List.sum_cons]
        exact hasDegree_of_eq (hasDegree_action_mul (hasDegree_dot_pow _ _) ih)
          (by push_cast; ring)
  rw [Fin.sum_univ_def]
  exact key _

/-- `D_k` on a block has degree `-C(k,2)`. -/
theorem hasDegree_blockD {p k : ℕ} (h : p + k ≤ n+2) :
    HasDegree (Vd (n+2)) (-(k.choose 2 : ℕ)) (action n (blockD n p k)) := by
  have hd := hasDegree_product (StrandCrossing.triWord n p k)
  rwa [length_triWord h] at hd

theorem length_crossList (p a b : ℕ) : (StrandCrossing.crossList p a b).length = a * b := by
  induction b generalizing p with
  | zero => rfl
  | succ b ih =>
      simp only [StrandCrossing.crossList, List.length_append, ih, StrandCrossing.downList,
        List.length_reverse, List.length_range']
      ring

/-- The crossing `X_{a,b}` has degree `-ab`. -/
theorem hasDegree_crossWord {a b : ℕ} (hab : a + b = n+2) :
    HasDegree (Vd (n+2)) (-(a * b : ℕ)) (action n (product (StrandCrossing.crossWord n 0 a b))) := by
  have hd := hasDegree_product (StrandCrossing.crossWord n 0 a b)
  rwa [← List.length_map (f := Fin.val), StrandCrossing.natWord_values n _ fun j hj => by
    have := StrandCrossing.mem_crossList hj; omega, length_crossList] at hd

/-- The degree `|α| - ab` of `σ_α`. -/
def shift (a b : ℕ) (α : Fin a → ℕ) : ℤ := (∑ i, α i : ℕ) - (a * b : ℕ)

/-- `σ_α` has degree `|α| - ab`. -/
theorem hasDegree_sigma {a b : ℕ} (hab : a + b = n+2) (α : Fin a → ℕ) :
    HasDegree (Vd (n+2)) (shift a b α) (action n (sigma n a b hab α)) := by
  have hL : 0 + a ≤ n+2 := by omega
  rw [sigma, blockE_schur_blockE]
  refine hasDegree_of_eq (hasDegree_action_mul (hasDegree_action_mul (hasDegree_action_smul _
    (hasDegree_action_mul (hasDegree_action_mul (hasDegree_blockE 0 a)
      (hasDegree_blockMono hL _)) (hasDegree_blockD hL))) (hasDegree_blockE a b))
    (hasDegree_crossWord hab)) ?_
  rw [sum_expA, shift]
  push_cast
  ring

/-- `λ_α` has degree `ab - |α|` for `α ∈ P(a,b)`. -/
theorem hasDegree_lam {a b : ℕ} (hab : a + b = n+2) {α : Fin a → ℕ} (hα : ∀ k, α k ≤ b) :
    HasDegree (Vd (n+2)) (-shift a b α) (action n (lam n a b hab α)) := by
  have hR : a + b ≤ n+2 := by omega
  rw [lam, blockE_dualSchur_blockE]
  refine hasDegree_of_eq (hasDegree_action_smul _ (hasDegree_action_mul hasDegree_projector
    (hasDegree_action_mul (hasDegree_blockE 0 a) (hasDegree_action_smul _
      (hasDegree_action_mul (hasDegree_action_mul (hasDegree_blockE a b)
        (hasDegree_blockMono hR _)) (hasDegree_blockD hR)))))) ?_
  have hs : ((∑ k, hat b α k : ℕ) : ℤ) + ((∑ j, α j : ℕ) : ℤ) = (b : ℤ) * a := by
    exact_mod_cast sum_hat hα
  rw [sum_expB, shift]
  push_cast at hs ⊢
  linear_combination hs

end Degrees

/-! ## Theorem 4.16 -/

section Decomposition
variable {n a b : ℕ}

theorem blockE_pair_idem (hab : a + b = n+2) :
    blockE n 0 a * blockE n a b * (blockE n 0 a * blockE n a b) = blockE n 0 a * blockE n a b := by
  have hc : blockE n 0 a * blockE n a b = blockE n a b * blockE n 0 a :=
    OnhWindow.even_commute (blockE_mem_even (by omega))
      (homog_blockE (p := a) (k := b) (by omega)).mem_supported (by omega)
  calc blockE n 0 a * blockE n a b * (blockE n 0 a * blockE n a b)
      = blockE n 0 a * (blockE n a b * blockE n 0 a) * blockE n a b := by simp only [mul_assoc]
    _ = blockE n 0 a * blockE n 0 a * (blockE n a b * blockE n a b) := by
        rw [← hc]; simp only [mul_assoc]
    _ = blockE n 0 a * blockE n a b := by
        rw [blockE_mul_blockE (by omega), blockE_mul_blockE (by omega)]

/-- Per-degree trace identity `tr(e_a ⊗ e_b | V_d) = ∑_{α ∈ P(a,b)} tr(e_{a+b} | V_{d-|α|+ab})`. -/
theorem trace_identity (hab : a + b = n+2) (d : ℤ) :
    trace ℤ (Vd (n+2) d) ((hasDegree_blockE_blockE (n := n) (a := a) (b := b)).res d d
      (add_zero d)) =
      ∑ α : BoxPartitionCount.box a b, trace ℤ (Vd (n+2) (d - shift a b α.1))
        (hasDegree_projector.res _ _ (add_zero _)) := by
  have hC : (n+2).choose 2 = a.choose 2 + b.choose 2 + a * b := by
    rw [← hab, choose_two_add]
  simp only [trace_projector, card_index, hC]
  rcases lt_or_le d 0 with hd | hd
  · have he : expSet (n+2) d = ∅ := Finset.filter_false_of_mem fun _ _ => not_le.2 hd
    rw [trace_res_eq, he, Finset.sum_empty, eq_comm]
    refine Finset.sum_eq_zero fun α _ => if_neg ?_
    simp only [shift]
    generalize a * b = m
    omega
  · obtain ⟨d', rfl⟩ := Int.eq_ofNat_of_zero_le hd
    rw [trace_blockE_blockE hab]
    simp only [sum_coeff_blockOp]
    calc ∑ ij ∈ Finset.antidiagonal d',
          ((if a.choose 2 ≤ ij.1 then BoxPartitionCount.pcount a (ij.1 - a.choose 2) else 0 : ℕ)
            : ℤ) *
          ((if b.choose 2 ≤ ij.2 then BoxPartitionCount.pcount b (ij.2 - b.choose 2) else 0 : ℕ)
            : ℤ)
        = ((∑ α ∈ BoxPartitionCount.box a b,
            if a.choose 2 + b.choose 2 + ∑ i, α i ≤ d' then
              BoxPartitionCount.pcount (a+b) (d' - a.choose 2 - b.choose 2 - ∑ i, α i) else 0 : ℕ)
            : ℤ) := by
          rw [← count_identity]
          push_cast
          rfl
      _ = _ := by
          rw [Nat.cast_sum, ← Finset.sum_coe_sort (BoxPartitionCount.box a b)]
          refine Finset.sum_congr rfl fun α _ => ?_
          rw [hab]
          simp only [shift]
          split_ifs with h1 h2 h2
          · congr 2
            generalize a * b = m at *
            omega
          · generalize a * b = m at *
            omega
          · generalize a * b = m at *
            omega
          · rfl

/-- **EKL Theorem 4.16** (4.56): `e_a ⊗ e_b = ∑_{α ∈ P(a,b)} e_α` in `ONH_{a+b}`. -/
theorem thm_4_16 (hab : a + b = n+2) :
    blockE n 0 a * blockE n a b = ∑ α ∈ BoxPartitionCount.box a b, idem n a b hab α := by
  have hbox : ∀ α : BoxPartitionCount.box a b, Antitone α.1 ∧ ∀ k, α.1 k ≤ b := fun α =>
    BoxPartitionCount.mem_box.1 α.2
  apply NilHeckeBasis.action_injective n
  have hmain := eq_sum_of_trace (Vd := Vd (n+2)) (I := BoxPartitionCount.box a b)
    (s := fun α => shift a b α.1) (P := action n (blockE n 0 a * blockE n a b))
    (e := action n (ZeroHecke.projector n)) (σ := fun α => action n (sigma n a b hab α.1))
    (ρ := fun α => action n (lam n a b hab α.1)) (iSup_Vd _) hasDegree_blockE_blockE
    hasDegree_projector (fun α => hasDegree_sigma hab α.1)
    (fun α => hasDegree_lam hab (hbox α).2)
    (by rw [← Module.End.mul_eq_comp, ← map_mul, blockE_pair_idem hab])
    (fun α => by
      rw [← Module.End.mul_eq_comp, ← map_mul,
        eq_4_54 hab (hbox α).1 (hbox α).2 (hbox α).1 (hbox α).2, if_pos rfl])
    (fun α β hne => by
      rw [← Module.End.mul_eq_comp, ← map_mul,
        eq_4_54 hab (hbox α).1 (hbox α).2 (hbox β).1 (hbox β).2,
        if_neg fun h => hne (Subtype.ext h.symm), map_zero])
    (fun α => by rw [← Module.End.mul_eq_comp, ← map_mul, blockE_mul_sigma])
    (fun α => by rw [← Module.End.mul_eq_comp, ← map_mul, lam_mul_blockE])
    (fun α => by simp only [← Module.End.mul_eq_comp, ← map_mul, projector_mul_lam])
    (trace_identity hab)
  rw [hmain, map_sum, ← Finset.sum_coe_sort (BoxPartitionCount.box a b)]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [idem, map_mul, Module.End.mul_eq_comp]

/-- EKL (4.57): Theorem 4.16 with the diagrams written out,
`e_a ⊗ e_b = ∑_{α ∈ P(a,b)} (-1)^{X^{a,b}_α} σ_α · e_{a+b} (e_a ⊗ e_b ŝ_{α̂} e_b)`,
`σ_α = (e_a s_α e_a ⊗ e_b) X_{a,b}`. -/
theorem eq_4_57 (hab : a + b = n+2) :
    blockE n 0 a * blockE n a b = ∑ α ∈ BoxPartitionCount.box a b, (-1 : ℤ)^(signX a b α) •
      ((blockE n 0 a * blockSchur n 0 a (by omega) α * blockE n 0 a * blockE n a b *
          product (StrandCrossing.crossWord n 0 a b)) *
        (ZeroHecke.projector n * (blockE n 0 a *
          (blockE n a b * blockDualSchur n a b (by omega) (hat b α) * blockE n a b)))) := by
  rw [thm_4_16 hab]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [idem, lam, mul_smul_comm]
  rfl

/-- Theorem 4.16 for `b = 1`: `e_a = ∑_{α ∈ P(a,1)} e_α` in `ONH_{a+1}`. -/
theorem thm_4_16_right_one (hab : a + 1 = n+2) :
    blockE n 0 a = ∑ α ∈ BoxPartitionCount.box a 1, idem n a 1 hab α := by
  rw [← thm_4_16 hab, blockE_one, mul_one]

/-- Theorem 4.16 for `a = 1`: `e_b = ∑_{α ∈ P(1,b)} e_α` on the strands `[1, 1+b)`. -/
theorem thm_4_16_left_one (hab : 1 + b = n+2) :
    blockE n 1 b = ∑ α ∈ BoxPartitionCount.box 1 b, idem n 1 b hab α := by
  rw [← thm_4_16 hab, blockE_one, one_mul]

end Decomposition

end

end OddMath.Frontier.ThickDecomposition
