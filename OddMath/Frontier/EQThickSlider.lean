import OddMath.Frontier.EQThickRelations
import OddMath.Frontier.SmallRank
import OddMath.Frontier.EQZnAction

/-!
# Ellis–Qi §4.1: the slider relation

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*,
arXiv:1504.01712v2, §4.1, the displayed relation for splitters labelled by twisted odd elementary
polynomials (just before "In other words, the collection of these diagrams span …").

Conventions as in `EQThickSplitters`: `ONH_{a+b} = NilHeckeAction.Presented n` with
`a + b = n + 2`, `0`-indexed strands, a written product `x * y` is `x` drawn on top of `y`,
the splitter is `(e_a ⊗ e_b) e_{a+b}` (`splitter`), and a coupon `f` on a thick strand on the
strands `[p, p+k)` is `e_k f e_k` (`label`).  The coupon `ẽ_j` on the strands `[p, p+k)` is EKL's
elementary polynomial in those variables, with signs restarting at the block (`elemBlock`;
Ellis–Qi, text after Proposition 4.2).

Printed:
`(-1)^{C(s,2)} (ẽ_s on the thick strand below the splitter) =
  Σ_{l=0}^{s} (-1)^{al} (ẽ_{s-l} on the left leg, ẽ_l on the right leg)`,
with the right coupon drawn above the left one.

* `slider`: the correct relation is
  `(ẽ_s below the splitter) = Σ_{l=0}^{s} (-1)^{al} (ẽ_{s-l} on the left leg drawn above
  ẽ_l on the right leg)`, with no factor `(-1)^{C(s,2)}`, for all `a, b, s`.  It is the
  coproduct formula `ẽ_s(x) = Σ_l (-1)^{al} ẽ_{s-l}(x') ẽ_l(x'')` (`elementary_coproduct`).
* `slider_printed_false`: the printed relation fails for `a = 2`, `b = 1`, `s = 2` in `ONH_3`.
  For `s ≤ 1` the printed and the corrected relations agree.
-/

namespace OddMath.Frontier.EQThick

open OddMath.SkewPolynomial (SkewPolynomial generator monomial)
open NilHeckeAction NilCoxeterWords NilHeckeBasis ZeroHecke OnhWindow ThickBubble
open OddMath.Diagrams.OddNilHecke (eqIdempotent)
open OnhPolynomial (polyElem action_polyElem)
open FiniteCompleteElementary
open scoped BigOperators

noncomputable section

/-! ## Splitting an elementary sum into two blocks of variables -/

section Generic
variable {R : Type*} [Ring R]

/-- `ẽ_s` of a concatenated alphabet: the strict sums satisfy
`σ_s(x) = Σ_l σ_{s-l}(x') σ_l(x'')` for `x = x' ⊔ x''`. -/
theorem strictSum_blocks (a : ℕ) : ∀ (b : ℕ) (x : Fin (a + b) → R) (s : ℕ),
    FiniteWords.strictSum x s = ∑ l ∈ Finset.range (s + 1),
      FiniteWords.strictSum (fun i : Fin a => x (Fin.castAdd b i)) (s - l) *
        FiniteWords.strictSum (fun j : Fin b => x (Fin.natAdd a j)) l
  | 0, x, s => by
    rw [Finset.sum_range_succ']
    rw [Finset.sum_eq_zero fun l _ => by rw [FiniteWords.strictSum_empty, mul_zero],
      zero_add, FiniteWords.strictSum_zero, mul_one, Nat.sub_zero]
    rfl
  | b + 1, x, 0 => by simp
  | b + 1, x, k + 1 => by
    have hL := ElementaryBranching.strictSum_last (a + b) k x
    have ih1 := strictSum_blocks a b (fun i => x i.castSucc) (k + 1)
    have ih0 := strictSum_blocks a b (fun i => x i.castSucc) k
    set y : Fin a → R := fun i => x (Fin.castAdd (b + 1) i) with hy
    set v : Fin b → R := fun j => x (Fin.natAdd a j.castSucc) with hv
    set t : R := x (Fin.natAdd a (Fin.last b)) with ht
    have e1 : (fun i : Fin a => x (Fin.castSucc (Fin.castAdd b i))) = y := rfl
    have e2 : (fun j : Fin b => x (Fin.castSucc (Fin.natAdd a j))) = v := rfl
    have e3 : x (Fin.last (a + b)) = t := rfl
    rw [e1, e2] at ih1 ih0
    have hz : ∀ l, FiniteWords.strictSum (fun j : Fin (b + 1) => x (Fin.natAdd a j)) (l + 1) =
        FiniteWords.strictSum v (l + 1) + FiniteWords.strictSum v l * t :=
      fun l => ElementaryBranching.strictSum_last b l _
    rw [hL, e3, ih1, ih0, Finset.sum_range_succ' _ (k + 1), Finset.sum_mul,
      Finset.sum_range_succ' _ (k + 1)]
    simp only [hz, mul_add, Finset.sum_add_distrib, FiniteWords.strictSum_zero, Nat.sub_zero,
      Nat.succ_sub_succ, ← mul_assoc]
    abel

theorem strictSum_split {a b N : ℕ} (hab : a + b = N) (x : Fin N → R) (s : ℕ) :
    FiniteWords.strictSum x s = ∑ l ∈ Finset.range (s + 1),
      FiniteWords.strictSum (fun i : Fin a => x ⟨i.val, by omega⟩) (s - l) *
        FiniteWords.strictSum (fun j : Fin b => x ⟨a + j.val, by omega⟩) l := by
  subst hab
  exact strictSum_blocks a b x s

end Generic

variable {n a b : ℕ}

/-- The coproduct of the twisted odd elementary polynomials:
`ẽ_s(x_0, …, x_{a+b-1}) = Σ_l (-1)^{al} ẽ_{s-l}(x_0, …, x_{a-1}) ẽ_l(x_a, …, x_{a+b-1})`,
each factor with its own block-local twisting signs. -/
theorem elementary_coproduct (hab : a + b = n + 2) (s : ℕ) :
    elementaryPoly (n + 2) s = ∑ l ∈ Finset.range (s + 1),
      ProjectorRank.place 0 (left_le hab) (elementaryPoly a (s - l)) *
        ((-1 : ℤ) ^ (a * l) • ProjectorRank.place a (right_le hab) (elementaryPoly b l)) := by
  rw [elementaryPoly_eq_strictSum, strictSum_split hab]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [elementaryPoly_eq_strictSum, elementaryPoly_eq_strictSum, EQZn.ringHom_strictSum,
    EQZn.ringHom_strictSum, pow_mul, ← EQZn.strictSum_zsmul]
  congr 2
  · funext i
    rw [PlacticEvaluation.tildeGenerator, PlacticEvaluation.tildeGenerator, map_zsmul,
      ProjectorRank.place_generator]
    congr 1
  · funext j
    rw [PlacticEvaluation.tildeGenerator, PlacticEvaluation.tildeGenerator, map_zsmul,
      ProjectorRank.place_generator, smul_smul, ← pow_add]
    congr 1
    exact congrArg generator (Fin.ext (by simp; omega))

/-! ## Evaluation of labelled splitters in the polynomial representation -/

theorem sp_zero_mul {N : ℕ} (g : SkewPolynomial N) : (0 : SkewPolynomial N) * g = 0 :=
  OddMath.SkewPolynomial.zero_mul g

theorem sp_mul_zero {N : ℕ} (g : SkewPolynomial N) : g * (0 : SkewPolynomial N) = 0 :=
  OddMath.SkewPolynomial.mul_zero g

/-- A placed polynomial is killed by the crossings outside its window. -/
theorem divided_place_eq_zero {p k : ℕ} (h : p + k ≤ n + 2) (i : Fin (n + 1))
    (hi : i.val + 1 < p ∨ p + k ≤ i.val) (f : SkewPolynomial k) :
    AllRankDivided.divided i (ProjectorRank.place p h f) = 0 := by
  induction f using PrefixEmbedding.induction_generators with
  | hconst r => rw [map_zsmul, map_one, map_zsmul, AllRankDivided.divided_one, smul_zero]
  | hgen j =>
    rw [ProjectorRank.place_generator, AllRankDivided.divided_generator]
    have := j.isLt
    split_ifs with hj
    · rcases hj with hj | hj <;> (have := congrArg Fin.val hj; simp at this; omega)
    · rfl
  | hadd f g hf hg => rw [map_add, map_add, hf, hg, add_zero]
  | hmul f g hf hg =>
    rw [map_mul, AllRankDivided.divided_mul, hf, hg, sp_zero_mul, sp_mul_zero, add_zero]

/-- A windowed element acts right-linearly on polynomials killed by the window's crossings. -/
theorem action_windowHom_mul_kernel {m p : ℕ} (h : p + (m + 2) ≤ n + 2) (y : Presented m)
    (g q : SkewPolynomial (n + 2))
    (hq : ∀ i : Fin (m + 1), AllRankDivided.divided (shiftIndex h i) q = 0) :
    action n (windowHom m n p h y) (g * q) = action n (windowHom m n p h y) g * q := by
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective y
  induction c using FreeAlgebra.induction generalizing g with
  | grade0 r =>
    simp only [algebraMap_int_eq, eq_intCast, map_intCast, Module.End.intCast_apply]
    exact (smul_mul_assoc (α := ℤ) r g q).symm
  | grade1 x =>
    cases x with
    | inl j =>
      change action n (windowHom m n p h (dot m j)) _ = action n (windowHom m n p h (dot m j)) _ * _
      rw [windowHom_dot, action_dot_apply, action_dot_apply]
      exact (OddMath.SkewPolynomial.mul_assoc _ _ _).symm
    | inr i =>
      change action n (windowHom m n p h (crossing m i)) _ =
        action n (windowHom m n p h (crossing m i)) _ * _
      rw [windowHom_crossing, action_crossing_apply, action_crossing_apply,
        AllRankDivided.divided_mul]
      erw [hq i]
      rw [sp_mul_zero, add_zero]
  | add c d hc hd =>
    simp only [map_add, LinearMap.add_apply, hc, hd]
    exact (OddMath.SkewPolynomial.add_mul _ _ _).symm
  | mul c d hc hd =>
    rw [(Ideal.Quotient.mk _).map_mul, (windowHom _ _ _ _).map_mul, action_mul_apply, hd, hc,
      action_mul_apply]

theorem action_eqBlock_mul_kernel {p k : ℕ} (h : p + k ≤ n + 2) (g q : SkewPolynomial (n + 2))
    (hq : ∀ i : Fin (n + 1), p ≤ i.val → i.val + 1 < p + k → AllRankDivided.divided i q = 0) :
    action n (eqBlock n p k h) (g * q) = action n (eqBlock n p k h) g * q := by
  induction k using block_cases with
  | h0 => rw [eqBlock_zero, map_one (action n)]; rfl
  | h1 => rw [eqBlock_one, map_one (action n)]; rfl
  | h2 m =>
    rw [eqBlock_eq h]
    exact action_windowHom_mul_kernel h _ g q fun i =>
      hq _ (by simp [shiftIndex]) (by have := i.isLt; simp [shiftIndex]; omega)

theorem action_eqBlock_place_elementary {p k : ℕ} (h : p + k ≤ n + 2) (j : ℕ) :
    action n (eqBlock n p k h) (ProjectorRank.place p h (elementaryPoly k j)) =
      ProjectorRank.place p h (elementaryPoly k j) := by
  induction k using block_cases with
  | h0 => rw [eqBlock_zero, map_one (action n)]; rfl
  | h1 => rw [eqBlock_one, map_one (action n)]; rfl
  | h2 m =>
    rw [eqBlock_eq h, action_windowHom_place,
      action_eqIdempotent_kernel (OddSymmetricKernel.elementary_mem m j)]

/-- The coupon `ẽ_j` on the strands `[p, p+k)` (signs restarting at the block). -/
def elemBlock (n p k j : ℕ) (h : p + k ≤ n + 2) : Presented n :=
  polyElem n (ProjectorRank.place p h (elementaryPoly k j))

/-- A coupon `f` on the thick strand on `[p, p+k)`: `e_k f e_k`. -/
def label (n p k : ℕ) (h : p + k ≤ n + 2) (f : Presented n) : Presented n :=
  eqBlock n p k h * f * eqBlock n p k h

/-- A labelled thick strand acts on a polynomial killed by its window's crossings by
multiplication with the coupon. -/
theorem action_label_elem {p k : ℕ} (h : p + k ≤ n + 2) (j : ℕ) (q : SkewPolynomial (n + 2))
    (hq : ∀ i : Fin (n + 1), p ≤ i.val → i.val + 1 < p + k → AllRankDivided.divided i q = 0) :
    action n (label n p k h (elemBlock n p k j h)) q =
      ProjectorRank.place p h (elementaryPoly k j) * q := by
  rw [label, elemBlock, action_mul_apply, action_mul_apply, action_polyElem]
  have h1 : action n (eqBlock n p k h) q = q := by
    rw [← one_mul q, action_eqBlock_mul_kernel h 1 q hq, action_eqBlock_one]
  rw [h1, action_eqBlock_mul_kernel h _ q hq, action_eqBlock_place_elementary]

theorem kernel_killed {q : SkewPolynomial (n + 2)} (hq : q ∈ K n) (i : Fin (n + 1)) :
    AllRankDivided.divided i q = 0 := (OddSymmetricKernel.mem_kernelSubring q).mp hq i

theorem divided_place_mul {p k : ℕ} (h : p + k ≤ n + 2) (i : Fin (n + 1))
    (hi : i.val + 1 < p ∨ p + k ≤ i.val) (f : SkewPolynomial k) {q : SkewPolynomial (n + 2)}
    (hq : AllRankDivided.divided i q = 0) :
    AllRankDivided.divided i (ProjectorRank.place p h f * q) = 0 := by
  rw [AllRankDivided.divided_mul, divided_place_eq_zero h i hi, hq, sp_zero_mul, sp_mul_zero,
    add_zero]

/-- The labelled splitter with `ẽ_i` on the left leg drawn above `ẽ_j` on the right leg acts by
`g ↦ ẽ_i(x') ẽ_j(x'') e_{a+b}(g)`. -/
theorem action_labels_splitter (hab : a + b = n + 2) (i j : ℕ) (g : SkewPolynomial (n + 2)) :
    action n (label n 0 a (left_le hab) (elemBlock n 0 a i (left_le hab)) *
        label n a b (right_le hab) (elemBlock n a b j (right_le hab)) * splitter n a b hab) g =
      ProjectorRank.place 0 (left_le hab) (elementaryPoly a i) *
        (ProjectorRank.place a (right_le hab) (elementaryPoly b j) *
          action n (eqIdempotent n) g) := by
  have hK := action_eqIdempotent_mem (m := n) g
  rw [splitter_eq, action_mul_apply, action_mul_apply,
    action_label_elem _ _ _ fun i _ _ => kernel_killed hK i,
    action_label_elem _ _ _ fun i' _ h2 =>
      divided_place_mul _ i' (Or.inl (by omega)) _ (kernel_killed hK i')]

/-- The same with the right coupon drawn above the left one. -/
theorem action_labels_splitter' (hab : a + b = n + 2) (i j : ℕ) (g : SkewPolynomial (n + 2)) :
    action n (label n a b (right_le hab) (elemBlock n a b j (right_le hab)) *
        label n 0 a (left_le hab) (elemBlock n 0 a i (left_le hab)) * splitter n a b hab) g =
      ProjectorRank.place a (right_le hab) (elementaryPoly b j) *
        (ProjectorRank.place 0 (left_le hab) (elementaryPoly a i) *
          action n (eqIdempotent n) g) := by
  have hK := action_eqIdempotent_mem (m := n) g
  rw [splitter_eq, action_mul_apply, action_mul_apply,
    action_label_elem _ _ _ fun i _ _ => kernel_killed hK i,
    action_label_elem _ _ _ fun i' h1 _ =>
      divided_place_mul _ i' (Or.inr (by omega)) _ (kernel_killed hK i')]

/-- The splitter with `ẽ_s` on the thick strand below it acts by `g ↦ ẽ_s e_{a+b}(g)`. -/
theorem action_splitter_elem (hab : a + b = n + 2) (s : ℕ) (g : SkewPolynomial (n + 2)) :
    action n (splitter n a b hab *
        (eqIdempotent n * polyElem n (elementaryPoly (n + 2) s) * eqIdempotent n)) g =
      elementaryPoly (n + 2) s * action n (eqIdempotent n) g := by
  rw [splitter_eq, action_mul_apply, action_mul_apply, action_mul_apply, action_polyElem,
    action_eqIdempotent_kernel (Subring.mul_mem _ (OddSymmetricKernel.elementary_mem n s)
      (action_eqIdempotent_mem g)),
    action_eqIdempotent_kernel (Subring.mul_mem _ (OddSymmetricKernel.elementary_mem n s)
      (action_eqIdempotent_mem g))]

/-- **Ellis–Qi §4.1, slider relation**, corrected: for `a + b = n + 2` and every `s`,
`(splitter) (e_{a+b} ẽ_s e_{a+b}) = Σ_{l=0}^{s} (-1)^{al}
  (e_a ẽ_{s-l} e_a) (e_b ẽ_l e_b) (splitter)`,
the left coupon drawn above the right one. -/
theorem slider (hab : a + b = n + 2) (s : ℕ) :
    splitter n a b hab * (eqIdempotent n * polyElem n (elementaryPoly (n + 2) s) * eqIdempotent n) =
      ∑ l ∈ Finset.range (s + 1), (-1 : ℤ) ^ (a * l) •
        (label n 0 a (left_le hab) (elemBlock n 0 a (s - l) (left_le hab)) *
          label n a b (right_le hab) (elemBlock n a b l (right_le hab)) * splitter n a b hab) := by
  apply NilHeckeBasis.action_injective n
  apply LinearMap.ext
  intro g
  rw [action_splitter_elem, map_sum, LinearMap.sum_apply]
  simp only [map_zsmul, LinearMap.smul_apply, action_labels_splitter]
  rw [← action_polyElem, elementary_coproduct hab, map_sum, map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_mul, map_zsmul, mul_smul_comm, map_zsmul, LinearMap.smul_apply, action_mul_apply,
    action_polyElem, action_polyElem]

/-- The printed slider relation (right coupon drawn above the left one, factor `(-1)^{C(s,2)}`)
fails for `a = 2`, `b = 1`, `s = 2` in `ONH_3`. -/
theorem slider_printed_false :
    (-1 : ℤ) ^ Nat.choose 2 2 • (splitter 1 2 1 rfl *
        (eqIdempotent 1 * polyElem 1 (elementaryPoly 3 2) * eqIdempotent 1)) ≠
      ∑ l ∈ Finset.range 3, (-1 : ℤ) ^ (2 * l) •
        (label 1 2 1 (right_le (n := 1) rfl) (elemBlock 1 2 1 l (right_le (n := 1) rfl)) *
          label 1 0 2 (left_le (n := 1) (b := 1) rfl)
            (elemBlock 1 0 2 (2 - l) (left_le (n := 1) (b := 1) rfl)) * splitter 1 2 1 rfl) := by
  intro h
  have hc := slider (n := 1) (a := 2) (b := 1) rfl 2
  have h1 := congrArg (fun z => polyElem 1 (action 1 z 1)) h
  have h2 := congrArg (fun z => polyElem 1 (action 1 z 1)) hc
  simp only [map_zsmul, LinearMap.smul_apply, action_splitter_elem, map_sum,
    LinearMap.sum_apply] at h1 h2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at h1 h2
  rw [action_labels_splitter', action_labels_splitter', action_labels_splitter'] at h1
  rw [action_labels_splitter, action_labels_splitter, action_labels_splitter] at h2
  simp only [action_eqIdempotent_one, map_mul, mul_one] at h1 h2
  set X := polyElem 1 (ProjectorRank.place 0 (left_le (n := 1) (b := 1) rfl) (elementaryPoly 2 2))
    with hX
  have hR0 : polyElem 1 (ProjectorRank.place 2 (right_le (n := 1) (a := 2) rfl)
      (elementaryPoly 1 0)) = 1 := by rw [elementaryPoly_zero, map_one, map_one]
  have hR2 : polyElem 1 (ProjectorRank.place 2 (right_le (n := 1) (a := 2) rfl)
      (elementaryPoly 1 2)) = 0 := by
    rw [elementaryPoly_eq_zero_of_lt (by norm_num), map_zero, map_zero]
  have hR1 : polyElem 1 (ProjectorRank.place 2 (right_le (n := 1) (a := 2) rfl)
      (elementaryPoly 1 1)) = dot 1 2 := by
    rw [SmallRank.elementaryPoly_one_one, ProjectorRank.place_generator,
      OnhPolynomial.polyElem_generator]
    rfl
  have hL0 : polyElem 1 (ProjectorRank.place 0 (left_le (n := 1) (b := 1) rfl)
      (elementaryPoly 2 0)) = 1 := by rw [elementaryPoly_zero, map_one, map_one]
  have hL1 : polyElem 1 (ProjectorRank.place 0 (left_le (n := 1) (b := 1) rfl)
      (elementaryPoly 2 1)) = dot 1 0 - dot 1 1 := by
    rw [CenterONHControls.e1_rankTwo, map_sub, map_sub, ProjectorRank.place_generator,
      ProjectorRank.place_generator, OnhPolynomial.polyElem_generator,
      OnhPolynomial.polyElem_generator]
    rfl
  simp only [hR0, hR1, hR2, hL0, hL1, Nat.choose_self, pow_one, neg_one_smul, one_mul, mul_one,
    mul_zero, smul_zero, add_zero, show (2 : ℕ) - 1 = 1 from rfl,
    show (2 : ℕ) - 2 = 0 from rfl] at h1 h2
  simp only [pow_zero, neg_one_sq, one_smul] at h1 h2
  have hanti : dot 1 2 * (dot 1 0 - dot 1 1) = -((dot 1 0 - dot 1 1) * dot 1 2) := by
    rw [mul_sub, sub_mul, ZeroHecke.dot_anticommute 2 0 (by decide),
      ZeroHecke.dot_anticommute 2 1 (by decide)]
    abel
  rw [hanti] at h1
  have hXX : X + X = 0 := by
    have h3 := congrArg₂ (· + ·) h1 h2
    simp only [neg_add_cancel] at h3
    rw [h3]
    abel
  have hx := congrArg (fun z => action 1 z 1) hXX
  simp only [map_add, LinearMap.add_apply, map_zero, LinearMap.zero_apply, hX, action_polyElem,
    mul_one] at hx
  have he : ProjectorRank.place 0 (left_le (n := 1) (b := 1) rfl) (elementaryPoly 2 2) = 0 := by
    ext c
    have := congrArg (fun q : SkewPolynomial 3 => q c) hx
    simp only [Finsupp.add_apply, Finsupp.coe_zero, Pi.zero_apply] at this
    simp only [Finsupp.coe_zero, Pi.zero_apply]
    omega
  have h0 : elementaryPoly 2 2 = 0 :=
    VariableEmbedding.embed_injective _
      (he.trans (map_zero (ProjectorRank.place 0 (left_le (n := 1) (b := 1) rfl))).symm)
  have := congrArg (fun q : SkewPolynomial 2 => q (fun _ => 1)) h0
  simp only [elementary_two_two, Finsupp.coe_zero, Pi.zero_apply] at this
  exact absurd this (by norm_num)

end

end OddMath.Frontier.EQThick
