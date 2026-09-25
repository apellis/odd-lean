import OddMath.Frontier.NilHeckeCenter
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.GroupTheory.Perm.Sign

/-! The corrected center of EKL arXiv:1111.1320v1, Prop. 2.15, p. 13 (polynomial side).

For every rank `N = n+2`, on the actual integer skew polynomial ring, the actual
divided differences and the actual signed action:

* `mem_center_iff`: a skew polynomial is central iff every exponent vector in its
  support is entrywise even, or `N` is odd and it is entrywise odd.
* `second_claim`: for a polynomial `f` in the squared variables,
  `∂_i f = 0 ↔ s_i f = f` (the second claim in the printed proof).
* `kernel_inter_center`: the central elements of the joint kernel are exactly
  `a + V b` (`N` odd) or `a` (`N` even) with `a, b` symmetric polynomials in the
  squared variables and `V = x_0 x_1 ⋯ x_{N-1}`.
* `even_rank`, `odd_rank`: the printed statement holds for even `N` and fails for
  every odd `N` (the volume `V` is a central kernel element outside the squared
  symmetric ring). -/
namespace OddMath.Frontier.CenterPoly
open OddMath.SkewPolynomial (SkewPolynomial generator monomial expSingle)
open OddMath.Frontier.AllRankDivided OddMath.Frontier.OddSymmetricKernel
noncomputable section
variable {n : ℕ}

/-! ### Monomial arithmetic -/

theorem mulMon {m : ℕ} (a b : Fin m → ℕ) (r t : ℤ) :
    monomial a r * monomial b t = monomial (a+b) (r*t*OddMath.skewSign a b) :=
  OddMath.SkewPolynomial.mul_monomial a b r t

theorem skewSign_mul_self {m : ℕ} (a b : Fin m → ℕ) :
    OddMath.skewSign a b * OddMath.skewSign a b = 1 := by
  simp only [OddMath.skewSign, ← pow_add, ← two_mul, pow_mul]
  norm_num

theorem mul_monomial_right {m : ℕ} (f : SkewPolynomial m) (b : Fin m → ℕ) (t : ℤ) :
    f * monomial b t = f.sum (fun a r => monomial (a+b) (r*t*OddMath.skewSign a b)) := by
  show OddMath.SkewPolynomial.mul f (monomial b t) = _
  unfold OddMath.SkewPolynomial.mul
  apply Finsupp.sum_congr
  intro a _
  rw [Finsupp.sum_single_index]
  simp

theorem mul_monomial_left {m : ℕ} (f : SkewPolynomial m) (b : Fin m → ℕ) (t : ℤ) :
    monomial b t * f = f.sum (fun a r => monomial (b+a) (t*r*OddMath.skewSign b a)) := by
  show OddMath.SkewPolynomial.mul (monomial b t) f = _
  unfold OddMath.SkewPolynomial.mul
  rw [Finsupp.sum_single_index]
  simp [Finsupp.sum]

/-- Coefficient extraction from a translated monomial sum. -/
theorem sum_translate_apply {m : ℕ} (f : SkewPolynomial m) (b c : Fin m → ℕ)
    (g : (Fin m → ℕ) → ℤ → ℤ) (hg : ∀ a, g a 0 = 0) :
    (f.sum fun a r => monomial (a+b) (g a r)) (c+b) = g c (f c) := by
  rw [Finsupp.sum_apply, Finsupp.sum_eq_single c]
  · simp
  · intro a _ hac
    rw [Finsupp.single_apply, if_neg]
    intro h
    exact hac (add_right_cancel h)
  · intro _
    simp [hg]

/-- Split a leading generator off a monomial. -/
theorem monomial_split {m : ℕ} (j : Fin m) (b : Fin m → ℕ) (c : ℤ) :
    monomial (expSingle j + b) c =
      generator j * monomial b (c * OddMath.skewSign (expSingle j) b) := by
  show _ = monomial (expSingle j) 1 * _
  rw [mulMon, one_mul, mul_assoc, skewSign_mul_self, mul_one]

/-! ### Crossing counts against a unit vector -/

theorem crossing_unit_left {m : ℕ} (j : Fin m) (c : Fin m → ℕ) :
    OddMath.crossingCount (expSingle j) c = ∑ k, if k < j then c k else 0 := by
  simp only [OddMath.crossingCount, expSingle, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ,
    if_true]
  rw [Finset.sum_filter]

theorem crossing_unit_right {m : ℕ} (j : Fin m) (c : Fin m → ℕ) :
    OddMath.crossingCount c (expSingle j) = ∑ k, if j < k then c k else 0 := by
  simp only [OddMath.crossingCount, expSingle, mul_ite, mul_one, mul_zero]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_ite_eq]
  simp

theorem crossing_unit_total {m : ℕ} (j : Fin m) (c : Fin m → ℕ) :
    OddMath.crossingCount (expSingle j) c + OddMath.crossingCount c (expSingle j) + c j =
      ∑ k, c k := by
  rw [crossing_unit_left, crossing_unit_right]
  have hj : c j = ∑ k, if k = j then c k else 0 := by simp
  rw [hj, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rcases lt_trichotomy k j with h | h | h
  · simp [h, h.ne, not_lt_of_gt h]
  · subst h; simp
  · simp [h, h.ne', not_lt_of_gt h]

/-! ### Parity bookkeeping -/

theorem neg_one_pow_eq_iff (x y : ℕ) : ((-1 : ℤ) ^ x = (-1) ^ y) ↔ Even (x + y) := by
  rcases Nat.even_or_odd x with hx | hx <;> rcases Nat.even_or_odd y with hy | hy <;>
    simp [hx.neg_one_pow, hy.neg_one_pow, Nat.even_add, hx, hy,
      Nat.not_even_iff_odd.mpr, Nat.not_odd_iff_even.mpr]

theorem parity_iff {m : ℕ} (c A : Fin m → ℕ) (hA : ∀ j, A j + c j = ∑ k, c k) :
    (∀ j, Even (A j)) ↔ (∀ j, Even (c j)) ∨ (Odd m ∧ ∀ j, Odd (c j)) := by
  have key : ∀ j, ((A j : ℕ) : ZMod 2) + (c j : ZMod 2) = ((∑ k, c k : ℕ) : ZMod 2) := by
    intro j; rw [← Nat.cast_add, hA]
  have hS : ((∑ k, c k : ℕ) : ZMod 2) = ∑ k, (c k : ZMod 2) := Nat.cast_sum _ _
  constructor
  · intro h
    have hc : ∀ j, (c j : ZMod 2) = ((∑ k, c k : ℕ) : ZMod 2) := by
      intro j
      have := key j
      rw [ZMod.eq_zero_iff_even.mpr (h j), zero_add] at this
      exact this
    rcases (show ∀ x : ZMod 2, x = 0 ∨ x = 1 by decide) ((∑ k, c k : ℕ) : ZMod 2) with h0 | h1
    · left
      intro j
      exact ZMod.eq_zero_iff_even.mp ((hc j).trans h0)
    · right
      refine ⟨?_, fun j => ZMod.eq_one_iff_odd.mp ((hc j).trans h1)⟩
      apply ZMod.eq_one_iff_odd.mp
      rw [← h1, hS, Finset.sum_congr rfl (fun k _ => (hc k).trans h1)]
      simp
  · rintro (h | ⟨hm, h⟩) j
    · rw [← ZMod.eq_zero_iff_even]
      have hc0 : ∀ k, (c k : ZMod 2) = 0 := fun k => ZMod.eq_zero_iff_even.mpr (h k)
      have hS0 : ((∑ k, c k : ℕ) : ZMod 2) = 0 := by rw [hS]; simp [hc0]
      linear_combination key j - hc0 j + hS0
    · rw [← ZMod.eq_zero_iff_even]
      have hc1 : ∀ k, (c k : ZMod 2) = 1 := fun k => ZMod.eq_one_iff_odd.mpr (h k)
      have hS1 : ((∑ k, c k : ℕ) : ZMod 2) = 1 := by
        rw [hS]; simp only [hc1, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, mul_one]
        exact ZMod.eq_one_iff_odd.mpr hm
      linear_combination key j - hc1 j + hS1

/-! ### First claim: the center of the skew polynomial ring -/

/-- Commuting with every generator implies ordinary centrality (genuine generation). -/
theorem mem_center_of_generators {m : ℕ} (z : SkewPolynomial m)
    (h : ∀ j, z * generator j = generator j * z) : z ∈ Subring.center (SkewPolynomial m) := by
  refine Subring.mem_center_iff.mpr (fun p => ?_)
  symm
  obtain ⟨a, rfl⟩ := PbwRealization.Phi_surjective m p
  induction a using Quotient.inductionOn' with
  | h w =>
    change z * PbwL3.evalAlg m w = PbwL3.evalAlg m w * z
    induction w using FreeAlgebra.induction with
    | grade0 r =>
      rw [AlgHom.commutes]
      change z * (r • 1) = (r • 1) * z
      simp only [mul_smul_comm, smul_mul_assoc, mul_one, one_mul]
    | grade1 j => rw [PbwL3.evalAlg_ι]; exact h j
    | add a b ha hb => rw [map_add, mul_add, add_mul, ha, hb]
    | mul a b ha hb =>
      rw [map_mul, ← mul_assoc, ha, mul_assoc, hb, ← mul_assoc]

theorem commute_generator_iff {m : ℕ} (z : SkewPolynomial m) (j : Fin m) :
    z * generator j = generator j * z ↔
      ∀ c, z c ≠ 0 → Even (OddMath.crossingCount (expSingle j) c +
        OddMath.crossingCount c (expSingle j)) := by
  have hR : z * generator j =
      z.sum (fun a r => monomial (a + expSingle j) (r * 1 * OddMath.skewSign a (expSingle j))) :=
    mul_monomial_right z _ 1
  have hL : generator j * z =
      z.sum (fun a r => monomial (a + expSingle j) (1 * r * OddMath.skewSign (expSingle j) a)) := by
    rw [show generator j = monomial (expSingle j) 1 from rfl, mul_monomial_left]
    apply Finsupp.sum_congr
    intro a _
    rw [add_comm]
  rw [hR, hL]
  constructor
  · intro h c hc
    have := congrArg (fun f => f (c + expSingle j)) h
    simp only at this
    rw [sum_translate_apply _ _ _ _ (fun a => by simp),
      sum_translate_apply _ _ _ _ (fun a => by simp)] at this
    have hs : OddMath.skewSign c (expSingle j) = OddMath.skewSign (expSingle j) c := by
      apply mul_left_cancel₀ hc
      linear_combination this
    rw [add_comm]
    exact (neg_one_pow_eq_iff _ _).mp hs
  · intro h
    apply Finsupp.sum_congr
    intro a ha
    have hs : OddMath.skewSign a (expSingle j) = OddMath.skewSign (expSingle j) a := by
      apply (neg_one_pow_eq_iff _ _).mpr
      rw [add_comm]
      exact h a (Finsupp.mem_support_iff.mp ha)
    rw [hs]
    ring_nf

/-- **First claim (corrected).** Ordinary centrality in the skew polynomial ring of
rank `n+2`, stated on the coefficient function. -/
theorem mem_center_iff (z : SkewPolynomial (n+2)) :
    z ∈ Subring.center (SkewPolynomial (n+2)) ↔
      ∀ a, z a ≠ 0 → (∀ j, Even (a j)) ∨ (Odd (n+2) ∧ ∀ j, Odd (a j)) := by
  constructor
  · intro hz a ha
    rw [← parity_iff a (fun j => OddMath.crossingCount (expSingle j) a +
      OddMath.crossingCount a (expSingle j)) (fun j => crossing_unit_total j a)]
    intro j
    exact (commute_generator_iff z j).mp
      (Subring.mem_center_iff.mp hz (generator j)).symm a ha
  · intro h
    apply mem_center_of_generators
    intro j
    apply (commute_generator_iff z j).mpr
    intro c hc
    exact (parity_iff c _ (fun j => crossing_unit_total j c)).mpr (h c hc) j

/-! ### Even exponents and the squared-variable homomorphism -/

theorem skewSign_even {m : ℕ} (a b : Fin m → ℕ)
    (h : (∀ j, Even (a j)) ∨ (∀ j, Even (b j))) : OddMath.skewSign a b = 1 := by
  unfold OddMath.skewSign
  apply Even.neg_one_pow
  unfold OddMath.crossingCount
  apply Finset.sum_induction _ Even (fun _ _ => Even.add) Even.zero
  intro i _
  apply Finset.sum_induction _ Even (fun _ _ => Even.add) Even.zero
  intro k _
  rcases h with h | h
  · exact (h i).mul_right _
  · exact (h k).mul_left _

theorem mul_even {m : ℕ} (a b : Fin m → ℕ) (r t : ℤ)
    (h : (∀ j, Even (a j)) ∨ (∀ j, Even (b j))) :
    monomial a r * monomial b t = monomial (a+b) (r*t) := by
  rw [mulMon, skewSign_even a b h, mul_one]

theorem sq_generator (j : Fin (n+2)) :
    generator j ^ 2 = monomial (expSingle j + expSingle j) 1 := by
  rw [pow_two]
  show monomial (expSingle j) 1 * monomial (expSingle j) 1 = _
  rw [mulMon, OddMath.SkewPolynomial.skewSign_expSingle]
  simp

theorem sq_mem_center (j : Fin (n+2)) :
    generator j ^ 2 ∈ Subring.center (SkewPolynomial (n+2)) := by
  rw [mem_center_iff]
  intro a ha
  rw [sq_generator, Finsupp.single_apply] at ha
  split_ifs at ha with h
  · subst h
    left
    intro _
    exact ⟨_, rfl⟩
  · exact absurd rfl ha

/-- The squared-variable homomorphism `X_j ↦ x_j^2`, landing in the center. -/
def squareHom : MvPolynomial (Fin (n+2)) ℤ →+* SkewPolynomial (n+2) :=
  (Subring.center (SkewPolynomial (n+2))).subtype.comp
    (MvPolynomial.eval₂Hom (Int.castRingHom _) (fun j => ⟨generator j ^ 2, sq_mem_center j⟩))

@[simp] theorem squareHom_X (j : Fin (n+2)) :
    squareHom (MvPolynomial.X j) = generator j ^ 2 := by
  simp [squareHom]

theorem squareHom_mem_center (p : MvPolynomial (Fin (n+2)) ℤ) :
    squareHom p ∈ Subring.center (SkewPolynomial (n+2)) := by
  simp only [squareHom, RingHom.comp_apply]
  exact Subtype.property _

theorem squareHom_commute (p : MvPolynomial (Fin (n+2)) ℤ) (f : SkewPolynomial (n+2)) :
    squareHom p * f = f * squareHom p :=
  (Subring.mem_center_iff.mp (squareHom_mem_center p) f).symm

/-- Doubling of an exponent vector. -/
def dbl (m : Fin (n+2) →₀ ℕ) : Fin (n+2) → ℕ := fun j => 2 * m j

theorem dbl_even (m : Fin (n+2) →₀ ℕ) : ∀ j, Even (dbl m j) :=
  fun _ => even_two_mul _

theorem dbl_injective : Function.Injective (dbl (n := n)) := by
  intro m m' h
  ext j
  have := congrFun h j
  simp only [dbl] at this
  omega

theorem sq_pow (j : Fin (n+2)) (k : ℕ) :
    (generator j ^ 2) ^ k = monomial (dbl (Finsupp.single j k)) 1 := by
  induction k with
  | zero =>
    have h0 : dbl (Finsupp.single j 0) = 0 := by funext i; simp [dbl]
    rw [pow_zero, h0]
    rfl
  | succ k ih =>
    rw [pow_succ, ih, sq_generator, mul_even _ _ _ _ (Or.inl (dbl_even _)), one_mul]
    congr 1
    funext i
    simp only [dbl, Pi.add_apply, expSingle, Finsupp.single_apply]
    split_ifs <;> omega

theorem intCast_eq_monomial (c : ℤ) : (c : SkewPolynomial (n+2)) = monomial 0 c := by
  show c • (monomial 0 1 : SkewPolynomial (n+2)) = _
  rw [Finsupp.smul_single, smul_eq_mul, mul_one]

theorem squareHom_intCast (c : ℤ) : squareHom (MvPolynomial.C c : MvPolynomial (Fin (n+2)) ℤ) =
    (c : SkewPolynomial (n+2)) := by
  rw [eq_intCast MvPolynomial.C c, map_intCast]

theorem squareHom_monomial (m : Fin (n+2) →₀ ℕ) (c : ℤ) :
    squareHom (MvPolynomial.monomial m c) = monomial (dbl m) c := by
  induction m using Finsupp.induction generalizing c with
  | zero =>
    have h0 : dbl (0 : Fin (n+2) →₀ ℕ) = 0 := by funext i; simp [dbl]
    rw [← MvPolynomial.C_apply, squareHom_intCast, h0, intCast_eq_monomial]
  | single_add j k f _ _ ih =>
    rw [MvPolynomial.monomial_single_add, map_mul, map_pow, squareHom_X, ih, sq_pow,
      mul_even _ _ _ _ (Or.inl (dbl_even _)), one_mul]
    congr 1
    funext i
    simp only [dbl, Pi.add_apply, Finsupp.add_apply]
    ring

theorem squareHom_eq_sum (p : MvPolynomial (Fin (n+2)) ℤ) :
    squareHom p = ∑ m ∈ p.support, monomial (dbl m) (p.coeff m) := by
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  simp only [squareHom_monomial]

theorem squareHom_apply_dbl (p : MvPolynomial (Fin (n+2)) ℤ) (m : Fin (n+2) →₀ ℕ) :
    squareHom p (dbl m) = p.coeff m := by
  rw [squareHom_eq_sum, Finsupp.finset_sum_apply, Finset.sum_eq_single m]
  · simp
  · intro b _ hb
    rw [Finsupp.single_apply, if_neg (fun h => hb (dbl_injective h))]
  · intro hm
    rw [MvPolynomial.not_mem_support_iff.mp hm]
    simp

theorem squareHom_apply_of_not_even (p : MvPolynomial (Fin (n+2)) ℤ) (a : Fin (n+2) → ℕ)
    (j : Fin (n+2)) (hj : ¬ Even (a j)) : squareHom p a = 0 := by
  rw [squareHom_eq_sum, Finsupp.finset_sum_apply]
  apply Finset.sum_eq_zero
  intro b _
  rw [Finsupp.single_apply, if_neg]
  rintro rfl
  exact hj (dbl_even b j)

theorem squareHom_injective : Function.Injective (squareHom (n := n)) := by
  intro p q h
  ext m
  rw [← squareHom_apply_dbl, ← squareHom_apply_dbl, h]

theorem monomial_eq_single {m : ℕ} (a : Fin m → ℕ) (c : ℤ) :
    monomial a c = Finsupp.single a c := rfl

/-! ### The volume element -/

/-- The volume `V = x_0 x_1 ⋯ x_{n+1}`: the product of the generators in index order. -/
def V (n : ℕ) : SkewPolynomial (n+2) := (List.ofFn (fun j : Fin (n+2) => generator j)).prod

theorem prefix_prod_eq {m : ℕ} (k : ℕ) (hk : k ≤ m) :
    (List.ofFn (fun i : Fin k => generator (Fin.castLE hk i))).prod =
      monomial (fun j : Fin m => if j.val < k then 1 else 0) 1 := by
  induction k with
  | zero =>
    have h0 : (fun j : Fin m => if j.val < 0 then 1 else 0) = 0 := by funext j; simp
    rw [List.ofFn_zero, List.prod_nil, h0]
    rfl
  | succ k ih =>
    rw [List.ofFn_succ', List.concat_eq_append, List.prod_append, List.prod_singleton]
    have ih' := ih (Nat.le_of_succ_le hk)
    simp only [Fin.castLE_castSucc] at ih' ⊢
    rw [ih']
    show _ * monomial _ 1 = _
    rw [mulMon, OddMath.skewSign, crossing_unit_right]
    have hz : (∑ i : Fin m, if Fin.castLE hk (Fin.last k) < i then
        (if i.val < k then 1 else 0) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      split_ifs with h1 h2
      · exfalso
        have : k < i.val := by simpa [Fin.lt_def] using h1
        omega
      · rfl
      · rfl
    rw [hz, pow_zero, mul_one, mul_one]
    congr 1
    funext j
    simp only [Pi.add_apply, expSingle, Fin.ext_iff, Fin.coe_castLE, Fin.val_last]
    split_ifs <;> omega

theorem V_eq_monomial : V n = monomial (fun _ => 1) 1 := by
  have := prefix_prod_eq (m := n+2) (n+2) le_rfl
  simp only [Fin.castLE_rfl, id_eq, Fin.is_lt, if_true] at this
  exact this

theorem V_mul_monomial_dbl (m : Fin (n+2) →₀ ℕ) (c : ℤ) :
    V n * monomial (dbl m) c = monomial ((fun _ => 1) + dbl m) c := by
  rw [V_eq_monomial, mul_even _ _ _ _ (Or.inr (dbl_even m)), one_mul]

theorem V_mem_center (hN : Odd (n+2)) : V n ∈ Subring.center (SkewPolynomial (n+2)) := by
  rw [mem_center_iff]
  intro a ha
  rw [V_eq_monomial, monomial_eq_single, Finsupp.single_apply] at ha
  split_ifs at ha with h
  · subst h
    exact Or.inr ⟨hN, fun _ => odd_one⟩
  · exact absurd rfl ha

theorem V_apply : V n (fun _ => 1) = 1 := by
  rw [V_eq_monomial, monomial_eq_single, Finsupp.single_eq_same]

theorem V_not_mem_range (p : MvPolynomial (Fin (n+2)) ℤ) : squareHom p ≠ V n := by
  intro h
  have h1 := squareHom_apply_of_not_even p (fun _ => 1) 0 (by simp)
  rw [h, V_apply] at h1
  exact one_ne_zero h1

/-- Divided differences kill monomials in spectator variables only. -/
theorem divided_spectator_monomial (i : Fin (n+1)) :
    ∀ (d : ℕ) (a : Fin (n+2) → ℕ), ∑ k, a k = d → a i.castSucc = 0 → a i.succ = 0 →
      ∀ c, divided i (monomial a c) = 0 := by
  intro d
  induction d with
  | zero =>
    intro a ha _ _ c
    have ha0 : a = 0 := by
      funext k
      exact (Finset.sum_eq_zero_iff.mp ha) k (Finset.mem_univ _)
    subst ha0
    have : monomial (0 : Fin (n+2) → ℕ) c = c • (1 : SkewPolynomial (n+2)) := by
      show _ = c • monomial 0 1
      rw [monomial_eq_single, monomial_eq_single, Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [this, map_smul, divided_one, smul_zero]
  | succ d ih =>
    intro a ha hl hr c
    obtain ⟨j, _, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ) (f := a)
      (by rw [ha]; omega)
    have hjl : j ≠ i.castSucc := by rintro rfl; exact hj hl
    have hjr : j ≠ i.succ := by rintro rfl; exact hj hr
    let a' : Fin (n+2) → ℕ := fun k => a k - expSingle j k
    have hsplit : a = expSingle j + a' := by
      funext k
      simp only [a', Pi.add_apply, expSingle]
      split_ifs with h
      · subst h; omega
      · omega
    have hsum : ∑ k, a' k = d := by
      have := congrArg (fun f : Fin (n+2) → ℕ => ∑ k, f k) hsplit
      simp only [Pi.add_apply, Finset.sum_add_distrib, expSingle, Finset.sum_ite_eq,
        Finset.mem_univ, if_true] at this
      omega
    rw [hsplit, monomial_split, divided_spectator_mul i j hjl hjr,
      ih a' hsum (by simp [a', hl]) (by simp [a', hr]), mul_zero]

theorem divided_V (i : Fin (n+1)) : divided i (V n) = 0 := by
  have hne := adjacent_ne i
  let u : Fin (n+2) → ℕ := fun k => if k = i.castSucc ∨ k = i.succ then 0 else 1
  let b : Fin (n+2) → ℕ := fun k => if k = i.castSucc then 0 else 1
  have h1 : (fun _ => 1 : Fin (n+2) → ℕ) = expSingle i.castSucc + b := by
    funext k
    by_cases hk1 : k = i.castSucc
    · subst hk1; simp [b, expSingle]
    · simp [b, expSingle, hk1, Ne.symm hk1]
  have h2 : b = expSingle i.succ + u := by
    funext k
    by_cases hk1 : k = i.castSucc
    · subst hk1; simp [b, u, expSingle, hne, Ne.symm hne]
    · by_cases hk2 : k = i.succ
      · subst hk2; simp [b, u, expSingle, hk1]
      · simp [b, u, expSingle, hk1, hk2, Ne.symm hk2]
  have hu : ∀ c, divided i (monomial u c) = 0 := fun c =>
    divided_spectator_monomial i _ u rfl (by simp [u]) (by simp [u]) c
  rw [V_eq_monomial, h1, monomial_split, h2, monomial_split, divided_left_mul, divided_right_mul, hu,
    mul_zero, sub_zero, sub_self]

theorem V_mem_kernel : V n ∈ kernelSubring n := fun i => divided_V i

/-- For a central element of the joint kernel, every `s_i` fixes it:
`s_i z = ∂_i(z x_i) = ∂_i(x_i z) = z - x_{i+1} ∂_i z = z`. -/
theorem s_fix_of_central_kernel (i : Fin (n+1)) (z : SkewPolynomial (n+2))
    (hz : z ∈ Subring.center (SkewPolynomial (n+2))) (hd : divided i z = 0) : s i z = z := by
  have hc : generator i.castSucc * z = z * generator i.castSucc :=
    Subring.mem_center_iff.mp hz _
  have h1 := divided_left_mul i z
  rw [hc, divided_mul, hd, divided_generator, if_pos (Or.inl rfl)] at h1
  simpa using h1

theorem s_V (hN : Odd (n+2)) (i : Fin (n+1)) : s i (V n) = V n :=
  s_fix_of_central_kernel i _ (V_mem_center hN) (divided_V i)

/-! ### Decomposition of central elements -/

/-- Halving of an exponent vector. -/
def half (a : Fin (n+2) → ℕ) : Fin (n+2) →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun j => a j / 2)

theorem dbl_half_even (a : Fin (n+2) → ℕ) (h : ∀ j, Even (a j)) : dbl (half a) = a := by
  funext j
  simp only [dbl, half, Finsupp.equivFunOnFinite_symm_apply_toFun]
  exact Nat.two_mul_div_two_of_even (h j)

theorem one_add_dbl_half_odd (a : Fin (n+2) → ℕ) (h : ∀ j, Odd (a j)) :
    (fun _ => 1) + dbl (half a) = a := by
  funext j
  simp only [dbl, half, Pi.add_apply, Finsupp.equivFunOnFinite_symm_apply_toFun]
  have := Nat.odd_iff.mp (h j)
  omega

/-- Every central element is `a + V b` with `a, b` in the squared variables, `b = 0` in
even rank. -/
theorem center_decomp (z : SkewPolynomial (n+2)) (hz : z ∈ Subring.center (SkewPolynomial (n+2))) :
    ∃ p q : MvPolynomial (Fin (n+2)) ℤ, z = squareHom p + V n * squareHom q ∧
      (Even (n+2) → q = 0) := by
  classical
  have hP := (mem_center_iff z).mp hz
  refine ⟨∑ a ∈ z.support.filter (fun a => ∀ j, Even (a j)),
      MvPolynomial.monomial (half a) (z a),
    ∑ a ∈ z.support.filter (fun a => ¬ ∀ j, Even (a j)),
      MvPolynomial.monomial (half a) (z a), ?_, ?_⟩
  · rw [map_sum, map_sum, Finset.mul_sum]
    conv_lhs => rw [← Finsupp.sum_single z]
    rw [Finsupp.sum, ← Finset.sum_filter_add_sum_filter_not z.support (fun a => ∀ j, Even (a j))]
    congr 1
    · apply Finset.sum_congr rfl
      intro a ha
      rw [squareHom_monomial, dbl_half_even a (Finset.mem_filter.mp ha).2, monomial_eq_single]
    · apply Finset.sum_congr rfl
      intro a ha
      obtain ⟨ha1, ha2⟩ := Finset.mem_filter.mp ha
      have hodd := ((hP a (Finsupp.mem_support_iff.mp ha1)).resolve_left ha2).2
      rw [squareHom_monomial, V_mul_monomial_dbl, one_add_dbl_half_odd a hodd,
        monomial_eq_single]
  · intro hev
    apply Finset.sum_eq_zero
    intro a ha
    exfalso
    obtain ⟨ha1, ha2⟩ := Finset.mem_filter.mp ha
    rcases hP a (Finsupp.mem_support_iff.mp ha1) with h | ⟨hodd, _⟩
    · exact ha2 h
    · exact (Nat.not_even_iff_odd.mpr hodd) hev

/-! ### Signed action and divided differences on the squared variables -/

theorem s_squareHom (i : Fin (n+1)) (p : MvPolynomial (Fin (n+2)) ℤ) :
    s i (squareHom p) =
      squareHom (MvPolynomial.rename (Equiv.swap i.castSucc i.succ) p) := by
  induction p using MvPolynomial.induction_on with
  | C a => rw [MvPolynomial.rename_C, squareHom_intCast, map_intCast]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j hp =>
    simp only [map_mul, MvPolynomial.rename_X, squareHom_X, map_pow, s_generator, neg_sq, hp]

theorem divided_intCast (i : Fin (n+1)) (a : ℤ) : divided i (a : SkewPolynomial (n+2)) = 0 := by
  have : (a : SkewPolynomial (n+2)) = a • (1 : SkewPolynomial (n+2)) := rfl
  rw [this, map_smul, divided_one, smul_zero]

/-- The linear form `x_i - x_{i+1}`. -/
def L (i : Fin (n+1)) : SkewPolynomial (n+2) := generator i.castSucc - generator i.succ

theorem divided_sq (i : Fin (n+1)) (j : Fin (n+2)) :
    ∃ d : MvPolynomial (Fin (n+2)) ℤ, divided i (generator j ^ 2) = L i * squareHom d := by
  have hne := adjacent_ne i
  rw [pow_two, divided_mul, divided_generator, s_generator]
  by_cases h1 : j = i.castSucc
  · subst h1
    refine ⟨1, ?_⟩
    rw [if_pos (Or.inl rfl), Equiv.swap_apply_left, map_one, L]
    noncomm_ring
  · by_cases h2 : j = i.succ
    · subst h2
      refine ⟨-1, ?_⟩
      rw [if_pos (Or.inr rfl), Equiv.swap_apply_right, map_neg, map_one, L]
      noncomm_ring
    · refine ⟨0, ?_⟩
      rw [if_neg (by tauto), map_zero]
      simp

/-- Divided differences of squared-variable polynomials are divisible by `x_i - x_{i+1}`. -/
theorem divided_squareHom (i : Fin (n+1)) (p : MvPolynomial (Fin (n+2)) ℤ) :
    ∃ q, divided i (squareHom p) = L i * squareHom q := by
  induction p using MvPolynomial.induction_on with
  | C a => exact ⟨0, by rw [squareHom_intCast, divided_intCast, map_zero, mul_zero]⟩
  | add p q hp hq =>
    obtain ⟨q1, h1⟩ := hp
    obtain ⟨q2, h2⟩ := hq
    exact ⟨q1 + q2, by rw [map_add, map_add, h1, h2, map_add, mul_add]⟩
  | mul_X p j hp =>
    obtain ⟨q1, hq1⟩ := hp
    obtain ⟨d, hd⟩ := divided_sq i j
    refine ⟨q1 * MvPolynomial.X j +
      MvPolynomial.rename (Equiv.swap i.castSucc i.succ) p * d, ?_⟩
    have hc := squareHom_commute (MvPolynomial.rename (Equiv.swap i.castSucc i.succ) p) (L i)
    rw [map_mul, divided_mul, hq1, s_squareHom, squareHom_X, hd]
    simp only [map_add, map_mul, squareHom_X, mul_add]
    rw [← mul_assoc (squareHom _) (L i), hc]
    simp only [mul_assoc]

theorem T_sq (i : Fin (n+1)) (j : Fin (n+2)) :
    generator i.castSucc * divided i (generator j ^ 2) +
        divided i (generator j ^ 2) * generator i.succ =
      generator j ^ 2 - s i (generator j ^ 2) := by
  have hne := adjacent_ne i
  rw [map_pow (s i), s_generator, neg_sq, pow_two, divided_mul, divided_generator, s_generator]
  by_cases h1 : j = i.castSucc
  · subst h1
    rw [if_pos (Or.inl rfl), Equiv.swap_apply_left]
    noncomm_ring
  · by_cases h2 : j = i.succ
    · subst h2
      rw [if_pos (Or.inr rfl), Equiv.swap_apply_right]
      noncomm_ring
    · rw [if_neg (by tauto), Equiv.swap_apply_of_ne_of_ne h1 h2]
      simp [pow_two]

theorem T_step {R : Type*} [Ring R] (x x' f sf Df y sy Dy : R) (hsc : x*sf = sf*x)
    (hyc : y*x' = x'*y) (hp : x*Df + Df*x' = f - sf) (hy : x*Dy + Dy*x' = y - sy) :
    x*(Df*y + sf*Dy) + (Df*y + sf*Dy)*x' = f*y - sf*sy := by
  calc x*(Df*y + sf*Dy) + (Df*y + sf*Dy)*x'
      = x*Df*y + (x*sf)*Dy + Df*(y*x') + sf*Dy*x' := by noncomm_ring
    _ = x*Df*y + (sf*x)*Dy + Df*(x'*y) + sf*Dy*x' := by rw [hsc, hyc]
    _ = (x*Df + Df*x')*y + sf*(x*Dy + Dy*x') := by noncomm_ring
    _ = (f - sf)*y + sf*(y - sy) := by rw [hp, hy]
    _ = f*y - sf*sy := by noncomm_ring

/-- The identity behind the printed proof's second claim:
`x_i ∂_i f + (∂_i f) x_{i+1} = f - s_i f` for `f` in the squared variables. -/
theorem T_squareHom (i : Fin (n+1)) (p : MvPolynomial (Fin (n+2)) ℤ) :
    generator i.castSucc * divided i (squareHom p) + divided i (squareHom p) * generator i.succ =
      squareHom p - s i (squareHom p) := by
  induction p using MvPolynomial.induction_on with
  | C a => rw [squareHom_intCast, divided_intCast, map_intCast]; simp
  | add p q hp hq =>
    rw [map_add, map_add, map_add, mul_add, add_mul]
    rw [show ∀ a b c d : SkewPolynomial (n+2), a + b + (c + d) = (a + c) + (b + d) from
      fun a b c d => by abel, hp, hq]
    abel
  | mul_X p j hp =>
    rw [map_mul, squareHom_X, divided_mul, map_mul]
    refine T_step _ _ _ _ _ _ _ _ ?_ ?_ hp (T_sq i j)
    · rw [s_squareHom]
      exact (squareHom_commute _ _).symm
    · exact (Subring.mem_center_iff.mp (sq_mem_center j) _).symm

/-- **Second claim of the printed proof (correct).** For `f` in the squared variables,
`∂_i f = 0 ↔ s_i f = f`. -/
theorem second_claim (i : Fin (n+1)) (p : MvPolynomial (Fin (n+2)) ℤ) :
    divided i (squareHom p) = 0 ↔ s i (squareHom p) = squareHom p := by
  constructor
  · exact s_fix_of_central_kernel i _ (squareHom_mem_center p)
  · intro h
    obtain ⟨q, hq⟩ := divided_squareHom i p
    have hT := T_squareHom i p
    rw [h, sub_self, hq] at hT
    have hcomm := squareHom_commute q (generator i.succ)
    have e : squareHom ((MvPolynomial.X i.castSucc - MvPolynomial.X i.succ) * q) =
        generator i.castSucc * (L i * squareHom q) + L i * squareHom q * generator i.succ := by
      rw [map_mul, map_sub, squareHom_X, squareHom_X, mul_assoc (L i), hcomm, L]
      noncomm_ring
    rw [hT, ← map_zero squareHom] at e
    have hne : (MvPolynomial.X i.castSucc - MvPolynomial.X i.succ :
        MvPolynomial (Fin (n+2)) ℤ) ≠ 0 :=
      sub_ne_zero.mpr (fun h => adjacent_ne i (MvPolynomial.X_injective h))
    have hq0 : q = 0 := (mul_eq_zero.mp (squareHom_injective e)).resolve_left hne
    rw [hq, hq0, map_zero, mul_zero]

theorem second_claim_range (i : Fin (n+1)) (f : SkewPolynomial (n+2))
    (hf : f ∈ (squareHom (n := n)).range) : divided i f = 0 ↔ s i f = f := by
  obtain ⟨p, rfl⟩ := hf
  exact second_claim i p

/-! ### Separation of the two parity summands -/

theorem V_mul_squareHom_eq_sum (q : MvPolynomial (Fin (n+2)) ℤ) :
    V n * squareHom q = ∑ m ∈ q.support, monomial ((fun _ => 1) + dbl m) (q.coeff m) := by
  rw [squareHom_eq_sum, Finset.mul_sum]
  simp only [V_mul_monomial_dbl]

theorem V_mul_squareHom_apply_dbl (q : MvPolynomial (Fin (n+2)) ℤ) (m : Fin (n+2) →₀ ℕ) :
    (V n * squareHom q) (dbl m) = 0 := by
  rw [V_mul_squareHom_eq_sum, Finsupp.finset_sum_apply]
  apply Finset.sum_eq_zero
  intro b _
  rw [monomial_eq_single, Finsupp.single_apply, if_neg]
  intro h
  have := congrFun h 0
  simp only [Pi.add_apply, dbl] at this
  omega

theorem V_mul_squareHom_apply_odd (q : MvPolynomial (Fin (n+2)) ℤ) (m : Fin (n+2) →₀ ℕ) :
    (V n * squareHom q) ((fun _ => 1) + dbl m) = q.coeff m := by
  rw [V_mul_squareHom_eq_sum, Finsupp.finset_sum_apply, Finset.sum_eq_single m]
  · rw [monomial_eq_single, Finsupp.single_eq_same]
  · intro b _ hb
    rw [monomial_eq_single, Finsupp.single_apply, if_neg]
    intro h
    exact hb (dbl_injective (add_left_cancel h))
  · intro hm
    rw [MvPolynomial.not_mem_support_iff.mp hm]
    simp

theorem squareHom_apply_odd (p : MvPolynomial (Fin (n+2)) ℤ) (m : Fin (n+2) →₀ ℕ) :
    squareHom p ((fun _ => 1) + dbl m) = 0 := by
  apply squareHom_apply_of_not_even p _ 0
  simp only [Pi.add_apply, dbl]
  rw [Nat.not_even_iff_odd]
  exact ⟨m 0, by ring⟩

theorem separate (p q p' q' : MvPolynomial (Fin (n+2)) ℤ)
    (h : squareHom p + V n * squareHom q = squareHom p' + V n * squareHom q') :
    p = p' ∧ q = q' := by
  constructor
  · ext m
    have := congrArg (fun f : SkewPolynomial (n+2) => f (dbl m)) h
    simp only [Finsupp.add_apply, squareHom_apply_dbl, V_mul_squareHom_apply_dbl,
      add_zero] at this
    exact this
  · ext m
    have := congrArg (fun f : SkewPolynomial (n+2) => f ((fun _ => 1) + dbl m)) h
    simp only [Finsupp.add_apply, squareHom_apply_odd, V_mul_squareHom_apply_odd,
      zero_add] at this
    exact this

/-! ### Symmetry from adjacent transpositions -/

theorem symmetric_of_adjacent (p : MvPolynomial (Fin (n+2)) ℤ)
    (h : ∀ i : Fin (n+1), MvPolynomial.rename (Equiv.swap i.castSucc i.succ) p = p) :
    p ∈ MvPolynomial.symmetricSubalgebra (Fin (n+2)) ℤ := by
  rw [MvPolynomial.mem_symmetricSubalgebra]
  intro e
  have he : e ∈ Submonoid.closure (Set.range fun i : Fin (n+1) => Equiv.swap i.castSucc i.succ) := by
    rw [Equiv.Perm.mclosure_swap_castSucc_succ]
    exact Submonoid.mem_top e
  induction he using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact h i
  | one => simp [MvPolynomial.rename_id]
  | mul x y _ _ hx hy => rw [Equiv.Perm.coe_mul, ← MvPolynomial.rename_rename, hy, hx]

/-! ### The squared symmetric ring and the headline -/

/-- The symmetric polynomials in the squared variables `x_0^2, …, x_{n+1}^2`: the image of
Mathlib's `symmetricSubalgebra` under `squareHom`. -/
def sq (n : ℕ) : Subring (SkewPolynomial (n+2)) :=
  (MvPolynomial.symmetricSubalgebra (Fin (n+2)) ℤ).toSubring.map squareHom

theorem mem_sq (z : SkewPolynomial (n+2)) :
    z ∈ sq n ↔ ∃ p ∈ MvPolynomial.symmetricSubalgebra (Fin (n+2)) ℤ, squareHom p = z := by
  simp only [sq, Subring.mem_map, Subalgebra.mem_toSubring]

theorem divided_sq_of_symmetric (p : MvPolynomial (Fin (n+2)) ℤ)
    (hp : p ∈ MvPolynomial.symmetricSubalgebra (Fin (n+2)) ℤ) (i : Fin (n+1)) :
    divided i (squareHom p) = 0 :=
  (second_claim i p).mpr (by
    rw [s_squareHom, (MvPolynomial.mem_symmetricSubalgebra p).mp hp])

/-- **Corrected EKL Prop. 2.15 (polynomial side), every rank `N = n+2`.** The central
elements of the joint kernel of the odd divided differences are exactly `a + V b`
(`N` odd) or `a` (`N` even), with `a, b` symmetric polynomials in the squared variables. -/
theorem kernel_inter_center (n : ℕ) (z : SkewPolynomial (n+2)) :
    (z ∈ kernelSubring n ∧ z ∈ Subring.center (SkewPolynomial (n+2))) ↔
      ∃ a ∈ sq n, ∃ b ∈ sq n, z = a + (if Odd (n+2) then V n * b else 0) := by
  constructor
  · rintro ⟨hk, hc⟩
    obtain ⟨p, q, hz, hq0⟩ := center_decomp z hc
    have hfix : ∀ i, s i z = z := fun i => s_fix_of_central_kernel i z hc (hk i)
    rcases Nat.even_or_odd (n+2) with hev | hodd
    · have hq := hq0 hev
      subst hq
      rw [map_zero, mul_zero, add_zero] at hz
      refine ⟨squareHom p, (mem_sq _).mpr ⟨p, symmetric_of_adjacent p (fun i => ?_), rfl⟩,
        0, zero_mem _, ?_⟩
      · have := hfix i
        rw [hz, s_squareHom] at this
        exact squareHom_injective this
      · rw [if_neg (Nat.not_odd_iff_even.mpr hev), add_zero, hz]
    · have hsym : ∀ i : Fin (n+1),
          MvPolynomial.rename (Equiv.swap i.castSucc i.succ) p = p ∧
          MvPolynomial.rename (Equiv.swap i.castSucc i.succ) q = q := fun i => by
        have := hfix i
        rw [hz, map_add, map_mul, s_squareHom, s_squareHom, s_V hodd] at this
        exact separate _ _ _ _ this
      refine ⟨squareHom p, (mem_sq _).mpr ⟨p, symmetric_of_adjacent p (fun i => (hsym i).1), rfl⟩,
        squareHom q, (mem_sq _).mpr ⟨q, symmetric_of_adjacent q (fun i => (hsym i).2), rfl⟩, ?_⟩
      rw [if_pos hodd, hz]
  · rintro ⟨a, ha, b, hb, rfl⟩
    obtain ⟨p, hp, rfl⟩ := (mem_sq _).mp ha
    obtain ⟨q, hq, rfl⟩ := (mem_sq _).mp hb
    constructor
    · rw [mem_kernelSubring]
      intro i
      split_ifs with h
      · rw [map_add, divided_mul, divided_V, divided_sq_of_symmetric p hp i,
          divided_sq_of_symmetric q hq i]
        simp
      · rw [add_zero]
        exact divided_sq_of_symmetric p hp i
    · split_ifs with h
      · exact Subring.add_mem _ (squareHom_mem_center p)
          (Subring.mul_mem _ (V_mem_center h) (squareHom_mem_center q))
      · rw [add_zero]
        exact squareHom_mem_center p

/-- Even rank: the printed statement holds. -/
theorem even_rank (n : ℕ) (h : Even (n+2)) (z : SkewPolynomial (n+2)) :
    (z ∈ kernelSubring n ∧ z ∈ Subring.center (SkewPolynomial (n+2))) ↔ z ∈ sq n := by
  have hno : ¬ Odd (n+2) := Nat.not_odd_iff_even.mpr h
  rw [kernel_inter_center]
  simp only [hno, if_false, add_zero]
  constructor
  · rintro ⟨a, ha, b, _, rfl⟩
    exact ha
  · intro hz
    exact ⟨z, hz, 0, zero_mem _, rfl⟩

/-- Odd rank: the volume is a central kernel element outside the squared symmetric ring. -/
theorem odd_rank (n : ℕ) (h : Odd (n+2)) :
    V n ∈ kernelSubring n ∧ V n ∈ Subring.center (SkewPolynomial (n+2)) ∧ V n ∉ sq n := by
  refine ⟨V_mem_kernel, V_mem_center h, fun hv => ?_⟩
  obtain ⟨p, _, hp⟩ := (mem_sq _).mp hv
  exact V_not_mem_range p hp

/-- The printed statement (kernel ∩ center = squared symmetric ring) holds exactly in even rank. -/
theorem printed_statement_iff (n : ℕ) :
    (∀ z : SkewPolynomial (n+2),
      (z ∈ kernelSubring n ∧ z ∈ Subring.center (SkewPolynomial (n+2))) ↔ z ∈ sq n) ↔
      Even (n+2) := by
  constructor
  · intro hall
    by_contra hev
    have hodd := Nat.not_even_iff_odd.mp hev
    obtain ⟨hk, hc, hn⟩ := odd_rank n hodd
    exact hn ((hall (V n)).mp ⟨hk, hc⟩)
  · exact fun h z => even_rank n h z

end
end OddMath.Frontier.CenterPoly
