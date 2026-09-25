import OddMath.Frontier.OddSymmetricKernel
import Mathlib.Order.PiLex
import Mathlib.Data.DFinsupp.WellFounded

/-! Integral elementary generation, EKL 1111.1320v1 Prop. 2.2, pp. 7–8.
All term-order lemmas below serve the integral elimination proof. The exponent
order is first-coordinate-first lexicographic order; coefficients retain the
actual increasing-index skew-product signs. -/
namespace OddMath.Frontier.ElementaryGeneration
open OddMath.SkewPolynomial (SkewPolynomial generator monomial expSingle
  generator_anticommute mul_monomial)
open FiniteCompleteElementary OddSymmetricKernel AllRankDivided
open scoped BigOperators
noncomputable section

/-- The exact elementary-generated subring in the assigned statement. -/
def elementaryClosure (n : ℕ) : Subring (SkewPolynomial (n+2)) :=
  Subring.closure {f | ∃ k, 1 ≤ k ∧ k ≤ n+2 ∧ f = elementaryPoly (n+2) k}

theorem elementaryClosure_le_kernel (n : ℕ) : elementaryClosure n ≤ kernelSubring n := by
  apply Subring.closure_le.mpr
  rintro f ⟨k, _, _, rfl⟩
  exact elementary_mem n k

abbrev Exp (n : ℕ) := Fin n → ℕ

def Bounded {n : ℕ} (f : SkewPolynomial n) (a : Exp n) : Prop :=
  ∀ b, f b ≠ 0 → toLex b ≤ toLex a

def Leading {n : ℕ} (f : SkewPolynomial n) (a : Exp n) (c : ℤ) : Prop :=
  Bounded f a ∧ f a = c

theorem bounded_smul {n : ℕ} (c : ℤ) {f : SkewPolynomial n} {a : Exp n}
    (hf : Bounded f a) : Bounded (c • f) a := by
  intro b hb
  apply hf b
  intro h
  rw [Finsupp.smul_apply,h,smul_zero] at hb
  exact hb rfl

theorem bounded_neg {n : ℕ} {f : SkewPolynomial n} {a : Exp n}
    (hf : Bounded f a) : Bounded (-f) a := by
  intro b hb
  apply hf b
  simpa only [Finsupp.neg_apply, neg_ne_zero] using hb

theorem lex_add_lt_right {n : ℕ} {a b : Exp n} (h : toLex a < toLex b) (c : Exp n) :
    toLex (a+c) < toLex (b+c) := by
  obtain ⟨i, hi, hab⟩ := h
  refine ⟨i, fun j hj => ?_, Nat.add_lt_add_right hab _⟩
  change a j + c j = b j + c j
  exact congrArg (fun x => x + c j) (hi j hj)

theorem lex_add_le_right {n : ℕ} {a b : Exp n} (h : toLex a ≤ toLex b) (c : Exp n) :
    toLex (a+c) ≤ toLex (b+c) := by
  rcases h.lt_or_eq with h | h
  · exact (lex_add_lt_right h c).le
  · have hab : a = b := h; subst b; exact le_rfl

theorem lex_add_le_add {n : ℕ} {a b c d : Exp n}
    (h : toLex a ≤ toLex b) (k : toLex c ≤ toLex d) :
    toLex (a+c) ≤ toLex (b+d) := by
  exact (lex_add_le_right h c).trans (by simpa only [add_comm] using lex_add_le_right k b)

theorem bounded_zero {n : ℕ} (a : Exp n) : Bounded (0 : SkewPolynomial n) a := by
  intro b hb; exact False.elim (hb rfl)

theorem bounded_single {n : ℕ} (a : Exp n) (c : ℤ) : Bounded (monomial a c) a := by
  intro b hb
  by_cases h : a = b
  · subst b; exact le_rfl
  · exact False.elim (hb (Finsupp.single_eq_of_ne h))

theorem bounded_add {n : ℕ} {f g : SkewPolynomial n} {a : Exp n}
    (hf : Bounded f a) (hg : Bounded g a) : Bounded (f+g) a := by
  intro b hb
  by_cases h : f b = 0
  · apply hg b; intro h'; exact hb (by simp [h, h'])
  · exact hf b h

theorem bounded_mono {n : ℕ} {f : SkewPolynomial n} {a b : Exp n}
    (hf : Bounded f a) (h : toLex a ≤ toLex b) : Bounded f b :=
  fun c hc => (hf c hc).trans h

theorem bounded_sum {n : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → SkewPolynomial n) (a : Exp n) (h : ∀ i ∈ s, Bounded (f i) a) :
    Bounded (∑ i ∈ s, f i) a := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using bounded_zero a
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact bounded_add (h i (by simp)) (ih (fun j hj => h j (by simp [hj])))

theorem bounded_mul {n : ℕ} {f g : SkewPolynomial n} {a b : Exp n}
    (hf : Bounded f a) (hg : Bounded g b) : Bounded (f*g) (a+b) := by
  classical
  change Bounded (f.sum fun u r => g.sum fun v s =>
    monomial (u+v) (r*s*OddMath.skewSign u v)) (a+b)
  apply bounded_sum
  intro u hu
  apply bounded_sum
  intro v hv
  exact bounded_mono (bounded_single _ _) (lex_add_le_add
    (hf u (Finsupp.mem_support_iff.mp hu)) (hg v (Finsupp.mem_support_iff.mp hv)))

theorem mul_coeff {n : ℕ} (f g : SkewPolynomial n) (w : Exp n) :
    (f*g) w = ∑ u ∈ f.support, ∑ v ∈ g.support,
      if u+v=w then f u*g v*OddMath.skewSign u v else 0 := by
  classical
  change (f.sum fun u r => g.sum fun v s => monomial (u+v) (r*s*OddMath.skewSign u v)) w = _
  simp only [Finsupp.sum, Finsupp.finset_sum_apply, monomial, Finsupp.single_apply]

theorem add_eq_of_bounded {n : ℕ} {u v a b : Exp n}
    (hu : toLex u ≤ toLex a) (hv : toLex v ≤ toLex b) (he : u+v=a+b) : u=a ∧ v=b := by
  have hua : u=a := by
    by_contra h
    have hlt : toLex u < toLex a := lt_of_le_of_ne hu h
    have hsum : toLex (u+v) < toLex (a+b) :=
      (lex_add_lt_right hlt v).trans_le (by simpa only [add_comm] using lex_add_le_right hv a)
    rw [he] at hsum
    exact (lt_irrefl _ hsum)
  subst u
  exact ⟨rfl, add_left_cancel he⟩

theorem leading_mul {n : ℕ} {f g : SkewPolynomial n} {a b : Exp n} {c d : ℤ}
    (hf : Leading f a c) (hg : Leading g b d) :
    Leading (f*g) (a+b) (c*d*OddMath.skewSign a b) := by
  classical
  refine ⟨bounded_mul hf.1 hg.1, ?_⟩
  rw [mul_coeff]
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single b]
    · simp [hf.2, hg.2]
    · intro v hv hne
      apply if_neg
      intro he
      exact hne (add_left_cancel he)
    · intro hb
      simp [Finsupp.not_mem_support_iff.mp hb, ← hg.2]
  · intro u hu hne
    apply Finset.sum_eq_zero
    intro v hv
    apply if_neg
    intro he
    exact hne (add_eq_of_bounded (hf.1 u (Finsupp.mem_support_iff.mp hu))
      (hg.1 v (Finsupp.mem_support_iff.mp hv)) he).1
  · intro ha
    simp [Finsupp.not_mem_support_iff.mp ha, ← hf.2]

/-- Squares commute with every generator, using only distinct anticommutation. -/
theorem square_comm_generator {n : ℕ} (i j : Fin n) :
    generator i ^ 2 * generator j = generator j * generator i ^ 2 := by
  by_cases h : i=j
  · subst j; noncomm_ring
  · have hc : generator i * generator j = -(generator j * generator i) :=
      generator_anticommute i j h
    rw [pow_two, _root_.mul_assoc, hc, _root_.mul_neg, ← _root_.mul_assoc, hc]
    simp [_root_.mul_assoc]

/-- Centrality needed for the divided-difference intertwining identity. -/
theorem square_comm {n : ℕ} (i : Fin n) (f : SkewPolynomial n) :
    generator i ^ 2 * f = f * generator i ^ 2 := by
  obtain ⟨x, rfl⟩ := PbwRealization.Phi_surjective n f
  induction x using Quotient.inductionOn' with
  | h w =>
    change generator i ^ 2 * PbwL3.evalAlg n w = PbwL3.evalAlg n w * generator i ^ 2
    induction w using FreeAlgebra.induction with
    | grade0 r =>
      rw [AlgHom.commutes]
      exact (Int.cast_commute r _).symm.eq
    | grade1 j => rw [PbwL3.evalAlg_ι]; exact square_comm_generator i j
    | add a b ha hb => simp only [map_add, _root_.mul_add, _root_.add_mul, ha, hb]
    | mul a b ha hb => rw [map_mul, ← _root_.mul_assoc, ha, _root_.mul_assoc, hb,
        ← _root_.mul_assoc]

/-- Universal odd divided-difference intertwiner. Its zero-kernel specialization
is the premise used to constrain the leading exponent, not an invariance claim. -/
theorem divided_intertwiner {n : ℕ} (i : Fin (n+1)) (f : SkewPolynomial (n+2)) :
    (generator i.castSucc ^ 2 - generator i.succ ^ 2) * divided i f =
      (generator i.castSucc - generator i.succ) * f -
        s i f * (generator i.castSucc - generator i.succ) := by
  let X := generator i.castSucc
  let Y := generator i.succ
  have central (g : SkewPolynomial (n+2)) : (X^2-Y^2)*g = g*(X^2-Y^2) := by
    dsimp [X, Y]; rw [sub_mul, mul_sub, square_comm, square_comm]
  obtain ⟨x, rfl⟩ := PbwRealization.Phi_surjective (n+2) f
  induction x using Quotient.inductionOn' with
  | h w =>
    change (X^2-Y^2)*divided i (PbwL3.evalAlg (n+2) w) =
      (X-Y)*PbwL3.evalAlg (n+2) w - s i (PbwL3.evalAlg (n+2) w)*(X-Y)
    induction w using FreeAlgebra.induction with
    | grade0 r =>
      rw [AlgHom.commutes]
      change (X^2-Y^2)*divided i (r • (1 : SkewPolynomial (n+2))) =
        (X-Y)*(r • 1) - s i (r • 1)*(X-Y)
      simp only [map_smul, divided_one, smul_zero, mul_zero, map_zsmul, map_one,
        smul_mul_assoc, mul_smul_comm, one_mul, mul_one, sub_self]
    | grade1 j =>
      rw [PbwL3.evalAlg_ι, divided_generator, s_generator]
      by_cases hl : j=i.castSucc
      · subst j
        simp only [true_or, ↓reduceIte, Equiv.swap_apply_left, _root_.mul_one]
        dsimp [X,Y]; noncomm_ring
      · by_cases hr : j=i.succ
        · subst j
          simp only [or_true, ↓reduceIte, Equiv.swap_apply_right, _root_.mul_one]
          dsimp [X,Y]; noncomm_ring
        · simp only [hl, hr, false_or, ↓reduceIte, mul_zero,
            Equiv.swap_apply_of_ne_of_ne hl hr]
          have hx : X * generator j = -(generator j * X) :=
            generator_anticommute _ _ (Ne.symm hl)
          have hy : Y * generator j = -(generator j * Y) :=
            generator_anticommute _ _ (Ne.symm hr)
          noncomm_ring [hx,hy]
    | add a b ha hb =>
      simp only [map_add, _root_.mul_add, _root_.add_mul]
      rw [ha,hb]; noncomm_ring
    | mul a b ha hb =>
      rw [map_mul, divided_mul, map_mul, _root_.mul_add,
        ← _root_.mul_assoc, ha, ← _root_.mul_assoc, central, _root_.mul_assoc, hb]
      noncomm_ring

theorem kernel_intertwiner {n : ℕ} (f : SkewPolynomial (n+2))
    (hf : f ∈ kernelSubring n) (i : Fin (n+1)) :
    (generator i.castSucc - generator i.succ)*f =
      s i f*(generator i.castSucc - generator i.succ) := by
  have h := divided_intertwiner i f
  rw [hf i, mul_zero] at h
  exact sub_eq_zero.mp h.symm

/-- Crossing coefficients are integral units, including repeated indices. -/
theorem skewSign_square {n : ℕ} (a b : Exp n) :
    OddMath.skewSign a b * OddMath.skewSign a b = 1 := by
  unfold OddMath.skewSign
  rw [← mul_pow]
  norm_num

theorem s_word_monomial {n : ℕ} (i : Fin (n+1)) (w : List (Fin (n+2))) :
    ∃ c : ℤ, c*c=1 ∧ s i ((w.map generator).prod) =
      monomial (PbwRealization.exponents w ∘ Equiv.swap i.castSucc i.succ) c := by
  induction w with
  | nil => exact ⟨1, by norm_num, by simp [PbwRealization.exponents_nil]; rfl⟩
  | cons j w ih =>
    obtain ⟨c,hc,he⟩ := ih
    let σ := Equiv.swap i.castSucc i.succ
    let a := PbwRealization.exponents w ∘ σ
    let b := expSingle (σ j)
    have hb : expSingle j ∘ σ = b := by
      funext k
      simp only [Function.comp_apply, expSingle, b]
      congr 1
      apply propext
      constructor
      · intro h; simpa only [σ, Equiv.swap_apply_self] using congrArg σ h
      · intro h; simpa only [σ, Equiv.swap_apply_self] using congrArg σ h
    refine ⟨-c*OddMath.skewSign b a, ?_, ?_⟩
    · calc
        (-c*OddMath.skewSign b a)*(-c*OddMath.skewSign b a) =
            (c*c)*(OddMath.skewSign b a*OddMath.skewSign b a) := by ring
        _ = 1 := by rw [hc,skewSign_square]; norm_num
    · simp only [List.map_cons, List.prod_cons, map_mul, s_generator, he]
      rw [neg_mul]
      change -(OddMath.SkewPolynomial.mul (monomial b 1) (monomial a c)) = _
      rw [mul_monomial, ← Finsupp.single_neg]
      have hexp : PbwRealization.exponents (j::w) ∘ σ = b+a := by
        rw [PbwRealization.exponents_cons]
        exact congrArg (fun x => x+a) hb
      rw [hexp]
      congr 1
      ring

/-- The genuine signed adjacent action permutes each monomial's exponent and
multiplies its coefficient by an actual unit. No support-invariance assumption. -/
theorem s_monomial {n : ℕ} (i : Fin (n+1)) (a : Exp (n+2)) (d : ℤ) :
    ∃ c : ℤ, c*c=1 ∧ s i (monomial a d) =
      monomial (a ∘ Equiv.swap i.castSucc i.succ) (c*d) := by
  obtain ⟨w, _, hw, he⟩ := PbwRealization.exists_ordered_word a
  have hwpoly : (w.map generator).prod = monomial a 1 := by
    rw [← he]
    simp [PbwRealization.word, map_list_prod, List.map_map, Function.comp_def, PbwL3.Phi_q]
  obtain ⟨c,hc,h⟩ := s_word_monomial i w
  rw [hwpoly, hw] at h
  refine ⟨c,hc,?_⟩
  have hd : monomial a d = d • monomial a 1 := by simp [monomial, Finsupp.smul_single]
  rw [hd, map_zsmul, h]
  simp only [monomial, Finsupp.smul_single, smul_eq_mul, mul_comm d c]

/-- Nonzero coefficients survive at the literally swapped exponent. -/
theorem s_coeff_nonzero {n : ℕ} (i : Fin (n+1)) (f : SkewPolynomial (n+2))
    (a : Exp (n+2)) (ha : f a ≠ 0) :
    s i f (a ∘ Equiv.swap i.castSucc i.succ) ≠ 0 := by
  classical
  let σ := Equiv.swap i.castSucc i.succ
  have inj : Function.Injective (fun b : Exp (n+2) => b ∘ σ) := by
    intro b c h
    funext j
    simpa [σ] using congrFun h (σ j)
  obtain ⟨c,hc,he⟩ := s_monomial i a (f a)
  have hc0 : c ≠ 0 := by intro h; simp [h] at hc
  have hf : f = ∑ b ∈ f.support, monomial b (f b) := (Finsupp.sum_single f).symm
  conv_lhs => rw [hf]
  rw [map_sum]
  change (∑ b ∈ f.support, s i (monomial b (f b))) (a ∘ σ) ≠ 0
  rw [Finsupp.finset_sum_apply, Finset.sum_eq_single a]
  · rw [he, Finsupp.single_eq_same]
    exact mul_ne_zero hc0 ha
  · intro b hb hba
    obtain ⟨d,_,hd⟩ := s_monomial i b (f b)
    rw [hd]
    apply Finsupp.single_eq_of_ne
    exact fun h => hba (inj h)
  · intro h
    exact False.elim (h (Finsupp.mem_support_iff.mpr ha))

theorem exists_leading {n : ℕ} (f : SkewPolynomial n) (hf : f ≠ 0) :
    ∃ a : Exp n, f a ≠ 0 ∧ Leading f a (f a) := by
  classical
  have hs : f.support.Nonempty := Finsupp.support_nonempty_iff.mpr hf
  obtain ⟨a,ha,hmax⟩ := Finset.exists_max_image f.support (fun a => toLex a) hs
  exact ⟨a,Finsupp.mem_support_iff.mp ha,
    ⟨fun b hb => hmax b (Finsupp.mem_support_iff.mpr hb),rfl⟩⟩

theorem lex_add_le_cancel_right {n : ℕ} {a b c : Exp n}
    (h : toLex (a+c) ≤ toLex (b+c)) : toLex a ≤ toLex b := by
  by_contra hab
  exact (not_lt_of_ge h) (lex_add_lt_right (lt_of_not_ge hab) c)

theorem leading_difference {n : ℕ} (i j : Fin n) (h : i < j) :
    Leading (generator i - generator j) (expSingle i) 1 := by
  have hji : toLex (expSingle j) < toLex (expSingle i) := by
    refine ⟨i, fun k hk => ?_, ?_⟩
    · change expSingle j k = expSingle i k
      simp [expSingle, ne_of_gt hk, ne_of_gt (hk.trans h)]
    · change expSingle j i < expSingle i i
      simp [expSingle, h.ne.symm]
  have hne : expSingle j ≠ expSingle i := fun he => (ne_of_lt hji) (congrArg toLex he)
  refine ⟨?_,?_⟩
  · rw [sub_eq_add_neg]
    apply bounded_add (bounded_single _ _)
    have hn : -generator j = monomial (expSingle j) (-1) := (Finsupp.single_neg _ _).symm
    rw [hn]
    exact bounded_mono (bounded_single _ _) hji.le
  · change (Finsupp.single (expSingle i) (1:ℤ) -
      Finsupp.single (expSingle j) 1 : SkewPolynomial n) (expSingle i) = 1
    simp [Finsupp.single_apply, hne]

/-- The intertwiner bounds the genuine signed swap by the same leading exponent.
This does not assert that a kernel polynomial is fixed by the swap. -/
theorem kernel_swap_bounded {n : ℕ} (f : SkewPolynomial (n+2))
    (hf : f ∈ kernelSubring n) (a : Exp (n+2)) (hfa : Bounded f a)
    (i : Fin (n+1)) : Bounded (s i f) a := by
  classical
  by_cases hz : s i f = 0
  · rw [hz]; exact bounded_zero a
  obtain ⟨b,hb,hlead⟩ := exists_leading (s i f) hz
  have hd := leading_difference i.castSucc i.succ (by simp)
  have hleft := bounded_mul hd.1 hfa
  rw [kernel_intertwiner f hf i] at hleft
  have hright := leading_mul hlead hd
  have hsign : OddMath.skewSign b (expSingle i.castSucc) ≠ 0 := by
    intro h; have hh := skewSign_square b (expSingle i.castSucc); simp [h] at hh
  have hcoeff : (s i f * (generator i.castSucc-generator i.succ))
      (b+expSingle i.castSucc) ≠ 0 := by
    rw [hright.2]
    exact mul_ne_zero (mul_ne_zero hb one_ne_zero) hsign
  have hba : toLex b ≤ toLex a := lex_add_le_cancel_right
    (by simpa only [add_comm (expSingle i.castSucc) a] using hleft _ hcoeff)
  exact bounded_mono hlead.1 hba

/-- Every nonzero lexicographically highest monomial of an actual joint-kernel
polynomial has weakly decreasing exponents, integrally and in every rank. -/
theorem kernel_leading_antitone {n : ℕ} (f : SkewPolynomial (n+2))
    (hf : f ∈ kernelSubring n) (a : Exp (n+2)) (hfa : Bounded f a)
    (ha : f a ≠ 0) : Antitone a := by
  apply Fin.antitone_iff_succ_le.mpr
  intro i
  by_contra h
  have hlt : a i.castSucc < a i.succ := lt_of_not_ge h
  have hswap := kernel_swap_bounded f hf a hfa i _ (s_coeff_nonzero i f a ha)
  have hlex : toLex a < toLex (a ∘ Equiv.swap i.castSucc i.succ) := by
    refine ⟨i.castSucc, fun j hj => ?_, ?_⟩
    · change a j = a (Equiv.swap i.castSucc i.succ j)
      rw [Equiv.swap_apply_of_ne_of_ne hj.ne (by intro he; subst j; change i.val + 1 < i.val at hj; omega)]
    · simpa using hlt
  exact (not_lt_of_ge hswap) hlex

/-- Exponent of the first `k` distinct variables. -/
def prefixExp (n k : ℕ) : Exp n := fun j => if j.val < k then 1 else 0

theorem strictMono_val_ge {n k : ℕ} (f : Fin k → Fin n) (hf : StrictMono f)
    (j : Fin k) : j.val ≤ (f j).val := by
  cases k with
  | zero => exact Fin.elim0 j
  | succ k =>
    induction j using Fin.induction with
    | zero => exact Nat.zero_le _
    | succ j ih =>
      have h := hf (Fin.castSucc_lt_succ j)
      change (f j.castSucc).val < (f j.succ).val at h
      change j.val ≤ (f j.castSucc).val at ih
      change j.val + 1 ≤ _
      omega

theorem exponents_ofFn_injective {n k : ℕ} (f : Fin k → Fin n)
    (hf : Function.Injective f) (j : Fin n) :
    PbwRealization.exponents (List.ofFn f) j = if j ∈ Set.range f then 1 else 0 := by
  classical
  change (List.ofFn f).count j = _
  by_cases h : j ∈ Set.range f
  · rw [if_pos h]
    exact List.count_eq_one_of_mem (List.nodup_ofFn.mpr hf) (List.mem_ofFn.mpr h)
  · rw [if_neg h]
    exact List.count_eq_zero.mpr (fun hm => h (List.mem_ofFn.mp hm))

theorem exponents_initial {n k : ℕ} (hk : k ≤ n) :
    PbwRealization.exponents (List.ofFn (Fin.castLE hk)) = prefixExp n k := by
  funext j
  rw [exponents_ofFn_injective _ (Fin.castLE_injective hk)]
  unfold prefixExp
  congr 1
  apply propext
  constructor
  · rintro ⟨i,rfl⟩; exact i.isLt
  · intro h; exact ⟨⟨j.val,h⟩,Fin.ext rfl⟩

/-- A non-initial increasing k-subset has strictly smaller exponent vector.
This proves the conjugate-column convention rather than relying on source shorthand. -/
theorem strict_exponents_lt {n k : ℕ} (hk : k ≤ n) (f : Fin k → Fin n)
    (hf : StrictMono f) (hne : f ≠ Fin.castLE hk) :
    toLex (PbwRealization.exponents (List.ofFn f)) < toLex (prefixExp n k) := by
  classical
  have hex : ∃ j, f j ≠ Fin.castLE hk j := Function.ne_iff.mp hne
  obtain ⟨j,hj,hmin⟩ := (Set.toFinite {j | f j ≠ Fin.castLE hk j}).exists_minimal_wrt
    id {j | f j ≠ Fin.castLE hk j} (by simpa using hex)
  have before : ∀ r, r < j → f r = Fin.castLE hk r := by
    intro r hr
    by_contra h
    exact (ne_of_lt hr) (hmin r h hr.le).symm
  have hjlt : j.val < (f j).val := by
    have hle := strictMono_val_ge f hf j
    have hne' : j.val ≠ (f j).val := by
      intro h; apply hj; exact Fin.ext h.symm
    omega
  refine ⟨Fin.castLE hk j, ?_, ?_⟩
  · intro t ht
    change PbwRealization.exponents (List.ofFn f) t = prefixExp n k t
    have htj : t.val < j.val := ht
    let r : Fin k := ⟨t.val, lt_trans htj j.isLt⟩
    have hrj : r < j := htj
    have hfr : f r = t := (before r hrj).trans (Fin.ext rfl)
    rw [exponents_ofFn_injective _ hf.injective, if_pos ⟨r,hfr⟩]
    simp [prefixExp, lt_trans htj j.isLt]
  · change PbwRealization.exponents (List.ofFn f) (Fin.castLE hk j) <
      prefixExp n k (Fin.castLE hk j)
    have hnot : Fin.castLE hk j ∉ Set.range f := by
      rintro ⟨r,hr⟩
      by_cases h : r < j
      · have hfr := before r h
        have hv := congrArg Fin.val (hfr.symm.trans hr)
        change r.val = j.val at hv
        exact (ne_of_lt h) (Fin.ext hv)
      · have hh := hf.monotone (le_of_not_gt h)
        rw [hr] at hh
        change (f j).val ≤ j.val at hh
        omega
    rw [exponents_ofFn_injective _ hf.injective, if_neg hnot]
    simp [prefixExp]

/-- Any actual tilde word is a unit-coefficient monomial at its multiplicities. -/
theorem tildeWord_monomial {n : ℕ} (w : List (Fin n)) :
    ∃ c : ℤ, c*c=1 ∧ (w.map PlacticEvaluation.tildeGenerator).prod =
      monomial (PbwRealization.exponents w) c := by
  induction w with
  | nil => exact ⟨1,by norm_num,by simp [PbwRealization.exponents_nil]; rfl⟩
  | cons j w ih =>
    obtain ⟨c,hc,he⟩ := ih
    let t : ℤ := (-1)^j.val
    let z := OddMath.skewSign (expSingle j) (PbwRealization.exponents w)
    have ht : t*t=1 := by dsimp [t]; rw [← mul_pow]; norm_num
    have hz : z*z=1 := skewSign_square _ _
    refine ⟨t*c*z,?_,?_⟩
    · calc
        (t*c*z)*(t*c*z) = (t*t)*(c*c)*(z*z) := by ring
        _ = 1 := by rw [ht,hc,hz]; norm_num
    · simp only [List.map_cons, List.prod_cons, he, PlacticEvaluation.tildeGenerator,
        smul_mul_assoc, PbwRealization.exponents_cons]
      change t • OddMath.SkewPolynomial.mul (monomial (expSingle j) 1)
        (monomial (PbwRealization.exponents w) c) = _
      rw [mul_monomial, Finsupp.smul_single]
      congr 1
      change t*(1*c*z) = t*c*z
      ring

/-- Each literal e_k has highest exponent (1,...,1,0,...,0) and unit
coefficient, with the actual sign computed by its initial tilde word. -/
theorem elementary_leading (n k : ℕ) (hk : k ≤ n) :
    ∃ c : ℤ, c*c=1 ∧ Leading (elementaryPoly n k) (prefixExp n k) c := by
  classical
  let f₀ := Fin.castLE hk
  have hf₀ : StrictMono f₀ := fun _ _ h => h
  obtain ⟨c,hc,he⟩ := tildeWord_monomial (List.ofFn f₀)
  rw [exponents_initial hk] at he
  have he' : (List.ofFn (fun i => PlacticEvaluation.tildeGenerator (f₀ i))).prod =
      monomial (prefixExp n k) c := by simpa only [List.map_ofFn] using he
  refine ⟨c,hc,?_,?_⟩
  · unfold elementaryPoly
    apply bounded_sum
    intro f _
    by_cases hf : StrictMono f
    · rw [if_pos hf]
      by_cases hh : f=f₀
      · subst f; rw [he']; exact bounded_single _ _
      · obtain ⟨d,_,hd⟩ := tildeWord_monomial (List.ofFn f)
        simp only [List.map_ofFn, Function.comp_def] at hd
        rw [hd]
        exact bounded_mono (bounded_single _ _) (strict_exponents_lt hk f hf hh).le
    · rw [if_neg hf]; exact bounded_zero _
  · unfold elementaryPoly
    rw [Finsupp.finset_sum_apply, Finset.sum_eq_single f₀]
    · rw [if_pos hf₀,he',Finsupp.single_eq_same]
    · intro f _ hne
      by_cases hf : StrictMono f
      · rw [if_pos hf]
        obtain ⟨d,_,hd⟩ := tildeWord_monomial (List.ofFn f)
        simp only [List.map_ofFn, Function.comp_def] at hd
        rw [hd]
        apply Finsupp.single_eq_of_ne
        exact fun h => (ne_of_lt (strict_exponents_lt hk f hf hne)) (congrArg toLex h)
      · simp [hf]
    · simp

def columnExponent (n : ℕ) (w : List ℕ) : Exp n :=
  (w.map (prefixExp n)).sum

def elementaryWord (n : ℕ) (w : List ℕ) : SkewPolynomial n :=
  (w.map (elementaryPoly n)).prod

/-- Removing one box from each nonempty row gives one genuine column of the
conjugate partition. The column height is the number of positive row lengths. -/
theorem positive_prefix {n : ℕ} (a : Exp n) (ha : Antitone a) :
    ∃ k, k ≤ n ∧ ∀ j : Fin n, (j.val < k ↔ 0 < a j) := by
  classical
  let S := Finset.univ.filter (fun j => 0 < a j)
  refine ⟨S.card, (Finset.card_le_card (Finset.subset_univ S)).trans_eq (Fintype.card_fin n), ?_⟩
  intro j
  constructor
  · intro h
    by_contra hpos
    have hsub : S ⊆ Finset.Iio j := by
      intro t ht
      have htpos := (Finset.mem_filter.mp ht).2
      apply Finset.mem_Iio.mpr
      by_contra htj
      have hh := ha (le_of_not_gt htj)
      omega
    have hc := Finset.card_le_card hsub
    simp only [Fin.card_Iio] at hc
    omega
  · intro h
    have hsub : Finset.Iic j ⊆ S := by
      intro t ht
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, lt_of_lt_of_le h (ha (Finset.mem_Iic.mp ht))⟩
    have hc := Finset.card_le_card hsub
    simp only [Fin.card_Iic] at hc
    omega

/-- Construct, for every partition exponent vector, a finite product of literal
odd elementary polynomials with that leading exponent and coefficient ±1.
`columnExponent = a` explicitly records conjugation of row/column conventions. -/
theorem elementaryWord_leading (n : ℕ) (a : Exp n) (ha : Antitone a) :
    ∃ w : List ℕ, (∀ k ∈ w, 1 ≤ k ∧ k ≤ n) ∧ columnExponent n w = a ∧
      ∃ c : ℤ, c*c=1 ∧ Leading (elementaryWord n w) a c := by
  classical
  generalize hd : (∑ j, a j) = d
  induction d using Nat.strong_induction_on generalizing a with
  | h d ih =>
    by_cases hz : a=0
    · subst a
      refine ⟨[],by simp,by simp [columnExponent],1,by norm_num,?_⟩
      change Leading (monomial 0 1) 0 1
      exact ⟨bounded_single _ _, Finsupp.single_eq_same⟩
    obtain ⟨k,hkn,hk⟩ := positive_prefix a ha
    have hapos : ∃ j, 0 < a j := by
      by_contra h
      apply hz
      funext j
      have hj : ¬ 0 < a j := fun hj => h ⟨j,hj⟩
      exact Nat.eq_zero_of_not_pos hj
    have hkpos : 1 ≤ k := by
      obtain ⟨j,hj⟩ := hapos
      have hh := (hk j).mpr hj
      omega
    let b : Exp n := fun j => a j - 1
    have hba : Antitone b := fun _ _ h => Nat.sub_le_sub_right (ha h) 1
    have hsum : (∑ j, b j) < d := by
      rw [← hd]
      apply Finset.sum_lt_sum
      · intro j _; exact Nat.sub_le _ _
      · obtain ⟨j,hj⟩ := hapos
        exact ⟨j,Finset.mem_univ _,Nat.sub_lt hj (by decide)⟩
    have hexp : prefixExp n k + b = a := by
      funext j
      simp only [Pi.add_apply,prefixExp,b]
      by_cases hj : 0 < a j
      · rw [if_pos ((hk j).mpr hj)]; omega
      · rw [if_neg (fun hh => hj ((hk j).mp hh))]; omega
    obtain ⟨w,hw,hew,c,hc,hl⟩ := ih _ hsum b hba rfl
    obtain ⟨e,he,hle⟩ := elementary_leading n k hkn
    refine ⟨k::w,?_,?_, e*c*OddMath.skewSign (prefixExp n k) b,?_,?_⟩
    · intro t ht
      rcases List.mem_cons.mp ht with rfl|ht
      · exact ⟨hkpos,hkn⟩
      · exact hw t ht
    · simp only [columnExponent,List.map_cons,List.sum_cons]
      change prefixExp n k + columnExponent n w = a
      rw [hew,hexp]
    · calc
        (e*c*OddMath.skewSign (prefixExp n k) b)*(e*c*OddMath.skewSign (prefixExp n k) b) =
          (e*e)*(c*c)*(OddMath.skewSign (prefixExp n k) b*OddMath.skewSign (prefixExp n k) b) := by ring
        _ = 1 := by rw [he,hc,skewSign_square]; norm_num
    · have hh := leading_mul hle hl
      rw [hexp] at hh
      exact hh

theorem elementaryWord_mem (n : ℕ) (w : List ℕ)
    (hw : ∀ k ∈ w, 1 ≤ k ∧ k ≤ n+2) :
    elementaryWord (n+2) w ∈ elementaryClosure n := by
  induction w with
  | nil => exact (elementaryClosure n).one_mem
  | cons k w ih =>
    apply (elementaryClosure n).mul_mem
    · apply Subring.subset_closure
      exact ⟨k,(hw k (by simp)).1,(hw k (by simp)).2,rfl⟩
    · exact ih (fun t ht => hw t (by simp [ht]))

/-- Integral elimination strictly lowers the highest lexicographic exponent.
The correcting scalar is an integer because the elementary leading coefficient
is a unit; no field, dimension argument, mod-2 lift or saturation assumption. -/
theorem kernel_mem_elementaryClosure (n : ℕ) (f : SkewPolynomial (n+2))
    (hf : f ∈ kernelSubring n) : f ∈ elementaryClosure n := by
  classical
  have elimination : ∀ A : Lex (Exp (n+2)), ∀ g : SkewPolynomial (n+2),
      g ∈ kernelSubring n → Bounded g (ofLex A) → g ∈ elementaryClosure n := by
    intro A
    induction A using WellFoundedLT.induction with
    | ind A ih =>
      intro g hg hga
      by_cases hzero : g=0
      · rw [hzero]; exact (elementaryClosure n).zero_mem
      obtain ⟨a,ha,hl⟩ := exists_leading g hzero
      have hale : toLex a ≤ A := hga a ha
      by_cases hlt : toLex a < A
      · exact ih (toLex a) hlt g hg hl.1
      have haeq : toLex a = A := le_antisymm hale (le_of_not_gt hlt)
      obtain ⟨w,hw,_,c,hc,hp⟩ := elementaryWord_leading (n+2) a
        (kernel_leading_antitone g hg a hl.1 ha)
      let p := elementaryWord (n+2) w
      have hpmem : p ∈ elementaryClosure n := elementaryWord_mem n w hw
      let z : ℤ := g a*c
      let r := g - z • p
      have hzmem : z • p ∈ elementaryClosure n := (elementaryClosure n).zsmul_mem hpmem z
      have hrkernel : r ∈ kernelSubring n :=
        (kernelSubring n).sub_mem hg (elementaryClosure_le_kernel n hzmem)
      have hra : r a = 0 := by
        change g a - (z • p) a = 0
        rw [Finsupp.smul_apply]
        change g a - z*p a = 0
        rw [hp.2]
        dsimp [z]
        rw [mul_assoc,hc,mul_one,sub_self]
      have hrbounded : Bounded r a := bounded_add hl.1 (bounded_neg (bounded_smul z hp.1))
      have hrmem : r ∈ elementaryClosure n := by
        by_cases hrzero : r=0
        · rw [hrzero]; exact (elementaryClosure n).zero_mem
        obtain ⟨b,hb,hbl⟩ := exists_leading r hrzero
        have hba := hrbounded b hb
        have hne : b ≠ a := by intro h; subst b; exact hb hra
        have hlt : toLex b < A := by
          rw [← haeq]
          exact lt_of_le_of_ne hba hne
        exact ih (toLex b) hlt r hrkernel hbl.1
      have hfinish := (elementaryClosure n).add_mem hrmem hzmem
      simpa only [r,sub_add_cancel] using hfinish
  by_cases hz : f=0
  · rw [hz]; exact (elementaryClosure n).zero_mem
  obtain ⟨a,_,hl⟩ := exists_leading f hz
  exact elimination (toLex a) f hf hl.1

/-- EKL Prop. 2.2: the actual common kernel is exactly the subring generated by
its literal odd elementary polynomials, for every nontrivial divided-difference rank. -/
theorem kernel_eq_elementaryClosure (n : ℕ) :
    kernelSubring n = elementaryClosure n := by
  apply le_antisymm
  · exact fun f hf => kernel_mem_elementaryClosure n f hf
  · exact elementaryClosure_le_kernel n

end
end OddMath.Frontier.ElementaryGeneration
