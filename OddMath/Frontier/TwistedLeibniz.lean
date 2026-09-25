import OddMath.DividedDifferences
import OddMath.PbwL3
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-! Universal twisted Leibniz on the actual rank-two integer skew polynomials.
Source: EKL arXiv:1111.1320v1, §2.1, (2.2)–(2.6), pp.3–4.
The imported ring multiplication is definitionally SkewPolynomial.mul.
-/
namespace OddMath.Frontier.TwistedLeibniz
open OddMath.SkewPolynomial OddMath.DividedDifferences
open scoped BigOperators

abbrev P := SkewPolynomial 2
noncomputable abbrev x : P := generator 0
noncomputable abbrev y : P := generator 1
noncomputable abbrev M (a b : ℕ) : P := monomial ![a,b] 1

lemma sign_two (a b : Fin 2 → ℕ) : OddMath.skewSign a b = (-1 : ℤ) ^ (a 1 * b 0) := by
  simp [OddMath.skewSign, OddMath.crossingCount, Fin.sum_univ_two,
    Finset.sum_filter, Fin.forall_fin_two]

lemma vec_add (a b c d : ℕ) : (![a,b] + ![c,d] : Fin 2 → ℕ) = ![a+c,b+d] := by
  ext i
  fin_cases i <;> rfl

lemma mono_smul (a b : ℕ) (r : ℤ) : monomial ![a,b] r = r • M a b := by
  simp [M, monomial, Finsupp.smul_single]

lemma mono_mul (a b c d : ℕ) (r s : ℤ) :
    (monomial ![a,b] r : P) * monomial ![c,d] s =
      monomial ![a+c,b+d] (r*s*(-1 : ℤ)^(b*c)) := by
  change mul _ _ = _
  rw [mul_monomial, sign_two, vec_add]
  rfl

lemma x_mono (a b : ℕ) (r : ℤ) : x * monomial ![a,b] r = monomial ![a+1,b] r := by
  rw [show x = monomial ![1,0] 1 from generator_zero_monomial, mono_mul]
  simp [Nat.add_comm]

lemma y_mono (a b : ℕ) (r : ℤ) : y * monomial ![a,b] r =
    monomial ![a,b+1] (r * (-1 : ℤ)^a) := by
  rw [show y = monomial ![0,1] 1 from generator_one_monomial, mono_mul]
  simp [Nat.add_comm]

lemma mono_y (a b : ℕ) (r : ℤ) : (monomial ![a,b] r : P) * y = monomial ![a,b+1] r := by
  rw [show y = monomial ![0,1] 1 from generator_one_monomial, mono_mul]
  simp

lemma M_zero : M 0 0 = (1 : P) := by
  change monomial ![0,0] 1 = monomial 0 1
  congr 1
  ext i
  fin_cases i <;> rfl

lemma xy : y*x = -(x*y) := by
  change mul (generator (1 : Fin 2)) (generator 0) = -mul (generator 0) (generator 1)
  exact generator_anticommute 1 0 (by decide)

noncomputable def D : P →+ P := { toFun := div1, map_zero' := div1_zero, map_add' := div1_add }
noncomputable def S : P →+ P := { toFun := symm1, map_zero' := symm1_zero, map_add' := symm1_add }

lemma D_mono (a b : ℕ) (r : ℤ) : D (monomial ![a,b] r) = r • divMonomial a b := by
  exact div1_monomial ![a,b] r

lemma powDiv2_succ (m : ℕ) : powDiv2 (m+1) = M 0 m - x * powDiv2 m := by
  unfold powDiv2
  rw [Finset.sum_range_succ']
  simp only [Nat.add_sub_cancel, Nat.sub_zero, pow_zero]
  rw [Finset.mul_sum, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [x_mono, ← monomial_neg]
  congr 1
  · have h : m - (i + 1) = m - 1 - i := by omega
    rw [h]
  · simp [pow_succ]

lemma powDiv1_succ (m : ℕ) : powDiv1 (m+1) = M m 0 - y * powDiv1 m := by
  unfold powDiv1
  rw [Finset.sum_range_succ']
  simp only [Nat.add_sub_cancel, Nat.sub_zero, Nat.zero_mul, pow_zero]
  rw [Finset.mul_sum, sub_eq_add_neg, ← Finset.sum_neg_distrib, add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have him : i < m := Finset.mem_range.mp hi
  rw [y_mono, ← monomial_neg]
  have he : m - (i+1) = m-1-i := by omega
  have hp : (i+1)*(m+1-(i+1)) = i*(m-i)+(m-1-i)+1 := by
    have hmi : m-i = (m-1-i)+1 := by omega
    rw [show m+1-(i+1) = m-i by omega, hmi]
    ring
  rw [he, hp, pow_add, pow_add]
  simp

lemma M_mul (a b c d : ℕ) : M a b * M c d = (-1 : ℤ)^(b*c) • M (a+c) (b+d) := by
  rw [mono_mul, _root_.one_mul, _root_.one_mul, mono_smul]

lemma divM_eq (a b : ℕ) : divMonomial a b =
    powDiv1 a * M 0 b + (monomial ![0,a] ((-1 : ℤ)^a) : P) * powDiv2 b := rfl

lemma divMonomial_succ_left (a b : ℕ) : divMonomial (a+1) b = M a b - y * divMonomial a b := by
  rw [divM_eq, divM_eq, powDiv1_succ]
  have hM : M a 0 * M 0 b = M a b := by simp [M_mul]
  have hY : (monomial ![0,a+1] ((-1 : ℤ)^(a+1)) : P) =
      -(y * monomial ![0,a] ((-1 : ℤ)^a)) := by
    rw [y_mono, ← monomial_neg]
    simp [pow_succ]
  rw [hY]
  simp only [_root_.sub_mul, _root_.mul_add, _root_.neg_mul, _root_.mul_assoc, hM]
  abel

lemma div1_x_mul (f : P) : D (x*f) = f - y * D f := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
      simp only [_root_.mul_add, map_add, hf, hg]
      abel
  | single e r =>
      have he : e = ![e 0, e 1] := by ext i; fin_cases i <;> rfl
      rw [he]
      change D (x * monomial _ r) = monomial _ r - y * D (monomial _ r)
      rw [x_mono, D_mono, D_mono, divMonomial_succ_left, smul_sub, mul_smul_comm, ← mono_smul]

lemma div1_y_M (a b : ℕ) : D (y * M a b) = M a b - x * D (M a b) := by
  induction a with
  | zero =>
      rw [y_mono, D_mono, D_mono]
      simp only [pow_zero, _root_.mul_one, one_smul, divMonomial_zero_left, powDiv2_succ]
  | succ a ih =>
      have hM : M (a+1) b = x * M a b := (x_mono a b 1).symm
      have hswap : y * (x * M a b) = -(x * (y * M a b)) := by
        rw [← _root_.mul_assoc, xy, _root_.neg_mul, _root_.mul_assoc]
      rw [hM, hswap, map_neg, div1_x_mul, ih, div1_x_mul]
      simp only [_root_.mul_sub, neg_sub, ← _root_.mul_assoc, xy, _root_.neg_mul]
      abel

lemma div1_y_mul (f : P) : D (y*f) = f - x * D f := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
      simp only [_root_.mul_add, map_add, hf, hg]
      abel
  | single e r =>
      have he : e = ![e 0, e 1] := by ext i; fin_cases i <;> rfl
      rw [he]
      change D (y * monomial _ r) = monomial _ r - x * D (monomial _ r)
      rw [mono_smul, mul_smul_comm, map_zsmul, div1_y_M, smul_sub, map_zsmul, mul_smul_comm]

lemma S_mono (a b : ℕ) (r : ℤ) : S (monomial ![a,b] r) =
    monomial ![b,a] (r * (-1 : ℤ)^(a+b+a*b)) := by
  change symm1 _ = _
  rw [symm1_monomial]
  congr 1
  ext i
  fin_cases i <;> rfl

lemma S_x_M (a b : ℕ) : S (x * M a b) = -(y * S (M a b)) := by
  rw [x_mono, S_mono, S_mono, y_mono, ← monomial_neg]
  congr 1
  have he : a+1+b+(a+1)*b = (a+b+a*b)+b+1 := by ring
  rw [he, pow_add, pow_add]
  simp

lemma S_y_M_zero (b : ℕ) : S (y * M 0 b) = -(x * S (M 0 b)) := by
  rw [y_mono, S_mono, S_mono, x_mono, ← monomial_neg]
  simp [pow_succ]

lemma leibniz_M_zero (b : ℕ) (g : P) :
    D (M 0 b * g) = D (M 0 b) * g + S (M 0 b) * D g := by
  induction b with
  | zero =>
      rw [M_zero]
      change div1 ((1 : P)*g) = div1 1 * g + symm1 1 * div1 g
      change div1 ((1 : P)*g) = div1 one * g + symm1 one * div1 g
      rw [div1_one, symm1_one]
      change div1 ((1 : P)*g) = 0 * g + (1 : P) * div1 g
      simp
  | succ b ih =>
      have hM : M 0 (b+1) = y * M 0 b := by simp [y_mono]
      rw [hM, _root_.mul_assoc, div1_y_mul, ih, div1_y_mul, S_y_M_zero]
      simp only [_root_.mul_add, _root_.sub_mul, _root_.neg_mul, _root_.mul_assoc]
      abel

lemma leibniz_M (a b : ℕ) (g : P) :
    D (M a b * g) = D (M a b) * g + S (M a b) * D g := by
  induction a with
  | zero => exact leibniz_M_zero b g
  | succ a ih =>
      have hM : M (a+1) b = x * M a b := (x_mono a b 1).symm
      rw [hM, _root_.mul_assoc, div1_x_mul, ih, div1_x_mul, S_x_M]
      simp only [_root_.mul_add, _root_.sub_mul, _root_.neg_mul, _root_.mul_assoc]
      abel

/-- EKL (2.4), on the actual closed-sum operator, with arbitrary inputs. -/
theorem div1_mul (f g : SkewPolynomial 2) :
    div1 (mul f g) = mul (div1 f) g + mul (symm1 f) (div1 g) := by
  change D (f*g) = D f * g + S f * D g
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f h hf hh =>
      simp only [_root_.add_mul, map_add, hf, hh]
      abel
  | single e r =>
      have he : e = ![e 0, e 1] := by ext i; fin_cases i <;> rfl
      rw [he]
      change D (monomial _ r * g) = D (monomial _ r) * g + S (monomial _ r) * D g
      rw [mono_smul, smul_mul_assoc, map_zsmul, leibniz_M, smul_add,
        map_zsmul, map_zsmul, smul_mul_assoc, smul_mul_assoc]

end OddMath.Frontier.TwistedLeibniz
