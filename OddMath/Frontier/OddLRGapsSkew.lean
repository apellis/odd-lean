import OddMath.Frontier.DividedSquareZero
import Mathlib.Data.Fin.Tuple.NatAntidiagonal
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.Algebra.DirectSum.Module

/-!
# Skew polynomials: three remarks of E §2.1

Ellis, "The odd Littlewood–Richardson rule", arXiv:1111.3932v1 ("E"), §2.1, pp. 3–4, on
`OPol_n = SkewPolynomial n` (increasing-index normal form, `x_i x_j = -x_j x_i` for `i ≠ j`),
with its ring structure `PbwL3.instRing` and the odd divided differences
`AllRankDivided.divided` and signed transpositions `AllRankDivided.s`.

* p. 3: "Although the generators `x_1, …, x_n` pairwise supercommute, the algebra `OPol_n` is not
  supercommutative: `(x_1 + x_2)x_1 = x_1(x_1 − x_2)`" (`skew_identity`, `skew_identity_12`,
  `not_superCommutative`). The `ℤ/2`-degree of a homogeneous polynomial of degree `d` is `d mod 2`
  (E: `deg(x_i) = (2, 1)`).
* p. 3: "The algebra `OPol_n` is finite dimensional in each degree": `degreePart n d`, the span of
  the monomials `x^a` with `Σ a_i = d`, is a free `ℤ`-module of finite rank `#{a : Σ a_i = d}`
  (`degreePart_free`, `degreePart_finite`, `finrank_degreePart`), the degree parts are closed under
  multiplication (`degreePart_mul`), and `OPol_n = ⊕_d degreePart n d` (`degreePart_isInternal`).
* p. 4: "On `OPol_n`, the kernel and image of `∂_i` coincide; by contrast with the even case,
  however, these do not equal the space of invariants or anti-invariants of the action of
  `s_i`" (`DividedSquareZero.ker_eq_range`; `ker_ne_invariants`, `ker_ne_antiInvariants`,
  `range_ne_invariants`, `range_ne_antiInvariants`). Witnesses: `x_i x_{i+1}` lies in `ker ∂_i`
  but `s_i(x_i x_{i+1}) = -x_i x_{i+1}`; `x_i + x_{i+1}` is `s_i`-anti-invariant with
  `∂_i(x_i + x_{i+1}) = 2`.
-/

namespace OddMath.Frontier.OddLRGaps

open OddMath.SkewPolynomial (SkewPolynomial generator monomial expSingle)
open PbwL3 AllRankDivided

noncomputable section

/-! ## Degree parts -/

/-- The degree-`d` part of `OPol_n`: the span of the monomials `x^a` with `Σ_i a_i = d`
(E §2.1, p. 3; the `ℤ × ℤ/2`-degree of `x^a` is `(2d, d mod 2)`). -/
def degreePart (n d : ℕ) : Submodule ℤ (SkewPolynomial n) :=
  Finsupp.supported ℤ ℤ {a : Fin n → ℕ | ∑ i, a i = d}

theorem degreeSet_eq (n d : ℕ) :
    {a : Fin n → ℕ | ∑ i, a i = d} = ↑(Finset.Nat.antidiagonalTuple n d) := by
  ext a
  simp [Finset.Nat.mem_antidiagonalTuple]

instance degreeSet_finite (n d : ℕ) : Finite {a : Fin n → ℕ | ∑ i, a i = d} := by
  rw [degreeSet_eq]
  exact Finite.of_fintype _

/-- The monomial basis of the degree-`d` part. -/
noncomputable def degreeBasis (n d : ℕ) :
    Basis {a : Fin n → ℕ | ∑ i, a i = d} ℤ (degreePart n d) :=
  (Finsupp.basisSingleOne).map (Finsupp.supportedEquivFinsupp _).symm

/-- E §2.1, p. 3: each degree part of `OPol_n` is a free `ℤ`-module … -/
instance degreePart_free (n d : ℕ) : Module.Free ℤ (degreePart n d) :=
  Module.Free.of_basis (degreeBasis n d)

/-- … of finite rank. -/
instance degreePart_finite (n d : ℕ) : Module.Finite ℤ (degreePart n d) :=
  Module.Finite.of_basis (degreeBasis n d)

/-- The rank of the degree-`d` part is the number of exponent vectors of total degree `d`. -/
theorem finrank_degreePart (n d : ℕ) :
    Module.finrank ℤ (degreePart n d) = (Finset.Nat.antidiagonalTuple n d).card := by
  rw [Module.finrank_eq_nat_card_basis (degreeBasis n d), degreeSet_eq, Nat.card_eq_fintype_card]
  simp

theorem monomial_mem_degreePart {n : ℕ} (a : Fin n → ℕ) (c : ℤ) :
    monomial a c ∈ degreePart n (∑ i, a i) :=
  Finsupp.single_mem_supported ℤ c (show a ∈ {a : Fin n → ℕ | ∑ i, a i = ∑ i, a i} from rfl)

theorem generator_mem_degreePart {n : ℕ} (i : Fin n) : generator i ∈ degreePart n 1 := by
  have h := monomial_mem_degreePart (expSingle i) 1
  rwa [OddMath.SkewPolynomial.sum_expSingle, if_pos (Finset.mem_univ _)] at h

/-- The degree parts multiply as a grading. -/
theorem degreePart_mul {n d e : ℕ} {f g : SkewPolynomial n} (hf : f ∈ degreePart n d)
    (hg : g ∈ degreePart n e) : f * g ∈ degreePart n (d + e) := by
  change OddMath.SkewPolynomial.mul f g ∈ _
  unfold OddMath.SkewPolynomial.mul
  refine Submodule.finsuppSum_mem _ _ _ _ fun a ha => ?_
  refine Submodule.finsuppSum_mem _ _ _ _ fun b hb => ?_
  have ha' : ∑ i, a i = d := (Finsupp.mem_supported ℤ f).mp hf (Finsupp.mem_support_iff.mpr ha)
  have hb' : ∑ i, b i = e := (Finsupp.mem_supported ℤ g).mp hg (Finsupp.mem_support_iff.mpr hb)
  have h := monomial_mem_degreePart (a + b) (f a * g b * OddMath.skewSign a b)
  rwa [show ∑ i, (a + b) i = d + e by simp [Finset.sum_add_distrib, ha', hb']] at h

theorem iSup_degreePart (n : ℕ) : ⨆ d, degreePart n d = ⊤ := by
  unfold degreePart
  rw [← Finsupp.supported_iUnion, eq_top_iff]
  intro f _
  rw [Finsupp.mem_supported]
  intro a _
  exact Set.mem_iUnion.mpr ⟨∑ i, a i, rfl⟩

theorem degreePart_iSupIndep (n : ℕ) : iSupIndep (degreePart n) := by
  intro d
  unfold degreePart
  refine Disjoint.mono_right (c := Finsupp.supported ℤ ℤ {a : Fin n → ℕ | ∑ i, a i ≠ d})
    (iSup₂_le fun e he => Finsupp.supported_mono fun a (ha : ∑ i, a i = e) => ?_) ?_
  · show ∑ i, a i ≠ d
    rw [ha]; exact he
  · apply Finsupp.disjoint_supported_supported
    rw [Set.disjoint_left]
    intro a ha hb
    exact hb ha

/-- `OPol_n` is the internal direct sum of its degree parts. -/
theorem degreePart_isInternal (n : ℕ) : DirectSum.IsInternal (degreePart n) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top (degreePart_iSupIndep n)
    (iSup_degreePart n)

/-! ## `OPol_n` is not supercommutative -/

/-- E §2.1, p. 3: `(x_i + x_j) x_i = x_i (x_i - x_j)` for `i ≠ j`. -/
theorem skew_identity {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    (generator i + generator j) * generator i = generator i * (generator i - generator j) := by
  have h : generator j * generator i = -(generator i * generator j) :=
    OddMath.SkewPolynomial.generator_anticommute j i hij.symm
  rw [add_mul, mul_sub, h, sub_eq_add_neg]

/-- E §2.1, p. 3, literally: `(x_1 + x_2) x_1 = x_1 (x_1 - x_2)` in `OPol_n`, `n ≥ 2`. -/
theorem skew_identity_12 (n : ℕ) :
    (generator (0 : Fin (n+2)) + generator 1) * generator 0 =
      generator 0 * (generator 0 - generator 1) :=
  skew_identity _ _ (by simp)

/-- Supercommutativity for the grading of E §2.1 (`deg x_i = (2, 1)`, so a homogeneous polynomial
of degree `d` has parity `d mod 2`): `ab = (-1)^{de} ba` for `a, b` homogeneous of degrees
`d, e`. -/
def SuperCommutative (n : ℕ) : Prop :=
  ∀ d e : ℕ, ∀ a ∈ degreePart n d, ∀ b ∈ degreePart n e, a * b = (-1 : ℤ) ^ (d * e) • (b * a)

/-- Distinct generators do supercommute. -/
theorem generators_supercommute {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    generator i * generator j = (-1 : ℤ) ^ (1 * 1) • (generator j * generator i) := by
  have h : generator i * generator j = -(generator j * generator i) :=
    OddMath.SkewPolynomial.generator_anticommute i j hij
  rw [h]
  simp

theorem generator_sq_ne_zero {n : ℕ} (i : Fin n) : generator i * generator i ≠ 0 :=
  OddMath.SkewPolynomial.generator_square_ne_zero i

/-- The odd elements `x_i + x_j` and `x_i` do not supercommute. -/
theorem odd_pair_not_supercommute {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    (generator i + generator j) * generator i ≠
      -(generator i * (generator i + generator j)) := by
  intro h
  have h' : (2 : ℤ) • (generator i * generator i) = 0 := by
    have hji : generator j * generator i = -(generator i * generator j) :=
      OddMath.SkewPolynomial.generator_anticommute j i hij.symm
    rw [add_mul, mul_add, hji] at h
    rw [two_smul]
    calc generator i * generator i + generator i * generator i
        = (generator i * generator i + -(generator i * generator j)) +
            (generator i * generator i + generator i * generator j) := by abel
      _ = 0 := by rw [h]; abel
  rcases smul_eq_zero.mp h' with h2 | h2
  · norm_num at h2
  · exact generator_sq_ne_zero i h2

/-- E §2.1, p. 3: for `n ≥ 2`, `OPol_n` is not supercommutative. -/
theorem not_superCommutative (n : ℕ) : ¬ SuperCommutative (n+2) := by
  intro h
  have ha : generator (0 : Fin (n+2)) + generator 1 ∈ degreePart (n+2) 1 :=
    Submodule.add_mem _ (generator_mem_degreePart _) (generator_mem_degreePart _)
  have := h 1 1 _ ha _ (generator_mem_degreePart 0)
  rw [show (-1 : ℤ) ^ (1 * 1) = -1 by norm_num, neg_one_smul] at this
  exact odd_pair_not_supercommute (0 : Fin (n+2)) 1 (by simp) this

/-! ## Kernel and image of `∂_i` versus invariants of `s_i` -/

variable {n : ℕ}

/-- The signed transposition `s_i` as a `ℤ`-linear map. -/
noncomputable def sLin (i : Fin (n+1)) : SkewPolynomial (n+2) →ₗ[ℤ] SkewPolynomial (n+2) :=
  (s i).toRingHom.toAddMonoidHom.toIntLinearMap

/-- The `s_i`-invariants `{f : s_i f = f}`. -/
noncomputable def invariants (i : Fin (n+1)) : Submodule ℤ (SkewPolynomial (n+2)) :=
  LinearMap.ker (sLin i - LinearMap.id)

/-- The `s_i`-anti-invariants `{f : s_i f = -f}`. -/
noncomputable def antiInvariants (i : Fin (n+1)) : Submodule ℤ (SkewPolynomial (n+2)) :=
  LinearMap.ker (sLin i + LinearMap.id)

theorem mem_invariants {i : Fin (n+1)} {f : SkewPolynomial (n+2)} :
    f ∈ invariants i ↔ s i f = f := by
  simp [invariants, sLin, sub_eq_zero]

theorem mem_antiInvariants {i : Fin (n+1)} {f : SkewPolynomial (n+2)} :
    f ∈ antiInvariants i ↔ s i f = -f := by
  simp [antiInvariants, sLin, add_eq_zero_iff_eq_neg]

theorem eq_zero_of_eq_neg {f : SkewPolynomial (n+2)} (h : f = -f) : f = 0 := by
  have h2 : (2 : ℤ) • f = 0 := by rw [two_smul]; nth_rw 1 [h]; exact neg_add_cancel f
  rcases smul_eq_zero.mp h2 with h' | h'
  · norm_num at h'
  · exact h'

theorem generator_mul_ne_zero {m : ℕ} (a b : Fin m) : generator a * generator b ≠ 0 := by
  change OddMath.SkewPolynomial.mul _ _ ≠ 0
  rw [OddMath.SkewPolynomial.mul_generator, OddMath.SkewPolynomial.skewSign_expSingle]
  refine Finsupp.single_ne_zero.mpr ?_
  split_ifs <;> norm_num

/-- `∂_i(x_i x_{i+1}) = 0`. -/
theorem divided_x_mul_x (i : Fin (n+1)) :
    divided i (generator i.castSucc * generator i.succ) = 0 := by
  rw [divided_left_mul, divided_generator, if_pos (Or.inr rfl), mul_one, sub_self]

/-- `s_i(x_i x_{i+1}) = -x_i x_{i+1}`. -/
theorem s_x_mul_x (i : Fin (n+1)) :
    s i (generator i.castSucc * generator i.succ) =
      -(generator i.castSucc * generator i.succ) := by
  rw [map_mul, s_generator, s_generator, Equiv.swap_apply_left, Equiv.swap_apply_right,
    neg_mul_neg]
  exact OddMath.SkewPolynomial.generator_anticommute _ _ (adjacent_ne i).symm

/-- `s_i(x_i + x_{i+1}) = -(x_i + x_{i+1})`. -/
theorem s_x_add_x (i : Fin (n+1)) :
    s i (generator i.castSucc + generator i.succ) =
      -(generator i.castSucc + generator i.succ) := by
  rw [map_add, s_generator, s_generator, Equiv.swap_apply_left, Equiv.swap_apply_right]
  abel

/-- `∂_i(x_i + x_{i+1}) = 2 ≠ 0`. -/
theorem divided_x_add_x (i : Fin (n+1)) :
    divided i (generator i.castSucc + generator i.succ) = (2 : ℤ) • (1 : SkewPolynomial (n+2)) := by
  rw [map_add, divided_generator, divided_generator, if_pos (Or.inl rfl), if_pos (Or.inr rfl),
    two_smul]

theorem divided_x_add_x_ne_zero (i : Fin (n+1)) :
    divided i (generator i.castSucc + generator i.succ) ≠ 0 := by
  rw [divided_x_add_x]
  intro h
  rcases smul_eq_zero.mp h with h' | h'
  · norm_num at h'
  · exact Finsupp.single_ne_zero.mpr one_ne_zero h'

theorem x_mul_x_mem_ker (i : Fin (n+1)) :
    generator i.castSucc * generator i.succ ∈ LinearMap.ker (divided i) :=
  divided_x_mul_x i

theorem x_mul_x_not_mem_invariants (i : Fin (n+1)) :
    generator i.castSucc * generator i.succ ∉ invariants i := by
  rw [mem_invariants, s_x_mul_x]
  intro h
  exact generator_mul_ne_zero _ _ (eq_zero_of_eq_neg h.symm)

theorem x_add_x_mem_antiInvariants (i : Fin (n+1)) :
    generator i.castSucc + generator i.succ ∈ antiInvariants i :=
  mem_antiInvariants.mpr (s_x_add_x i)

theorem x_add_x_not_mem_ker (i : Fin (n+1)) :
    generator i.castSucc + generator i.succ ∉ LinearMap.ker (divided i) :=
  divided_x_add_x_ne_zero i

/-- E §2.1, p. 4: `ker ∂_i` is not the space of `s_i`-invariants (witness `x_i x_{i+1}`). -/
theorem ker_ne_invariants (i : Fin (n+1)) : LinearMap.ker (divided i) ≠ invariants i := by
  intro h
  exact x_mul_x_not_mem_invariants i (h ▸ x_mul_x_mem_ker i)

/-- E §2.1, p. 4: `ker ∂_i` is not the space of `s_i`-anti-invariants (witness
`x_i + x_{i+1}`). -/
theorem ker_ne_antiInvariants (i : Fin (n+1)) : LinearMap.ker (divided i) ≠ antiInvariants i := by
  intro h
  exact x_add_x_not_mem_ker i (h ▸ x_add_x_mem_antiInvariants i)

/-- E §2.1, p. 4: `im ∂_i = ker ∂_i` is not the space of `s_i`-invariants. -/
theorem range_ne_invariants (i : Fin (n+1)) : LinearMap.range (divided i) ≠ invariants i := by
  rw [← DividedSquareZero.ker_eq_range]; exact ker_ne_invariants i

/-- E §2.1, p. 4: `im ∂_i = ker ∂_i` is not the space of `s_i`-anti-invariants. -/
theorem range_ne_antiInvariants (i : Fin (n+1)) :
    LinearMap.range (divided i) ≠ antiInvariants i := by
  rw [← DividedSquareZero.ker_eq_range]; exact ker_ne_antiInvariants i

end

end OddMath.Frontier.OddLRGaps
