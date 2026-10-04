import OddMath.Frontier.EQFunctorDual

/-!
# Ellis–Qi, Proposition 4.12 (2): `END(Z_{a,b}) = Z_{a,b} ⊗ Z_{a,b}^∨` through rank-one maps

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2,
§4.3.2, the paragraph before Proposition 4.12 and Proposition 4.12 (2).

The source builds endomorphisms of `Z_{a,b}` from the trace pairing,
`Z_{a,b} ⊗_{OΛ_{a+b}} Z_{a,b}^∨ → END_{OΛ_{a+b}^{op}}(Z_{a,b})`, `g z ⊗ z^∨ f ↦ (x ↦ g z · (z^∨ f)(x))`,
calls the algebra they span `E_{a,b}` (defined only diagrammatically), and asserts
`E_{a,b} ≅ END(Z_{a,b})` "by a graded rank count". What is formalized:

* generic (`RightBasis.eq_sum_rankOne`, `RightBasis.rankOne_injective`): for a right module `M`
  with a finite basis `(b_i)` and dual basis `δ_i` (the coefficient maps, `RightBasis.coeffHom`),
  every right-linear additive endomorphism `f` of `M` is `Σ_i f(b_i) · δ_i(−)`, a sum of rank-one
  maps `m · φ(−)` (`rankOne m φ`), and the `m_i` in `Σ_i m_i · δ_i(−)` are unique; so the trace
  pairing map `M ⊗_A M^∨ → END_A(M)` is bijective (`M^∨` being free on the `δ_i`);
* **Proposition 4.12 (2)** for `Z_{a,b}` (`prop_4_12_two`, `prop_4_12_two_unique`): every right
  `OΛ_{a+b}`-linear endomorphism of `Z_{a,b}` is `Σ_μ f(s̃_μ(y) z) · δ_μ(−)`, uniquely; i.e.
  `END_{OΛ_{a+b}^{op}}(Z_{a,b})` is exactly the span of the maps `φ` of the source, free over
  the basis of Corollary 4.8 in each of the `binom(a+b, a)` slots.
-/

namespace OddMath.Frontier.EQFunctor

open DG MulOpposite

section Generic

variable {A : Type*} [Ring A] {M : Type*} [AddCommGroup M] [DGAddCommGroup M] [Module Aᵐᵒᵖ M]

/-- The rank-one map `x ↦ m · φ(x)`. -/
def rankOne (m : M) (φ : M →+ A) : M →+ M where
  toFun x := op (φ x) • m
  map_zero' := by rw [map_zero, op_zero, zero_smul]
  map_add' x y := by rw [map_add, op_add, add_smul]

omit [DGAddCommGroup M] in
@[simp] theorem rankOne_apply (m : M) (φ : M →+ A) (x : M) : rankOne m φ x = op (φ x) • m := rfl

variable {ι : Type*} [Fintype ι] (R : RightBasis A M ι)

/-- Every right-linear additive endomorphism is `Σ_i f(b_i) · δ_i(−)`. -/
theorem RightBasis.eq_sum_rankOne (f : M →+ M) (hf : ∀ (a : A) (x : M), f (op a • x) = op a • f x) :
    f = ∑ i, rankOne (f (R.b i)) (R.coeffHom i) := by
  ext x
  conv_lhs => rw [← R.sum_coeff x]
  rw [map_sum, AddMonoidHom.finsetSum_apply]
  exact Finset.sum_congr rfl fun i _ => by rw [hf]; rfl

/-- The coefficients `m_i` of `Σ_i m_i · δ_i(−)` are unique. -/
theorem RightBasis.rankOne_injective [DecidableEq ι] (m m' : ι → M)
    (h : ∑ i, rankOne (m i) (R.coeffHom i) = ∑ i, rankOne (m' i) (R.coeffHom i)) : m = m' := by
  funext j
  have key : ∀ m : ι → M, (∑ i, rankOne (m i) (R.coeffHom i)) (R.b j) = m j := by
    intro m
    rw [AddMonoidHom.finsetSum_apply, Finset.sum_eq_single j]
    · rw [rankOne_apply, RightBasis.coeffHom_apply, R.coeff_basis, Pi.single_eq_same, op_one,
        one_smul]
    · intro i _ hij
      rw [rankOne_apply, RightBasis.coeffHom_apply, R.coeff_basis, Pi.single_eq_of_ne hij,
        op_zero, zero_smul]
    · intro hj; exact absurd (Finset.mem_univ j) hj
  rw [← key m, h, key m']

end Generic

variable (a b : ℕ)

/-- **Ellis–Qi, Proposition 4.12 (2)** (spanning): every right `OΛ_{a+b}`-linear endomorphism `f`
of `Z_{a,b}` is the sum `Σ_μ f(s̃_μ(y) z) · δ_μ(−)` of the trace-pairing maps of the source. -/
theorem prop_4_12_two (f : EQFix.Zab a b →+ EQFix.Zab a b)
    (hf : ∀ (c : EQSkewDifferential.osymDG (a+b)) (x : EQFix.Zab a b), f (op c • x) = op c • f x) :
    f = ∑ μ, rankOne (f ((zabRightBasis a b).b μ)) ((zabRightBasis a b).coeffHom μ) :=
  (zabRightBasis a b).eq_sum_rankOne f hf

/-- **Ellis–Qi, Proposition 4.12 (2)** (uniqueness): `Σ_μ m_μ · δ_μ(−)` determines the `m_μ ∈ Z_{a,b}`;
so the trace pairing `Z_{a,b} ⊗ Z_{a,b}^∨ → END(Z_{a,b})` is injective. -/
theorem prop_4_12_two_unique (m m' : EQFix.ParIdx a b → EQFix.Zab a b)
    (h : ∑ μ, rankOne (m μ) ((zabRightBasis a b).coeffHom μ) =
      ∑ μ, rankOne (m' μ) ((zabRightBasis a b).coeffHom μ)) : m = m' := by
  classical
  exact (zabRightBasis a b).rankOne_injective m m' h

end OddMath.Frontier.EQFunctor
