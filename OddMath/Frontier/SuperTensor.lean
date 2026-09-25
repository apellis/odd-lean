import OddMath.SkewPolynomial
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.Data.Fin.Tuple.Basic

/-!
# The signed tensor product of genuine skew-polynomial blocks

Integer module tensor products, concatenation of exponent blocks, and the
Koszul multiplication rule. Source: Ellis, arXiv:1111.3932v1, §2.1, unnumbered
super tensor multiplication display following deg(x_i)=(2,1); EKL,
arXiv:1111.1320v1, §2.1.1 (2.1). Increasing-index order is the locked convention.
This does not construct odd symmetric functions or a Hopf structure, nor
identify the finite-support model with a presented quotient.
-/

noncomputable section
open scoped TensorProduct
open OddMath.SkewPolynomial

namespace OddMath.Frontier.SuperTensor

abbrev Tensor (m n : ℕ) := SkewPolynomial m ⊗[ℤ] SkewPolynomial n

def degree {n : ℕ} (a : Fin n → ℕ) : ℕ := ∑ i, a i

def koszul {m n : ℕ} (b : Fin n → ℕ) (c : Fin m → ℕ) : ℤ :=
  (-1) ^ (degree b * degree c)

/-- Concatenating blocks is a bijection on actual exponent vectors. -/
def exponentEquiv (m n : ℕ) :
    ((Fin m → ℕ) × (Fin n → ℕ)) ≃ (Fin (m+n) → ℕ) where
  toFun p := Fin.append p.1 p.2
  invFun a := (fun i => a (Fin.castAdd n i), fun j => a (Fin.natAdd m j))
  left_inv p := by simp
  right_inv a := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp

/-- The actual integer tensor module, not a label-pair substitute. -/
def blockEquiv (m n : ℕ) : Tensor m n ≃ₗ[ℤ] SkewPolynomial (m+n) :=
  (finsuppTensorFinsupp' ℤ (Fin m → ℕ) (Fin n → ℕ)).trans
    (Finsupp.domLCongr (exponentEquiv m n))

@[simp] theorem blockEquiv_monomial {m n : ℕ} (a : Fin m → ℕ) (b : Fin n → ℕ)
    (r s : ℤ) :
    blockEquiv m n (monomial a r ⊗ₜ[ℤ] monomial b s) =
      monomial (Fin.append a b) (r*s) := by
  simp [blockEquiv, monomial, exponentEquiv]

theorem append_add {m n : ℕ} (a c : Fin m → ℕ) (b d : Fin n → ℕ) :
    Fin.append a b + Fin.append c d = Fin.append (a+c) (b+d) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp

/-- The only cross-block crossings go from the first right block to the
second left block; this is the source of the super tensor sign. -/
theorem crossingCount_append {m n : ℕ} (a c : Fin m → ℕ) (b d : Fin n → ℕ) :
    crossingCount (Fin.append a b) (Fin.append c d) =
      crossingCount a c + crossingCount b d + degree b * degree c := by
  have hLR (i : Fin m) (j : Fin n) : ¬ Fin.natAdd m j < Fin.castAdd n i := by
    change ¬ m + j.val < i.val
    omega
  have hRL (i : Fin n) (j : Fin m) : Fin.castAdd n j < Fin.natAdd m i := by
    change j.val < m + i.val
    omega
  have hLL (i j : Fin m) : (Fin.castAdd n j < Fin.castAdd n i) ↔ j < i := Iff.rfl
  simp only [crossingCount, Finset.sum_filter]
  rw [Fin.sum_univ_add]
  simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right,
    hLL, Fin.natAdd_lt_natAdd_iff, hLR, hRL,
    ite_false, ite_true, Finset.sum_const_zero, add_zero, Finset.sum_add_distrib]
  simp only [degree, ← Finset.mul_sum, ← Finset.sum_mul]
  ac_rfl

theorem skewSign_append {m n : ℕ} (a c : Fin m → ℕ) (b d : Fin n → ℕ) :
    skewSign (Fin.append a b) (Fin.append c d) =
      skewSign a c * skewSign b d * koszul b c := by
  simp only [skewSign, crossingCount_append, pow_add, koszul]

/-- Multiplication transported from the actual skew-polynomial algebra.
Its nontrivial agreement with the Koszul rule is `tensorMul_monomial`. -/
def tensorMul {m n : ℕ} (x y : Tensor m n) : Tensor m n :=
  (blockEquiv m n).symm (mul (blockEquiv m n x) (blockEquiv m n y))

@[simp] theorem blockEquiv_tensorMul {m n : ℕ} (x y : Tensor m n) :
    blockEquiv m n (tensorMul x y) = mul (blockEquiv m n x) (blockEquiv m n y) := by
  simp [tensorMul]

theorem tensorMul_assoc {m n : ℕ} (x y z : Tensor m n) :
    tensorMul (tensorMul x y) z = tensorMul x (tensorMul y z) := by
  apply (blockEquiv m n).injective
  simp only [blockEquiv_tensorMul, mul_assoc]

@[simp] theorem tensorMul_zero_left {m n : ℕ} (y : Tensor m n) :
    tensorMul 0 y = 0 := by simp [tensorMul, zero_mul]

@[simp] theorem tensorMul_zero_right {m n : ℕ} (x : Tensor m n) :
    tensorMul x 0 = 0 := by simp [tensorMul, mul_zero]

theorem tensorMul_add_left {m n : ℕ} (x y z : Tensor m n) :
    tensorMul (x+y) z = tensorMul x z + tensorMul y z := by
  simp [tensorMul, add_mul]

theorem tensorMul_add_right {m n : ℕ} (x y z : Tensor m n) :
    tensorMul x (y+z) = tensorMul x y + tensorMul x z := by
  simp [tensorMul, mul_add]

theorem tensorMul_smul_left {m n : ℕ} (r : ℤ) (x y : Tensor m n) :
    tensorMul (r • x) y = r • tensorMul x y :=
  (show Tensor m n →+ Tensor m n from
    { toFun := fun x => tensorMul x y
      map_zero' := tensorMul_zero_left y
      map_add' := fun x z => tensorMul_add_left x z y }).map_zsmul x r

theorem tensorMul_smul_right {m n : ℕ} (r : ℤ) (x y : Tensor m n) :
    tensorMul x (r • y) = r • tensorMul x y :=
  (show Tensor m n →+ Tensor m n from
    { toFun := tensorMul x
      map_zero' := tensorMul_zero_right x
      map_add' := tensorMul_add_right x }).map_zsmul y r

/-- Explicit integer-bilinear multiplication on the genuine tensor module. -/
def tensorMulLinear (m n : ℕ) : Tensor m n →ₗ[ℤ] Tensor m n →ₗ[ℤ] Tensor m n where
  toFun x :=
    { toFun := tensorMul x
      map_add' := tensorMul_add_right x
      map_smul' := fun r y => tensorMul_smul_right r x y }
  map_add' x y := by
    apply LinearMap.ext
    intro z
    exact tensorMul_add_left x y z
  map_smul' r x := by
    apply LinearMap.ext
    intro y
    exact tensorMul_smul_left r x y

/-- The Koszul rule for arbitrary scalar monomials, uniformly in both ranks
and all exponents. The sign uses the FIRST right and SECOND left blocks. -/
theorem tensorMul_monomial {m n : ℕ} (a c : Fin m → ℕ) (b d : Fin n → ℕ)
    (r s t u : ℤ) :
    tensorMul (monomial a r ⊗ₜ[ℤ] monomial b s)
      (monomial c t ⊗ₜ[ℤ] monomial d u) =
    koszul b c • (mul (monomial a r) (monomial c t) ⊗ₜ[ℤ]
      mul (monomial b s) (monomial d u)) := by
  apply (blockEquiv m n).injective
  simp only [blockEquiv_tensorMul, blockEquiv_monomial, mul_monomial,
    map_smul, append_add, skewSign_append, monomial, Finsupp.smul_single,
    smul_eq_mul]
  congr 1
  ac_rfl

/-- Extension in both arguments over arbitrary finite sums of tensors. -/
theorem tensorMul_sum_left {m n : ℕ} {ι : Type*} (S : Finset ι)
    (x : ι → Tensor m n) (y : Tensor m n) :
    tensorMul (∑ i ∈ S, x i) y = ∑ i ∈ S, tensorMul (x i) y :=
  map_sum ((tensorMulLinear m n).flip y) x S

theorem tensorMul_sum_right {m n : ℕ} {ι : Type*} (S : Finset ι)
    (x : Tensor m n) (y : ι → Tensor m n) :
    tensorMul x (∑ i ∈ S, y i) = ∑ i ∈ S, tensorMul x (y i) :=
  map_sum (tensorMulLinear m n x) y S

/-- Expanding a genuine pure tensor in its monomial tensor basis. -/
theorem tmul_eq_sum {m n : ℕ} (f : SkewPolynomial m) (g : SkewPolynomial n) :
    f ⊗ₜ[ℤ] g = f.sum (fun a r => g.sum (fun b s =>
      monomial a r ⊗ₜ[ℤ] monomial b s)) := by
  calc
    f ⊗ₜ[ℤ] g = (f.sum monomial) ⊗ₜ[ℤ] (g.sum monomial) := by
      simp only [monomial, Finsupp.sum_single]
    _ = _ := by
      simp only [Finsupp.sum]
      rw [TensorProduct.sum_tmul]
      simp only [TensorProduct.tmul_sum]

/-- The signed multiplication rule extended to all polynomials. Each sum is
finite support, with no degree/rank bound and no homogeneity assumption. -/
theorem tensorMul_tmul {m n : ℕ} (f h : SkewPolynomial m) (g k : SkewPolynomial n) :
    tensorMul (f ⊗ₜ[ℤ] g) (h ⊗ₜ[ℤ] k) =
    f.sum (fun a r => g.sum (fun b s => h.sum (fun c t => k.sum (fun d u =>
      koszul b c • (mul (monomial a r) (monomial c t) ⊗ₜ[ℤ]
        mul (monomial b s) (monomial d u)))))) := by
  conv_lhs => rw [tmul_eq_sum f g, tmul_eq_sum h k]
  simp only [Finsupp.sum]
  simp only [tensorMul_sum_left]
  simp only [tensorMul_sum_right, tensorMul_monomial]

end OddMath.Frontier.SuperTensor
