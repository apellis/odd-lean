import OddMath.Frontier.SmallRankONH
import OddMath.Frontier.OnhStructure2

/-!
# `ONH_a ⊗ ONH_b ⊂ ONH_{a+b}` when `a` or `b` is `0` or `1`

EKL arXiv:1111.1320v1, §6, p. 46: placing diagrams side by side gives an inclusion
`ONH_a ⊗ ONH_b ⊂ ONH_{a+b}`. For `a, b ≥ 2` this is `OnhStructure.tensorMap_injective`. Here
`ONH_0 = ℤ` and `ONH_1 = OPol_1 = ℤ[x]`, whose generator `x` goes to a dot:

* `a = 0` or `b = 0`: `z ⊗ y ↦ z y` and `y ⊗ z ↦ z y` are isomorphisms (`tensorZeroLeft`,
  `tensorZeroRight`).
* `a = b = 1`: `f ⊗ g ↦ f(x_1) g(x_2) ∈ ONH_2` (`tensorOneOne_injective`).
* `a = 1`, `b ≥ 2`: `f ⊗ y ↦ f(x_1) ι_R(y) ∈ ONH_{1+b}`, `ι_R` the window on the strands
  `[1, 1+b)` (`tensorOneLeft_injective`); symmetrically `b = 1`, `a ≥ 2`
  (`tensorOneRight_injective`).

The super sign rule `(x ⊗ y)(x' ⊗ y') = (-1)^{|y||x'|} xx' ⊗ yy'` (`OnhStructure.tensorMap_mul`)
holds in these cases too, with `x ∈ ONH_1` of super-degree its `x`-degree (`tensorOneLeft_mul`,
`tensorOneRight_mul`, `tensorOneOne_mul`).

The injectivity for `a = 1 ≤ b - 1` is reduced to `a = 2`: shifting everything one strand to the
right embeds `ONH_{1+b}` in `ONH_{2+b}`, and on `ONH_1 ⊗ ONH_b` this is `tensorMap` after
`f ↦ f(x_2)`, which is injective by the PBW basis (Prop 2.11) and flatness of `ONH_b`.
-/

namespace OddMath.Frontier.SmallRank
open OddMath.SkewPolynomial (SkewPolynomial generator monomial)
open NilHeckeAction NilCoxeterWords NilHeckeBasis OnhWindow OnhStructure
open scoped TensorProduct BigOperators

noncomputable section

/-! ## Evaluating `ℤ[x]` at an element -/

section Eval
variable {R : Type*} [Ring R]

/-- `f ↦ f(r)`, `OPol_1 = ℤ[x] → R`. -/
def dotEval (r : R) : SkewPolynomial 1 →+* R :=
  (Polynomial.eval₂RingHom' (Int.castRingHom R) r fun a => Int.cast_commute a r).comp
    rankOneEquiv.toRingHom

theorem dotEval_monomial (r : R) (a : Fin 1 → ℕ) (c : ℤ) :
    dotEval r (monomial a c) = (c : R) * r ^ (a 0) := by
  simp [dotEval, Polynomial.eval₂_monomial]

theorem dotEval_generator (r : R) : dotEval r (generator 0) = r := by
  simp [dotEval]

theorem map_dotEval {S : Type*} [Ring S] (φ : R →+* S) (r : R) (f : SkewPolynomial 1) :
    φ (dotEval r f) = dotEval (φ r) f := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, map_add, hf, hg, map_add]
  | single a c =>
    change φ (dotEval r (monomial a c)) = dotEval (φ r) (monomial a c)
    rw [dotEval_monomial, dotEval_monomial, map_mul, map_pow, map_intCast]

end Eval

/-! ## `a = 0` or `b = 0` -/

/-- `ONH_0 ⊗ ONH_b ≅ ONH_b`, `z ⊗ y ↦ z y`. -/
def tensorZeroLeft (b : ℕ) : ONH 0 ⊗[ℤ] ONH b ≃ₗ[ℤ] ONH b := TensorProduct.lid ℤ (ONH b)

theorem tensorZeroLeft_tmul (b : ℕ) (z : ONH 0) (y : ONH b) :
    tensorZeroLeft b (z ⊗ₜ y) = (show ℤ from z) • y := rfl

/-- `ONH_a ⊗ ONH_0 ≅ ONH_a`, `y ⊗ z ↦ z y`. -/
def tensorZeroRight (a : ℕ) : ONH a ⊗[ℤ] ONH 0 ≃ₗ[ℤ] ONH a := TensorProduct.rid ℤ (ONH a)

theorem tensorZeroRight_tmul (a : ℕ) (y : ONH a) (z : ONH 0) :
    tensorZeroRight a (y ⊗ₜ z) = (show ℤ from z) • y := rfl

/-! ## The dot embeddings `ONH_1 → ONH_2` and a signed-basis criterion -/

theorem chosenWord_one (n : ℕ) : chosenWord (1 : Perm n) = [] :=
  List.length_eq_zero_iff.mp (by simp)

theorem dividedElement_one' (n : ℕ) : dividedElement (1 : Perm n) = 1 := by
  simp [dividedElement, chosenWord_one, product]

theorem dotMonomial_two (i j : ℕ) : dotMonomial ![i, j] = dot 0 0 ^ i * dot 0 1 ^ j := by
  simp [dotMonomial, List.finRange_succ]

theorem basisElement_two (i j : ℕ) :
    basisElement (![i, j], (1 : Perm 0)) = dot 0 0 ^ i * dot 0 1 ^ j := by
  rw [basisElement, dividedElement_one', mul_one, dotMonomial_two]

/-- `f ↦ f(x_{k+1})`, `ONH_1 → ONH_2`, `k ∈ {0, 1}`. -/
def dotTwo (k : Fin 2) : SkewPolynomial 1 →ₗ[ℤ] Presented 0 :=
  (dotEval (dot 0 k)).toIntAlgHom.toLinearMap

theorem dotTwo_apply (k : Fin 2) (f : SkewPolynomial 1) : dotTwo k f = dotEval (dot 0 k) f := rfl

theorem dotTwo_basis (k : Fin 2) (a : Fin 1 → ℕ) :
    dotTwo k (Finsupp.basisSingleOne a) =
      basis 0 (if k = 0 then ![a 0, 0] else ![0, a 0], (1 : Perm 0)) := by
  rw [basis_apply, Finsupp.coe_basisSingleOne, dotTwo_apply]
  change dotEval _ (monomial a 1) = _
  rw [dotEval_monomial, Int.cast_one, one_mul]
  fin_cases k
  · simp [basisElement_two]
  · simp [basisElement_two]

theorem dotTwo_injective (k : Fin 2) : Function.Injective (dotTwo k) := by
  refine injective_of_signed_basis Finsupp.basisSingleOne (basis 0) (dotTwo k)
    (fun a => (if k = 0 then ![a 0, 0] else ![0, a 0], (1 : Perm 0))) ?_
    fun a => Or.inl (dotTwo_basis k a)
  intro a a' h
  have h1 := congrArg (fun p => p.1 k) h
  funext i
  fin_cases i
  fin_cases k <;> simpa using h1

instance (n : ℕ) : Module.Free ℤ (Presented n) := Module.Free.of_basis (basis n)

/-! ## `a = b = 1` -/

/-- `ONH_1 ⊗ ONH_1 → ONH_2`, `f ⊗ g ↦ f(x_1) g(x_2)`. -/
def tensorOneOne : SkewPolynomial 1 ⊗[ℤ] SkewPolynomial 1 →ₗ[ℤ] Presented 0 :=
  TensorProduct.lift (LinearMap.mk₂ ℤ (fun f g => dotEval (dot 0 0) f * dotEval (dot 0 1) g)
    (fun f₁ f₂ g => by simp only [map_add, add_mul])
    (fun c f g => by simp only [map_zsmul, smul_mul_assoc])
    (fun f g₁ g₂ => by simp only [map_add, mul_add])
    (fun c f g => by simp only [map_zsmul, mul_smul_comm]))

@[simp] theorem tensorOneOne_tmul (f g : SkewPolynomial 1) :
    tensorOneOne (f ⊗ₜ g) = dotEval (dot 0 0) f * dotEval (dot 0 1) g := rfl

/-- **EKL §6, p. 46**, `a = b = 1`: `ONH_1 ⊗ ONH_1 → ONH_2` is injective. -/
theorem tensorOneOne_injective : Function.Injective tensorOneOne := by
  refine injective_of_signed_basis (Finsupp.basisSingleOne.tensorProduct Finsupp.basisSingleOne)
    (basis 0) tensorOneOne (fun p => (![p.1 0, p.2 0], (1 : Perm 0))) ?_ fun p => Or.inl ?_
  · rintro ⟨a, b⟩ ⟨a', b'⟩ h
    have h0 := congrArg (fun p => p.1 0) h
    have h1 := congrArg (fun p => p.1 1) h
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h0 h1
    simp only [Prod.mk.injEq]
    exact ⟨funext fun i => by fin_cases i; exact h0, funext fun i => by fin_cases i; exact h1⟩
  · rw [Basis.tensorProduct_apply, tensorOneOne_tmul, basis_apply, basisElement_two]
    simp only [Finsupp.coe_basisSingleOne]
    change dotEval _ (monomial p.1 1) * dotEval _ (monomial p.2 1) = _
    rw [dotEval_monomial, dotEval_monomial, Int.cast_one, one_mul, one_mul]

/-! ## `a = 1`, `b ≥ 2` -/

/-- `ι_R : ONH_b → ONH_{1+b}`, strands `[1, 1+b)`, `b = m'+2`. -/
def incR1 (m' : ℕ) : Presented m' →+* Presented (m'+1) :=
  windowHom m' (m'+1) 1 (by omega)

/-- `ONH_1 ⊗ ONH_b → ONH_{1+b}`, `f ⊗ y ↦ f(x_1) ι_R(y)`, `b = m'+2`. -/
def tensorOneLeft (m' : ℕ) : SkewPolynomial 1 ⊗[ℤ] Presented m' →ₗ[ℤ] Presented (m'+1) :=
  TensorProduct.lift (LinearMap.mk₂ ℤ (fun f y => dotEval (dot (m'+1) 0) f * incR1 m' y)
    (fun f₁ f₂ y => by simp only [map_add, add_mul])
    (fun c f y => by simp only [map_zsmul, smul_mul_assoc])
    (fun f y₁ y₂ => by simp only [map_add, mul_add])
    (fun c f y => by simp only [map_zsmul, mul_smul_comm]))

@[simp] theorem tensorOneLeft_tmul (m' : ℕ) (f : SkewPolynomial 1) (y : Presented m') :
    tensorOneLeft m' (f ⊗ₜ y) = dotEval (dot (m'+1) 0) f * incR1 m' y := rfl

/-- Shift `ONH_{1+b}` one strand to the right inside `ONH_{2+b}`. -/
def shiftOne (m' : ℕ) : Presented (m'+1) →+* Presented (0+2+m') := windowHom (m'+1) (0+2+m') 1
  (by omega)

theorem shiftOne_tensorOneLeft (m' : ℕ) (t : SkewPolynomial 1 ⊗[ℤ] Presented m') :
    shiftOne m' (tensorOneLeft m' t) = tensorMap 0 m' (LinearMap.rTensor _ (dotTwo 1) t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul f y =>
    rw [tensorOneLeft_tmul, LinearMap.rTensor_tmul, tensorMap_tmul, map_mul, dotTwo_apply,
      map_dotEval, map_dotEval, shiftOne, windowHom_dot, incL, windowHom_dot, incR1, incR,
      windowHom_comp_apply (h₃ := by omega)]
    rfl
  | add s t hs ht => rw [map_add, map_add, hs, ht, map_add, map_add]

/-- **EKL §6, p. 46**, `a = 1`, `b ≥ 2`: `ONH_1 ⊗ ONH_b → ONH_{1+b}` is injective. -/
theorem tensorOneLeft_injective (m' : ℕ) : Function.Injective (tensorOneLeft m') := by
  have hinj : Function.Injective (tensorMap 0 m' ∘ LinearMap.rTensor (Presented m') (dotTwo 1)) :=
    (tensorMap_injective 0 m').comp
      (Module.Flat.rTensor_preserves_injective_linearMap _ (dotTwo_injective 1))
  intro s t h
  apply hinj
  simp only [Function.comp_apply, ← shiftOne_tensorOneLeft, h]

/-! ## `a ≥ 2`, `b = 1` -/

/-- `ι_L : ONH_a → ONH_{a+1}`, strands `[0, a)`, `a = m+2`. -/
def incL1 (m : ℕ) : Presented m →+* Presented (m+1) :=
  windowHom m (m+1) 0 (by omega)

/-- `ONH_a ⊗ ONH_1 → ONH_{a+1}`, `y ⊗ f ↦ ι_L(y) f(x_{a+1})`, `a = m+2`. -/
def tensorOneRight (m : ℕ) : Presented m ⊗[ℤ] SkewPolynomial 1 →ₗ[ℤ] Presented (m+1) :=
  TensorProduct.lift (LinearMap.mk₂ ℤ
    (fun y f => incL1 m y * dotEval (dot (m+1) (Fin.last (m+2))) f)
    (fun y₁ y₂ f => by simp only [map_add, add_mul])
    (fun c y f => by simp only [map_zsmul, smul_mul_assoc])
    (fun y f₁ f₂ => by simp only [map_add, mul_add])
    (fun c y f => by simp only [map_zsmul, mul_smul_comm]))

@[simp] theorem tensorOneRight_tmul (m : ℕ) (y : Presented m) (f : SkewPolynomial 1) :
    tensorOneRight m (y ⊗ₜ f) = incL1 m y * dotEval (dot (m+1) (Fin.last (m+2))) f := rfl

/-- `ONH_{a+1}` on the first `a+1` strands of `ONH_{a+2}`. -/
def extendOne (m : ℕ) : Presented (m+1) →+* Presented (m+2+0) :=
  windowHom (m+1) (m+2+0) 0 (by omega)

theorem extendOne_tensorOneRight (m : ℕ) (t : Presented m ⊗[ℤ] SkewPolynomial 1) :
    extendOne m (tensorOneRight m t) = tensorMap m 0 (LinearMap.lTensor _ (dotTwo 0) t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul y f =>
    rw [tensorOneRight_tmul, LinearMap.lTensor_tmul, tensorMap_tmul, map_mul, dotTwo_apply,
      map_dotEval, map_dotEval, extendOne, windowHom_dot, incR, windowHom_dot, incL1, incL,
      windowHom_comp_apply (h₃ := by omega)]
    congr 3
    exact congrArg (dot (m+2+0)) (Fin.ext (by simp))
  | add s t hs ht => rw [map_add, map_add, hs, ht, map_add, map_add]

/-- **EKL §6, p. 46**, `a ≥ 2`, `b = 1`: `ONH_a ⊗ ONH_1 → ONH_{a+1}` is injective. -/
theorem tensorOneRight_injective (m : ℕ) : Function.Injective (tensorOneRight m) := by
  have hinj : Function.Injective (tensorMap m 0 ∘ LinearMap.lTensor (Presented m) (dotTwo 0)) :=
    (tensorMap_injective m 0).comp
      (Module.Flat.lTensor_preserves_injective_linearMap _ (dotTwo_injective 0))
  intro s t h
  apply hinj
  simp only [Function.comp_apply, ← extendOne_tensorOneRight, h]

/-! ## The super sign rule -/

theorem swap_sign {R : Type*} [Ring R] {u v : R} (k : ℕ) (h : u * v = (-1) ^ k * (v * u)) :
    v * u = (-1) ^ k * (u * v) := by
  rw [h, ← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]

theorem homog_dot_pow {n : ℕ} (j : Fin (n+2)) (k : ℕ) :
    Homog j.val (j.val+1) k (dot n j ^ k) := by
  have h := Homog.list_prod (l := j.val) (r := j.val+1) (List.replicate k (dot n j))
    fun x hx => by
      rw [List.eq_of_mem_replicate hx]
      exact IsGen.dot j le_rfl (Nat.lt_succ_self _)
  rwa [List.length_replicate, List.prod_replicate] at h

/-- The super sign rule for `ONH_1 ⊗ ONH_b ⊂ ONH_{1+b}`: `x^j ∈ ONH_1` has super-degree `j`, and
`y` is a product of `k` generators. -/
theorem tensorOneLeft_mul (m' : ℕ) (f : SkewPolynomial 1) {y y' : Presented m'} {k : ℕ}
    (hy : Homog 0 (m'+2) k y) (j : ℕ) :
    tensorOneLeft m' (f ⊗ₜ y) * tensorOneLeft m' ((generator 0 ^ j) ⊗ₜ y') =
      (-1) ^ (k * j) * tensorOneLeft m' ((f * generator 0 ^ j) ⊗ₜ (y * y')) := by
  have hY : Homog (0+1) (m'+2+1) k (incR1 m' y) := hy.windowHom
  have hX := homog_dot_pow (n := m'+1) 0 j
  have hsc := swap_sign _ (hX.supercomm hY (by simp))
  simp only [tensorOneLeft_tmul, map_mul, map_pow, dotEval_generator]
  rw [mul_comm k j, mul_assoc (dotEval _ f), ← mul_assoc (incR1 m' y), hsc]
  simp only [mul_assoc, ((Commute.neg_one_left _).pow_left _).eq]

/-- The super sign rule for `ONH_a ⊗ ONH_1 ⊂ ONH_{a+1}`. -/
theorem tensorOneRight_mul (m : ℕ) (y : Presented m) {y' : Presented m} {k : ℕ}
    (hy' : Homog 0 (m+2) k y') (j : ℕ) (f' : SkewPolynomial 1) :
    tensorOneRight m (y ⊗ₜ (generator 0 ^ j)) * tensorOneRight m (y' ⊗ₜ f') =
      (-1) ^ (j * k) * tensorOneRight m ((y * y') ⊗ₜ (generator 0 ^ j * f')) := by
  have hY : Homog (0+0) (m+2+0) k (incL1 m y') := hy'.windowHom
  have hX := homog_dot_pow (n := m+1) (Fin.last (m+2)) j
  have hsc := swap_sign _ (hY.supercomm hX (by simp))
  simp only [tensorOneRight_tmul, map_mul, map_pow, dotEval_generator]
  rw [mul_comm j k, mul_assoc (incL1 m y), ← mul_assoc (dot (m+1) (Fin.last (m+2)) ^ j), hsc]
  simp only [mul_assoc, ((Commute.neg_one_left _).pow_left _).eq]

/-- The super sign rule for `ONH_1 ⊗ ONH_1 ⊂ ONH_2`. -/
theorem tensorOneOne_mul (f g : SkewPolynomial 1) (i j : ℕ) :
    tensorOneOne (f ⊗ₜ (generator 0 ^ j)) * tensorOneOne ((generator 0 ^ i) ⊗ₜ g) =
      (-1) ^ (j * i) * tensorOneOne ((f * generator 0 ^ i) ⊗ₜ (generator 0 ^ j * g)) := by
  have hsc := swap_sign _ ((homog_dot_pow (n := 0) 0 i).supercomm (homog_dot_pow (n := 0) 1 j)
    (by simp))
  simp only [tensorOneOne_tmul, map_mul, map_pow, dotEval_generator]
  rw [mul_comm j i, mul_assoc (dotEval _ f), ← mul_assoc (dot 0 1 ^ j), hsc]
  simp only [mul_assoc, ((Commute.neg_one_left _).pow_left _).eq]

end

end OddMath.Frontier.SmallRank
