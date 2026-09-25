import OddMath.Frontier.EKFreeCoproduct
import OddMath.Frontier.EKPairingAdjoint
import OddMath.Frontier.EKPlatformBijection

/-!
# EK §2.1 at arbitrary q over an arbitrary commutative ring

Source: Ellis–Khovanov, arXiv:1107.5610v2, §2.1, pp.5–8.

* p.5: `Λ'` is the free associative graded `k`-algebra on `h₁, h₂, …` (`h₀ = 1`),
  `Λ'⊗²` carries `(x₁⊗x₂)(y₁⊗y₂) = q^{deg x₂ deg y₁} x₁y₁ ⊗ x₂y₂`,
  `Δ(hₙ) = Σ_{m=0}^n hₘ ⊗ h_{n-m}`, `ε(x) = 0` for `deg x > 0`.
* p.7 (2.1): `(h_β, h_α) = Σ_{c ∈ βS_α} q^{ℓ(c)}` if `|α| = |β|`, else `0`,
  with `ℓ(c)` the length of the minimal representative of the double coset `c`.
* p.7 (2.2): `(y₁⊗y₂, x₁⊗x₂) = (y₁,x₁)(y₂,x₂)` (no power of q).
* Proposition 2.2 (2.3): `(y₁⊗y₂, Δ(x)) = (y₁y₂, x)`.

Here `k` is an arbitrary commutative ring and `q : k` arbitrary (not assumed
invertible).  The form is DEFINED by the source double-coset sum (2.1) over the
genuine double cosets `S_β\S_n/S_α` of `EKPlatformBijection`, with EK's length of the
unique minimal representative; the matrix/crossing expression is a proved
consequence (the bijection and length identity are the existing q-independent
combinatorics).  No radical, quotient, antipode or Hopf claim is made.
-/
noncomputable section
open scoped TensorProduct BigOperators
namespace OddMath.Frontier.EKGeneralQ
open EKFreeCoproduct (W degree degree_one degree_mul partWord partWord_degree)
attribute [local instance] Classical.propDecidable

variable (k : Type*) [CommRing k]

/-- EK's `Λ'`: generator `i` is `h_(i+1)`. -/
abbrev L := FreeAlgebra k ℕ
/-- `Λ' ⊗ Λ'` as a `k`-module. -/
abbrev LL := L k ⊗[k] L k

/-- `h₀ = 1`, `h_(n+1)` the free generator. -/
def h : ℕ → L k
  | 0 => 1
  | n + 1 => FreeAlgebra.ι k n

@[simp] theorem h_zero : h k 0 = 1 := rfl

/-- Ordered products `h_α = h_{a₁}⋯h_{a_k}` (zero parts are units). -/
def hWord (α : List ℕ) : L k := (α.map (h k)).prod

def wordBasis : Basis W k (L k) := FreeAlgebra.basisFreeMonoid k ℕ

theorem wordBasis_eq (w : W) : wordBasis k w =
    (FreeAlgebra.equivMonoidAlgebraFreeMonoid : L k ≃ₐ[k] MonoidAlgebra k W).symm
      (MonoidAlgebra.single w 1) := rfl

@[simp] theorem wordBasis_one : wordBasis k (1 : W) = (1 : L k) := by
  rw [wordBasis_eq, ← MonoidAlgebra.one_def, map_one]

@[simp] theorem wordBasis_mul (u v : W) :
    wordBasis k (u*v) = wordBasis k u * wordBasis k v := by
  simp only [wordBasis_eq, ← map_mul, MonoidAlgebra.single_mul_single, one_mul]

@[simp] theorem wordBasis_of (i : ℕ) : wordBasis k (FreeMonoid.of i) = h k (i+1) := by
  rw [wordBasis_eq]
  apply (FreeAlgebra.equivMonoidAlgebraFreeMonoid : L k ≃ₐ[k] MonoidAlgebra k W).injective
  rw [AlgEquiv.apply_symm_apply]
  change _ = FreeAlgebra.lift k (fun x => MonoidAlgebra.single (FreeMonoid.of x) 1)
    (FreeAlgebra.ι k i)
  simp

@[simp] theorem partWord_value (α : List ℕ) : wordBasis k (partWord α) = hWord k α := by
  induction α with
  | nil => simp [partWord, hWord]
  | cons n α ih =>
    cases n <;> simp [partWord, ih, hWord]

def tensorBasis : Basis (W × W) k (LL k) := (wordBasis k).tensorProduct (wordBasis k)

@[simp] theorem tensorBasis_apply (u v : W) :
    tensorBasis k (u,v) = wordBasis k u ⊗ₜ[k] wordBasis k v := by
  simp [tensorBasis]

/-- Linear extension from a basis (any ring). -/
theorem basis_induction {M I : Type*} [AddCommGroup M] [Module k M]
    (b : Basis I k M) (P : M → Prop) (hz : P 0)
    (ha : ∀ x y, P x → P y → P (x+y))
    (hb : ∀ i (r : k), P (r • b i)) (x : M) : P x := by
  obtain ⟨f, rfl⟩ := b.repr.symm.surjective x
  induction f using Finsupp.induction_linear with
  | zero => simpa using hz
  | add f g hf hg => simpa using ha _ _ hf hg
  | single i r => simpa using hb i r

variable {k}
variable (q : k)

/-- EK p.5: `(x₁⊗x₂)(y₁⊗y₂) = q^{deg x₂ · deg y₁} x₁y₁ ⊗ x₂y₂`, bilinear on the
genuine tensor module. -/
def tensorMulLinear : LL k →ₗ[k] LL k →ₗ[k] LL k :=
  (tensorBasis k).constr k fun p => (tensorBasis k).constr k fun r =>
    (q^(degree p.2 * degree r.1)) • tensorBasis k (p.1*r.1, p.2*r.2)

def tensorMul (x y : LL k) : LL k := tensorMulLinear q x y

@[simp] theorem tensorMul_basis (p r : W × W) :
    tensorMul q (tensorBasis k p) (tensorBasis k r) =
      (q^(degree p.2 * degree r.1)) • tensorBasis k (p.1*r.1, p.2*r.2) := by
  simp [tensorMul, tensorMulLinear]

@[simp] theorem tensorMul_zero_left (x : LL k) : tensorMul q 0 x = 0 := by
  simp [tensorMul]
@[simp] theorem tensorMul_zero_right (x : LL k) : tensorMul q x 0 = 0 := by
  simp [tensorMul]
@[simp] theorem tensorMul_add_left (x y z : LL k) :
    tensorMul q (x+y) z = tensorMul q x z + tensorMul q y z := by simp [tensorMul]
@[simp] theorem tensorMul_add_right (x y z : LL k) :
    tensorMul q x (y+z) = tensorMul q x y + tensorMul q x z := by simp [tensorMul]
@[simp] theorem tensorMul_smul_left (r : k) (x y : LL k) :
    tensorMul q (r • x) y = r • tensorMul q x y := by simp [tensorMul]
@[simp] theorem tensorMul_smul_right (r : k) (x y : LL k) :
    tensorMul q x (r • y) = r • tensorMul q x y := by simp [tensorMul]

/-- The source rule on homogeneous word tensors, literal lists (zeros are units). -/
theorem tensorMul_hWords (α β γ δ : List ℕ) :
    tensorMul q (hWord k α ⊗ₜ[k] hWord k β) (hWord k γ ⊗ₜ[k] hWord k δ) =
      (q^(β.sum * γ.sum)) • ((hWord k α * hWord k γ) ⊗ₜ[k] (hWord k β * hWord k δ)) := by
  have ht := tensorMul_basis q (partWord α, partWord β) (partWord γ, partWord δ)
  simpa using ht

/-- Associativity of the q-twisted product (the q-exponent 2-cocycle identity). -/
theorem tensorMul_assoc (x y z : LL k) :
    tensorMul q (tensorMul q x y) z = tensorMul q x (tensorMul q y z) := by
  induction x using basis_induction k (tensorBasis k) with
  | hz => simp
  | ha x y hx hy => simp only [tensorMul_add_left, tensorMul_add_right, hx, hy]
  | hb p r =>
    induction y using basis_induction k (tensorBasis k) with
    | hz => simp
    | ha x y hx hy => simp only [tensorMul_add_left, tensorMul_add_right, hx, hy]
    | hb s u =>
      induction z using basis_induction k (tensorBasis k) with
      | hz => simp
      | ha x y hx hy => simp only [tensorMul_add_left, tensorMul_add_right, hx, hy]
      | hb t v =>
        simp only [tensorMul_smul_left, tensorMul_smul_right, tensorMul_basis,
          degree_mul, smul_smul, mul_assoc]
        congr 1
        simp only [pow_add, Nat.add_mul, Nat.mul_add]
        ring

variable (k) in
def tensorOne : LL k := (1 : L k) ⊗ₜ[k] (1 : L k)

theorem tensorOne_eq : tensorOne k = tensorBasis k ((1 : W), (1 : W)) := by
  simpa only [tensorOne, wordBasis_one] using (tensorBasis_apply k 1 1).symm

@[simp] theorem tensorMul_one_left (x : LL k) : tensorMul q (tensorOne k) x = x := by
  induction x using basis_induction k (tensorBasis k) with
  | hz => simp
  | ha x y hx hy => simp only [tensorMul_add_right, hx, hy]
  | hb p r => simp only [tensorOne_eq, tensorMul_smul_right, tensorMul_basis, degree_one,
      zero_mul, pow_zero, one_smul, one_mul]

@[simp] theorem tensorMul_one_right (x : LL k) : tensorMul q x (tensorOne k) = x := by
  induction x using basis_induction k (tensorBasis k) with
  | hz => simp
  | ha x y hx hy => simp only [tensorMul_add_left, hx, hy]
  | hb p r => simp only [tensorOne_eq, tensorMul_smul_left, tensorMul_basis, degree_one,
      mul_zero, pow_zero, one_smul, mul_one]

/-- `Λ'⊗Λ'` with the q-twisted product, as a type synonym (so the ordinary tensor
algebra structure cannot leak in). -/
def QTensor (_q : k) : Type _ := LL k

instance : AddCommGroup (QTensor q) := inferInstanceAs (AddCommGroup (LL k))
instance : Module k (QTensor q) := inferInstanceAs (Module k (LL k))

instance : Ring (QTensor q) where
  mul := tensorMul q
  one := tensorOne k
  mul_assoc := tensorMul_assoc q
  one_mul := tensorMul_one_left q
  mul_one := tensorMul_one_right q
  left_distrib := tensorMul_add_right q
  right_distrib := tensorMul_add_left q
  zero_mul := tensorMul_zero_left q
  mul_zero := tensorMul_zero_right q
  __ := inferInstanceAs (AddCommGroup (LL k))

/-- The q-twisted tensor algebra is a genuine `k`-algebra. -/
instance : Algebra k (QTensor q) :=
  Algebra.ofModule (tensorMul_smul_left q) (tensorMul_smul_right q)

/-- The identity map, from the q-twisted synonym back to the tensor module. -/
def qEquiv : QTensor q ≃ₗ[k] LL k := LinearEquiv.refl k (LL k)

variable (k) in
def generatorCoproduct (n : ℕ) : LL k :=
  ∑ i : Fin (n+1), h k i.val ⊗ₜ[k] h k (n-i.val)

/-- Δ as a `k`-algebra map into the q-twisted tensor algebra (EK p.5). -/
def coproductAlg : L k →ₐ[k] QTensor q :=
  FreeAlgebra.lift k (fun i => (generatorCoproduct k (i+1) : QTensor q))

/-- EK's Δ, linear on the actual tensor module. -/
def coproduct : L k →ₗ[k] LL k := (qEquiv q).toLinearMap.comp (coproductAlg q).toLinearMap

@[simp] theorem coproduct_one : coproduct q 1 = tensorOne k := (coproductAlg q).map_one

/-- Multiplicativity for the q-twisted product. -/
theorem coproduct_mul (x y : L k) :
    coproduct q (x*y) = tensorMul q (coproduct q x) (coproduct q y) :=
  (coproductAlg q).map_mul x y

/-- EK p.5 generator formula `Δ(hₙ) = Σ_{m=0}^n hₘ ⊗ h_{n-m}`, including `h₀`. -/
theorem coproduct_h (n : ℕ) : coproduct q (h k n) =
    ∑ i : Fin (n+1), h k i.val ⊗ₜ[k] h k (n-i.val) := by
  cases n with
  | zero => simp [tensorOne]
  | succ n =>
    exact FreeAlgebra.lift_ι_apply (A := QTensor q)
      (fun i => (generatorCoproduct k (i+1) : QTensor q)) n

/-- EK p.5 display: `Δ(hₙhₖ) = Σ_{m,r} q^{(n-m)r} hₘhᵣ ⊗ h_{n-m}h_{k-r}`. -/
theorem coproduct_two (n m : ℕ) : coproduct q (h k n * h k m) =
    ∑ i : Fin (n+1), ∑ j : Fin (m+1),
      (q^((n-i.val)*j.val)) • ((h k i.val * h k j.val) ⊗ₜ[k] (h k (n-i.val) * h k (m-j.val))) := by
  rw [coproduct_mul, coproduct_h, coproduct_h]
  simp only [tensorMul, map_sum, LinearMap.sum_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simpa [tensorMul, hWord] using tensorMul_hWords q [i.val] [n-i.val] [j.val] [m-j.val]

/-! ## Counit -/

variable (k) in
def counitAlg : L k →ₐ[k] k := FreeAlgebra.lift k (fun _ => 0)
variable (k) in
def counit : L k →ₗ[k] k := (counitAlg k).toLinearMap

@[simp] theorem counit_one : counit k 1 = 1 := (counitAlg k).map_one
@[simp] theorem counit_mul (x y : L k) : counit k (x*y) = counit k x * counit k y :=
  (counitAlg k).map_mul x y
@[simp] theorem counit_h_succ (n : ℕ) : counit k (h k (n+1)) = 0 :=
  FreeAlgebra.lift_ι_apply _ n

@[simp] theorem counit_word (w : W) :
    counit k (wordBasis k w) = if w = 1 then 1 else 0 := by
  induction w using FreeMonoid.recOn with
  | h0 => simp
  | ih i w ih => simp [counit_mul, wordBasis_mul, counit_h_succ]

@[simp] theorem counit_h (n : ℕ) : counit k (h k n) = if n=0 then 1 else 0 := by
  cases n <;> simp

variable (k) in
def leftCounit : LL k →ₗ[k] L k :=
  (TensorProduct.lid k (L k)).toLinearMap.comp (TensorProduct.map (counit k) LinearMap.id)
variable (k) in
def rightCounit : LL k →ₗ[k] L k :=
  (TensorProduct.rid k (L k)).toLinearMap.comp (TensorProduct.map LinearMap.id (counit k))

@[simp] theorem leftCounit_tmul (x y : L k) : leftCounit k (x ⊗ₜ[k] y) = counit k x • y := by
  simp [leftCounit]
@[simp] theorem rightCounit_tmul (x y : L k) : rightCounit k (x ⊗ₜ[k] y) = counit k y • x := by
  simp [rightCounit]

@[simp] theorem leftCounit_mul (x y : LL k) :
    leftCounit k (tensorMul q x y) = leftCounit k x * leftCounit k y := by
  induction x using basis_induction k (tensorBasis k) with
  | hz => simp
  | ha x y hx hy => simp only [tensorMul_add_left, map_add, hx, hy, add_mul]
  | hb p r =>
    induction y using basis_induction k (tensorBasis k) with
    | hz => simp
    | ha x y hx hy => simp only [tensorMul_add_right, map_add, hx, hy, mul_add]
    | hb s t =>
      rcases p with ⟨a,b⟩
      rcases s with ⟨c,d⟩
      simp only [tensorMul_smul_left, tensorMul_smul_right, tensorMul_basis]
      simp only [map_smul, tensorBasis_apply, wordBasis_mul, leftCounit_tmul,
        counit_mul, counit_word]
      by_cases ha : a = 1 <;> by_cases hc : c = 1 <;>
        simp [ha, hc, smul_smul, mul_comm, mul_left_comm, mul_assoc]

@[simp] theorem rightCounit_mul (x y : LL k) :
    rightCounit k (tensorMul q x y) = rightCounit k x * rightCounit k y := by
  induction x using basis_induction k (tensorBasis k) with
  | hz => simp
  | ha x y hx hy => simp only [tensorMul_add_left, map_add, hx, hy, add_mul]
  | hb p r =>
    induction y using basis_induction k (tensorBasis k) with
    | hz => simp
    | ha x y hx hy => simp only [tensorMul_add_right, map_add, hx, hy, mul_add]
    | hb s t =>
      rcases p with ⟨a,b⟩
      rcases s with ⟨c,d⟩
      simp only [tensorMul_smul_left, tensorMul_smul_right, tensorMul_basis]
      simp only [map_smul, tensorBasis_apply, wordBasis_mul, rightCounit_tmul,
        counit_mul, counit_word]
      by_cases hb : b = 1 <;> by_cases hd : d = 1 <;>
        simp [hb, hd, smul_smul, mul_comm, mul_left_comm, mul_assoc]

@[simp] theorem leftCounit_coproduct_h (n : ℕ) :
    leftCounit k (coproduct q (h k n)) = h k n := by
  rw [coproduct_h, map_sum]
  simp only [leftCounit_tmul, counit_h, ite_smul, one_smul, zero_smul]
  rw [Finset.sum_eq_single (0 : Fin (n+1))]
  · simp
  · intro b _ hb
    rw [if_neg]
    exact fun h => hb (Fin.ext h)
  · simp

@[simp] theorem rightCounit_coproduct_h (n : ℕ) :
    rightCounit k (coproduct q (h k n)) = h k n := by
  rw [coproduct_h, map_sum]
  simp only [rightCounit_tmul, counit_h, ite_smul, one_smul, zero_smul]
  rw [Finset.sum_eq_single (Fin.last n)]
  · simp
  · intro b _ hb
    rw [if_neg]
    intro h
    apply hb
    apply Fin.ext
    simp only [Fin.val_last]
    omega
  · simp

/-- Counitality on all of `Λ'`. -/
theorem counit_laws (x : L k) :
    leftCounit k (coproduct q x) = x ∧ rightCounit k (coproduct q x) = x := by
  induction x using basis_induction k (wordBasis k) with
  | hz => simp
  | ha x y hx hy => simp only [map_add, hx.1, hx.2, hy.1, hy.2, and_self]
  | hb w r =>
    suffices hw : leftCounit k (coproduct q (wordBasis k w)) = wordBasis k w ∧
        rightCounit k (coproduct q (wordBasis k w)) = wordBasis k w by
      simp only [map_smul, hw.1, hw.2, and_self]
    induction w using FreeMonoid.recOn with
    | h0 => simp [tensorOne]
    | ih i w ih =>
      simp only [wordBasis_mul, wordBasis_of, coproduct_mul, leftCounit_mul,
        rightCounit_mul, leftCounit_coproduct_h, rightCounit_coproduct_h, ih.1, ih.2,
        and_self]

/-! ## Grading and coassociativity -/

variable (k) in
/-- Degree-`d` part of `Λ'⊗Λ'`. -/
def tensorDegree (d : ℕ) : Submodule k (LL k) :=
  Submodule.span k {x | ∃ p : W × W, degree p.1 + degree p.2 = d ∧ tensorBasis k p = x}

theorem tensorDegree_basis (p : W × W) :
    tensorBasis k p ∈ tensorDegree k (degree p.1 + degree p.2) :=
  Submodule.subset_span ⟨p, rfl, rfl⟩

theorem tensorDegree_induction {d : ℕ} {x : LL k} (hx : x ∈ tensorDegree k d)
    (P : LL k → Prop) (hz : P 0) (ha : ∀ x y, P x → P y → P (x+y))
    (hs : ∀ (r : k) x, P x → P (r • x))
    (hb : ∀ p : W × W, degree p.1 + degree p.2 = d → P (tensorBasis k p)) : P x := by
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨p, hp, rfl⟩ := hx; exact hb p hp
  | zero => exact hz
  | add x y _ _ hx hy => exact ha x y hx hy
  | smul r x _ hx => exact hs r x hx

theorem tensorDegree_mul {m n : ℕ} {x y : LL k}
    (hx : x ∈ tensorDegree k m) (hy : y ∈ tensorDegree k n) :
    tensorMul q x y ∈ tensorDegree k (m+n) := by
  refine tensorDegree_induction hx (fun x => tensorMul q x y ∈ tensorDegree k (m+n))
    (by simp) ?_ ?_ ?_
  · intro x y hx hy
    simpa only [tensorMul_add_left] using Submodule.add_mem _ hx hy
  · intro r x hx
    simpa only [tensorMul_smul_left] using Submodule.smul_mem _ r hx
  · intro p hp
    refine tensorDegree_induction hy
      (fun y => tensorMul q (tensorBasis k p) y ∈ tensorDegree k (m+n)) (by simp) ?_ ?_ ?_
    · intro x y hx hy
      simpa only [tensorMul_add_right] using Submodule.add_mem _ hx hy
    · intro r x hx
      simpa only [tensorMul_smul_right] using Submodule.smul_mem _ r hx
    · intro s hs
      rw [tensorMul_basis]
      apply Submodule.smul_mem
      have hd : degree (p.1*s.1) + degree (p.2*s.2) = m+n := by
        simp only [degree_mul]; omega
      rw [← hd]
      exact tensorDegree_basis (p.1*s.1,p.2*s.2)

theorem coproduct_h_degree (n : ℕ) : coproduct q (h k n) ∈ tensorDegree k n := by
  rw [coproduct_h]
  apply Submodule.sum_mem
  intro i _
  have hd : degree (partWord [i.val]) + degree (partWord [n-i.val]) = n := by
    simp only [partWord_degree, List.sum_cons, List.sum_nil, add_zero]
    omega
  have hh := tensorDegree_basis (k := k) (partWord [i.val], partWord [n-i.val])
  rw [hd] at hh
  simpa [hWord] using hh

/-- Δ is a graded map: it sends a degree-`d` word into `(Λ'⊗Λ')_d`. -/
theorem coproduct_word_degree (w : W) :
    coproduct q (wordBasis k w) ∈ tensorDegree k (degree w) := by
  induction w using FreeMonoid.recOn with
  | h0 =>
    simpa only [wordBasis_one, coproduct_one, degree_one, zero_add,
      tensorBasis_apply, tensorOne] using tensorDegree_basis (k := k) (1,1)
  | ih i w ih =>
    rw [wordBasis_mul, wordBasis_of, coproduct_mul, degree_mul]
    exact tensorDegree_mul q (coproduct_h_degree q (i+1)) ih

variable (k) in
abbrev T3 := L k ⊗[k] LL k

variable (k) in
def tripleBasis : Basis (W × (W × W)) k (T3 k) := (wordBasis k).tensorProduct (tensorBasis k)

def tripleMulLinear : T3 k →ₗ[k] T3 k →ₗ[k] T3 k :=
  (tripleBasis k).constr k fun p => (tripleBasis k).constr k fun r =>
    (q^(degree p.2.1 * degree r.1 + degree p.2.2 * (degree r.1 + degree r.2.1))) •
      tripleBasis k (p.1*r.1, p.2.1*r.2.1, p.2.2*r.2.2)
def tripleMul (x y : T3 k) : T3 k := tripleMulLinear q x y

theorem tripleMul_basis (p r : W × (W × W)) :
    tripleMul q (tripleBasis k p) (tripleBasis k r) =
    (q^(degree p.2.1 * degree r.1 + degree p.2.2 * (degree r.1 + degree r.2.1))) •
      tripleBasis k (p.1*r.1, p.2.1*r.2.1, p.2.2*r.2.2) := by
  simp [tripleMul, tripleMulLinear]

def leftDelta : LL k →ₗ[k] T3 k :=
  (TensorProduct.assoc k (L k) (L k) (L k)).toLinearMap.comp
    (TensorProduct.map (coproduct q) LinearMap.id)
def rightDelta : LL k →ₗ[k] T3 k := TensorProduct.map LinearMap.id (coproduct q)

variable (k) in
def appendTensor (w : W) : LL k →ₗ[k] T3 k :=
  (TensorProduct.assoc k (L k) (L k) (L k)).toLinearMap.comp
    ((TensorProduct.mk k (LL k) (L k)).flip (wordBasis k w))
variable (k) in
def prependTensor (w : W) : LL k →ₗ[k] T3 k := TensorProduct.mk k (L k) (LL k) (wordBasis k w)

theorem appendTensor_basis (w : W) (p : W × W) :
    appendTensor k w (tensorBasis k p) = tripleBasis k (p.1,p.2,w) := by
  rcases p with ⟨a,b⟩
  simp [appendTensor, tripleBasis, tensorBasis]
theorem prependTensor_basis (w : W) (p : W × W) :
    prependTensor k w (tensorBasis k p) = tripleBasis k (w,p) := by
  simp [prependTensor, tripleBasis]

theorem leftDelta_basis (p : W × W) :
    leftDelta q (tensorBasis k p) = appendTensor k p.2 (coproduct q (wordBasis k p.1)) := by
  rcases p with ⟨a,b⟩
  simp [leftDelta, appendTensor]
theorem rightDelta_basis (p : W × W) :
    rightDelta q (tensorBasis k p) = prependTensor k p.1 (coproduct q (wordBasis k p.2)) := by
  rcases p with ⟨a,b⟩
  simp [rightDelta, prependTensor]

@[simp] theorem tripleMul_zero_left (x : T3 k) : tripleMul q 0 x = 0 := by
  simp [tripleMul]
@[simp] theorem tripleMul_zero_right (x : T3 k) : tripleMul q x 0 = 0 := by
  simp [tripleMul]
@[simp] theorem tripleMul_add_left (x y z : T3 k) :
    tripleMul q (x+y) z = tripleMul q x z + tripleMul q y z := by simp [tripleMul]
@[simp] theorem tripleMul_add_right (x y z : T3 k) :
    tripleMul q x (y+z) = tripleMul q x y + tripleMul q x z := by simp [tripleMul]
@[simp] theorem tripleMul_smul_left (r : k) (x y : T3 k) :
    tripleMul q (r • x) y = r • tripleMul q x y := by simp [tripleMul]
@[simp] theorem tripleMul_smul_right (r : k) (x y : T3 k) :
    tripleMul q x (r • y) = r • tripleMul q x y := by simp [tripleMul]

theorem appendTensor_mul (b d : W) (x y : LL k) (n : ℕ) (hy : y ∈ tensorDegree k n) :
    tripleMul q (appendTensor k b x) (appendTensor k d y) =
      (q^(degree b*n)) • appendTensor k (b*d) (tensorMul q x y) := by
  induction x using basis_induction k (tensorBasis k) with
  | hz => simp
  | ha x z hx hz =>
    simp only [map_add, tripleMul_add_left, tensorMul_add_left, smul_add, hx, hz]
  | hb p r =>
    refine tensorDegree_induction hy (fun y =>
      tripleMul q (appendTensor k b (r • tensorBasis k p)) (appendTensor k d y) =
        (q^(degree b*n)) • appendTensor k (b*d) (tensorMul q (r • tensorBasis k p) y))
      (by simp) ?_ ?_ ?_
    · intro y z hy hz
      simp only [map_add, tripleMul_add_right, tensorMul_add_right, smul_add, hy, hz]
    · intro s y hy
      simp only [map_smul] at hy
      simp only [map_smul, tripleMul_smul_right, tensorMul_smul_right, hy]
      exact smul_comm s (q^(degree b*n))
        (appendTensor k (b*d) (tensorMul q (r • tensorBasis k p) y))
    · intro s hs
      simp only [map_smul, tripleMul_smul_left, tensorMul_smul_left]
      rw [appendTensor_basis, appendTensor_basis, tripleMul_basis, tensorMul_basis,
        map_smul, appendTensor_basis]
      simp only [smul_smul, ← hs]
      congr 1
      simp only [pow_add]
      ring

theorem prependTensor_mul (a c : W) (x y : LL k) (m : ℕ) (hx : x ∈ tensorDegree k m) :
    tripleMul q (prependTensor k a x) (prependTensor k c y) =
      (q^(m*degree c)) • prependTensor k (a*c) (tensorMul q x y) := by
  refine tensorDegree_induction hx (fun x =>
    tripleMul q (prependTensor k a x) (prependTensor k c y) =
      (q^(m*degree c)) • prependTensor k (a*c) (tensorMul q x y))
    (by simp) ?_ ?_ ?_
  · intro x z hx hz
    simp only [map_add, tripleMul_add_left, tensorMul_add_left, smul_add, hx, hz]
  · intro r x hx
    simp only [map_smul, tripleMul_smul_left, tensorMul_smul_left, hx]
    exact smul_comm r _ _
  · intro p hp
    induction y using basis_induction k (tensorBasis k) with
    | hz => simp
    | ha y z hy hz =>
      simp only [map_add, tripleMul_add_right, tensorMul_add_right, smul_add, hy, hz]
    | hb s t =>
      simp only [map_smul, tripleMul_smul_right, tensorMul_smul_right]
      rw [prependTensor_basis, prependTensor_basis, tripleMul_basis, tensorMul_basis,
        map_smul, prependTensor_basis]
      simp only [smul_smul, ← hp]
      congr 1
      simp only [Nat.add_mul, Nat.mul_add, pow_add]
      ring

theorem leftDelta_mul (x y : LL k) :
    leftDelta q (tensorMul q x y) = tripleMul q (leftDelta q x) (leftDelta q y) := by
  induction x using basis_induction k (tensorBasis k) with
  | hz => simp
  | ha x y hx hy => simp only [tensorMul_add_left, map_add, tripleMul_add_left, hx, hy]
  | hb p r =>
    induction y using basis_induction k (tensorBasis k) with
    | hz => simp
    | ha x y hx hy => simp only [tensorMul_add_right, map_add, tripleMul_add_right, hx, hy]
    | hb s t =>
      simp only [tensorMul_smul_left, tensorMul_smul_right, tensorMul_basis,
        map_smul, tripleMul_smul_left, tripleMul_smul_right, leftDelta_basis,
        wordBasis_mul, coproduct_mul]
      rw [appendTensor_mul q _ _ _ _ _ (coproduct_word_degree q s.1)]

theorem rightDelta_mul (x y : LL k) :
    rightDelta q (tensorMul q x y) = tripleMul q (rightDelta q x) (rightDelta q y) := by
  induction x using basis_induction k (tensorBasis k) with
  | hz => simp
  | ha x y hx hy => simp only [tensorMul_add_left, map_add, tripleMul_add_left, hx, hy]
  | hb p r =>
    induction y using basis_induction k (tensorBasis k) with
    | hz => simp
    | ha x y hx hy => simp only [tensorMul_add_right, map_add, tripleMul_add_right, hx, hy]
    | hb s t =>
      simp only [tensorMul_smul_left, tensorMul_smul_right, tensorMul_basis,
        map_smul, tripleMul_smul_left, tripleMul_smul_right, rightDelta_basis,
        wordBasis_mul, coproduct_mul]
      rw [prependTensor_mul q _ _ _ _ _ (coproduct_word_degree q p.2)]

/-- Reindex the two parenthesizations by the same ordered three-part split. -/
def splitEquiv (n : ℕ) :
    (Σ i : Fin (n+1), Fin (i.val+1)) ≃ (Σ i : Fin (n+1), Fin (n-i.val+1)) where
  toFun p := ⟨⟨p.2.val, by have := p.1.isLt; have := p.2.isLt; omega⟩,
    ⟨p.1.val-p.2.val, by
      change p.1.val-p.2.val < n-p.2.val+1
      have := p.1.isLt; have := p.2.isLt; omega⟩⟩
  invFun p := ⟨⟨p.1.val+p.2.val, by have := p.1.isLt; have := p.2.isLt; omega⟩,
    ⟨p.1.val, by change p.1.val < p.1.val+p.2.val+1; omega⟩⟩
  left_inv p := by
    apply Sigma.ext
    · apply Fin.ext
      simp only
      have := p.2.isLt
      omega
    · apply (Fin.heq_ext_iff (by dsimp; have := p.2.isLt; omega)).2
      rfl
  right_inv p := by
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      apply Fin.ext
      simp

theorem split_sum (n : ℕ) (f : ℕ → ℕ → ℕ → T3 k) :
    (∑ i : Fin (n+1), ∑ j : Fin (i.val+1), f j.val (i.val-j.val) (n-i.val)) =
    ∑ i : Fin (n+1), ∑ j : Fin (n-i.val+1), f i.val j.val (n-i.val-j.val) := by
  have he := Fintype.sum_equiv (splitEquiv n)
    (fun p => f p.2.val (p.1.val-p.2.val) (n-p.1.val))
    (fun p => f p.1.val p.2.val (n-p.1.val-p.2.val)) (by
      intro p
      change f p.2.val (p.1.val-p.2.val) (n-p.1.val) =
        f p.2.val (p.1.val-p.2.val) (n-p.2.val-(p.1.val-p.2.val))
      congr 1
      have := p.1.isLt
      have := p.2.isLt
      omega)
  simpa only [Fintype.sum_sigma] using he

theorem coassociativity_h (n : ℕ) :
    leftDelta q (coproduct q (h k n)) = rightDelta q (coproduct q (h k n)) := by
  simp only [coproduct_h, map_sum, leftDelta, rightDelta, LinearMap.comp_apply,
    LinearEquiv.coe_coe, TensorProduct.map_tmul, LinearMap.id_apply]
  simp only [coproduct_h, TensorProduct.sum_tmul, TensorProduct.tmul_sum, map_sum,
    TensorProduct.assoc_tmul]
  exact split_sum n (fun i j l => h k i ⊗ₜ[k] (h k j ⊗ₜ[k] h k l))

/-- Coassociativity under the genuine tensor associator, for every `x ∈ Λ'`. -/
theorem coassociativity (x : L k) :
    TensorProduct.assoc k (L k) (L k) (L k)
        (TensorProduct.map (coproduct q) LinearMap.id (coproduct q x)) =
      TensorProduct.map LinearMap.id (coproduct q) (coproduct q x) := by
  change leftDelta q (coproduct q x) = rightDelta q (coproduct q x)
  induction x using basis_induction k (wordBasis k) with
  | hz => simp
  | ha x y hx hy => simp only [map_add, hx, hy]
  | hb w r =>
    simp only [map_smul]
    congr 1
    induction w using FreeMonoid.recOn with
    | h0 => simpa only [wordBasis_one, h_zero] using coassociativity_h q 0
    | ih i w ih =>
      simp only [wordBasis_mul, wordBasis_of, coproduct_mul, leftDelta_mul,
        rightDelta_mul, coassociativity_h, ih]

/-! ## The bilinear form (2.1) and its tensor extension (2.2) -/

open EKPairingMatrices (Mat crossing crossCols Splits upper lower transposeEquiv
  crossing_transpose eraseZeroEquiv crossing_erase_zero zero_row total_eq
  matrixEquivSplit crossing_joinMat SplitMatrices)
open EKPlatformBijection (DoubleCosets endpoint endpoint_monotone cosetLength
  doubleCosetEquiv cosetLength_eq_crossing)

/-- EK (2.1) on the equal-degree branch, literally: the sum over the actual double
cosets `S_β \ S_n / S_α` (top platforms `β`, bottom platforms `α`) of `q^{ℓ(c)}`, where
`ℓ(c)` is the inversion length of the unique minimal representative of `c`. -/
def sourceForm {r c : ℕ} (β : Fin r → ℕ) (α : Fin c → ℕ) (hd : (∑ i, β i) = ∑ j, α j) : k :=
  ∑ x : DoubleCosets (endpoint β rfl) (endpoint α hd.symm),
    q ^ cosetLength (endpoint_monotone β rfl) (endpoint_monotone α hd.symm) x

/-- EK (2.1) including the orthogonal branch `|α| ≠ |β|`. -/
def sourceFormAll {r c : ℕ} (β : Fin r → ℕ) (α : Fin c → ℕ) : k :=
  if hd : (∑ i, β i) = ∑ j, α j then sourceForm q β α hd else 0

/-- Matrix/crossing expression of the form (proved equal to (2.1) below). -/
def matForm {r c : ℕ} (β : Fin r → ℕ) (α : Fin c → ℕ) : k :=
  ∑ M : Mat β α, q ^ crossing M

theorem matForm_degree_mismatch {r c : ℕ} (β : Fin r → ℕ) (α : Fin c → ℕ)
    (hd : (∑ i, β i) ≠ ∑ j, α j) : matForm q β α = 0 := by
  haveI : IsEmpty (Mat β α) := ⟨fun M => hd (total_eq M)⟩
  exact Finset.sum_eq_zero (fun M _ => isEmptyElim M)

theorem sourceForm_eq_matForm {r c : ℕ} (β : Fin r → ℕ) (α : Fin c → ℕ)
    (hd : (∑ i, β i) = ∑ j, α j) : sourceForm q β α hd = matForm q β α := by
  unfold sourceForm matForm
  apply Fintype.sum_equiv (doubleCosetEquiv β α hd)
  intro x
  exact congrArg (fun n => q^n) (cosetLength_eq_crossing β α hd x)

theorem sourceFormAll_eq_matForm {r c : ℕ} (β : Fin r → ℕ) (α : Fin c → ℕ) :
    sourceFormAll q β α = matForm q β α := by
  unfold sourceFormAll
  split_ifs with hd
  · exact sourceForm_eq_matForm q β α hd
  · exact (matForm_degree_mismatch q β α hd).symm

theorem matForm_transpose {r c : ℕ} (β : Fin r → ℕ) (α : Fin c → ℕ) :
    matForm q β α = matForm q α β := by
  unfold matForm
  apply Fintype.sum_equiv (transposeEquiv β α)
  intro M
  exact congrArg (fun n => q ^ n) (crossing_transpose M).symm

theorem matForm_erase_zero_row {r c : ℕ} (β : Fin (r+1) → ℕ) (α : Fin c → ℕ)
    (p : Fin (r+1)) (hp : β p = 0) :
    matForm q β α = matForm q (fun i => β (p.succAbove i)) α := by
  unfold matForm
  apply Fintype.sum_equiv (eraseZeroEquiv β α p hp)
  intro M
  exact congrArg (fun n => q ^ n) (crossing_erase_zero p M (zero_row M p hp)).symm

theorem matForm_erase_zero_column {r c : ℕ} (β : Fin r → ℕ) (α : Fin (c+1) → ℕ)
    (p : Fin (c+1)) (hp : α p = 0) :
    matForm q β α = matForm q β (fun j => α (p.succAbove j)) := by
  rw [matForm_transpose q β α, matForm_erase_zero_row q α β p hp,
    matForm_transpose q (fun j => α (p.succAbove j)) β]

/-- Row-block convolution: the combinatorial core of Proposition 2.2 at general q. -/
theorem matForm_convolution {r s c : ℕ}
    (β : Fin r → ℕ) (γ : Fin s → ℕ) (α : Fin c → ℕ) :
    matForm q (Fin.addCases β γ) α =
      ∑ u : Splits α, q ^ crossCols (upper u) (lower u) *
        matForm q β (upper u) * matForm q γ (lower u) := by
  classical
  unfold matForm
  rw [← (matrixEquivSplit β γ α).symm.sum_comp (fun M => q ^ crossing M)]
  change (∑ z : SplitMatrices β γ α, q ^ crossing (EKPairingMatrices.joinMat z)) = _
  simp only [crossing_joinMat, pow_add, Fintype.sum_sigma, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl; intro u _
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro U _
  apply Finset.sum_congr rfl; intro V _
  ring

/-- Platform list of a basis word (all parts positive). -/
abbrev parts (w : W) : Fin w.toList.length → ℕ := EKPairingAdjoint.parts w

variable (k) in
/-- Ordered product indexed by a tuple (zero parts are `h₀ = 1`). -/
def vWord {n : ℕ} (α : Fin n → ℕ) : L k := hWord k (List.ofFn α)

/-- EK (2.1) as a `k`-bilinear form on `Λ'`: on the word basis `h_β, h_α` it is the
source double-coset sum `sourceFormAll`. -/
def form : L k →ₗ[k] L k →ₗ[k] k :=
  (wordBasis k).constr k fun v => (wordBasis k).constr k fun w =>
    sourceFormAll q (parts v) (parts w)

@[simp] theorem form_basis (v w : W) :
    form q (wordBasis k v) (wordBasis k w) = sourceFormAll q (parts v) (parts w) := by
  simp [form]

theorem form_basis_mat (v w : W) :
    form q (wordBasis k v) (wordBasis k w) = matForm q (parts v) (parts w) := by
  rw [form_basis, sourceFormAll_eq_matForm]

/-- (2.1) is symmetric. -/
theorem form_symm (x y : L k) : form q x y = form q y x := by
  induction x using basis_induction k (wordBasis k) with
  | hz => simp
  | ha x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz]
  | hb v r =>
    induction y using basis_induction k (wordBasis k) with
    | hz => simp
    | ha y z hy hz => simp only [map_add, LinearMap.add_apply, hy, hz]
    | hb w t => simp only [map_smul, LinearMap.smul_apply, form_basis_mat, smul_eq_mul,
        matForm_transpose q (parts v) (parts w)]; ring

@[simp] theorem vWord_nil (α : Fin 0 → ℕ) : vWord k α = 1 := by
  simp [vWord, hWord]

theorem vWord_succ {n : ℕ} (α : Fin (n+1) → ℕ) :
    vWord k α = h k (α 0) * vWord k (fun i => α i.succ) := by
  simp [vWord, List.ofFn_succ, hWord]

theorem vWord_erase_zero {n : ℕ} (α : Fin (n+1) → ℕ) (p : Fin (n+1)) (hp : α p = 0) :
    vWord k α = vWord k (fun i => α (p.succAbove i)) := by
  induction n with
  | zero =>
    have hα : α = fun _ => 0 := by
      funext i; have hi : i = p := Fin.ext (by omega); simpa [hi] using hp
    simp [hα, vWord, List.ofFn_succ, hWord]
  | succ n ih =>
    revert hp
    refine Fin.cases ?_ (fun p => ?_) p
    · intro hp
      rw [vWord_succ, hp, h_zero, one_mul]
      rfl
    · intro hp
      conv_lhs => rw [vWord_succ]
      conv_rhs => rw [vWord_succ]
      simp only [Fin.succ_succAbove_zero, Fin.succ_succAbove_succ]
      rw [ih (fun i => α i.succ) p hp]

@[simp] theorem vWord_parts (w : W) : vWord k (parts w) = wordBasis k w := by
  have hl : List.ofFn (parts w) = w.toList.map (·+1) := by
    exact List.ext_get (by simp) (by intro n h₁ h₂; simp [parts, EKPairingAdjoint.parts])
  rw [vWord, hl, ← partWord_value]
  congr 1
  clear hl
  induction w using FreeMonoid.recOn with
  | h0 => rfl
  | ih i w ih => simpa [partWord] using congrArg (FreeMonoid.of i * ·) ih

theorem form_vWord_positive {r c : ℕ} (β : Fin r → ℕ) (α : Fin c → ℕ)
    (hβ : ∀ i, 0 < β i) (hα : ∀ i, 0 < α i) :
    form q (vWord k β) (vWord k α) = matForm q β α := by
  have hb := EKPairingAdjoint.partWord_positive (List.ofFn β) (by simpa using hβ)
  have ha := EKPairingAdjoint.partWord_positive (List.ofFn α) (by simpa using hα)
  rw [vWord, vWord, ← partWord_value, ← partWord_value, form_basis_mat]
  unfold parts EKPairingAdjoint.parts
  simp only [hb, ha, List.length_map, List.length_ofFn, List.get_eq_getElem,
    List.getElem_map, List.getElem_ofFn]
  congr 1
  · simp [hb]
  · simp [ha]
  · apply Function.hfunext (by simp [hb])
    intro i j hij
    have hv : i.val = j.val := Fin.val_eq_val_of_heq hij
    have he : (⟨i.val, by simpa [hb] using i.isLt⟩ : Fin r) = j := Fin.ext hv
    simpa only [he, heq_eq_eq] using Nat.succ_pred_eq_of_pos (hβ j)
  · apply Function.hfunext (by simp [ha])
    intro i j hij
    have hv : i.val = j.val := Fin.val_eq_val_of_heq hij
    have he : (⟨i.val, by simpa [ha] using i.isLt⟩ : Fin c) = j := Fin.ext hv
    simpa only [he, heq_eq_eq] using Nat.succ_pred_eq_of_pos (hα j)

/-- Zero platforms are erased, consistently with `h₀ = 1`. -/
theorem form_vWord {r c : ℕ} (β : Fin r → ℕ) (α : Fin c → ℕ) :
    form q (vWord k β) (vWord k α) = matForm q β α := by
  induction r generalizing c with
  | zero =>
    induction c with
    | zero => exact form_vWord_positive q β α (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
    | succ c ih =>
      by_cases hz : ∃ p, α p = 0
      · obtain ⟨p, hp⟩ := hz
        rw [vWord_erase_zero α p hp, matForm_erase_zero_column q β α p hp]
        exact ih _
      · exact form_vWord_positive q β α (fun i => Fin.elim0 i)
          (fun i => Nat.pos_of_ne_zero (fun h => hz ⟨i,h⟩))
  | succ r ih =>
    by_cases hz : ∃ p, β p = 0
    · obtain ⟨p, hp⟩ := hz
      rw [vWord_erase_zero β p hp, matForm_erase_zero_row q β α p hp]
      exact ih _ _
    · have hb : ∀ i, 0 < β i := fun i => Nat.pos_of_ne_zero (fun h => hz ⟨i,h⟩)
      induction c with
      | zero => exact form_vWord_positive q β α hb (fun i => Fin.elim0 i)
      | succ c ihc =>
        by_cases hz : ∃ p, α p = 0
        · obtain ⟨p, hp⟩ := hz
          rw [vWord_erase_zero α p hp, matForm_erase_zero_column q β α p hp]
          exact ihc _
        · exact form_vWord_positive q β α hb (fun i => Nat.pos_of_ne_zero (fun h => hz ⟨i,h⟩))

/-- EK (2.1) exactly as printed, for arbitrary literal sequences `β, α` (zero parts
allowed, `h₀ = 1`): `(h_β, h_α) = Σ_{c ∈ βS_α} q^{ℓ(c)}` if `|α| = |β|`, else `0`. -/
theorem form_hWords (β α : List ℕ) :
    form q (hWord k β) (hWord k α) = sourceFormAll q β.get α.get := by
  rw [sourceFormAll_eq_matForm]
  simpa only [vWord, List.ofFn_get] using form_vWord q β.get α.get

variable (k) in
/-- EK (2.2): `(y₁⊗y₂, x₁⊗x₂) = (y₁,x₁)(y₂,x₂)`, with no power of q. -/
def tensorFormAux (q : k) : LL k →ₗ[k] LL k →ₗ[k] k := TensorProduct.lift
  { toFun := fun a =>
      { toFun := fun b => TensorProduct.lift
          ((LinearMap.mul k k).compl₁₂ (form q a) (form q b))
        map_add' := by intros b c; ext x y; simp [mul_add]
        map_smul' := by
          intros r b; ext x y
          change form q a x * form q (r • b) y = r • (form q a x * form q b y)
          simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
          ring }
    map_add' := by intros a b; ext c x y; simp [add_mul]
    map_smul' := by
      intros r a; ext b x y
      change form q (r • a) x * form q b y = r • (form q a x * form q b y)
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
      ring }

def tensorForm : LL k →ₗ[k] LL k →ₗ[k] k := tensorFormAux k q

@[simp] theorem tensorForm_tmul (a b c d : L k) :
    tensorForm q (a ⊗ₜ[k] b) (c ⊗ₜ[k] d) = form q a c * form q b d := by
  simp [tensorForm, tensorFormAux]

theorem tensorForm_symm (x y : LL k) : tensorForm q x y = tensorForm q y x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz]
  | tmul a b =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y z hy hz => simp only [map_add, LinearMap.add_apply, hy, hz]
    | tmul c d => simp only [tensorForm_tmul, form_symm q a c, form_symm q b d]

theorem vWord_join {r s : ℕ} (β : Fin r → ℕ) (γ : Fin s → ℕ) :
    vWord k (Fin.addCases β γ) = vWord k β * vWord k γ := by
  have hw (a b : List ℕ) : hWord k (a ++ b) = hWord k a * hWord k b := by
    induction a with
    | nil => simp [hWord]
    | cons n a ih => simp [hWord, ih, mul_assoc]
  unfold vWord
  rw [List.ofFn_add]
  simpa using hw (List.ofFn β) (List.ofFn γ)

@[simp] theorem vWord_singleton (n : ℕ) : vWord k (fun _ : Fin 1 => n) = h k n := by
  simp [vWord, List.ofFn_succ, hWord]

theorem tensorMul_vWords {r s c d : ℕ} (α : Fin r → ℕ) (β : Fin s → ℕ)
    (γ : Fin c → ℕ) (δ : Fin d → ℕ) :
    tensorMul q (vWord k α ⊗ₜ[k] vWord k β) (vWord k γ ⊗ₜ[k] vWord k δ) =
      q^((∑ i, β i)*(∑ j, γ j)) •
        ((vWord k α * vWord k γ) ⊗ₜ[k] (vWord k β * vWord k δ)) := by
  simpa only [vWord, List.sum_ofFn] using
    tensorMul_hWords q (List.ofFn α) (List.ofFn β) (List.ofFn γ) (List.ofFn δ)

/-- Δ on an arbitrary ordered product: all coordinate splits, with the crossings
forced by the q-twisted multiplication. -/
theorem coproduct_vWord {c : ℕ} (α : Fin c → ℕ) :
    coproduct q (vWord k α) =
      ∑ u : Splits α, q^crossCols (upper u) (lower u) •
          (vWord k (upper u) ⊗ₜ[k] vWord k (lower u)) := by
  induction c with
  | zero => simp [crossCols, tensorOne]
  | succ c ih =>
    rw [vWord_succ, coproduct_mul, coproduct_h, ih]
    rw [← (Fin.insertNthEquiv (fun j => Fin (α j + 1)) 0).sum_comp]
    simp only [Fintype.sum_prod_type]
    simp only [tensorMul, map_sum, LinearMap.sum_apply]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro u _
    change tensorMul q _ _ = _
    rw [tensorMul_smul_right]
    have hm := tensorMul_vWords q (fun _ : Fin 1 => i.val)
      (fun _ : Fin 1 => α 0-i.val) (upper u) (lower u)
    simp only [vWord_singleton, Fin.sum_univ_one] at hm
    rw [hm]
    simp only [Fin.insertNthEquiv, Equiv.coe_fn_mk, Fin.insertNth_zero,
      EKPairingAdjoint.crossCols_succ, Fin.cons_zero, Fin.cons_succ, vWord_succ, pow_add,
      smul_smul]
    congr 1
    change q^crossCols (upper u) (lower u) * q^((α 0-i.val)*(∑ j, (u j).val)) =
      q^((∑ j, (u j).val)*(α 0-i.val)) * q^crossCols (upper u) (lower u)
    rw [Nat.mul_comm]
    ring

theorem adjointness_vWords {r s c : ℕ} (β : Fin r → ℕ) (γ : Fin s → ℕ) (α : Fin c → ℕ) :
    tensorForm q (vWord k β ⊗ₜ[k] vWord k γ) (coproduct q (vWord k α)) =
      form q (vWord k β * vWord k γ) (vWord k α) := by
  rw [coproduct_vWord, ← vWord_join, form_vWord, matForm_convolution]
  simp only [map_sum, map_smul, tensorForm_tmul, form_vWord, smul_eq_mul, mul_assoc]

theorem adjointness_basis (u v w : W) :
    tensorForm q (wordBasis k u ⊗ₜ[k] wordBasis k v) (coproduct q (wordBasis k w)) =
      form q (wordBasis k u * wordBasis k v) (wordBasis k w) := by
  simpa only [vWord_parts] using adjointness_vWords q (parts u) (parts v) (parts w)

/-- EK Proposition 2.2, (2.3), at arbitrary `q` over an arbitrary commutative ring:
`(y₁⊗y₂, Δ(x)) = (y₁y₂, x)` for all `x, y₁, y₂ ∈ Λ'`. -/
theorem adjointness (x y₁ y₂ : L k) :
    tensorForm q (y₁ ⊗ₜ[k] y₂) (coproduct q x) = form q (y₁*y₂) x := by
  induction x using basis_induction k (wordBasis k) with
  | hz => simp
  | ha x z hx hz => simp only [map_add, hx, hz]
  | hb w r =>
    simp only [map_smul]
    congr 1
    induction y₁ using basis_induction k (wordBasis k) with
    | hz => simp
    | ha a b ha hb =>
      simp only [TensorProduct.add_tmul, map_add, LinearMap.add_apply, add_mul, ha, hb]
    | hb u s =>
      simp only [← TensorProduct.smul_tmul', map_smul, LinearMap.smul_apply, smul_mul_assoc]
      congr 1
      induction y₂ using basis_induction k (wordBasis k) with
      | hz => simp
      | ha a b ha hb =>
        simp only [TensorProduct.tmul_add, map_add, LinearMap.add_apply, mul_add, ha, hb]
      | hb v t =>
        simp only [TensorProduct.tmul_smul, map_smul, LinearMap.smul_apply, mul_smul_comm]
        rw [adjointness_basis]

/-! ## Main theorem (arbitrary commutative `k`, arbitrary `q : k`) -/

variable (k) in
/-- EK §2.1 at general q, as printed: `Λ'` with the q-twisted Δ is a q-bialgebra
(the q-twisted product on `Λ'⊗Λ'` is associative and unital; Δ is given on generators
by EK p.5, is unital, multiplicative for the q-twisted product, graded, coassociative
and counital; ε is multiplicative and kills positive degree), the form is (2.1) on
every `h_β, h_α`, it is symmetric, its tensor extension is (2.2), and Proposition 2.2
(2.3) holds. -/
theorem ek_sec21_general_q (q : k) :
    (∀ x y z : LL k, tensorMul q (tensorMul q x y) z = tensorMul q x (tensorMul q y z)) ∧
    (∀ x : LL k, tensorMul q (tensorOne k) x = x ∧ tensorMul q x (tensorOne k) = x) ∧
    (∀ n, coproduct q (h k n) = ∑ i : Fin (n+1), h k i.val ⊗ₜ[k] h k (n-i.val)) ∧
    coproduct q 1 = tensorOne k ∧
    (∀ x y : L k, coproduct q (x*y) = tensorMul q (coproduct q x) (coproduct q y)) ∧
    (∀ w : W, coproduct q (wordBasis k w) ∈ tensorDegree k (degree w)) ∧
    (∀ x : L k, TensorProduct.assoc k (L k) (L k) (L k)
        (TensorProduct.map (coproduct q) LinearMap.id (coproduct q x)) =
      TensorProduct.map LinearMap.id (coproduct q) (coproduct q x)) ∧
    (∀ x : L k, TensorProduct.lid k (L k)
        (TensorProduct.map (counit k) LinearMap.id (coproduct q x)) = x ∧
      TensorProduct.rid k (L k)
        (TensorProduct.map LinearMap.id (counit k) (coproduct q x)) = x) ∧
    counit k 1 = 1 ∧
    (∀ x y : L k, counit k (x*y) = counit k x * counit k y) ∧
    (∀ n, counit k (h k (n+1)) = 0) ∧
    (∀ β α : List ℕ, form q (hWord k β) (hWord k α) = sourceFormAll q β.get α.get) ∧
    (∀ x y : L k, form q x y = form q y x) ∧
    (∀ a b c d : L k, tensorForm q (a ⊗ₜ[k] b) (c ⊗ₜ[k] d) = form q a c * form q b d) ∧
    (∀ x y₁ y₂ : L k, tensorForm q (y₁ ⊗ₜ[k] y₂) (coproduct q x) = form q (y₁*y₂) x) :=
  ⟨tensorMul_assoc q, fun x => ⟨tensorMul_one_left q x, tensorMul_one_right q x⟩,
    coproduct_h q, coproduct_one q, coproduct_mul q, coproduct_word_degree q,
    coassociativity q, fun x => counit_laws q x, counit_one, counit_mul, counit_h_succ,
    form_hWords q, form_symm q, tensorForm_tmul q, adjointness q⟩

/-! ## Specialization to the existing `q = -1`, `k = ℤ` objects -/

theorem h_int (n : ℕ) : h ℤ n = CompleteElementary.h n := by cases n <;> rfl

theorem tensorMul_neg_one (x y : LL ℤ) :
    tensorMul (-1 : ℤ) x y = EKFreeCoproduct.tensorMul x y := by
  induction x using basis_induction ℤ (tensorBasis ℤ) with
  | hz => simp
  | ha x z hx hz => rw [tensorMul_add_left, EKFreeCoproduct.tensorMul_add_left, hx, hz]
  | hb p r =>
    induction y using basis_induction ℤ (tensorBasis ℤ) with
    | hz => simp
    | ha y z hy hz => rw [tensorMul_add_right, EKFreeCoproduct.tensorMul_add_right, hy, hz]
    | hb t s =>
      rw [tensorMul_smul_left, tensorMul_smul_right, EKFreeCoproduct.tensorMul_smul_left,
        EKFreeCoproduct.tensorMul_smul_right, tensorMul_basis]
      exact congrArg (fun z => r • s • z) (EKFreeCoproduct.tensorMul_basis p t).symm

theorem coproduct_neg_one (x : L ℤ) :
    coproduct (-1 : ℤ) x = EKFreeCoproduct.coproduct x := by
  induction x using basis_induction ℤ (wordBasis ℤ) with
  | hz => simp
  | ha x z hx hz => rw [map_add, map_add, hx, hz]
  | hb w r =>
    rw [map_smul, map_smul]
    congr 1
    induction w using FreeMonoid.recOn with
    | h0 => rw [wordBasis_one, coproduct_one, EKFreeCoproduct.coproduct_one]; rfl
    | ih i w ih =>
      rw [wordBasis_mul, wordBasis_of, coproduct_mul, ih, tensorMul_neg_one,
        coproduct_h, h_int]
      change _ = EKFreeCoproduct.coproduct
        (CompleteElementary.h (i+1) * EKFreeCoproduct.wordBasis w)
      rw [EKFreeCoproduct.coproduct_mul, EKFreeCoproduct.coproduct_h]
      simp only [h_int]
      rfl

theorem counit_neg_one (x : L ℤ) : counit ℤ x = EKFreeCoproduct.counit x := rfl

theorem matForm_neg_one {r c : ℕ} (β : Fin r → ℕ) (α : Fin c → ℕ) :
    matForm (-1 : ℤ) β α = EKPairingMatrices.pairing β α := rfl

theorem sourceFormAll_neg_one {r c : ℕ} (β : Fin r → ℕ) (α : Fin c → ℕ) :
    sourceFormAll (-1 : ℤ) β α = EKPlatformBijection.sourcePairingAll β α := by
  rw [sourceFormAll_eq_matForm, matForm_neg_one,
    EKPlatformBijection.sourcePairingAll_eq_pairing]

theorem form_neg_one (x y : L ℤ) : form (-1 : ℤ) x y = EKPairingAdjoint.pairing x y := by
  induction x using basis_induction ℤ (wordBasis ℤ) with
  | hz => simp
  | ha x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz]
  | hb v r =>
    induction y using basis_induction ℤ (wordBasis ℤ) with
    | hz => simp
    | ha y z hy hz => simp only [map_add, LinearMap.add_apply, hy, hz]
    | hb w t =>
      simp only [map_smul, LinearMap.smul_apply, form_basis_mat, matForm_neg_one]
      rw [show wordBasis ℤ = EKFreeCoproduct.wordBasis from rfl,
        EKPairingAdjoint.pairing_basis]

theorem tensorForm_neg_one (x y : LL ℤ) :
    tensorForm (-1 : ℤ) x y = EKPairingAdjoint.tensorPairing x y := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz]
  | tmul a b =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y z hy hz => simp only [map_add, LinearMap.add_apply, hy, hz]
    | tmul c d =>
      rw [tensorForm_tmul, EKPairingAdjoint.tensorPairing_tmul, form_neg_one, form_neg_one]

/-- ONE theorem: at `k = ℤ`, `q = -1` every general-q object is the existing one
(`CompleteElementary.h`, `EKFreeCoproduct.tensorMul/coproduct/counit`,
`EKPlatformBijection.sourcePairingAll`, `EKPairingAdjoint.pairing/tensorPairing`),
and the existing q=-1 adjointness and coassociativity are recovered as instances of
the general-q theorems. -/
theorem specialization_neg_one :
    (∀ n, h ℤ n = CompleteElementary.h n) ∧
    (∀ x y : LL ℤ, tensorMul (-1 : ℤ) x y = EKFreeCoproduct.tensorMul x y) ∧
    (∀ x : L ℤ, coproduct (-1 : ℤ) x = EKFreeCoproduct.coproduct x) ∧
    (∀ x : L ℤ, counit ℤ x = EKFreeCoproduct.counit x) ∧
    (∀ (r c : ℕ) (β : Fin r → ℕ) (α : Fin c → ℕ),
      sourceFormAll (-1 : ℤ) β α = EKPlatformBijection.sourcePairingAll β α) ∧
    (∀ x y : L ℤ, form (-1 : ℤ) x y = EKPairingAdjoint.pairing x y) ∧
    (∀ x y : LL ℤ, tensorForm (-1 : ℤ) x y = EKPairingAdjoint.tensorPairing x y) ∧
    (∀ x y₁ y₂ : CompleteElementary.A,
      EKPairingAdjoint.tensorPairing (y₁ ⊗ₜ[ℤ] y₂) (EKFreeCoproduct.coproduct x) =
        EKPairingAdjoint.pairing (y₁*y₂) x) ∧
    (∀ x : CompleteElementary.A,
      TensorProduct.assoc ℤ CompleteElementary.A CompleteElementary.A CompleteElementary.A
        (TensorProduct.map EKFreeCoproduct.coproduct LinearMap.id (EKFreeCoproduct.coproduct x)) =
      TensorProduct.map LinearMap.id EKFreeCoproduct.coproduct (EKFreeCoproduct.coproduct x)) := by
  refine ⟨h_int, tensorMul_neg_one, coproduct_neg_one, counit_neg_one,
    fun _ _ => sourceFormAll_neg_one, form_neg_one, tensorForm_neg_one, ?_, ?_⟩
  · intro x y₁ y₂
    rw [← coproduct_neg_one, ← tensorForm_neg_one, ← form_neg_one]
    exact adjointness (-1 : ℤ) x y₁ y₂
  · intro x
    have hc : (EKFreeCoproduct.coproduct : CompleteElementary.A →ₗ[ℤ] _) =
        coproduct (-1 : ℤ) := LinearMap.ext fun z => (coproduct_neg_one z).symm
    rw [hc]
    exact coassociativity (-1 : ℤ) x

end OddMath.Frontier.EKGeneralQ
