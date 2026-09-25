import OddMath.Frontier.CompleteElementary
import Mathlib.LinearAlgebra.FreeAlgebra
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Associator

/-!
# EK's odd free-h coproduct
Source: Ellis–Khovanov 1107.5610v2 §2.1, p.5. Integer, q=-1 specialization.
All constructions use the actual free algebra and its genuine tensor module.
No radical quotient, pairing adjointness, or general-q claim is made here.
-/
noncomputable section
open scoped TensorProduct BigOperators
namespace OddMath.Frontier.EKFreeCoproduct
open CompleteElementary
attribute [local instance] Classical.propDecidable

abbrev W := FreeMonoid ℕ
abbrev T := A ⊗[ℤ] A

def wordBasis : Basis W ℤ A := FreeAlgebra.basisFreeMonoid ℤ ℕ

def degree (w : W) : ℕ := (w.toList.map (· + 1)).sum

@[simp] theorem degree_one : degree (1 : W) = 0 := rfl
@[simp] theorem degree_mul (u v : W) : degree (u*v) = degree u + degree v := by
  simp [degree]

theorem wordBasis_eq (w : W) : wordBasis w =
    (FreeAlgebra.equivMonoidAlgebraFreeMonoid : A ≃ₐ[ℤ] MonoidAlgebra ℤ W).symm
      (MonoidAlgebra.single w 1) := rfl

@[simp] theorem wordBasis_one : wordBasis (1 : W) = (1 : A) := by
  rw [wordBasis_eq, ← MonoidAlgebra.one_def, map_one]

@[simp] theorem wordBasis_mul (u v : W) : wordBasis (u*v) = wordBasis u * wordBasis v := by
  simp only [wordBasis_eq, ← map_mul, MonoidAlgebra.single_mul_single, one_mul]

@[simp] theorem wordBasis_of (i : ℕ) : wordBasis (FreeMonoid.of i) = h (i+1) := by
  rw [wordBasis_eq]
  apply (FreeAlgebra.equivMonoidAlgebraFreeMonoid : A ≃ₐ[ℤ] MonoidAlgebra ℤ W).injective
  rw [AlgEquiv.apply_symm_apply]
  change _ = FreeAlgebra.lift ℤ (fun x => MonoidAlgebra.single (FreeMonoid.of x) 1)
    (FreeAlgebra.ι ℤ i)
  simp

def tensorBasis : Basis (W × W) ℤ T := wordBasis.tensorProduct wordBasis
@[simp] theorem tensorBasis_apply (u v : W) :
    tensorBasis (u,v) = wordBasis u ⊗ₜ[ℤ] wordBasis v := by
  simp [tensorBasis]

/-- The basis representation is a proved linear equivalence, not a toy carrier. -/
def tensorCoordinates : T ≃ₗ[ℤ] ((W × W) →₀ ℤ) := tensorBasis.repr

/-- Bilinear Koszul multiplication; first right crosses second left. -/
def tensorMulLinear : T →ₗ[ℤ] T →ₗ[ℤ] T :=
  tensorBasis.constr ℤ fun p => tensorBasis.constr ℤ fun q =>
    ((-1 : ℤ)^(degree p.2 * degree q.1)) • tensorBasis (p.1*q.1,p.2*q.2)

def tensorMul (x y : T) : T := tensorMulLinear x y

@[simp] theorem tensorMul_basis (p q : W × W) :
    tensorMul (tensorBasis p) (tensorBasis q) =
      ((-1 : ℤ)^(degree p.2 * degree q.1)) • tensorBasis (p.1*q.1,p.2*q.2) := by
  simp [tensorMul, tensorMulLinear]

@[simp] theorem tensorMul_zero_left (x : T) : tensorMul 0 x = 0 := by
  simp [tensorMul]
@[simp] theorem tensorMul_zero_right (x : T) : tensorMul x 0 = 0 := by
  simp [tensorMul]
@[simp] theorem tensorMul_add_left (x y z : T) :
    tensorMul (x+y) z = tensorMul x z + tensorMul y z := by simp [tensorMul]
@[simp] theorem tensorMul_add_right (x y z : T) :
    tensorMul x (y+z) = tensorMul x y + tensorMul x z := by simp [tensorMul]
@[simp] theorem tensorMul_smul_left (r : ℤ) (x y : T) :
    tensorMul (r • x) y = r • tensorMul x y := by simp [tensorMul]
@[simp] theorem tensorMul_smul_right (r : ℤ) (x y : T) :
    tensorMul x (r • y) = r • tensorMul x y := by simp [tensorMul]

/-- Basis induction used only to extend the source word laws by linearity. -/
private theorem basis_induction {M I : Type*} [AddCommGroup M]
    (b : Basis I ℤ M) (P : M → Prop) (hz : P 0)
    (ha : ∀ x y, P x → P y → P (x+y))
    (hb : ∀ i (r : ℤ), P (r • b i)) (x : M) : P x := by
  obtain ⟨f, rfl⟩ := b.repr.symm.surjective x
  induction f using Finsupp.induction_linear with
  | zero => simpa using hz
  | add f g hf hg => simpa using ha _ _ hf hg
  | single i r => simpa using hb i r

/-- Associativity is the Koszul 2-cocycle identity on genuine tensor words. -/
theorem tensorMul_assoc (x y z : T) :
    tensorMul (tensorMul x y) z = tensorMul x (tensorMul y z) := by
  induction x using basis_induction tensorBasis with
  | hz => simp
  | ha x y hx hy => simp only [tensorMul_add_left, tensorMul_add_right, hx, hy]
  | hb p r =>
    induction y using basis_induction tensorBasis with
    | hz => simp
    | ha x y hx hy => simp only [tensorMul_add_left, tensorMul_add_right, hx, hy]
    | hb q s =>
      induction z using basis_induction tensorBasis with
      | hz => simp
      | ha x y hx hy => simp only [tensorMul_add_left, tensorMul_add_right, hx, hy]
      | hb t u =>
        simp only [tensorMul_smul_left, tensorMul_smul_right, tensorMul_basis,
          degree_mul, smul_smul, Prod.fst, Prod.snd, mul_assoc]
        congr 1
        simp only [pow_add, Nat.add_mul, Nat.mul_add]
        ring

def tensorOne : T := (1 : A) ⊗ₜ[ℤ] (1 : A)

@[simp] theorem tensorMul_one_left (x : T) : tensorMul tensorOne x = x := by
  have he : tensorOne = tensorBasis (1,1) := by
    simpa only [tensorOne, wordBasis_one] using (tensorBasis_apply 1 1).symm
  induction x using basis_induction tensorBasis with
  | hz => simp
  | ha x y hx hy => simp only [tensorMul_add_right, hx, hy]
  | hb p r => simp only [he, tensorMul_smul_right, tensorMul_basis, degree_one,
      zero_mul, pow_zero, one_smul, one_mul]

@[simp] theorem tensorMul_one_right (x : T) : tensorMul x tensorOne = x := by
  have he : tensorOne = tensorBasis (1,1) := by
    simpa only [tensorOne, wordBasis_one] using (tensorBasis_apply 1 1).symm
  induction x using basis_induction tensorBasis with
  | hz => simp
  | ha x y hx hy => simp only [tensorMul_add_left, hx, hy]
  | hb p r => simp only [he, tensorMul_smul_left, tensorMul_basis, degree_one,
      mul_zero, pow_zero, one_smul, mul_one]

/-- A type synonym isolates the signed ring from the ordinary tensor ring. -/
def SignedTensor := T
instance : AddCommGroup SignedTensor := inferInstanceAs (AddCommGroup T)
instance : Ring SignedTensor where
  mul := tensorMul
  one := tensorOne
  mul_assoc := tensorMul_assoc
  one_mul := tensorMul_one_left
  mul_one := tensorMul_one_right
  left_distrib := tensorMul_add_right
  right_distrib := tensorMul_add_left
  zero_mul := tensorMul_zero_left
  mul_zero := tensorMul_zero_right
  __ := inferInstanceAs (AddCommGroup T)

/-- The algebra structure uses integer scaling; it does not change tensor addition. -/
instance : Algebra ℤ SignedTensor := Ring.toIntAlgebra SignedTensor

def signedEquiv : SignedTensor ≃ₗ[ℤ] T := LinearEquiv.refl ℤ T

def generatorCoproduct (n : ℕ) : T :=
  ∑ i : Fin (n+1), h i.val ⊗ₜ[ℤ] h (n-i.val)

def coproductAlg : A →ₐ[ℤ] SignedTensor :=
  FreeAlgebra.lift ℤ (fun i => generatorCoproduct (i+1))

/-- Genuine free-algebra coproduct, linear on the actual integer tensor module. -/
def coproduct : A →ₗ[ℤ] T := signedEquiv.toLinearMap.comp coproductAlg.toLinearMap

@[simp] theorem coproduct_one : coproduct 1 = tensorOne := coproductAlg.map_one

theorem coproduct_mul (x y : A) :
    coproduct (x*y) = tensorMul (coproduct x) (coproduct y) := coproductAlg.map_mul x y

/-- EK p.5 generator formula, including the unit h_0. -/
theorem coproduct_h (n : ℕ) : coproduct (h n) =
    ∑ i : Fin (n+1), h i.val ⊗ₜ[ℤ] h (n-i.val) := by
  cases n with
  | zero => simp [tensorOne]
  | succ n =>
    exact FreeAlgebra.lift_ι_apply (A := SignedTensor) (fun i => generatorCoproduct (i+1)) n

/-- Convert literal part lists (zeros are units) to the true positive-generator basis. -/
def partWord : List ℕ → W
  | [] => 1
  | 0 :: α => partWord α
  | (n+1) :: α => FreeMonoid.of n * partWord α

@[simp] theorem partWord_degree (α : List ℕ) : degree (partWord α) = α.sum := by
  induction α with
  | nil => rfl
  | cons n α ih =>
    have hd (i : ℕ) : degree (FreeMonoid.of i) = i+1 := by simp [degree]
    cases n <;> simp only [partWord, degree_mul, hd, ih, List.sum_cons, zero_add]

@[simp] theorem partWord_value (α : List ℕ) : wordBasis (partWord α) = hWord α := by
  induction α with
  | nil => simp [partWord, hWord]
  | cons n α ih =>
    cases n <;> simp [partWord, ih, hWord]

/-- Source Koszul rule, with the literal hWord part convention, zeros included. -/
theorem tensorMul_hWords (α β γ δ : List ℕ) :
    tensorMul (hWord α ⊗ₜ[ℤ] hWord β) (hWord γ ⊗ₜ[ℤ] hWord δ) =
      ((-1 : ℤ)^(β.sum * γ.sum)) •
        ((hWord α * hWord γ) ⊗ₜ[ℤ] (hWord β * hWord δ)) := by
  have ht := tensorMul_basis (partWord α,partWord β) (partWord γ,partWord δ)
  simpa using ht

/-- EK's two-generator formula for arbitrary degrees, not a numerical check. -/
theorem coproduct_two (n k : ℕ) : coproduct (h n * h k) =
    ∑ i : Fin (n+1), ∑ j : Fin (k+1),
      ((-1 : ℤ)^((n-i.val)*j.val)) •
        ((h i.val * h j.val) ⊗ₜ[ℤ] (h (n-i.val) * h (k-j.val))) := by
  rw [coproduct_mul, coproduct_h, coproduct_h]
  simp only [tensorMul, map_sum, LinearMap.sum_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simpa [tensorMul, hWord] using tensorMul_hWords [i.val] [n-i.val] [j.val] [k-j.val]

def counitAlg : A →ₐ[ℤ] ℤ := FreeAlgebra.lift ℤ (fun _ => 0)
def counit : A →ₗ[ℤ] ℤ := counitAlg.toLinearMap

@[simp] theorem counit_one : counit 1 = 1 := counitAlg.map_one
@[simp] theorem counit_mul (x y : A) : counit (x*y) = counit x * counit y :=
  counitAlg.map_mul x y
@[simp] theorem counit_h_succ (n : ℕ) : counit (h (n+1)) = 0 :=
  FreeAlgebra.lift_ι_apply _ n

@[simp] theorem counit_word (w : W) : counit (wordBasis w) = if w = 1 then 1 else 0 := by
  induction w using FreeMonoid.recOn with
  | h0 => simp
  | ih i w ih => simp [counit_mul, wordBasis_mul, counit_h_succ]

def leftCounit : T →ₗ[ℤ] A :=
  (TensorProduct.lid ℤ A).toLinearMap.comp (TensorProduct.map counit LinearMap.id)
def rightCounit : T →ₗ[ℤ] A :=
  (TensorProduct.rid ℤ A).toLinearMap.comp (TensorProduct.map LinearMap.id counit)

@[simp] theorem leftCounit_tmul (x y : A) : leftCounit (x ⊗ₜ[ℤ] y) = counit x • y := by
  simp [leftCounit]
@[simp] theorem rightCounit_tmul (x y : A) : rightCounit (x ⊗ₜ[ℤ] y) = counit y • x := by
  simp [rightCounit]

@[simp] theorem leftCounit_mul (x y : T) :
    leftCounit (tensorMul x y) = leftCounit x * leftCounit y := by
  induction x using basis_induction tensorBasis with
  | hz => simp
  | ha x y hx hy => simp only [tensorMul_add_left, map_add, hx, hy, add_mul]
  | hb p r =>
    induction y using basis_induction tensorBasis with
    | hz => simp
    | ha x y hx hy => simp only [tensorMul_add_right, map_add, hx, hy, mul_add]
    | hb q s =>
      rcases p with ⟨a,b⟩
      rcases q with ⟨c,d⟩
      simp only [tensorMul_smul_left, tensorMul_smul_right, tensorMul_basis]
      simp only [map_smul, tensorBasis_apply, wordBasis_mul, leftCounit_tmul,
        counit_mul, counit_word, Prod.fst, Prod.snd]
      by_cases ha : a = 1 <;> by_cases hc : c = 1 <;>
        simp only [ha, hc, if_pos, if_neg, degree_one, zero_mul, mul_zero,
          pow_zero, one_smul, zero_smul, smul_zero, one_mul, mul_one,
          smul_mul_assoc, mul_smul_comm, ite_false]

@[simp] theorem rightCounit_mul (x y : T) :
    rightCounit (tensorMul x y) = rightCounit x * rightCounit y := by
  induction x using basis_induction tensorBasis with
  | hz => simp
  | ha x y hx hy => simp only [tensorMul_add_left, map_add, hx, hy, add_mul]
  | hb p r =>
    induction y using basis_induction tensorBasis with
    | hz => simp
    | ha x y hx hy => simp only [tensorMul_add_right, map_add, hx, hy, mul_add]
    | hb q s =>
      rcases p with ⟨a,b⟩
      rcases q with ⟨c,d⟩
      simp only [tensorMul_smul_left, tensorMul_smul_right, tensorMul_basis]
      simp only [map_smul, tensorBasis_apply, wordBasis_mul, rightCounit_tmul,
        counit_mul, counit_word, Prod.fst, Prod.snd]
      by_cases hb : b = 1 <;> by_cases hd : d = 1 <;>
        simp only [hb, hd, if_pos, if_neg, degree_one, zero_mul, mul_zero,
          pow_zero, one_smul, zero_smul, smul_zero, one_mul, mul_one,
          smul_mul_assoc, mul_smul_comm, ite_false]

@[simp] theorem counit_h (n : ℕ) : counit (h n) = if n=0 then 1 else 0 := by
  cases n <;> simp

@[simp] theorem leftCounit_coproduct_h (n : ℕ) : leftCounit (coproduct (h n)) = h n := by
  rw [coproduct_h, map_sum]
  simp only [leftCounit_tmul, counit_h, ite_smul, one_smul, zero_smul]
  rw [Finset.sum_eq_single (0 : Fin (n+1))]
  · simp
  · intro b _ hb
    rw [if_neg]
    exact fun h => hb (Fin.ext h)
  · simp

@[simp] theorem rightCounit_coproduct_h (n : ℕ) : rightCounit (coproduct (h n)) = h n := by
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

/-- Both actual counit composites are the identity, on all free algebra elements. -/
theorem counit_laws (x : A) : leftCounit (coproduct x) = x ∧ rightCounit (coproduct x) = x := by
  induction x using basis_induction wordBasis with
  | hz => simp
  | ha x y hx hy => simp only [map_add, hx.1, hx.2, hy.1, hy.2, and_self]
  | hb w r =>
    suffices hw : leftCounit (coproduct (wordBasis w)) = wordBasis w ∧
        rightCounit (coproduct (wordBasis w)) = wordBasis w by
      simp only [map_smul, hw.1, hw.2, and_self]
    induction w using FreeMonoid.recOn with
    | h0 => simp [tensorOne]
    | ih i w ih =>
      simp only [wordBasis_mul, wordBasis_of, coproduct_mul, leftCounit_mul,
        rightCounit_mul, leftCounit_coproduct_h, rightCounit_coproduct_h, ih.1, ih.2,
        and_self]

theorem counit_left (x : A) : TensorProduct.lid ℤ A
    (TensorProduct.map counit LinearMap.id (coproduct x)) = x := (counit_laws x).1

theorem counit_right (x : A) : TensorProduct.rid ℤ A
    (TensorProduct.map LinearMap.id counit (coproduct x)) = x := (counit_laws x).2

/-- Actual degree-d submodule of the tensor algebra; used to discharge the
Koszul exponent when extending Δ to three tensor factors. -/
def tensorDegree (d : ℕ) : Submodule ℤ T :=
  Submodule.span ℤ {x | ∃ p : W × W, degree p.1 + degree p.2 = d ∧ tensorBasis p = x}

private theorem tensorDegree_basis (p : W × W) :
    tensorBasis p ∈ tensorDegree (degree p.1 + degree p.2) :=
  Submodule.subset_span ⟨p, rfl, rfl⟩

private theorem tensorDegree_induction {d : ℕ} {x : T} (hx : x ∈ tensorDegree d)
    (P : T → Prop) (hz : P 0) (ha : ∀ x y, P x → P y → P (x+y))
    (hs : ∀ (r : ℤ) x, P x → P (r • x))
    (hb : ∀ p : W × W, degree p.1 + degree p.2 = d → P (tensorBasis p)) : P x := by
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨p, hp, rfl⟩ := hx; exact hb p hp
  | zero => exact hz
  | add x y _ _ hx hy => exact ha x y hx hy
  | smul r x _ hx => exact hs r x hx

private theorem tensorDegree_mul {m n : ℕ} {x y : T}
    (hx : x ∈ tensorDegree m) (hy : y ∈ tensorDegree n) :
    tensorMul x y ∈ tensorDegree (m+n) := by
  refine tensorDegree_induction hx (fun x => tensorMul x y ∈ tensorDegree (m+n))
    (by simp) ?_ ?_ ?_
  · intro x y hx hy
    simpa only [tensorMul_add_left] using Submodule.add_mem _ hx hy
  · intro r x hx
    simpa only [tensorMul_smul_left] using Submodule.smul_mem _ r hx
  · intro p hp
    refine tensorDegree_induction hy (fun y => tensorMul (tensorBasis p) y ∈ tensorDegree (m+n))
      (by simp) ?_ ?_ ?_
    · intro x y hx hy
      simpa only [tensorMul_add_right] using Submodule.add_mem _ hx hy
    · intro r x hx
      simpa only [tensorMul_smul_right] using Submodule.smul_mem _ r hx
    · intro q hq
      rw [tensorMul_basis]
      apply Submodule.smul_mem
      have hd : degree (p.1*q.1) + degree (p.2*q.2) = m+n := by
        simp only [degree_mul]; omega
      rw [← hd]
      exact tensorDegree_basis (p.1*q.1,p.2*q.2)

private theorem coproduct_h_degree (n : ℕ) : coproduct (h n) ∈ tensorDegree n := by
  rw [coproduct_h]
  apply Submodule.sum_mem
  intro i _
  have hd : degree (partWord [i.val]) + degree (partWord [n-i.val]) = n := by
    simp only [partWord_degree, List.sum_cons, List.sum_nil, add_zero]
    omega
  have hh := tensorDegree_basis (partWord [i.val], partWord [n-i.val])
  rw [hd] at hh
  simpa [hWord] using hh

/-- Degree preservation on every genuine free-algebra basis word. -/
theorem coproduct_word_degree (w : W) : coproduct (wordBasis w) ∈ tensorDegree (degree w) := by
  induction w using FreeMonoid.recOn with
  | h0 =>
    simpa only [wordBasis_one, coproduct_one, degree_one, zero_add,
      tensorBasis_apply, tensorOne] using tensorDegree_basis (1,1)
  | ih i w ih =>
    rw [wordBasis_mul, wordBasis_of, coproduct_mul, degree_mul]
    exact tensorDegree_mul (coproduct_h_degree (i+1)) ih

abbrev T3 := A ⊗[ℤ] T
private def tripleBasis : Basis (W × (W × W)) ℤ T3 := wordBasis.tensorProduct tensorBasis
private def tripleMulLinear : T3 →ₗ[ℤ] T3 →ₗ[ℤ] T3 :=
  tripleBasis.constr ℤ fun p => tripleBasis.constr ℤ fun q =>
    ((-1 : ℤ)^(degree p.2.1 * degree q.1 + degree p.2.2 * (degree q.1 + degree q.2.1))) •
      tripleBasis (p.1*q.1, p.2.1*q.2.1, p.2.2*q.2.2)
private def tripleMul (x y : T3) : T3 := tripleMulLinear x y

private theorem tripleMul_basis (p q : W × (W × W)) :
    tripleMul (tripleBasis p) (tripleBasis q) =
    ((-1 : ℤ)^(degree p.2.1 * degree q.1 + degree p.2.2 * (degree q.1 + degree q.2.1))) •
      tripleBasis (p.1*q.1, p.2.1*q.2.1, p.2.2*q.2.2) := by
  simp [tripleMul, tripleMulLinear]

private def leftDelta : T →ₗ[ℤ] T3 :=
  (TensorProduct.assoc ℤ A A A).toLinearMap.comp (TensorProduct.map coproduct LinearMap.id)
private def rightDelta : T →ₗ[ℤ] T3 := TensorProduct.map LinearMap.id coproduct

private def appendTensor (w : W) : T →ₗ[ℤ] T3 :=
  (TensorProduct.assoc ℤ A A A).toLinearMap.comp
    ((TensorProduct.mk ℤ T A).flip (wordBasis w))
private def prependTensor (w : W) : T →ₗ[ℤ] T3 := TensorProduct.mk ℤ A T (wordBasis w)

private theorem appendTensor_basis (w : W) (p : W × W) :
    appendTensor w (tensorBasis p) = tripleBasis (p.1,p.2,w) := by
  rcases p with ⟨a,b⟩
  simp [appendTensor, tripleBasis, tensorBasis]
private theorem prependTensor_basis (w : W) (p : W × W) :
    prependTensor w (tensorBasis p) = tripleBasis (w,p) := by
  simp [prependTensor, tripleBasis]

private theorem leftDelta_basis (p : W × W) :
    leftDelta (tensorBasis p) = appendTensor p.2 (coproduct (wordBasis p.1)) := by
  rcases p with ⟨a,b⟩
  simp [leftDelta, appendTensor]
private theorem rightDelta_basis (p : W × W) :
    rightDelta (tensorBasis p) = prependTensor p.1 (coproduct (wordBasis p.2)) := by
  rcases p with ⟨a,b⟩
  simp [rightDelta, prependTensor]

@[simp] private theorem tripleMul_zero_left (x : T3) : tripleMul 0 x = 0 := by
  simp [tripleMul]
@[simp] private theorem tripleMul_zero_right (x : T3) : tripleMul x 0 = 0 := by
  simp [tripleMul]
@[simp] private theorem tripleMul_add_left (x y z : T3) :
    tripleMul (x+y) z = tripleMul x z + tripleMul y z := by simp [tripleMul]
@[simp] private theorem tripleMul_add_right (x y z : T3) :
    tripleMul x (y+z) = tripleMul x y + tripleMul x z := by simp [tripleMul]
@[simp] private theorem tripleMul_smul_left (r : ℤ) (x y : T3) :
    tripleMul (r • x) y = r • tripleMul x y := by simp [tripleMul]
@[simp] private theorem tripleMul_smul_right (r : ℤ) (x y : T3) :
    tripleMul x (r • y) = r • tripleMul x y := by simp [tripleMul]

/-- The left extension's only sign premise is the total degree of its second Δ factor. -/
private theorem appendTensor_mul (b d : W) (x y : T) (n : ℕ) (hy : y ∈ tensorDegree n) :
    tripleMul (appendTensor b x) (appendTensor d y) =
      ((-1 : ℤ)^(degree b*n)) • appendTensor (b*d) (tensorMul x y) := by
  induction x using basis_induction tensorBasis with
  | hz => simp
  | ha x z hx hz =>
    simp only [map_add, tripleMul_add_left, tensorMul_add_left, smul_add, hx, hz]
  | hb p r =>
    refine tensorDegree_induction hy (fun y =>
      tripleMul (appendTensor b (r • tensorBasis p)) (appendTensor d y) =
        ((-1 : ℤ)^(degree b*n)) • appendTensor (b*d) (tensorMul (r • tensorBasis p) y))
      (by simp) ?_ ?_ ?_
    · intro y z hy hz
      simp only [map_add, tripleMul_add_right, tensorMul_add_right, smul_add, hy, hz]
    · intro s y hy
      simp only [map_smul] at hy
      simp only [map_smul, tripleMul_smul_right, tensorMul_smul_right, hy]
      exact smul_comm s ((-1 : ℤ)^(degree b*n)) (appendTensor (b*d) (tensorMul (r • tensorBasis p) y))
    · intro q hq
      simp only [map_smul, tripleMul_smul_left, tensorMul_smul_left]
      rw [appendTensor_basis, appendTensor_basis, tripleMul_basis, tensorMul_basis,
        map_smul, appendTensor_basis]
      simp only [smul_smul, Prod.fst, Prod.snd, ← hq]
      congr 1
      simp only [pow_add]
      ring

/-- The right extension uses the total degree of its first Δ factor. -/
private theorem prependTensor_mul (a c : W) (x y : T) (m : ℕ) (hx : x ∈ tensorDegree m) :
    tripleMul (prependTensor a x) (prependTensor c y) =
      ((-1 : ℤ)^(m*degree c)) • prependTensor (a*c) (tensorMul x y) := by
  refine tensorDegree_induction hx (fun x =>
    tripleMul (prependTensor a x) (prependTensor c y) =
      ((-1 : ℤ)^(m*degree c)) • prependTensor (a*c) (tensorMul x y))
    (by simp) ?_ ?_ ?_
  · intro x z hx hz
    simp only [map_add, tripleMul_add_left, tensorMul_add_left, smul_add, hx, hz]
  · intro r x hx
    simp only [map_smul, tripleMul_smul_left, tensorMul_smul_left, hx]
    exact smul_comm r _ _
  · intro p hp
    induction y using basis_induction tensorBasis with
    | hz => simp
    | ha y z hy hz =>
      simp only [map_add, tripleMul_add_right, tensorMul_add_right, smul_add, hy, hz]
    | hb q s =>
      simp only [map_smul, tripleMul_smul_right, tensorMul_smul_right]
      rw [prependTensor_basis, prependTensor_basis, tripleMul_basis, tensorMul_basis,
        map_smul, prependTensor_basis]
      simp only [smul_smul, Prod.fst, Prod.snd, ← hp]
      congr 1
      simp only [Nat.add_mul, Nat.mul_add, pow_add]
      ring

private theorem leftDelta_mul (x y : T) :
    leftDelta (tensorMul x y) = tripleMul (leftDelta x) (leftDelta y) := by
  induction x using basis_induction tensorBasis with
  | hz => simp
  | ha x y hx hy => simp only [tensorMul_add_left, map_add, tripleMul_add_left, hx, hy]
  | hb p r =>
    induction y using basis_induction tensorBasis with
    | hz => simp
    | ha x y hx hy => simp only [tensorMul_add_right, map_add, tripleMul_add_right, hx, hy]
    | hb q s =>
      simp only [tensorMul_smul_left, tensorMul_smul_right, tensorMul_basis,
        map_smul, tripleMul_smul_left, tripleMul_smul_right, leftDelta_basis,
        wordBasis_mul, coproduct_mul]
      rw [appendTensor_mul _ _ _ _ _ (coproduct_word_degree q.1)]

private theorem rightDelta_mul (x y : T) :
    rightDelta (tensorMul x y) = tripleMul (rightDelta x) (rightDelta y) := by
  induction x using basis_induction tensorBasis with
  | hz => simp
  | ha x y hx hy => simp only [tensorMul_add_left, map_add, tripleMul_add_left, hx, hy]
  | hb p r =>
    induction y using basis_induction tensorBasis with
    | hz => simp
    | ha x y hx hy => simp only [tensorMul_add_right, map_add, tripleMul_add_right, hx, hy]
    | hb q s =>
      simp only [tensorMul_smul_left, tensorMul_smul_right, tensorMul_basis,
        map_smul, tripleMul_smul_left, tripleMul_smul_right, rightDelta_basis,
        wordBasis_mul, coproduct_mul]
      rw [prependTensor_mul _ _ _ _ _ (coproduct_word_degree p.2)]

/-- Reindex the two parenthesizations by the same ordered three-part split. -/
private def splitEquiv (n : ℕ) :
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

private theorem split_sum (n : ℕ) (f : ℕ → ℕ → ℕ → T3) :
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

private theorem coassociativity_h (n : ℕ) :
    leftDelta (coproduct (h n)) = rightDelta (coproduct (h n)) := by
  simp only [coproduct_h, map_sum, leftDelta, rightDelta, LinearMap.comp_apply,
    LinearEquiv.coe_coe, TensorProduct.map_tmul, LinearMap.id_apply]
  simp only [coproduct_h, TensorProduct.sum_tmul, TensorProduct.tmul_sum, map_sum,
    TensorProduct.assoc_tmul]
  exact split_sum n (fun i j k => h i ⊗ₜ[ℤ] (h j ⊗ₜ[ℤ] h k))

/-- Coassociativity under the genuine tensor associator, for every free-algebra element. -/
theorem coassociativity (x : A) :
    TensorProduct.assoc ℤ A A A (TensorProduct.map coproduct LinearMap.id (coproduct x)) =
      TensorProduct.map LinearMap.id coproduct (coproduct x) := by
  change leftDelta (coproduct x) = rightDelta (coproduct x)
  induction x using basis_induction wordBasis with
  | hz => simp
  | ha x y hx hy => simp only [map_add, hx, hy]
  | hb w r =>
    simp only [map_smul]
    congr 1
    induction w using FreeMonoid.recOn with
    | h0 => simpa only [wordBasis_one, h_zero] using coassociativity_h 0
    | ih i w ih =>
      simp only [wordBasis_mul, wordBasis_of, coproduct_mul, leftDelta_mul,
        rightDelta_mul, coassociativity_h, ih]

end OddMath.Frontier.EKFreeCoproduct
