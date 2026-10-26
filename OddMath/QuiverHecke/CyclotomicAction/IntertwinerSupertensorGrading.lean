/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.IntertwinerSupertensorScalars

/-!
# Homogeneous right polynomial supertensor actions

The ordered tensor `t^m ⊗ c`, with `c` of parity `q`, acts with parity
`m p(i) + q` on the source and shifted target of the moving-strand map.
The homogeneous tensor component is the ground-ring span of these tensors;
thus the action theorem includes arbitrary finite homogeneous balanced tensors.
The proofs use the existing dot and coefficient actions and keep the quotient
superspaces and target shift unchanged. Q is the previously proved even map.

This is the homogeneous-action step toward KKO I Proposition 8.4, not a
signed-left superlinearity assertion, a QP identity, or nondegeneracy.
-/

noncomputable section
open CategoryTheory StringDiagrams Categorification Supercategory
open scoped TensorProduct
namespace OddMath.QuiverHecke
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
variable (i : I) (a : I → _root_.Polynomial k)
  (ha : CyclotomicPolynomialParity D a) (n : ℕ)

private theorem end_pow_parity {V : SVec k} {p : ZMod 2} (T : Module.End k V)
    (hT : SVec.ofHom T ∈ SVec.parityHom V V p) (m : ℕ) :
    SVec.ofHom (T ^ m) ∈ SVec.parityHom V V ((m : ZMod 2) * p) := by
  induction m with
  | zero =>
    apply SVec.mem_parityHom_of_apply_mem
    intro q x hx
    simpa using hx
  | succ m ih =>
    apply SVec.mem_parityHom_of_apply_mem
    intro q x hx
    have h := SVec.apply_mem_part hT (SVec.apply_mem_part ih hx)
    simpa only [pow_succ', Module.End.mul_apply, SVec.ofHom_apply,
      Nat.cast_succ, add_mul, one_mul, add_assoc] using h

/-- Dot-first monomials have the sum of the dot and coefficient degrees. -/
theorem sourceRightMonomial_parity (m : ℕ) (q : ZMod 2)
    (c : CyclotomicAlgebra D Sc a n) (hc : c ∈ cyclotomicParity D Sc a ha n q) :
    SVec.ofHom (sourceRightMonomial D Sc i a ha n m c) ∈
      SVec.parityHom (qSourceSpace D Sc i a ha n) (qSourceSpace D Sc i a ha n)
        ((m : ZMod 2) * D.parity i + q) := by
  apply SVec.mem_parityHom_of_apply_mem
  intro r x hx
  have h := SVec.apply_mem_part (sourceRightCoefficient_parity D Sc i a ha n q c hc)
    (SVec.apply_mem_part (end_pow_parity _ (sourceRightDot_parity D Sc i a ha n) m) hx)
  simpa only [sourceRightMonomial, targetRightMonomial, AddMonoidHom.coe_mk,
    ZeroHom.coe_mk, SVec.ofHom_apply, Module.End.mul_apply, add_assoc] using h

/-- The target shift does not alter the degree of a right monomial. -/
theorem targetRightMonomial_parity (β : Multiset I) (m : ℕ) (q : ZMod 2)
    (c : CyclotomicAlgebra D Sc a n) (hc : c ∈ cyclotomicParity D Sc a ha n q) :
    SVec.ofHom (targetRightMonomial D Sc i β a ha n m c) ∈
      SVec.parityHom (qTargetSpace D Sc i β a ha n) (qTargetSpace D Sc i β a ha n)
        ((m : ZMod 2) * D.parity i + q) := by
  apply SVec.mem_parityHom_of_apply_mem
  intro r x hx
  have h := SVec.apply_mem_part (targetRightCoefficient_parity D Sc i β a ha n q c hc)
    (SVec.apply_mem_part (end_pow_parity _ (targetRightDot_parity D Sc i β a ha n) m) hx)
  simpa only [sourceRightMonomial, targetRightMonomial, AddMonoidHom.coe_mk,
    ZeroHom.coe_mk, SVec.ofHom_apply, Module.End.mul_apply, add_assoc] using h

/-- The degree component in the scalar-balanced polynomial tensor product.
Membership permits arbitrary finite sums and ground-ring scalar multiples. -/
def polynomialSupertensorPart (d : ZMod 2) :
    Submodule k (_root_.Polynomial k ⊗[k] CyclotomicAlgebra D Sc a n) :=
  Submodule.span k {z | ∃ (m : ℕ) (q : ZMod 2) (c : CyclotomicAlgebra D Sc a n),
    c ∈ cyclotomicParity D Sc a ha n q ∧ (m : ZMod 2) * D.parity i + q = d ∧
      z = ((_root_.Polynomial.X : _root_.Polynomial k) ^ m) ⊗ₜ[k] c}

/-- A homogeneous pure tensor belongs to its prescribed component. -/
theorem polynomialSupertensor_tmul_mem (m : ℕ) (q : ZMod 2)
    (c : CyclotomicAlgebra D Sc a n) (hc : c ∈ cyclotomicParity D Sc a ha n q) :
    ((_root_.Polynomial.X : _root_.Polynomial k) ^ m) ⊗ₜ[k] c ∈
      polynomialSupertensorPart D Sc i a ha n ((m : ZMod 2) * D.parity i + q) :=
  Submodule.subset_span ⟨m, q, c, hc, rfl, rfl⟩

/-- Every finite homogeneous balanced tensor acts with its degree on the source. -/
theorem sourceRightSupertensor_parity (d : ZMod 2)
    (f : _root_.Polynomial k ⊗[k] CyclotomicAlgebra D Sc a n)
    (hf : f ∈ polynomialSupertensorPart D Sc i a ha n d) :
    SVec.ofHom (sourceRightSupertensor D Sc i a ha n f).unop ∈
      SVec.parityHom (qSourceSpace D Sc i a ha n) (qSourceSpace D Sc i a ha n) d := by
  induction hf using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨m, q, c, hc, hd, rfl⟩ := hz
    rw [sourceRightSupertensor_tmul, ← hd]
    exact sourceRightMonomial_parity D Sc i a ha n m q c hc
  | zero =>
    rw [(sourceRightSupertensor D Sc i a ha n).map_zero]
    change (0 : qSourceSpace D Sc i a ha n ⟶ qSourceSpace D Sc i a ha n) ∈ _
    exact (SVec.parityHom _ _ d).zero_mem
  | add x y _ _ hx hy =>
    rw [(sourceRightSupertensor D Sc i a ha n).map_add]
    exact (SVec.parityHom _ _ d).add_mem hx hy
  | smul r x _ hx =>
    rw [sourceRightSupertensor_smul]
    exact (SVec.parityHom _ _ d).smul_mem r hx

/-- The same degree statement retains the target's coefficient parity shift. -/
theorem targetRightSupertensor_parity (β : Multiset I) (d : ZMod 2)
    (f : _root_.Polynomial k ⊗[k] CyclotomicAlgebra D Sc a n)
    (hf : f ∈ polynomialSupertensorPart D Sc i a ha n d) :
    SVec.ofHom (targetRightSupertensor D Sc i a ha n β f).unop ∈
      SVec.parityHom (qTargetSpace D Sc i β a ha n) (qTargetSpace D Sc i β a ha n) d := by
  induction hf using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨m, q, c, hc, hd, rfl⟩ := hz
    rw [targetRightSupertensor_tmul, ← hd]
    exact targetRightMonomial_parity D Sc i a ha n β m q c hc
  | zero =>
    rw [(targetRightSupertensor D Sc i a ha n β).map_zero]
    change (0 : qTargetSpace D Sc i β a ha n ⟶ qTargetSpace D Sc i β a ha n) ∈ _
    exact (SVec.parityHom _ _ d).zero_mem
  | add x y _ _ hx hy =>
    rw [(targetRightSupertensor D Sc i a ha n β).map_add]
    exact (SVec.parityHom _ _ d).add_mem hx hy
  | smul r x _ hx =>
    rw [targetRightSupertensor_smul]
    exact (SVec.parityHom _ _ d).smul_mem r hx

/-- Q is an even equivariant map for each homogeneous balanced tensor.
No additional equivariance or evenness hypothesis is used. -/
theorem rightSupertensor_Q_gradedSquare (β : Multiset I) (d : ZMod 2)
    (f : _root_.Polynomial k ⊗[k] CyclotomicAlgebra D Sc a n)
    (hf : f ∈ polynomialSupertensorPart D Sc i a ha n d) :
    SVec.ofHom (parityCyclotomicContentQLinear D Sc i β a ha n) ∈
      SVec.parityHom (qSourceSpace D Sc i a ha n) (qTargetSpace D Sc i β a ha n) 0 ∧
    SVec.ofHom (sourceRightSupertensor D Sc i a ha n f).unop ∈
      SVec.parityHom (qSourceSpace D Sc i a ha n) (qSourceSpace D Sc i a ha n) d ∧
    SVec.ofHom (targetRightSupertensor D Sc i a ha n β f).unop ∈
      SVec.parityHom (qTargetSpace D Sc i β a ha n) (qTargetSpace D Sc i β a ha n) d ∧
    (targetRightSupertensor D Sc i a ha n β f).unop.comp
        (parityCyclotomicContentQLinear D Sc i β a ha n) =
      (parityCyclotomicContentQLinear D Sc i β a ha n).comp
        (sourceRightSupertensor D Sc i a ha n f).unop :=
  ⟨parityCyclotomicContentQ_even D Sc i β a ha n,
    sourceRightSupertensor_parity D Sc i a ha n d f hf,
    targetRightSupertensor_parity D Sc i a ha n β d f hf,
    rightSupertensor_Q D Sc i a ha n β f⟩

end OddMath.QuiverHecke
