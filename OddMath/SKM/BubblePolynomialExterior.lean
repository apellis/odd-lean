/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.BubbleExterior
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Polynomial and exterior presentation of the abstract coefficients

The independent coefficient algebra of Brundan–Ellis (1.21)–(1.22), used in
the weighted cyclotomic separation route of research issue #345. There are
no SKM bubble-evaluation or Hom-space hypotheses in this construction.
-/

noncomputable section
open scoped Classical TensorProduct
namespace OddMath.SKM.SYM
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X]
variable (D : Datum I X) (k : Type w) [CommRing k]

theorem e_commute_all (i : I) (n : ℕ) (x : SYM D k) : Commute (e D k i n) x := by
  obtain ⟨p, rfl⟩ := RingQuot.mkAlgHom_surjective k (SYMRel D k) x
  change Commute (e D k i n) (mk D k p)
  induction p using FreeAlgebra.induction with
  | grade0 r =>
    change e D k i n * mk D k (algebraMap k _ r) = mk D k (algebraMap k _ r) * e D k i n
    simpa only [AlgHom.commutes] using (Algebra.commutes r (e D k i n)).symm
  | grade1 g =>
    cases g with
    | inl a => exact e_commute D k i a.1 n a.2
    | inr j => exact e_delta_commute D k i n j
  | mul p q hp hq => rw [map_mul]; exact hp.mul_right hq
  | add p q hp hq => rw [map_add]; exact hp.add_right hq

def elementaryCentral (a : I × ℕ) : Subalgebra.center k (SYM D k) :=
  ⟨e D k a.1 a.2, Subalgebra.mem_center_iff.mpr fun x => (e_commute_all D k a.1 a.2 x).eq.symm⟩

def polynomialCentral : MvPolynomial (I × ℕ) k →ₐ[k] Subalgebra.center k (SYM D k) :=
  MvPolynomial.aeval (elementaryCentral D k)

def polynomialInclude : MvPolynomial (I × ℕ) k →ₐ[k] SYM D k :=
  (Subalgebra.center k (SYM D k)).val.comp (polynomialCentral D k)

@[simp] theorem polynomialInclude_X (a : I × ℕ) :
    polynomialInclude D k (MvPolynomial.X a) = e D k a.1 a.2 := by
  simp [polynomialInclude, polynomialCentral, elementaryCentral]

theorem polynomialInclude_commute (p : MvPolynomial (I × ℕ) k) (x : SYM D k) :
    Commute (polynomialInclude D k p) x :=
  (Subalgebra.mem_center_iff.mp (polynomialCentral D k p).property x).symm

/-- The even polynomial algebra tensored with the full odd exterior algebra.
The ordinary tensor multiplication is correct because the polynomial factor is even. -/
abbrev PolynomialExterior :=
  MvPolynomial (I × ℕ) k ⊗[k] ExteriorAlgebra k (OddModule D k)

def polynomialExteriorInclude : PolynomialExterior D k →ₐ[k] SYM D k :=
  Algebra.TensorProduct.lift (polynomialInclude D k) (exteriorInclude D k)
    (fun p x => polynomialInclude_commute D k p (exteriorInclude D k x))

@[simp] theorem polynomialExteriorInclude_tmul (p : MvPolynomial (I × ℕ) k)
    (x : ExteriorAlgebra k (OddModule D k)) :
    polynomialExteriorInclude D k (p ⊗ₜ[k] x) =
      polynomialInclude D k p * exteriorInclude D k x :=
  Algebra.TensorProduct.lift_tmul _ _ _ _ _

private def polynomialExteriorGen (g : SYMGen D) : PolynomialExterior D k :=
  match g with
  | .inl a => MvPolynomial.X a ⊗ₜ[k] (1 : ExteriorAlgebra k (OddModule D k))
  | .inr i => (1 : MvPolynomial (I × ℕ) k) ⊗ₜ[k]
      ExteriorAlgebra.ι k (Finsupp.single i 1)

private theorem polynomialExterior_rel {x y : FreeAlgebra k (SYMGen D)}
    (h : SYMRel D k x y) :
    FreeAlgebra.lift k (polynomialExteriorGen D k) x =
      FreeAlgebra.lift k (polynomialExteriorGen D k) y := by
  cases h with
  | polynomial a b =>
    simp [polynomialExteriorGen, Algebra.TensorProduct.tmul_mul_tmul, mul_comm]
  | mixed a i => simp [polynomialExteriorGen, Algebra.TensorProduct.tmul_mul_tmul]
  | exterior i j =>
    simp only [map_mul, map_neg, FreeAlgebra.lift_ι_apply, polynomialExteriorGen,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← TensorProduct.tmul_neg]
    congr 1
    exact eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap (R := k) _ _)
  | square i =>
    rw [map_pow, map_zero, FreeAlgebra.lift_ι_apply]
    simp only [polynomialExteriorGen, pow_two, Algebra.TensorProduct.tmul_mul_tmul,
      one_mul, ExteriorAlgebra.ι_sq_zero, TensorProduct.tmul_zero]

def polynomialExteriorProjection : SYM D k →ₐ[k] PolynomialExterior D k :=
  RingQuot.liftAlgHom k
    ⟨FreeAlgebra.lift k (polynomialExteriorGen D k), fun _ _ h => polynomialExterior_rel D k h⟩

@[simp] theorem polynomialExteriorProjection_e (i : I) (n : ℕ) :
    polynomialExteriorProjection D k (e D k i n) =
      MvPolynomial.X (i, n) ⊗ₜ[k] (1 : ExteriorAlgebra k (OddModule D k)) := by
  simp only [polynomialExteriorProjection, e, ι, mk, RingQuot.liftAlgHom_mkAlgHom_apply,
    FreeAlgebra.lift_ι_apply, polynomialExteriorGen]

@[simp] theorem polynomialExteriorProjection_delta (i : {i : I // D.parity i = 1}) :
    polynomialExteriorProjection D k (delta D k i) =
      (1 : MvPolynomial (I × ℕ) k) ⊗ₜ[k]
        ExteriorAlgebra.ι k (Finsupp.single i 1) := by
  simp only [polynomialExteriorProjection, delta, ι, mk, RingQuot.liftAlgHom_mkAlgHom_apply,
    FreeAlgebra.lift_ι_apply, polynomialExteriorGen]

theorem polynomialExteriorInclude_comp_projection :
    (polynomialExteriorInclude D k).comp (polynomialExteriorProjection D k) =
      AlgHom.id k (SYM D k) := by
  apply hom_ext
  intro g
  cases g with
  | inl a =>
    change polynomialExteriorInclude D k (polynomialExteriorProjection D k (e D k a.1 a.2)) = _
    simp
    rfl
  | inr i =>
    change polynomialExteriorInclude D k (polynomialExteriorProjection D k (delta D k i)) = _
    simp
    rfl

theorem polynomialExteriorProjection_comp_polynomialInclude :
    (polynomialExteriorProjection D k).comp (polynomialInclude D k) =
      (Algebra.TensorProduct.includeLeft : MvPolynomial (I × ℕ) k →ₐ[k] PolynomialExterior D k) := by
  ext a
  simp

theorem polynomialExteriorProjection_comp_exteriorInclude :
    (polynomialExteriorProjection D k).comp (exteriorInclude D k) =
      (Algebra.TensorProduct.includeRight : ExteriorAlgebra k (OddModule D k) →ₐ[k]
        PolynomialExterior D k) := by
  apply ExteriorAlgebra.hom_ext
  apply LinearMap.ext
  intro x
  change polynomialExteriorProjection D k (exteriorInclude D k (ExteriorAlgebra.ι k x)) =
    (1 : MvPolynomial (I × ℕ) k) ⊗ₜ[k] ExteriorAlgebra.ι k x
  rw [exteriorInclude_ι]
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy, TensorProduct.tmul_add]
  | single i a =>
    rw [oddLinear_single, map_smul, polynomialExteriorProjection_delta]
    rw [show Finsupp.single i a = a • Finsupp.single i 1 by simp, map_smul,
      TensorProduct.tmul_smul]

theorem polynomialExteriorProjection_comp_include :
    (polynomialExteriorProjection D k).comp (polynomialExteriorInclude D k) =
      AlgHom.id k (PolynomialExterior D k) := by
  apply Algebra.TensorProduct.ext'
  intro p x
  change polynomialExteriorProjection D k (polynomialExteriorInclude D k (p ⊗ₜ[k] x)) = p ⊗ₜ[k] x
  rw [polynomialExteriorInclude_tmul, map_mul]
  have hp := DFunLike.congr_fun (polynomialExteriorProjection_comp_polynomialInclude D k) p
  have hx := DFunLike.congr_fun (polynomialExteriorProjection_comp_exteriorInclude D k) x
  change polynomialExteriorProjection D k (polynomialInclude D k p) = p ⊗ₜ[k] 1 at hp
  change polynomialExteriorProjection D k (exteriorInclude D k x) = 1 ⊗ₜ[k] x at hx
  rw [hp, hx]
  simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- The abstract all-colour coefficient presentation is the polynomial algebra
on elementary generators tensored with the exterior algebra on distinct odd colours. -/
def polynomialExteriorEquiv : SYM D k ≃ₐ[k] PolynomialExterior D k :=
  AlgEquiv.ofAlgHom (polynomialExteriorProjection D k) (polynomialExteriorInclude D k)
    (polynomialExteriorProjection_comp_include D k) (polynomialExteriorInclude_comp_projection D k)

end OddMath.SKM.SYM
