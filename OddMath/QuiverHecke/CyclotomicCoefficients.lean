/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicSeparation
import Mathlib.LinearAlgebra.TensorProduct.Associator

/-!
# Coefficientwise cyclotomic detection

Supporting the full-SYM coefficient detection step of research issue #345,
toward Brundan–Ellis §8 Nondegeneracy Conjecture. Low-dot PBW coordinate maps
descend to the actual monomial cyclotomic quotient. Tensoring these explicit
coordinate maps detects coefficients in any module, without flatness.
This is a module statement, not yet a construction of supertensor multiplication
or a weighted deformed cyclotomic action.
-/

noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams
open scoped TensorProduct Classical

universe u v w z
variable {I : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  {k : Type w} [CommRing k] (Sc : SKM.Scalars D k)

theorem dotAtLeast_le_ker_coord {t t' : List I} (i : NFIdx t t') {N : ℕ}
    (hi : i.1.1.length < N) :
    DotAtLeast D Sc t t' N ≤ LinearMap.ker ((basisNF D Sc t t').coord i) := by
  classical
  apply Submodule.span_le.mpr
  rintro _ ⟨j, hj, rfl⟩
  change (basisNF D Sc t t').repr j.nf i = 0
  rw [← basisNF_apply D Sc t t' j, Module.Basis.repr_self]
  apply Finsupp.single_eq_of_ne
  intro he
  subst j
  simp only [Set.mem_ofPred_eq] at hj
  omega

/-- A specified low-dot PBW coordinate descends through the cyclotomic ideal. -/
def quotientCoordinate {t t' : List I} {N : ℕ} (i : NFIdx t t')
    (ht : 0 < t.length) (hi : i.1.1.length + 2 * t.length.choose 2 < N) :
    (((pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t')) ⧸
      CyclotomicSpan D Sc t t' N) →ₗ[k] k :=
  (CyclotomicSpan D Sc t t' N).liftQ ((basisNF D Sc t t').coord i)
    ((cyclotomicSpan_le_dotAtLeast D Sc ht (by omega)).trans
      (dotAtLeast_le_ker_coord D Sc i (by omega)))

@[simp] theorem quotientCoordinate_nf {t t' : List I} {N : ℕ}
    (i j : NFIdx t t') (ht : 0 < t.length)
    (hi : i.1.1.length + 2 * t.length.choose 2 < N) :
    quotientCoordinate D Sc i ht hi ((CyclotomicSpan D Sc t t' N).mkQ j.nf) =
      if j = i then 1 else 0 := by
  classical
  change (basisNF D Sc t t').repr j.nf i = _
  rw [← basisNF_apply D Sc t t' j, Module.Basis.repr_self, Finsupp.single_apply]

variable (A : Type z) [AddCommGroup A] [Module k A]

/-- Tensor the descended coordinate with any coefficient module; no tensor
injectivity assumption or flatness instance is used. -/
def tensorQuotientCoordinate {t t' : List I} {N : ℕ} (i : NFIdx t t')
    (ht : 0 < t.length) (hi : i.1.1.length + 2 * t.length.choose 2 < N) :
    (A ⊗[k] ((((pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t')) ⧸
      CyclotomicSpan D Sc t t' N))) →ₗ[k] A :=
  (TensorProduct.rid k A).toLinearMap.comp
    (TensorProduct.map (LinearMap.id : A →ₗ[k] A) (quotientCoordinate D Sc i ht hi))

@[simp] theorem tensorQuotientCoordinate_nf {t t' : List I} {N : ℕ}
    (i j : NFIdx t t') (ht : 0 < t.length)
    (hi : i.1.1.length + 2 * t.length.choose 2 < N) (a : A) :
    tensorQuotientCoordinate D Sc A i ht hi
      (a ⊗ₜ[k] (CyclotomicSpan D Sc t t' N).mkQ j.nf) =
        if j = i then a else 0 := by
  classical
  simp only [tensorQuotientCoordinate, LinearMap.comp_apply, TensorProduct.map_tmul,
    LinearMap.id_apply, LinearEquiv.coe_coe, TensorProduct.rid_tmul, quotientCoordinate_nf]
  split_ifs <;> simp

/-- A finite coefficient relation in the tensor of the actual quotient forces
all its low-dot coefficients to vanish, even when the coefficient module has
zero divisors or independent exterior generators. -/
theorem tensor_cyclotomic_coefficients_eq_zero {t t' : List I} {N : ℕ}
    (c : NFIdx t t' →₀ A) (ht : 0 < t.length)
    (hbound : ∀ i ∈ c.support, i.1.1.length + 2 * t.length.choose 2 < N)
    (hzero : (∑ i ∈ c.support,
      c i ⊗ₜ[k] (CyclotomicSpan D Sc t t' N).mkQ i.nf) = 0) : c = 0 := by
  classical
  ext i
  by_cases hi : i ∈ c.support
  · have he := congrArg (tensorQuotientCoordinate D Sc A i ht (hbound i hi)) hzero
    simpa only [map_sum, tensorQuotientCoordinate_nf, map_zero,
      Finset.sum_ite_eq', ite_eq_left hi, Finsupp.zero_apply] using he
  · simpa only [Finsupp.zero_apply] using Finsupp.notMem_support_iff.mp hi

/-- The family of monomial cyclotomic quotients jointly detects every finite
coefficientwise PBW expression, over an arbitrary coefficient module. -/
theorem tensor_cyclotomic_jointly_detects {t t' : List I}
    (c : NFIdx t t' →₀ A) (ht : 0 < t.length)
    (hzero : ∀ N : ℕ, (∑ i ∈ c.support,
      c i ⊗ₜ[k] (CyclotomicSpan D Sc t t' N).mkQ i.nf) = 0) : c = 0 := by
  classical
  let d := c.support.sup fun i => i.1.1.length
  apply tensor_cyclotomic_coefficients_eq_zero D Sc A c ht
    (N := d + 2 * t.length.choose 2 + 1) _ (hzero _)
  intro i hi
  have hd : i.1.1.length ≤ d := Finset.le_sup (f := fun j => j.1.1.length) hi
  omega

end OddMath.QuiverHecke
