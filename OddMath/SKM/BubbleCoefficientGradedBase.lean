/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.BubbleELVGrading
import OddMath.Diagrams.BasisGrading

/-!
# Coefficient algebras over a graded base ring

Let `R` be a commutative `K`-algebra graded by `K`-submodules `𝒜 : ℤ → Submodule K R`. The
coefficient algebra `SYM D R` is free over `R` with the homogeneous basis `coefficientBasis`, so
it is graded over `K` by coefficientwise degree: an element has degree `n` when its coordinate at
a basis vector of degree `δ` has degree `n - δ` in `R` (`coefficientDegreePartOver`). This is a
graded `K`-algebra (`coefficientDegreeGradedAlgebraOver`); the ELV coefficient ideal is
homogeneous for it (`elvCoefficientIdeal_degreeOver`), so the ELV coefficient algebra over `R` is
a graded `K`-algebra (`elvCoefficientDegreeOver`).

For `𝒜` concentrated in degree `0` (`K = R`) these are the gradings `coefficientDegreePart` and
`elvCoefficientDegree`. Over the truncated Rees rings `K[h]/(h^N)` they supply the coefficient
factor of the ELV grading over a graded base (`docs/Nondegeneracy/Phase2Plan.md`, step 2).
-/

noncomputable section

open scoped Classical

namespace OddMath.SKM.SYM

open OddMath.Diagrams

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] (D : Datum I X) (sy : Symmetrizer D)
  {K : Type*} [CommRing K] {R : Type w} [CommRing R] [Algebra K R]
  (𝒜 : ℤ → Submodule K R)

/-- The degree-`n` part of `SYM D R` over `K`: coordinates at basis vectors of degree `δ` lie
in `𝒜 (n - δ)`. -/
def coefficientDegreePartOver (n : ℤ) : Submodule K (SYM D R) :=
  BasisGrading.basisPart 𝒜 (coefficientDegree D sy) (coefficientBasis D R) n

variable {D sy 𝒜}

theorem smul_coefficientBasis_mem {a : CoefficientIndex D} {e : ℤ} {r : R} (hr : r ∈ 𝒜 e) :
    r • coefficientBasis D R a ∈ coefficientDegreePartOver D sy 𝒜 (e + coefficientDegree D sy a) :=
  BasisGrading.smul_basis_mem_basisPart hr

variable [GradedAlgebra 𝒜]

theorem coefficientBasis_mem_over (a : CoefficientIndex D) :
    coefficientBasis D R a ∈ coefficientDegreePartOver D sy 𝒜 (coefficientDegree D sy a) := by
  simpa using smul_coefficientBasis_mem (sy := sy)
    (SetLike.GradedOne.one_mem : (1 : R) ∈ 𝒜 0) (a := a)

variable (D sy 𝒜) in
theorem coefficientDegreePartOver_internal :
    DirectSum.IsInternal (coefficientDegreePartOver D sy 𝒜) :=
  BasisGrading.isInternal_basisPart _ _ _

theorem coefficientDegreePartOver_mul {m n : ℤ} {x y : SYM D R}
    (hx : x ∈ coefficientDegreePartOver D sy 𝒜 m) (hy : y ∈ coefficientDegreePartOver D sy 𝒜 n) :
    x * y ∈ coefficientDegreePartOver D sy 𝒜 (m + n) := by
  rw [← (coefficientBasis D R).linearCombination_repr x,
    ← (coefficientBasis D R).linearCombination_repr y, Finsupp.linearCombination_apply,
    Finsupp.linearCombination_apply, Finsupp.sum_mul]
  refine Submodule.sum_mem _ fun a _ => ?_
  rw [Finsupp.mul_sum]
  refine Submodule.sum_mem _ fun c _ => ?_
  rw [smul_mul_smul_comm]
  by_cases h : Disjoint a.2 c.2
  · obtain ⟨z, hz⟩ := coefficientBasis_mul_int D R h
    rw [hz, smul_smul]
    have ha : (coefficientBasis D R).repr x a ∈ 𝒜 (m - coefficientDegree D sy a) := hx a
    have hc : (coefficientBasis D R).repr y c ∈ 𝒜 (n - coefficientDegree D sy c) := hy c
    have hz' : (z : R) ∈ 𝒜 0 := SetLike.intCast_mem_graded 𝒜 z
    have hmem := SetLike.GradedMul.mul_mem (SetLike.GradedMul.mul_mem ha hc) hz'
    have := smul_coefficientBasis_mem (sy := sy) hmem (a := (a.1 + c.1, a.2 ∪ c.2))
    convert this using 2
    rw [coefficientDegree_mul D sy h]
    ring
  · rw [coefficientBasis_mul_zero D R h, smul_zero]
    exact zero_mem _

variable (D sy 𝒜) in
/-- `SYM D R` is a graded `K`-algebra for the coefficientwise degree. -/
@[instance_reducible]
def coefficientDegreeGradedAlgebraOver : GradedAlgebra (coefficientDegreePartOver D sy 𝒜) :=
  { (coefficientDegreePartOver_internal D sy 𝒜).chooseDecomposition with
    one_mem := by
      have h1 : coefficientBasis D R ((0, ∅) : CoefficientIndex D) = 1 := by
        apply (polynomialExteriorEquiv D R).injective
        rw [map_one (polynomialExteriorEquiv D R), coefficientBasis_projection,
          oddExteriorBasis_empty]
        exact (Algebra.TensorProduct.one_def : (1 : PolynomialExterior D R) = 1 ⊗ₜ[R] 1).symm
      have h := coefficientBasis_mem_over (sy := sy) (𝒜 := 𝒜) ((0, ∅) : CoefficientIndex D)
      rw [h1] at h
      simpa [coefficientDegree] using h
    mul_mem := fun _ _ _ _ hx hy => coefficientDegreePartOver_mul hx hy }

/-- Each ELV coefficient relation is homogeneous for the coefficientwise degree. -/
theorem elvCoefficientRelation_degreeOver {cutoff : I → ℕ} {x : SYM D R}
    (hx : ELVCoefficientRelation D R cutoff x) :
    ∃ n, x ∈ coefficientDegreePartOver D sy 𝒜 n := by
  rcases hx with ⟨i, r, _, rfl⟩ | ⟨i, _, rfl⟩
  · exact ⟨_, by simpa using coefficientBasis_mem_over (sy := sy) (𝒜 := 𝒜)
      ((Finsupp.single (i, r) 1, ∅) : CoefficientIndex D)⟩
  · have hd : delta D R i ∈ coefficientDegreePartOver D sy 𝒜 _ := by
      simpa using coefficientBasis_mem_over (sy := sy) (𝒜 := 𝒜)
        ((0, {i}) : CoefficientIndex D)
    cases h : cutoff i.1 / 2 with
    | zero => exact ⟨_, by simpa [elvChi, h] using hd⟩
    | succ r =>
      have he : e D R i.1 r ∈ coefficientDegreePartOver D sy 𝒜 _ := by
        simpa using coefficientBasis_mem_over (sy := sy) (𝒜 := 𝒜)
          ((Finsupp.single (i.1, r) 1, ∅) : CoefficientIndex D)
      exact ⟨_, by simpa [elvChi, h] using coefficientDegreePartOver_mul hd he⟩

attribute [local instance] coefficientDegreeGradedAlgebraOver

/-- The ELV coefficient ideal over `R` is homogeneous for the coefficientwise degree. -/
theorem elvCoefficientIdeal_degreeOver (cutoff : I → ℕ) {x : SYM D R}
    (hx : x ∈ elvCoefficientIdeal D R cutoff) (n : ℤ) :
    GradedAlgebra.proj (coefficientDegreePartOver D sy 𝒜) n x ∈ elvCoefficientIdeal D R cutoff :=
  coefficient_span_proj_mem (k := K) (A := SYM D R) (coefficientDegreePartOver D sy 𝒜)
    {a | ELVCoefficientRelation D R cutoff a}
    (fun _ hx => elvCoefficientRelation_degreeOver hx) hx n

variable (D sy 𝒜) in
/-- The degree-`n` part over `K` of the ELV coefficient algebra over `R`. -/
def elvCoefficientDegreeOver (cutoff : I → ℕ) (n : ℤ) :
    Submodule K (ELVCoefficientAlgebra (k := R) D cutoff) :=
  (coefficientDegreePartOver D sy 𝒜 n).map
    ((elvCoefficientQuotient D cutoff).restrictScalars K).toLinearMap

variable (D sy 𝒜) in
/-- The ELV coefficient algebra over `R` is a graded `K`-algebra. -/
@[instance_reducible]
def elvCoefficientDegreeGradedAlgebraOver (cutoff : I → ℕ) :
    GradedAlgebra (elvCoefficientDegreeOver D sy 𝒜 cutoff) :=
  quotientDegreeGrading (k := K) (A := SYM D R) (coefficientDegreePartOver D sy 𝒜)
    ((elvCoefficientQuotient D cutoff).restrictScalars K)
    (RingCon.mkₐ_surjective (α := R) _) (by
      intro x hx n
      apply elvCoefficientQuotient_eq_zero
      exact elvCoefficientIdeal_degreeOver cutoff (Quotient.exact hx) n)

end OddMath.SKM.SYM
