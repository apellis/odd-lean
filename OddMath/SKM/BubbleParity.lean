/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.BubblePolynomialExterior
import Mathlib.LinearAlgebra.CliffordAlgebra.Grading
import Mathlib.RingTheory.GradedAlgebra.TensorProduct

/-!
# Parity on the independent polynomial/exterior coefficient model

Brundan–Ellis (1.21)–(1.22), supporting the signed coefficient extension in
research issue #345. The model is algebra-isomorphic to abstract `SYM` by
`polynomialExteriorEquiv`; no diagrammatic evaluation is used.
-/

noncomputable section
open scoped Classical TensorProduct
namespace OddMath.SKM.SYM
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X]
variable (D : Datum I X) (k : Type w) [CommRing k]

abbrev exteriorParity : ZMod 2 → Submodule k (ExteriorAlgebra k (OddModule D k)) :=
  CliffordAlgebra.evenOdd (0 : QuadraticForm k (OddModule D k))

/-- The polynomial factor is even; the exterior factor has its usual parity. -/
def polynomialExteriorParity (p : ZMod 2) : Submodule k (PolynomialExterior D k) :=
  ((exteriorParity D k p).baseChange (MvPolynomial (I × ℕ) k)).restrictScalars k

instance polynomialExteriorGradedAlgebra : GradedAlgebra (polynomialExteriorParity D k) := by
  unfold polynomialExteriorParity
  infer_instance

theorem polynomialExterior_e_mem_even (i : I) (n : ℕ) :
    polynomialExteriorEquiv D k (e D k i n) ∈ polynomialExteriorParity D k 0 := by
  change polynomialExteriorProjection D k (e D k i n) ∈ _
  rw [polynomialExteriorProjection_e]
  change MvPolynomial.X (i, n) ⊗ₜ[k] (1 : ExteriorAlgebra k (OddModule D k)) ∈
    (exteriorParity D k 0).baseChange (MvPolynomial (I × ℕ) k)
  exact Submodule.tmul_mem_baseChange_of_mem _
    (Submodule.one_le.mp (CliffordAlgebra.one_le_evenOdd_zero (0 : QuadraticForm k (OddModule D k))))

theorem polynomialExterior_delta_mem_odd (i : {i : I // D.parity i = 1}) :
    polynomialExteriorEquiv D k (delta D k i) ∈ polynomialExteriorParity D k 1 := by
  change polynomialExteriorProjection D k (delta D k i) ∈ _
  rw [polynomialExteriorProjection_delta]
  change (1 : MvPolynomial (I × ℕ) k) ⊗ₜ[k]
    ExteriorAlgebra.ι k (Finsupp.single i 1 : OddModule D k) ∈
      (exteriorParity D k 1).baseChange (MvPolynomial (I × ℕ) k)
  exact Submodule.tmul_mem_baseChange_of_mem _
    (CliffordAlgebra.ι_mem_evenOdd_one (0 : QuadraticForm k (OddModule D k)) _)

end OddMath.SKM.SYM
