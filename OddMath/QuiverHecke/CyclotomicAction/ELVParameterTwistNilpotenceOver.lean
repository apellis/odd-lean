/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVTruncatedNilpotenceOver
import OddMath.QuiverHecke.CyclotomicAction.ParameterTransportGrading

/-!
# Nilpotence of the appended dot for transported graded parameters

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, the parameters
(1.6) over a base ring graded in degrees `0, …, b`. If the `tᵢⱼ` have degree `0` and each
nonzero `sᵢⱼ^{pq}` has its coefficient degree, then the parity-transported parameters
`parameterTwist D Sc` satisfy `TruncatedAppendDotNilpotent`, the only parameter input of the
reservoir dot nilpotence and of the mixed denominator units
(`elvProbeCrossDenominatorUnitsOf`, `elvProbeCrossCoeffOf`).
-/

noncomputable section

namespace OddMath.QuiverHecke.ELVOld

universe u

variable {I X : Type u} [AddCommGroup X] (D : SKM.Datum I X) (sy : SKM.Symmetrizer D)
  {K : Type u} [CommRing K] {R : Type u} [CommRing R] [Algebra K R]
  (𝒜 : ℤ → Submodule K R) [GradedAlgebra 𝒜] (Sc : SKM.Scalars D R)

/-- The appended dot is nilpotent for the parity-transported parameters over a base ring
graded in degrees `0, …, b`. -/
theorem parameterTwist_truncatedAppendDotNilpotentOver [Finite I]
    (ht : ∀ i j, ((Sc.t i j : Rˣ) : R) ∈ 𝒜 0)
    (hs : ∀ i j (p q : ℕ), i ≠ j → (p : ℤ) < D.d i j → (q : ℤ) < D.d j i →
      Sc.s i j p q ≠ 0 → Sc.s i j p q ∈ 𝒜 (SKM.coefficientDegree sy i j p q))
    (b : ℤ) (h𝒜 : ∀ m, m ∉ Set.Icc (0 : ℤ) b → 𝒜 m = ⊥) (cutoff : I → ℕ) (N : ℕ) :
    TruncatedAppendDotNilpotent D (parameterTwist D Sc) cutoff N :=
  truncatedAppendDotNilpotentOver D sy 𝒜 (parameterTwist D Sc)
    (isHomogeneous_parameterTwist D sy 𝒜 Sc ht hs) cutoff N b h𝒜

end OddMath.QuiverHecke.ELVOld
