import OddMath.QuiverHecke.CyclotomicAction.SuperAdjunction
import OddMath.QuiverHecke.CoefficientGrading
import OddMath.QuiverHecke.CyclotomicAction.WeightedPower

/-!
# Parameter transport

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-!
# Graded parameters under the parity transport

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, the parameters
(1.6) over a graded ring as in `OddMath.QuiverHecke.CoefficientGrading`. The parity transport
`parameterTwist` multiplies every `tᵢⱼ` and every `sᵢⱼ^{pq}` by a sign. Signs have degree `0`,
so if the `tᵢⱼ` have degree `0` and each nonzero `sᵢⱼ^{pq}` has its coefficient degree, the
same holds for the transported parameters (`parameterTwist_t_mem`, `parameterTwist_s_mem`), and
the quiver Hecke presentation with the transported parameters is coefficient-graded
homogeneous (`isHomogeneous_parameterTwist`).

For the trivial grading this is `parameterTwist_homogeneous`.
-/

noncomputable section

namespace OddMath.QuiverHecke

open scoped Classical
open OddMath.Diagrams

universe u v

variable {I : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  {K : Type*} [CommRing K] {k : Type u} [CommRing k] [Algebra K k]
  (sy : SKM.Symmetrizer D) (𝒜 : ℤ → Submodule K k) [SetLike.GradedMonoid 𝒜]
  (Sc : SKM.Scalars D k)

variable {𝒜} in
/-- The parity sign units have degree zero. -/
theorem parameterSignUnit_mem (p : ZMod 2) :
    ((parameterSignUnit (k := k) p : kˣ) : k) ∈ 𝒜 0 := by
  unfold parameterSignUnit
  split_ifs
  · exact neg_mem SetLike.GradedOne.one_mem
  · exact SetLike.GradedOne.one_mem

variable {𝒜 Sc} in
/-- Transported units keep degree zero. -/
theorem parameterTwist_t_mem (ht : ∀ i j, ((Sc.t i j : kˣ) : k) ∈ 𝒜 0) (i j : I) :
    (((parameterTwist D Sc).t i j : kˣ) : k) ∈ 𝒜 0 := by
  change ((if i = j then Sc.t i j else
    parameterSignUnit (k := k) (parameterSignExponent D i j (D.dn i j) 0) * Sc.t i j : kˣ) : k)
      ∈ 𝒜 0
  split_ifs
  · exact ht i j
  · rw [Units.val_mul]
    simpa using SetLike.mul_mem_graded (parameterSignUnit_mem _) (ht i j)

variable {𝒜 Sc} in
/-- Transported nonzero two-dot coefficients keep their coefficient degree. -/
theorem parameterTwist_s_mem
    (hs : ∀ i j (p q : ℕ), i ≠ j → (p : ℤ) < D.d i j → (q : ℤ) < D.d j i →
      Sc.s i j p q ≠ 0 → Sc.s i j p q ∈ 𝒜 (SKM.coefficientDegree sy i j p q))
    (i j : I) (p q : ℕ) (hij : i ≠ j) (hp' : (p : ℤ) < D.d i j)
    (hq' : (q : ℤ) < D.d j i) (h0 : (parameterTwist D Sc).s i j p q ≠ 0) :
    (parameterTwist D Sc).s i j p q ∈ 𝒜 (SKM.coefficientDegree sy i j p q) := by
  change SKM.zsign k (parameterSignExponent D i j p q) * Sc.s i j p q ∈ _
  have hs0 : Sc.s i j p q ≠ 0 := by
    intro hz
    exact h0 (by change SKM.zsign k _ * Sc.s i j p q = 0; rw [hz, mul_zero])
  simpa using SetLike.mul_mem_graded (zsign_mem _) (hs i j p q hij hp' hq' hs0)

/-- **Graded parameters under the parity transport.** If the `tᵢⱼ` have degree `0` and every
nonzero `sᵢⱼ^{pq}` has its coefficient degree, the quiver Hecke presentation with the
transported parameters `parameterTwist D Sc` is coefficient-graded homogeneous. -/
theorem isHomogeneous_parameterTwist (ht : ∀ i j, ((Sc.t i j : kˣ) : k) ∈ 𝒜 0)
    (hs : ∀ i j (p q : ℕ), i ≠ j → (p : ℤ) < D.d i j → (q : ℤ) < D.d j i →
      Sc.s i j p q ≠ 0 → Sc.s i j p q ∈ 𝒜 (SKM.coefficientDegree sy i j p q)) :
    CoefficientGrading.IsHomogeneous 𝒜 (gdeg D sy) (pres D (parameterTwist D Sc)) :=
  isHomogeneous_coefficientGraded D sy 𝒜 _ (parameterTwist_t_mem D ht)
    (parameterTwist_s_mem D sy hs)

end OddMath.QuiverHecke
end

end

section

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

namespace OddMath.QuiverHecke.ELV

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

end OddMath.QuiverHecke.ELV
end

end
