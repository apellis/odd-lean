import OddMath.QuiverHecke.SwappedAssembly.Sigma.PaddedResidualInversion
import OddMath.QuiverHecke.SwappedAssembly.Sigma.ReservoirWindowCoefficientIdealOver
import OddMath.QuiverHecke.CyclotomicAction.ELVParameterTwistNilpotenceOver

/-! # The central augmented matrix over a graded base

SwappedActionAssembly §6 and SwappedHomInversion §§3–6 over a coefficient
ring graded in degrees `0, …, b`, with degree-zero `t` parameters and
`s` parameters in their coefficient degrees. The appended dot of the
parity-transported parameters is nilpotent and the reservoir windows lie
in the graded content coefficient ideal, so the output-content and
augmented central matrices are invertible as over a field.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath.SKM BicategoryStruct
namespace OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
open CyclotomicAction ELVOld ProbeWindow
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Finite I]
  (D : Datum I X) (Sc : Scalars D k) (m cutoff : I → ℕ) (bound : ℕ)
  (ΛP ΛR : X)
  (hP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)
  (sy : Symmetrizer D) {K : Type u} [CommRing K] [Algebra K k]
  (𝒜 : ℤ → Submodule K k) [GradedAlgebra 𝒜]
  (ht : ∀ i j, ((Sc.t i j : kˣ) : k) ∈ 𝒜 0)
  (hs : ∀ i j (p q : ℕ), 0 < p → (p : ℤ) < D.d i j → 0 < q → (q : ℤ) < D.d j i →
    Sc.s i j p q ≠ 0 → Sc.s i j p q ∈ 𝒜 (SKM.coefficientDegree sy i j p q))
  (b : ℤ) (h𝒜 : ∀ m, m ∉ Set.Icc (0 : ℤ) b → 𝒜 m = ⊥)
local notation "P" => elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR
local notation "hdotG" => parameterTwist_truncatedAppendDotNilpotentOver D sy 𝒜 Sc ht hs b h𝒜
  cutoff bound
local instance paddedResidualOverHomPi (A B : PiSCat.{u,u,u+1} k) :
    PiSupercategory k (A ⟶ B) := PiTwoSupercategory.homPiLeft A B

/-- Over a graded base, the graded content coefficient ideal carries every
reservoir window. -/
theorem reservoirWindowIdealOver :
    ReservoirWindowIdeal D Sc m cutoff bound ΛP ΛR hP hR := by
  refine ⟨fun i t Z β c => ?_⟩
  refine ⟨contentModuleCoefficientIdealOver D sy 𝒜 (parameterTwist D Sc)
    (isHomogeneous_parameterTwist D sy 𝒜 Sc ht hs) cutoff bound β.1 b h𝒜
    ((P).T.obj (-((P).muP t))), ?_, ?_, ?_, ?_, ?_⟩
  · intro A B f
    exact reservoirOutput_mem_zeroOver D Sc m cutoff bound ΛP ΛR hP hR sy 𝒜 ht hs b h𝒜 t β f
  · intro hh r s
    exact reservoirCapInverseData_closure_memOver D Sc m cutoff bound ΛP ΛR hP hR sy 𝒜 ht hs
      b h𝒜 i t Z β c hh r s
  · intro hh r s
    exact reservoirCupInverseData_closure_memOver D Sc m cutoff bound ΛP ΛR hP hR sy 𝒜 ht hs
      b h𝒜 i t Z β c hh r s
  · intro hh j r hjr
    exact reservoirCapInverseData_boundary_memOver D Sc m cutoff bound ΛP ΛR hP hR sy 𝒜 ht hs
      b h𝒜 i t Z β c hh j r hjr
  · intro hh j r hjr
    exact reservoirCupInverseData_boundary_memOver D Sc m cutoff bound ΛP ΛR hP hR sy 𝒜 ht hs
      b h𝒜 i t Z β c hh j r hjr

/-- Over a graded base, every output-content component of the padded
central matrix is invertible, in both signs. -/
theorem centralFactorMatrix_content_isIsoOver (i : I) (t : Sector I)
    (Z : H D (parameterTwist D Sc) m cutoff bound ΛP ΛR t)
    (β : WeightBlocks D ΛR ((P).muM t)) :
    (0 ≤ D.h i ((P).wt t) → IsIso ((P).augPosFactorMatrix
      (elvProbeCrossCoeffOf D Sc m cutoff bound ΛP ΛR hP hR hdotG) i ((P).wt t) t Z.obj
        (reservoirOutputEval D Sc m cutoff bound ΛP ΛR hP hR t β))) ∧
    (D.h i ((P).wt t) ≤ 0 → IsIso ((P).augNegFactorMatrix
      (elvProbeCrossCoeffOf D Sc m cutoff bound ΛP ΛR hP hR hdotG) i ((P).wt t) t Z.obj
        (reservoirOutputEval D Sc m cutoff bound ΛP ΛR hP hR t β))) :=
  centralFactorMatrix_content_isIsoOf D Sc m cutoff bound ΛP ΛR hP hR hdotG
    (reservoirWindowIdealOver D Sc m cutoff bound ΛP ΛR hP hR sy 𝒜 ht hs b h𝒜) i t Z β

/-- Over a graded base, the literal augmented central matrices are invertible. -/
theorem centralAugmentedMatrix_isIsoOver (i : I) (t : Sector I)
    (Z : H D (parameterTwist D Sc) m cutoff bound ΛP ΛR t) :
    (0 ≤ D.h i ((P).wt t) → IsIso ((P).augPosMat
      (elvProbeCrossCoeffOf D Sc m cutoff bound ΛP ΛR hP hR hdotG) i ((P).wt t) t t Z.obj)) ∧
    (D.h i ((P).wt t) ≤ 0 → IsIso ((P).augNegMat
      (elvProbeCrossCoeffOf D Sc m cutoff bound ΛP ΛR hP hR hdotG) i ((P).wt t) t t Z.obj)) :=
  centralAugmentedMatrix_isIsoOf D Sc m cutoff bound ΛP ΛR hP hR hdotG
    (reservoirWindowIdealOver D Sc m cutoff bound ΛP ΛR hP hR sy 𝒜 ht hs b h𝒜) i t Z

end OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
