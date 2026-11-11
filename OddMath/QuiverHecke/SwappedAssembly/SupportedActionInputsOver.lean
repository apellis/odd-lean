/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.SupportedAction
import OddMath.QuiverHecke.SwappedAssembly.Sigma.PaddedResidualInversionOver

/-! # The inputs of the supported action over a graded base

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, §8, over a
coefficient ring graded in degrees `0, …, b`, with the `tᵢⱼ` in degree `0` and each nonzero
`sᵢⱼ^{pq}` in its coefficient degree. The inputs of the supported action,
`ProbeActionInputs` (nilpotence of the appended dot and the reservoir window ideal), hold as
over a field with homogeneous parameters (`probeActionInputs`). Nilpotence of the pure
coefficients (`ScalarData.PureNilpotent`) is an explicit argument here; over a graded base it
is `pureNilpotent_of_graded`.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath.SKM
namespace OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
open CyclotomicAction ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Finite I]
  (D : Datum I X) (Sc : Scalars D k) (m cutoff : I → ℕ) (bound : ℕ)
  (ΛP ΛR : X)
  (hP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)
  (sy : Symmetrizer D) {K : Type u} [CommRing K] [Algebra K k]
  (𝒜 : ℤ → Submodule K k) [GradedAlgebra 𝒜]
  (ht : ∀ i j, ((Sc.t i j : kˣ) : k) ∈ 𝒜 0)
  (hs : ∀ i j (p q : ℕ), i ≠ j → (p : ℤ) < D.d i j → (q : ℤ) < D.d j i →
    Sc.s i j p q ≠ 0 → Sc.s i j p q ∈ 𝒜 (SKM.coefficientDegree sy i j p q))
  (b : ℤ) (h𝒜 : ∀ m, m ∉ Set.Icc (0 : ℤ) b → 𝒜 m = ⊥)

include sy 𝒜 ht hs b h𝒜 in
/-- The inputs of the supported action over a base graded in degrees `0, …, b`. -/
theorem probeActionInputsOver (hpure : Sc.PureNilpotent) :
    ProbeActionInputs D Sc m cutoff bound ΛP ΛR hP hR :=
  ⟨parameterTwist_truncatedAppendDotNilpotentOver D sy 𝒜 Sc ht hs b h𝒜 cutoff bound,
    reservoirWindowIdealOver D Sc m cutoff bound ΛP ΛR hP hR sy 𝒜 ht hs b h𝒜, hpure⟩

end OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
