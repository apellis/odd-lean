/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVTruncatedCategory
import OddMath.QuiverHecke.SwappedAssembly.CentralInverse.ModuleCoefficients

/-! # One-strand bounds for truncated ELV module coefficients

The reservoir is the endomorphism algebra of the one-strand truncated ELV
category, not an assumed graded algebra. The one-strand support theorem kills
high-degree regular coefficients and their module-superfunctor realizations.
No bound on other contents or arbitrary module Hom spaces is asserted.
-/

noncomputable section
open CategoryTheory StringDiagrams BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld
open SwappedAssembly.RegularReservoir
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)

/-- The explicit one-strand upper-support bound on the endomorphism algebra. -/
theorem truncatedEndGSuperAlg_single_degree_eq_bot (i : I) (M : ℤ) (hM : 0 ≤ M)
    (hbound : ∀ a, SKM.SYM.coefficientDegree D sy a ≤ M * SKM.SYM.coefficientWeight D a)
    (d : ℤ) (hd : M * N + 2 * sy.d i * (cutoff i - 1 : ℕ) < d) :
    (truncatedEndGSuperAlg D Sc cutoff N sy hc [i]).degree d = ⊥ :=
  truncatedSingle_degree_eq_bot D Sc cutoff sy hc N i M hM hbound d hd

/-- Finite colours give a natural threshold suitable for regular coefficient bounds. -/
theorem truncatedEndGSuperAlg_single_bounded [Finite I] (i : I) :
    ∃ K : ℕ, ∀ d : ℤ, (K : ℤ) ≤ d →
      (truncatedEndGSuperAlg D Sc cutoff N sy hc [i]).degree d = ⊥ := by
  obtain ⟨B, hB⟩ := truncatedSingle_boundedAbove D Sc cutoff sy hc N i
  refine ⟨B.toNat + 1, fun d hd => hB d ?_⟩
  omega

/-- High-degree closed regular coefficients vanish in the one-strand reservoir. -/
theorem truncatedSingle_regular_coefficients_bounded [Finite I] (i : I) :
    ∃ K : ℕ, ∀ (d : ℤ), (K : ℤ) ≤ d →
      ∀ c : 𝟙 (truncatedEndGSuperAlg D Sc cutoff N sy hc [i]).toSuperAlg ⟶
        𝟙 (truncatedEndGSuperAlg D Sc cutoff N sy hc [i]).toSuperAlg,
      c ∈ (coeffGrading (truncatedEndGSuperAlg D Sc cutoff N sy hc [i])).deg d → c = 0 := by
  obtain ⟨K, hK⟩ := truncatedEndGSuperAlg_single_bounded D Sc cutoff N sy hc i
  exact ⟨K, fun d hd c h => coefficient_eq_zero _ K hK d hd c h⟩

/-- The same bound holds for the faithful realization on the module supercategory. -/
theorem truncatedSingle_module_coefficients_bounded [Finite I] (i : I) :
    ∃ K : ℕ, ∀ (d : ℤ), (K : ℤ) ≤ d →
      ∀ c : 𝟙 (truncatedEndGSuperAlg D Sc cutoff N sy hc [i]).toSuperAlg ⟶
        𝟙 (truncatedEndGSuperAlg D Sc cutoff N sy hc [i]).toSuperAlg,
      c ∈ (coeffGrading (truncatedEndGSuperAlg D Sc cutoff N sy hc [i])).deg d →
        realize (truncatedEndGSuperAlg D Sc cutoff N sy hc [i]) c = 0 := by
  obtain ⟨K, hK⟩ := truncatedEndGSuperAlg_single_bounded D Sc cutoff N sy hc i
  exact ⟨K, fun _ hd c h => realize_eq_zero_of_high_degree _ K hK c h hd⟩

end OddMath.QuiverHecke.ELVOld
