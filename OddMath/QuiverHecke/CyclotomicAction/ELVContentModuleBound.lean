/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVContentSupport
import OddMath.QuiverHecke.CyclotomicAction.ELVTruncatedModuleBound

/-! # Arbitrary-content bounds for the regular reservoir

The source support theorem supplies the existing regular-bimodule and module
superfunctor coefficient ideals. Thresholds depend on the word, as required;
no uniform bound over a weight fibre or grading of arbitrary modules is used.
-/
noncomputable section
open CategoryTheory StringDiagrams BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld
open SwappedAssembly.RegularReservoir
universe u
variable {I L k : Type u} [AddCommGroup L] [CommRing k]
  (D : SKM.Datum I L) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)

/-- The actual reservoir endomorphism algebra has a natural high-degree threshold. -/
theorem truncatedEndGSuperAlg_bounded [Finite I] (v : List I) :
    ∃ K : ℕ, ∀ d : ℤ, (K : ℤ) ≤ d →
      (truncatedEndGSuperAlg D Sc cutoff N sy hc v).degree d = ⊥ := by
  obtain ⟨B, hB⟩ := truncatedContent_bounded D Sc cutoff sy hc N v v
  exact ⟨B + 1, fun d hd => hB d (Or.inr (by omega))⟩

/-- Closed regular coefficients vanish at high degree, for every strand content. -/
theorem truncatedContent_regular_coefficients_bounded [Finite I] (v : List I) :
    ∃ K : ℕ, ∀ (d : ℤ), (K : ℤ) ≤ d →
      ∀ c : 𝟙 (truncatedEndGSuperAlg D Sc cutoff N sy hc v).toSuperAlg ⟶
        𝟙 (truncatedEndGSuperAlg D Sc cutoff N sy hc v).toSuperAlg,
      c ∈ (coeffGrading (truncatedEndGSuperAlg D Sc cutoff N sy hc v)).deg d → c = 0 := by
  obtain ⟨K, hK⟩ := truncatedEndGSuperAlg_bounded D Sc cutoff N sy hc v
  exact ⟨K, fun d hd c h => coefficient_eq_zero _ K hK d hd c h⟩

/-- The corresponding ideal on the actual module-superfunctor target. -/
def truncatedContentModuleCoefficientIdeal [Finite I] (v : List I) (T : PiSCat k) :
    SwappedAssembly.ProbeWindow.CoefficientIdeal
      (T ⟶ moduleTarget (truncatedEndGSuperAlg D Sc cutoff N sy hc v)) :=
  moduleCoefficientIdeal _ T
    (truncatedEndGSuperAlg_bounded D Sc cutoff N sy hc v).choose
    (truncatedEndGSuperAlg_bounded D Sc cutoff N sy hc v).choose_spec

/-- The regular kernel coefficient ideal, with the source support discharged. -/
def truncatedContentCoefficientIdeal [Finite I] (v : List I) (T : SuperAlg k) :
    SwappedAssembly.ProbeWindow.CoefficientIdeal
      (T ⟶ (truncatedEndGSuperAlg D Sc cutoff N sy hc v).toSuperAlg) :=
  coefficientIdeal _ T
    (truncatedEndGSuperAlg_bounded D Sc cutoff N sy hc v).choose
    (truncatedEndGSuperAlg_bounded D Sc cutoff N sy hc v).choose_spec

/-- Joint coefficient-ideal nilpotence lifts matrix isomorphisms at arbitrary content.
The remaining hypothesis is coefficient-error membership, not algebra support. -/
theorem truncatedContent_isIso_of_coefficient_error [Finite I] (v : List I) (T : SuperAlg k)
    {X Y : Mat_ (T ⟶ (truncatedEndGSuperAlg D Sc cutoff N sy hc v).toSuperAlg)}
    (F G : X ⟶ Y) [IsIso G]
    (hFG : ∀ i j, (F - G) i j ∈ SwappedAssembly.ProbeWindow.coeffIdeal
      (coeffGrading (truncatedEndGSuperAlg D Sc cutoff N sy hc v)) 1 _ _) : IsIso F :=
  isIso_of_coefficient_error _ T
    (truncatedEndGSuperAlg_bounded D Sc cutoff N sy hc v).choose
    (truncatedEndGSuperAlg_bounded D Sc cutoff N sy hc v).choose_spec F G hFG

end OddMath.QuiverHecke.ELVOld
