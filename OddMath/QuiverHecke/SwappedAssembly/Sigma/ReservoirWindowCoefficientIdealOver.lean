/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.Sigma.ReservoirWindowCoefficientIdeal
import OddMath.QuiverHecke.CyclotomicAction.ELVReservoirIdealOver
import OddMath.QuiverHecke.CyclotomicAction.ParameterTransportGrading

/-! # Padded chosen reservoir contractions in the coefficient ideal over a graded base

SwappedHomInversion §4 (7)–(9), over a commutative `K`-algebra `k` graded by `𝒜` in degrees
`0, …, b`, for parameters whose units have degree `0` and whose nonzero two-dot coefficients
have their coefficient degree. The transported parameters `parameterTwist D Sc` are then
coefficient-graded homogeneous (`isHomogeneous_parameterTwist`), and the named principal and
finite inverse entries of `ReservoirWindowInverseData` lie in the jointly nilpotent coefficient
ideal `ELVOld.contentModuleCoefficientIdealOver` after the whole-output evaluation.

For `K = k` with the trivial grading these are the statements of
`OddMath.QuiverHecke.SwappedAssembly.Sigma.ReservoirWindowCoefficientIdeal`.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath.SKM BicategoryStruct
open scoped Classical
namespace OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
open CyclotomicAction ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : Datum I X) (Sc : Scalars D k) (m : I → ℕ) (cutoff : I → ℕ) (bound : ℕ)
  (ΛP ΛR : X)
  (hP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)
local notation "Sc'" => parameterTwist D Sc
local notation "P" => elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR
local instance reservoirIdealOverHomPi (A B : PiSCat.{u,u,u + 1} k) :
    PiSupercategory k (A ⟶ B) := PiTwoSupercategory.homPiLeft A B
local notation "hG" => isHomogeneous_parameterTwist D sy 𝒜 Sc ht hs

variable [Finite I] (sy : Symmetrizer D) {K : Type u} [CommRing K] [Algebra K k]
  (𝒜 : ℤ → Submodule K k) [GradedAlgebra 𝒜]
  (ht : ∀ i j, ((Sc.t i j : kˣ) : k) ∈ 𝒜 0)
  (hs : ∀ i j (p q : ℕ), 0 < p → (p : ℤ) < D.d i j → 0 < q → (q : ℤ) < D.d j i →
    Sc.s i j p q ≠ 0 → Sc.s i j p q ∈ 𝒜 (SKM.coefficientDegree sy i j p q))
  (b : ℤ) (h𝒜 : ∀ m, m ∉ Set.Icc (0 : ℤ) b → 𝒜 m = ⊥)
  (i : I) (t : Sector I) (Z : H D Sc' m cutoff bound ΛP ΛR t)
  (β : WeightBlocks D ΛR ((P).muM t)) (c : (P).CrossCoeff)
/-- The source coefficient filtration's zeroth level contains every fixed-output morphism. -/
theorem reservoirOutput_mem_zeroOver (t : Sector I)
    (β : WeightBlocks D ΛR ((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).muM t))
    {A B : (P).T.obj (-((P).muP t)) ⟶ contentModuleTarget D Sc' cutoff bound β.1} (f : A ⟶ B) :
    (contentModuleCoefficientIdealOver D sy 𝒜 Sc' hG cutoff bound β.1 b h𝒜 ((P).T.obj (-((P).muP t)))).mem 0 f :=
  ProbeWindow.mem_coeffIdeal_zero (Gr := contentModuleCoeffGradingOver D sy 𝒜 Sc' hG cutoff bound β.1) f

/-- The named padded cap principal closes in the positive coefficient ideal. -/
theorem reservoirCapInverseData_closure_memOver (i : I) (t : Sector I)
    (Z : H D (parameterTwist D Sc) m cutoff bound ΛP ΛR t)
    (β : WeightBlocks D ΛR ((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).muM t))
    (c : (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).CrossCoeff)
    (hh : 0 ≤ D.h i ((P).muM t)) (r s : ℕ) :
    (contentModuleCoefficientIdealOver D sy 𝒜 Sc' hG cutoff bound β.1 b h𝒜 ((P).T.obj (-((P).muP t)))).mem 1 ((P).centralPaddedUnit i t Z.obj (reservoirOutputEval D Sc m cutoff bound ΛP ΛR hP hR t β) false r ≫
      (reservoirCapInverseData D Sc m cutoff bound ΛP ΛR hP hR i t Z (reservoirOutputEval D Sc m cutoff bound ΛP ΛR hP hR t β) c hh).principal ≫
        (P).centralPaddedCap i t Z.obj (reservoirOutputEval D Sc m cutoff bound ΛP ΛR hP hR t β) false s) := by
  by_cases ha : StepValid (up i) false t
  · simp only [reservoirCapInverseData, dite_eq_left ha]
    rw [ProbeReservoir.reservoirCapInverseData_closure_eq]
    simpa only [reservoirOutputEval_map, reservoirOutputEval_obj, elvProbeReservoir_W, Category.id_comp, Category.comp_id] using
      ReservoirClosures.positiveNativeClosure_evaluate_memOver D sy 𝒜 Sc' hG cutoff bound ΛR hR i
        ((P).muM_postE i ha) ((P).muM_postF i t) β b h𝒜 (P).T.obj t.1 ((P).muP t) hh r s
        (𝟙 Z.obj) (𝟙 Z.obj)
  · rw [reservoirCapInverseData_principal_of_absent D Sc m cutoff bound ΛP ΛR hP hR i t Z (reservoirOutputEval D Sc m cutoff bound ΛP ΛR hP hR t β) c hh ha]
    simpa only [Limits.comp_zero, Limits.zero_comp] using (contentModuleCoefficientIdealOver D sy 𝒜 Sc' hG cutoff bound β.1 b h𝒜 ((P).T.obj (-((P).muP t)))).zero_mem 1

/-- The named padded unit principal closes in the positive coefficient ideal. -/
theorem reservoirCupInverseData_closure_memOver (i : I) (t : Sector I)
    (Z : H D (parameterTwist D Sc) m cutoff bound ΛP ΛR t)
    (β : WeightBlocks D ΛR ((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).muM t))
    (c : (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).CrossCoeff)
    (hh : D.h i ((P).muM t) ≤ 0) (r s : ℕ) :
    (contentModuleCoefficientIdealOver D sy 𝒜 Sc' hG cutoff bound β.1 b h𝒜 ((P).T.obj (-((P).muP t)))).mem 1 ((P).centralPaddedUnit i t Z.obj (reservoirOutputEval D Sc m cutoff bound ΛP ΛR hP hR t β) false r ≫
      (reservoirCupInverseData D Sc m cutoff bound ΛP ΛR hP hR i t Z (reservoirOutputEval D Sc m cutoff bound ΛP ΛR hP hR t β) c hh).principal ≫
        (P).centralPaddedCap i t Z.obj (reservoirOutputEval D Sc m cutoff bound ΛP ΛR hP hR t β) false s) := by
  by_cases ha : StepValid (up i) false t
  · simp only [reservoirCupInverseData, dite_eq_left ha]
    rw [ProbeReservoir.reservoirCupInverseData_closure_eq]
    simpa only [reservoirOutputEval_map, reservoirOutputEval_obj, elvProbeReservoir_W, Category.id_comp, Category.comp_id] using
      ReservoirClosures.negativeNativeClosure_evaluate_memOver D sy 𝒜 Sc' hG cutoff bound ΛR hR i
        ((P).muM_postE i ha) ((P).muM_postF i t) β b h𝒜 (P).T.obj t.1 ((P).muP t) hh r s
        (𝟙 Z.obj) (𝟙 Z.obj)
  · rw [reservoirCupInverseData_principal_of_absent D Sc m cutoff bound ΛP ΛR hP hR i t Z (reservoirOutputEval D Sc m cutoff bound ΛP ΛR hP hR t β) c hh ha]
    simpa only [Limits.comp_zero, Limits.zero_comp] using (contentModuleCoefficientIdealOver D sy 𝒜 Sc' hG cutoff bound β.1 b h𝒜 ((P).T.obj (-((P).muP t)))).zero_mem 1

/-- Every named cap inverse column contracts off its finite window into level one. -/
theorem reservoirCapInverseData_boundary_memOver (i : I) (t : Sector I)
    (Z : H D (parameterTwist D Sc) m cutoff bound ΛP ΛR t)
    (β : WeightBlocks D ΛR ((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).muM t))
    (c : (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).CrossCoeff)
    (hh : 0 ≤ D.h i ((P).muM t))
    (j : Fin (D.h i ((P).muM t)).toNat) (r : ℕ) (hjr : (j : ℕ) < r) :
    (contentModuleCoefficientIdealOver D sy 𝒜 Sc' hG cutoff bound β.1 b h𝒜 ((P).T.obj (-((P).muP t)))).mem 1 ((reservoirCapInverseData D Sc m cutoff bound ΛP ΛR hP hR i t Z (reservoirOutputEval D Sc m cutoff bound ΛP ΛR hP hR t β) c hh).window j ≫
      (P).centralPaddedCap i t Z.obj (reservoirOutputEval D Sc m cutoff bound ΛP ΛR hP hR t β) false r) := by
  by_cases ha : StepValid (up i) false t
  · simp only [reservoirCapInverseData, dite_eq_left ha]
    rw [ProbeReservoir.reservoirCapInverseData_boundary_eq]
    simpa only [reservoirOutputEval_map, reservoirOutputEval_obj, elvProbeReservoir_W, Category.id_comp, Category.comp_id] using
      ReservoirBoundaries.positiveNativeBoundary_evaluate_memOver D sy 𝒜 Sc' hG cutoff bound ΛR hR i
        ((P).muM_postE i ha) ((P).muM_postF i t) β b h𝒜 (P).T.obj t.1 ((P).muP t) hh j r j.isLt hjr
        (𝟙 Z.obj) (𝟙 Z.obj)
  · rw [reservoirCapInverseData_window_of_absent D Sc m cutoff bound ΛP ΛR hP hR i t Z (reservoirOutputEval D Sc m cutoff bound ΛP ΛR hP hR t β) c hh ha]
    simpa only [Limits.zero_comp] using (contentModuleCoefficientIdealOver D sy 𝒜 Sc' hG cutoff bound β.1 b h𝒜 ((P).T.obj (-((P).muP t)))).zero_mem 1

/-- The absent unit rows retain their native positive-degree off-window boundary. -/
theorem reservoirCupInverseData_boundary_memOver (i : I) (t : Sector I)
    (Z : H D (parameterTwist D Sc) m cutoff bound ΛP ΛR t)
    (β : WeightBlocks D ΛR ((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).muM t))
    (c : (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).CrossCoeff)
    (hh : D.h i ((P).muM t) ≤ 0)
    (j : Fin (-D.h i ((P).muM t)).toNat) (r : ℕ) (hjr : (j : ℕ) < r) :
    (contentModuleCoefficientIdealOver D sy 𝒜 Sc' hG cutoff bound β.1 b h𝒜 ((P).T.obj (-((P).muP t)))).mem 1 ((P).centralPaddedUnit i t Z.obj (reservoirOutputEval D Sc m cutoff bound ΛP ΛR hP hR t β) false r ≫
      (reservoirCupInverseData D Sc m cutoff bound ΛP ΛR hP hR i t Z (reservoirOutputEval D Sc m cutoff bound ΛP ΛR hP hR t β) c hh).window j) := by
  by_cases ha : StepValid (up i) false t
  · simp only [reservoirCupInverseData, dite_eq_left ha]
    rw [ProbeReservoir.reservoirCupInverseData_boundary_eq]
    simpa only [reservoirOutputEval_map, reservoirOutputEval_obj, elvProbeReservoir_W, Category.id_comp, Category.comp_id] using
      ReservoirBoundaries.negativeNativeBoundary_evaluate_memOver D sy 𝒜 Sc' hG cutoff bound ΛR hR i
        ((P).muM_postE i ha) ((P).muM_postF i t) β b h𝒜 (P).T.obj t.1 ((P).muP t) hh j r j.isLt hjr
        (𝟙 Z.obj) (𝟙 Z.obj)
  · simp only [reservoirCupInverseData, dite_eq_right ha]
    rw [ProbeReservoir.reservoirCupInverseData_boundary_eq_of_absent]
    simpa only [reservoirOutputEval_map, reservoirOutputEval_obj, elvProbeReservoir_W, Category.id_comp, Category.comp_id] using
      ReservoirBoundaries.negativeNativeBoundary_evaluate_memOver D sy 𝒜 Sc' hG cutoff bound ΛR hR i
        (show (P).muM t - D.α i + D.α i = (P).muM t from sub_add_cancel _ _) ((P).muM_postF i t) β b h𝒜 (P).T.obj t.1 ((P).muP t) hh j r j.isLt hjr
        (𝟙 Z.obj) (𝟙 Z.obj)

/-- All dotted cap rows agree with the finite Kronecker pairing modulo level one. -/
theorem reservoirCapInverseData_contraction_memOver (i : I) (t : Sector I)
    (Z : H D (parameterTwist D Sc) m cutoff bound ΛP ΛR t)
    (β : WeightBlocks D ΛR ((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).muM t))
    (c : (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).CrossCoeff)
    (hh : 0 ≤ D.h i ((P).muM t))
    (j : Fin (D.h i ((P).muM t)).toNat) (r : ℕ) :
    (contentModuleCoefficientIdealOver D sy 𝒜 Sc' hG cutoff bound β.1 b h𝒜 ((P).T.obj (-((P).muP t)))).mem 1 ((reservoirCapInverseData D Sc m cutoff bound ΛP ΛR hP hR i t Z (reservoirOutputEval D Sc m cutoff bound ΛP ΛR hP hR t β) c hh).window j ≫
      (P).centralPaddedCap i t Z.obj (reservoirOutputEval D Sc m cutoff bound ΛP ΛR hP hR t β) false r - if (j : ℕ) = r then 𝟙 _ else 0) := by
  apply ProbeWindow.cap_contraction (contentModuleCoefficientIdealOver D sy 𝒜 Sc' hG cutoff bound β.1 b h𝒜 ((P).T.obj (-((P).muP t))))
    (reservoirCapInverseData D Sc m cutoff bound ΛP ΛR hP hR i t Z (reservoirOutputEval D Sc m cutoff bound ΛP ΛR hP hR t β) c hh).isInverse
  intro n a ha
  exact reservoirCapInverseData_boundary_memOver D Sc m cutoff bound ΛP ΛR hP hR sy 𝒜 ht hs b h𝒜 i t Z β c hh n a
    (lt_of_lt_of_le n.isLt ha)

/-- All dotted unit rows agree with the finite Kronecker pairing modulo level one. -/
theorem reservoirCupInverseData_contraction_memOver (i : I) (t : Sector I)
    (Z : H D (parameterTwist D Sc) m cutoff bound ΛP ΛR t)
    (β : WeightBlocks D ΛR ((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).muM t))
    (c : (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).CrossCoeff)
    (hh : D.h i ((P).muM t) ≤ 0)
    (r : ℕ) (j : Fin (-D.h i ((P).muM t)).toNat) :
    (contentModuleCoefficientIdealOver D sy 𝒜 Sc' hG cutoff bound β.1 b h𝒜 ((P).T.obj (-((P).muP t)))).mem 1 ((P).centralPaddedUnit i t Z.obj (reservoirOutputEval D Sc m cutoff bound ΛP ΛR hP hR t β) false r ≫
      (reservoirCupInverseData D Sc m cutoff bound ΛP ΛR hP hR i t Z (reservoirOutputEval D Sc m cutoff bound ΛP ΛR hP hR t β) c hh).window j -
        if r = (j : ℕ) then 𝟙 _ else 0) := by
  apply ProbeWindow.cup_contraction (contentModuleCoefficientIdealOver D sy 𝒜 Sc' hG cutoff bound β.1 b h𝒜 ((P).T.obj (-((P).muP t))))
    (reservoirCupInverseData D Sc m cutoff bound ΛP ΛR hP hR i t Z (reservoirOutputEval D Sc m cutoff bound ΛP ΛR hP hR t β) c hh).isInverse
  intro n a ha
  exact reservoirCupInverseData_boundary_memOver D Sc m cutoff bound ΛP ΛR hP hR sy 𝒜 ht hs b h𝒜 i t Z β c hh n a
    (lt_of_lt_of_le n.isLt ha)

/-- The central negative-principal cap convention preserves closure membership. -/
theorem reservoirCapInverseData_negPrincipal_closure_memOver (i : I) (t : Sector I)
    (Z : H D (parameterTwist D Sc) m cutoff bound ΛP ΛR t)
    (β : WeightBlocks D ΛR ((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).muM t))
    (c : (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).CrossCoeff)
    (hh : 0 ≤ D.h i ((P).muM t)) (r s : ℕ) :
    (contentModuleCoefficientIdealOver D sy 𝒜 Sc' hG cutoff bound β.1 b h𝒜 ((P).T.obj (-((P).muP t)))).mem 1 ((P).centralPaddedUnit i t Z.obj (reservoirOutputEval D Sc m cutoff bound ΛP ΛR hP hR t β) false r ≫
      (reservoirCapInverseData D Sc m cutoff bound ΛP ΛR hP hR i t Z (reservoirOutputEval D Sc m cutoff bound ΛP ΛR hP hR t β) c hh).negPrincipal.principal ≫
        (P).centralPaddedCap i t Z.obj (reservoirOutputEval D Sc m cutoff bound ΛP ΛR hP hR t β) false s) := by
  simpa only [ProbeWindow.CapInverseData.negPrincipal, Preadditive.comp_neg, Preadditive.neg_comp] using
    (contentModuleCoefficientIdealOver D sy 𝒜 Sc' hG cutoff bound β.1 b h𝒜 ((P).T.obj (-((P).muP t)))).neg_mem (reservoirCapInverseData_closure_memOver D Sc m cutoff bound ΛP ΛR hP hR sy 𝒜 ht hs b h𝒜 i t Z β c hh r s)

/-- The central negative-principal unit convention preserves closure membership. -/
theorem reservoirCupInverseData_negPrincipal_closure_memOver (i : I) (t : Sector I)
    (Z : H D (parameterTwist D Sc) m cutoff bound ΛP ΛR t)
    (β : WeightBlocks D ΛR ((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).muM t))
    (c : (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).CrossCoeff)
    (hh : D.h i ((P).muM t) ≤ 0) (r s : ℕ) :
    (contentModuleCoefficientIdealOver D sy 𝒜 Sc' hG cutoff bound β.1 b h𝒜 ((P).T.obj (-((P).muP t)))).mem 1 ((P).centralPaddedUnit i t Z.obj (reservoirOutputEval D Sc m cutoff bound ΛP ΛR hP hR t β) false r ≫
      (reservoirCupInverseData D Sc m cutoff bound ΛP ΛR hP hR i t Z (reservoirOutputEval D Sc m cutoff bound ΛP ΛR hP hR t β) c hh).negPrincipal.principal ≫
        (P).centralPaddedCap i t Z.obj (reservoirOutputEval D Sc m cutoff bound ΛP ΛR hP hR t β) false s) := by
  simpa only [ProbeWindow.CupInverseData.negPrincipal, Preadditive.comp_neg, Preadditive.neg_comp] using
    (contentModuleCoefficientIdealOver D sy 𝒜 Sc' hG cutoff bound β.1 b h𝒜 ((P).T.obj (-((P).muP t)))).neg_mem (reservoirCupInverseData_closure_memOver D Sc m cutoff bound ΛP ΛR hP hR sy 𝒜 ht hs b h𝒜 i t Z β c hh r s)


end OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
