/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.CentralInverse.ModuleCoefficients
import NonVacuity.RegularCoefficientBound

/-! A nonzero module-superfunctor coefficient and its algebra-derived bound.
The rational fixture has zero positive ideal; it is not a fixture for a nonzero odd coefficient.
-/
noncomputable section
open CategoryTheory StringDiagrams BicategoryStruct
open OddMath.QuiverHecke.SwappedAssembly RegularReservoir ProbeWindow
open RegularCoefficientBoundConsumer

namespace ModuleCoefficientConsumer

example : (realize rationalReservoir (𝟙 (𝟙 rationalReservoir.toSuperAlg))) ≠ 0 := by
  intro h
  have hz : realize rationalReservoir 0 = 0 := (realizeLinear rationalReservoir).map_zero
  have he := realize_injective rationalReservoir (h.trans hz.symm)
  have h1 := congrArg (fun f => f.1 (1 : ℚ)) he
  change (1 : ℚ) = 0 at h1
  exact one_ne_zero h1

example (d : ℤ) (hd : (1 : ℤ) ≤ d)
    (t : 𝟙 (moduleTarget rationalReservoir) ⟶ 𝟙 (moduleTarget rationalReservoir))
    (ht : t ∈ (moduleCoeffGrading rationalReservoir).deg d) : t = 0 :=
  module_coefficient_eq_zero rationalReservoir 1 support_bound d hd t ht

example (T : PiSCat ℚ) : CoefficientIdeal (T ⟶ moduleTarget rationalReservoir) :=
  moduleCoefficientIdeal rationalReservoir T 1 support_bound

example (T : PiSCat ℚ) {X Y : Mat_ (T ⟶ moduleTarget rationalReservoir)}
    (F G : X ⟶ Y) [IsIso G]
    (h : ∀ i j, (F - G) i j ∈ coeffIdeal (moduleCoeffGrading rationalReservoir) 1 _ _) :
    IsIso F :=
  (moduleCoefficientIdeal rationalReservoir T 1 support_bound).isIso_of_sub_mem F G
    (fun _ _ => mem_coeffIdeal_zero _) h

#print axioms RegularReservoir.realize_injective
#print axioms RegularReservoir.realize_total
#print axioms RegularReservoir.realize_comp
#print axioms RegularReservoir.realize_proj
#print axioms RegularReservoir.module_coefficient_eq_zero
#print axioms RegularReservoir.moduleCoefficientIdeal

end ModuleCoefficientConsumer
