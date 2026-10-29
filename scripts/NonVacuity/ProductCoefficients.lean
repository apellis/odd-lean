/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.CentralInverse.ProductCoefficients
import NonVacuity.RegularCoefficientBound

/-! An infinite product of nonzero rational module categories, with the explicitly
unbounded chosen bounds `n + 1`. The coefficient ideal in this fixture is zero;
no nonzero positive or odd coefficient is claimed. -/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath.QuiverHecke.SwappedAssembly RegularReservoir ProbeWindow
open RegularCoefficientBoundConsumer
namespace ProductCoefficientConsumer

def allModules : ObjectProperty (Modules rationalReservoir) := fun _ => True

lemma allModules_pi (M : Modules rationalReservoir) (_h : allModules M) :
    allModules ((PiSupercategory.pi (R := ℚ)).obj M) := trivial

abbrev target := productModuleTarget (fun _ : ℕ => rationalReservoir)
  (fun _ => allModules) (fun _ => allModules_pi)

def window : Mat_ (target ⟶ target) :=
  (Mat_.embedding (target ⟶ target)).obj (Superfunctor.id ℚ target)

lemma component_support (b : ℕ) (d : ℤ) (hd : ((b + 1 : ℕ) : ℤ) ≤ d) :
    rationalReservoir.degree d = ⊥ := support_bound d (by omega)

example : ¬ ∃ K : ℕ, ∀ b : ℕ, b + 1 ≤ K := by
  rintro ⟨K, hK⟩
  have := hK K
  omega

/-- The headline theorem is exercised with every hypothesis proved, on an infinite product. -/
example : IsIso (𝟙 window) := by
  apply isIso_of_component_coefficient_error (fun _ : ℕ => rationalReservoir)
    (fun _ => allModules) (fun _ => allModules_pi) target (fun b => b + 1)
    component_support (𝟙 window) (𝟙 window)
  · intro b
    rw [CategoryTheory.Functor.map_id]
    infer_instance
  · intro b i j
    rw [sub_self]
    change (0 : _ ⟶ _) ∈ _
    exact Submodule.zero_mem _

/-- Restriction and product realization do not kill the identity coefficient. -/
example : productRealize (fun _ : ℕ => rationalReservoir)
    (fun _ => allModules) (fun _ => allModules_pi)
    (fun _ => 𝟙 (𝟙 rationalReservoir.toSuperAlg)) ≠ 0 := by
  intro h
  let M : ∀ _ : ℕ, allModules.FullSubcategory := fun _ => ⟨regularModule rationalReservoir, trivial⟩
  have ht := congrArg (fun t => (t.total M 0).hom) h
  rw [productRealize_total] at ht
  change ProbeWindow.postCoeff (regularModule rationalReservoir)
    (𝟙 (𝟙 rationalReservoir.toSuperAlg)) = 0 + 0 at ht
  rw [add_zero] at ht
  rw [ProbeWindow.postCoeff_id (k := ℚ)] at ht
  have he := congrArg (fun f => f.1 (1 : ℚ)) ht
  change (1 : ℚ) = 0 at he
  exact one_ne_zero he

#print axioms RegularReservoir.restrictCoeff_proj
#print axioms RegularReservoir.full_coefficient_eq_zero
#print axioms RegularReservoir.assembleIso
#print axioms RegularReservoir.isIso_of_component_coefficient_error
#print axioms RegularReservoir.weightSpace_isIso_of_eval
end ProductCoefficientConsumer
