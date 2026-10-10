import OddMath.CoveringQuantum.PreF.QuotientForm
import OddMath.CoveringQuantum.Serre
import Mathlib.RingTheory.TwoSidedIdeal.Kernel

/-!
# The bilinear form on the Serre presentation

The form on the free algebra descends to the Serre presentation, since the Serre
relations lie in its radical. Its radical is exactly the kernel of `serreToRadical`.
Consequently, its nondegeneracy is equivalent to injectivity of that surjection,
or to equality of the Serre ideal and the radical of the free form.

These reductions are valid over the general coefficient ring used here. They do not
prove the Serre-ideal equality over the generic covering coefficient ring of [BE2] §10.
In particular, arbitrary specializations of `q` can make the form degenerate; `norm`
is a genuine inverse only when the corresponding denominator is a unit.
-/

noncomputable section

namespace OddMath.CoveringQuantum.SuperCartanDatum

variable {k I : Type*} [CommRing k] [DecidableEq I] (C : SuperCartanDatum I) (q : kˣ) (π : k)

/-- The nondegenerate form on the quotient by the radical. -/
abbrev radicalForm : LinearMap.BilinForm k (C.radicalF q π) :=
  PreF.quotientForm (C.chi q π) (C.norm q π)

/-- The form on the Serre presentation, obtained by pullback from the radical quotient. -/
def serreForm (hπ : π ^ 2 = 1) : LinearMap.BilinForm k (C.serreF q π) :=
  (C.radicalForm q π).compl₁₂ (C.serreToRadical q π hπ).toLinearMap (C.serreToRadical q π hπ).toLinearMap

@[simp] theorem serreForm_apply (hπ : π ^ 2 = 1) (x y : C.serreF q π) :
    C.serreForm q π hπ x y = C.radicalForm q π (C.serreToRadical q π hπ x) (C.serreToRadical q π hπ y) := rfl

/-- The quotient map from the free algebra preserves the form. -/
@[simp] theorem serreForm_toSerreF (hπ : π ^ 2 = 1) (x y : PreF k I) :
    C.serreForm q π hπ (C.toSerreF q π x) (C.toSerreF q π y) = C.form q π x y := by
  rw [serreForm_apply, serreToRadical_toSerreF, serreToRadical_toSerreF]
  rfl

/-- Symmetry of the form on the Serre presentation. -/
theorem serreForm_comm (hπ : π ^ 2 = 1) (x y : C.serreF q π) :
    C.serreForm q π hπ x y = C.serreForm q π hπ y x :=
  PreF.quotientForm_comm _ _ _ _

/-- The normalization of the descended form. -/
theorem serreForm_θ_θ (hπ : π ^ 2 = 1) (i j : I) :
    C.serreForm q π hπ (C.toSerreF q π (PreF.θ k i)) (C.toSerreF q π (PreF.θ k j)) =
      if i = j then C.norm q π i else 0 := by
  rw [serreForm_toSerreF, form_θ_θ]

@[simp] theorem serreForm_one_one (hπ : π ^ 2 = 1) : C.serreForm q π hπ 1 1 = 1 := by
  simpa only [map_one] using (C.serreForm_toSerreF q π hπ 1 1).trans (PreF.form_one_one _ _)

/-- The form descending the given free form is unique. -/
theorem serreForm_unique (hπ : π ^ 2 = 1) (B : LinearMap.BilinForm k (C.serreF q π))
    (hB : ∀ x y, B (C.toSerreF q π x) (C.toSerreF q π y) = C.form q π x y) :
    B = C.serreForm q π hπ := by
  ext x y
  obtain ⟨a, rfl⟩ := C.toSerreF_surjective q π x
  obtain ⟨b, rfl⟩ := C.toSerreF_surjective q π y
  exact (hB a b).trans (C.serreForm_toSerreF q π hπ a b).symm

/-- The radical on the Serre presentation is the kernel of its map to the radical quotient. -/
theorem serreForm_radical_iff (hπ : π ^ 2 = 1) (x : C.serreF q π) :
    (∀ y, C.serreForm q π hπ x y = 0) ↔ C.serreToRadical q π hπ x = 0 := by
  constructor
  · intro hx
    apply PreF.quotientForm_separatingLeft
    intro y
    obtain ⟨z, rfl⟩ := C.serreToRadical_surjective q π hπ y
    exact hx z
  · intro hx y
    rw [serreForm_apply, hx, map_zero, LinearMap.zero_apply]

/-- Nondegeneracy on the Serre presentation is exactly the missing injectivity statement. -/
theorem serreForm_nondegenerate_iff (hπ : π ^ 2 = 1) :
    (C.serreForm q π hπ).Nondegenerate ↔ Function.Injective (C.serreToRadical q π hπ) := by
  constructor
  · intro h
    apply (injective_iff_map_eq_zero _).mpr
    intro x hx
    exact h.1 x ((C.serreForm_radical_iff q π hπ x).mpr hx)
  · intro h
    have hleft : (C.serreForm q π hπ).SeparatingLeft := by
      intro x hx
      apply h
      rw [map_zero]
      exact (C.serreForm_radical_iff q π hπ x).mp hx
    exact ⟨hleft, fun y hy ↦ hleft y fun x ↦ by rw [serreForm_comm]; exact hy x⟩

/-- The ideal killed by the presentation with the quantum Serre relations. -/
def serreIdeal : TwoSidedIdeal (PreF k I) := TwoSidedIdeal.ker (C.toSerreF q π).toRingHom

omit [DecidableEq I] in
@[simp] theorem mem_serreIdeal (x : PreF k I) : x ∈ C.serreIdeal q π ↔ C.toSerreF q π x = 0 :=
  TwoSidedIdeal.mem_ker _

/-- The already-established inclusion of the Serre ideal in the radical. -/
theorem serreIdeal_le_radical (hπ : π ^ 2 = 1) : C.serreIdeal q π ≤ PreF.radical (C.chi q π) (C.norm q π) := by
  intro x hx
  apply (PreF.toQuotient_eq_zero_iff _ _).mp
  rw [← C.serreToRadical_toSerreF q π hπ, (C.mem_serreIdeal q π x).mp hx, map_zero]

/-- Injectivity is equivalent to identifying the entire free-form radical with the Serre ideal. -/
theorem serreToRadical_injective_iff (hπ : π ^ 2 = 1) :
    Function.Injective (C.serreToRadical q π hπ) ↔
      C.serreIdeal q π = PreF.radical (C.chi q π) (C.norm q π) := by
  constructor
  · intro h
    apply le_antisymm (C.serreIdeal_le_radical q π hπ)
    intro x hx
    apply (C.mem_serreIdeal q π x).mpr
    apply h
    rw [map_zero, serreToRadical_toSerreF]
    exact (PreF.toQuotient_eq_zero_iff _ _).mpr hx
  · intro h
    apply (injective_iff_map_eq_zero _).mpr
    intro x hx
    obtain ⟨a, rfl⟩ := C.toSerreF_surjective q π x
    rw [serreToRadical_toSerreF, PreF.toQuotient_eq_zero_iff, ← h] at hx
    exact (C.mem_serreIdeal q π a).mp hx

/-- An exact reduction of nondegeneracy to the Serre-ideal theorem, without assuming that theorem. -/
theorem serreForm_nondegenerate_iff_ideal_eq (hπ : π ^ 2 = 1) :
    (C.serreForm q π hπ).Nondegenerate ↔
      C.serreIdeal q π = PreF.radical (C.chi q π) (C.norm q π) :=
  (C.serreForm_nondegenerate_iff q π hπ).trans (C.serreToRadical_injective_iff q π hπ)

end OddMath.CoveringQuantum.SuperCartanDatum
