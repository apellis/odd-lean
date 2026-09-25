import OddMath.Frontier.CompleteTableauExpansion
import OddMath.Frontier.ElementaryRelations
import OddMath.Frontier.CompleteChangeOfGenerators

/-! PRE-production controls
(Ellis 1111.3932v1 §2.1 and Thm 3.8 first part; EK 1107.5610v2 (3.6)).

Compiled BEFORE `OddLREKIdentification`; nothing here mentions the production map `piN`
or the production EK Schur family.

* `recover_natural`: the mechanism the production proof relies on — the module-valued
  signed-Kostka inversion commutes with every additive map, for every degree.
* `unsigned_recover_natural`: the same holds for ANY integer matrix, so naturality alone
  cannot distinguish the signed from the unsigned Kostka inversion; the discriminating
  input must be the signed expansion `CompleteTableauExpansion.complete_tableau_expansion`.
* `complete_one_eq_elementary_one`: exact degree-one fixture h₁ = e₁ in every alphabet.
* `evaluation_on_elementary`: the free-algebra complete evaluation sends EK's universal
  elementary element to the literal finite elementary sum, and hence the elementary
  specialisation factors through the EK generator change (the e-route used to descend).
* Exact integer controls for |λ| ≤ 4, N ≤ 3 (positive: recover(h_μ) = s^p_λ; negative:
  the unsigned-Kostka inversion FAILS, e.g. N=2, λ=(1,1,1); EK relations for completes,
  a+b ≤ 6) are in an unpublished script (log controls.log),
  an independent Python re-implementation run before production.
-/
noncomputable section
open scoped BigOperators
namespace OddMath.Frontier.OddLREKIdentificationControls
open OddMath.SkewPolynomial FiniteCompleteElementary DegreeShapes

theorem recover_natural {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    (f : V →+ W) (d : ℕ) (H : DegreeShape d → V) (i : DegreeShape d) :
    f (KostkaModuleInversion.recover d H i) = KostkaModuleInversion.recover d (f ∘ H) i := by
  simp only [KostkaModuleInversion.recover, map_sum, map_zsmul, Function.comp_apply]

/-- Any integer matrix inversion is natural; naturality carries no sign information. -/
theorem unsigned_recover_natural {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    {I : Type*} [Fintype I] (M : Matrix I I ℤ) (f : V →+ W) (H : I → V) (i : I) :
    f (∑ j, M j i • H j) = ∑ j, M j i • f (H j) := by
  simp only [map_sum, map_zsmul]

theorem complete_one_eq_elementary_one (N : ℕ) : completePoly N 1 = elementaryPoly N 1 := by
  have h := elementary_complete_inverse N 1 (by omega)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.sub_zero,
    Nat.sub_self, elementaryPoly_zero, completePoly_zero, _root_.one_mul, _root_.mul_one] at h
  norm_num at h
  exact sub_eq_zero.mp (by simpa [sub_eq_add_neg] using h)

theorem evaluation_on_elementary (N k : ℕ) :
    completeEvaluation N (CompleteChangeOfGenerators.completeToElementary
      (CompleteElementary.h k)) = elementaryPoly N k := by
  rw [CompleteChangeOfGenerators.completeToElementary_h, completeEvaluation_elementary]

/-- The source relation that is nontrivial in lowest degree (a,b)=(0,3) of (2.12) for
elementary sums, as an exact fixture in every alphabet: 2e₃ = e₁e₂ + e₂e₁. -/
theorem elementary_fixture_03 (N : ℕ) :
    elementaryPoly N 1 * elementaryPoly N 2 + elementaryPoly N 2 * elementaryPoly N 1 =
      (2 : ℤ) • elementaryPoly N 3 := by
  simpa using ElementaryRelations.elementary_one_even N 1

end OddMath.Frontier.OddLREKIdentificationControls
