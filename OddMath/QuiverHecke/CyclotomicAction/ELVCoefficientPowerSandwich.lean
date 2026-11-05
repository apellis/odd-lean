import OddMath.QuiverHecke.CyclotomicAction.ELVCoefficientPowerComparison
import OddMath.SKM.ELVCoefficientPowers

/-! # The power/weight sandwich in the actual ELV coefficient algebra

The universal bounds from `ELVCoefficientPowers` descend through the actual
ELV coefficient quotient to the literal module comparison functors of
`SwappedNondegeneracy.md`, §2. No weighted/power quotient equality or
vacuum evaluation-kernel identification is asserted.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The paper's even elementary generators in the actual full ELV
coefficient quotient. The higher killed generators cause no change. -/
def elementaryCoefficients (a : I × ℕ) :
    SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff :=
  SKM.SYM.elvCoefficientQuotient D cutoff (SKM.SYM.e D k a.1 a.2)

theorem elementaryCoefficients_even (a : I × ℕ) :
    elementaryCoefficients (k := k) D cutoff a ∈ SKM.SYM.elvCoefficientParity D cutoff 0 := by
  have h := SKM.SYM.elvModelQuotient_mem D (cutoff := cutoff)
    (SKM.SYM.polynomialExterior_e_mem_even D (k := k) a.1 a.2)
  simpa only [elementaryCoefficients, SKM.SYM.elvModelQuotient, AlgHom.comp_apply,
    AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply] using h

variable [Fintype I]

/-- The upper finite power bound descends to the actual ELV coefficient
algebra by killing its defining ideal and taking literal power images. -/
theorem weighted_le_elementaryPowerIdeal (L : I × ℕ → ℕ) :
    coefficientWeightedIdeal (k := k) D cutoff
      (SKM.SYM.elvPowerWeightBound D cutoff L + 1) ≤
        coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L := by
  let T := coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L
  let q := (SKM.SYM.elvCoefficientQuotient (k := k) D cutoff).toRingHom
  have hJ : SKM.SYM.elvCoefficientIdeal D k cutoff ≤ T.comap q := by
    intro a ha
    apply (TwoSidedIdeal.mem_comap q).mpr
    change SKM.SYM.elvCoefficientQuotient D cutoff a ∈ T
    rw [SKM.SYM.elvCoefficientQuotient_eq_zero D ha]
    exact TwoSidedIdeal.zero_mem _
  have hP : SKM.SYM.coefficientPowerIdeal D k L ≤ T.comap q := by
    apply TwoSidedIdeal.span_le.mpr
    rintro _ ⟨a, rfl⟩
    apply (TwoSidedIdeal.mem_comap q).mpr
    change SKM.SYM.elvCoefficientQuotient D cutoff (SKM.SYM.e D k a.1 a.2 ^ L a) ∈ T
    rw [map_pow]
    exact TwoSidedIdeal.subset_span (Set.mem_range_self a)
  apply TwoSidedIdeal.span_le.mpr
  rintro _ ⟨b, hb, rfl⟩
  apply (TwoSidedIdeal.mem_comap q).mp
  exact (sup_le hJ hP) (SKM.SYM.coefficientBasis_mem_elv_sup_power D k cutoff L b (by omega))

/-- The actual power-to-weighted module functor at the explicit finite
upper bound. No algebraic ideal-containment hypothesis remains. -/
def elementaryPowerToWeighted (L : I × ℕ → ℕ) :=
  powerToWeighted D Sc cutoff (elementaryCoefficients (k := k) D cutoff) L
    (SKM.SYM.elvPowerWeightBound D cutoff L + 1)
    (weighted_le_elementaryPowerIdeal D cutoff L)

end OddMath.QuiverHecke.ELVOld
