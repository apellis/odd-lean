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

private theorem quotient_mem_weighted (N : ℕ) {a : SKM.SYM D k}
    (ha : a ∈ SKM.SYM.CoefficientAtLeast D k N) :
    SKM.SYM.elvCoefficientQuotient D cutoff a ∈ coefficientWeightedIdeal D cutoff N := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨b, hb, rfl⟩ := ha
    exact TwoSidedIdeal.subset_span ⟨b, hb, rfl⟩
  | zero => rw [map_zero]; exact TwoSidedIdeal.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact TwoSidedIdeal.add_mem _ ha hb
  | smul r a _ ha =>
    rw [map_smul]
    simpa only [Algebra.smul_def] using
      (coefficientWeightedIdeal (k := k) D cutoff N).mul_mem_left
        (algebraMap k _ r) (SKM.SYM.elvCoefficientQuotient D cutoff a) ha

/-- Every sufficiently high even power belongs to the actual weighted
coefficient ideal. Only the stated generator-weight inequalities are used. -/
theorem elementaryPowerIdeal_le_weighted (L : I × ℕ → ℕ) (N : ℕ)
    (hL : ∀ a, N ≤ L a * SKM.SYM.elementaryWeight D a) :
    coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L ≤
      coefficientWeightedIdeal D cutoff N := by
  apply TwoSidedIdeal.span_le.mpr
  rintro _ ⟨a, rfl⟩
  change (SKM.SYM.elvCoefficientQuotient D cutoff (SKM.SYM.e D k a.1 a.2)) ^ L a ∈ _
  rw [← map_pow]
  exact quotient_mem_weighted D cutoff N
    (SKM.SYM.coefficientAtLeast_antitone D k (hL a)
      (SKM.SYM.elementary_pow_mem_coefficientAtLeast D k a (L a)))

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

/-- The actual weighted-to-power module functor for the paper's
elementary family, with the lower numerical bound proved rather than assumed. -/
def elementaryWeightedToPower (L : I × ℕ → ℕ) (N : ℕ)
    (hL : ∀ a, N ≤ L a * SKM.SYM.elementaryWeight D a) :=
  weightedToPower D Sc cutoff (elementaryCoefficients (k := k) D cutoff) L N
    (elementaryPowerIdeal_le_weighted D cutoff L N hL)

/-- The actual power-to-weighted module functor at the explicit finite
upper bound. No algebraic ideal-containment hypothesis remains. -/
def elementaryPowerToWeighted (L : I × ℕ → ℕ) :=
  powerToWeighted D Sc cutoff (elementaryCoefficients (k := k) D cutoff) L
    (SKM.SYM.elvPowerWeightBound D cutoff L + 1)
    (weighted_le_elementaryPowerIdeal D cutoff L)

end OddMath.QuiverHecke.ELVOld
