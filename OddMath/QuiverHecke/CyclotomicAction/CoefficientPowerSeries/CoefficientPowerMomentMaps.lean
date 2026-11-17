import Mathlib.CategoryTheory.Category.ULift
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Expand
import OddMath.QuiverHecke.CyclotomicAction.CoefficientPowerSeries.CoefficientPowerVacuum

/-!
# Coefficient power series

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # Full moment maps on the literal coefficient-power vacuum

The all-vector interpretation of the scalar reservoir series in
`SwappedVacuumNonpositiveBubbles.md`, §2. The actual ordinary unit,
signed induction dot and prescribed inverse row define the maps.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.PowerVacuumCoefficient
open CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (L : I × ℕ → ℕ)

private abbrev coefficientProjection :=
  (coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon.mkₐ k
private abbrev target (i : I) := mateTargetSpace D Sc cutoff i (coefficientPowerVacuum D Sc cutoff L) ⟨[]⟩
private def dot (i : I) : Module.End k (target D Sc cutoff L i) :=
  inductionDot D Sc cutoff i (coefficientPowerVacuum D Sc cutoff L)
    ((append D Sc cutoff i).obj ⟨[]⟩)
private def outputCoefficient (i : I)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
    Module.End k (target D Sc cutoff L i) :=
  SVec.toLinearMap (((BalancedInduction.restriction (append D Sc cutoff i)).obj
    ((BalancedInduction.induction (append D Sc cutoff i)).obj
      (coefficientPowerVacuum D Sc cutoff L))).map (X := ⟨[]⟩) (Y := ⟨[]⟩)
        (coefficientEndomorphism D Sc cutoff [] a))

/-- The actual signed n-th-dot moment on every input vector of literal A/T. -/
def momentMap (i : I) (hN : 0 < cutoff i) (n : ℕ) :
    Module.End k (CoefficientPowerQuotient (k := k) D cutoff L) :=
  (functional D Sc cutoff L i hN).comp
    ((dot D Sc cutoff L i ^ n).comp (unit D Sc cutoff L i))

private theorem unit_eq (i : I) (z : CoefficientPowerQuotient (k := k) D cutoff L) :
    unit D Sc cutoff L i z = BalancedInduction.unit (append D Sc cutoff i)
      (coefficientPowerVacuum D Sc cutoff L).toFunctor (⟨[]⟩ : OldCategory D Sc cutoff)
        (coefficientPowerVacuumEmptyEquiv D Sc cutoff L z) := by
  exact adjunctionUnit_total_apply D Sc cutoff i (coefficientPowerVacuum D Sc cutoff L)
    (⟨[]⟩ : OldCategory D Sc cutoff) (coefficientPowerVacuumEmptyEquiv D Sc cutoff L z)

private theorem unit_coefficient (i : I)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff)
    (z : CoefficientPowerQuotient (k := k) D cutoff L) :
    outputCoefficient D Sc cutoff L i a (unit D Sc cutoff L i z) =
      unit D Sc cutoff L i (coefficientProjection D cutoff L a * z) := by
  let M := coefficientPowerVacuum D Sc cutoff L
  let J := append D Sc cutoff i
  let f : (⟨[]⟩ : OldCategory D Sc cutoff) ⟶ ⟨[]⟩ := coefficientEndomorphism D Sc cutoff [] a
  have h := LinearMap.congr_fun (BalancedInduction.unit_naturality J M.toFunctor f)
    (coefficientPowerVacuumEmptyEquiv D Sc cutoff L z)
  simp only [LinearMap.comp_apply] at h
  change outputCoefficient D Sc cutoff L i a
    (BalancedInduction.unit J M.toFunctor (⟨[]⟩ : OldCategory D Sc cutoff)
      (coefficientPowerVacuumEmptyEquiv D Sc cutoff L z)) =
    BalancedInduction.unit J M.toFunctor (⟨[]⟩ : OldCategory D Sc cutoff)
      ((coefficientPowerVacuum D Sc cutoff L).map (X := ⟨[]⟩) (Y := ⟨[]⟩)
        (coefficientEndomorphism D Sc cutoff [] a) (coefficientPowerVacuumEmptyEquiv D Sc cutoff L z)) at h
  rw [empty_coefficient_action D Sc cutoff L a z] at h
  simpa only [unit_eq] using h

private theorem scalar_commuting_power {V : Type u} [AddCommGroup V] [Module k V]
    (d a : Module.End k V) (s : k) (h : d.comp a = s • (a.comp d)) (n : ℕ) :
    (d ^ n).comp a = s ^ n • (a.comp (d ^ n)) := by
  have h' : d.comp a = a.comp (s • d) := by simpa only [LinearMap.comp_smul] using h
  have hp := Module.End.commute_pow_left_of_commute h' n
  simpa only [smul_pow, LinearMap.comp_smul] using hp

private theorem sign_nsmul (p : ZMod 2) (n : ℕ) : sign k (n • p) = sign k p ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [succ_nsmul, sign_add, ih, pow_succ]

private theorem dot_pow_coefficient (i : I) {p : ZMod 2}
    {a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff}
    (ha : a ∈ SKM.SYM.elvCoefficientParity D cutoff p) (n : ℕ) :
    (dot D Sc cutoff L i ^ n).comp (outputCoefficient D Sc cutoff L i a) =
      koszulSign (n • D.parity i) p •
        ((outputCoefficient D Sc cutoff L i a).comp (dot D Sc cutoff L i ^ n)) := by
  let M := coefficientPowerVacuum D Sc cutoff L
  let J := append D Sc cutoff i
  let f : J.obj (⟨[]⟩ : OldCategory D Sc cutoff) ⟶ J.obj ⟨[]⟩ :=
    J.map (X := ⟨[]⟩) (Y := ⟨[]⟩) (coefficientEndomorphism D Sc cutoff [] a)
  have hf : f ∈ parity (R := k) _ _ p :=
    IsSuperfunctor.map_mem (F := J) (coefficientEndomorphism_mem D Sc cutoff [] ha)
  have h := (BalancedInduction.transformLinear_supernatural
    (oldAppendDot_supernatural D Sc cutoff i) M).naturality hf
  change (dot D Sc cutoff L i).comp (outputCoefficient D Sc cutoff L i a) =
    sign k (D.parity i * p) •
      ((outputCoefficient D Sc cutoff L i a).comp (dot D Sc cutoff L i)) at h
  have hp := scalar_commuting_power (dot D Sc cutoff L i) (outputCoefficient D Sc cutoff L i a)
    (sign k (D.parity i * p)) h n
  rw [← sign_nsmul] at hp
  have he : n • (D.parity i * p) = (n • D.parity i) * p := by
    simp only [nsmul_eq_mul]
    ring
  rw [he, ← koszulSign_smul (R := k)] at hp
  exact hp

/-- Full coefficient superlinearity of every higher moment map, with
its total parity and the original left coefficient order. -/
theorem momentMap_coefficient (i : I) (hN : 0 < cutoff i) (n : ℕ) {p : ZMod 2}
    {a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff}
    (ha : a ∈ SKM.SYM.elvCoefficientParity D cutoff p) :
    momentMap D Sc cutoff L i hN n (coefficientProjection D cutoff L a) =
      koszulSign ((n + (cutoff i - 1)) • D.parity i) p •
        (coefficientProjection D cutoff L a * signedMoment D Sc cutoff L i hN n) := by
  have hu := unit_coefficient D Sc cutoff L i a (1 : CoefficientPowerQuotient (k := k) D cutoff L)
  rw [mul_one] at hu
  have hd := LinearMap.congr_fun (dot_pow_coefficient D Sc cutoff L i ha n)
    (unit D Sc cutoff L i 1)
  have h := congrArg (functional D Sc cutoff L i hN) hd
  simp only [LinearMap.comp_apply, LinearMap.smul_apply] at h
  have hcap := functional_coefficient D Sc cutoff L i hN ha
    ((dot D Sc cutoff L i ^ n) (unit D Sc cutoff L i 1))
  change functional D Sc cutoff L i hN
    (outputCoefficient D Sc cutoff L i a ((dot D Sc cutoff L i ^ n) (unit D Sc cutoff L i 1))) =
    koszulSign ((cutoff i - 1) • D.parity i) p •
      (coefficientProjection D cutoff L a * signedMoment D Sc cutoff L i hN n) at hcap
  rw [map_zsmul, hcap] at h
  rw [smul_smul, ← koszulSign_add_left, ← add_nsmul] at h
  change functional D Sc cutoff L i hN
    ((dot D Sc cutoff L i ^ n) (outputCoefficient D Sc cutoff L i a (unit D Sc cutoff L i 1))) = _ at h
  rw [hu] at h
  exact h

private theorem unit_apply_mem (i : I) {p : ZMod 2}
    {z : CoefficientPowerQuotient (k := k) D cutoff L}
    (hz : z ∈ coefficientPowerParity D cutoff L p) :
    unit D Sc cutoff L i z ∈ (target D Sc cutoff L i).part p := by
  rw [unit_eq]
  have h := SVec.apply_mem_part (BalancedInduction.unit_mem (append D Sc cutoff i)
    (coefficientPowerVacuum D Sc cutoff L) (⟨[]⟩ : OldCategory D Sc cutoff))
      (coefficientPowerVacuumEmptyEquiv_mem D Sc cutoff L hz)
  change BalancedInduction.unit (append D Sc cutoff i)
    (coefficientPowerVacuum D Sc cutoff L).toFunctor (⟨[]⟩ : OldCategory D Sc cutoff)
      (coefficientPowerVacuumEmptyEquiv D Sc cutoff L z) ∈
        (target D Sc cutoff L i).part (p + 0) at h
  simpa only [add_zero] using h

private theorem dot_pow_apply_mem (i : I) {p : ZMod 2}
    {z : target D Sc cutoff L i} (hz : z ∈ (target D Sc cutoff L i).part p) (n : ℕ) :
    (dot D Sc cutoff L i ^ n) z ∈ (target D Sc cutoff L i).part (p + n • D.parity i) := by
  induction n with
  | zero => simpa only [pow_zero, Module.End.one_apply, zero_nsmul, add_zero] using hz
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply]
    have h := SVec.apply_mem_part (BalancedInduction.transformLinear_mem
      (oldAppendDot_supernatural D Sc cutoff i) (coefficientPowerVacuum D Sc cutoff L)
        ((append D Sc cutoff i).obj (⟨[]⟩ : OldCategory D Sc cutoff))) ih
    change dot D Sc cutoff L i ((dot D Sc cutoff L i ^ n) z) ∈
      (target D Sc cutoff L i).part ((p + n • D.parity i) + D.parity i) at h
    simpa only [succ_nsmul, add_assoc] using h

/-- The actual full moment map retains the total parity of its chosen
inverse row and all n signed dots. -/
theorem momentMap_mem (i : I) (hN : 0 < cutoff i) (n : ℕ) :
    momentMap D Sc cutoff L i hN n ∈ parity (R := k)
      (coefficientPowerSpace D cutoff L) (coefficientPowerSpace D cutoff L)
        ((n + (cutoff i - 1)) • D.parity i) := by
  apply SVec.mem_parityHom_of_apply_mem
  intro p z hz
  have hu := unit_apply_mem D Sc cutoff L i hz
  have hd := dot_pow_apply_mem D Sc cutoff L i hu n
  have h := SVec.apply_mem_part (functional_mem D Sc cutoff L i hN) hd
  change momentMap D Sc cutoff L i hN n z ∈
    (coefficientPowerSpace D cutoff L).part (p + ((n + (cutoff i - 1)) • D.parity i))
  change momentMap D Sc cutoff L i hN n z ∈
    (coefficientPowerSpace D cutoff L).part ((p + n • D.parity i) + (cutoff i - 1) • D.parity i) at h
  simpa only [add_nsmul, add_assoc] using h

private theorem homogeneous_lift {p : ZMod 2}
    {z : CoefficientPowerQuotient (k := k) D cutoff L}
    (hz : z ∈ coefficientPowerParity D cutoff L p) :
    ∃ a ∈ SKM.SYM.elvCoefficientParity D cutoff p, coefficientProjection D cutoff L a = z := by
  obtain ⟨a, rfl⟩ := RingCon.mkₐ_surjective (α := k)
    (coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon z
  refine ⟨GradedAlgebra.proj (SKM.SYM.elvCoefficientParity D cutoff) p a,
    (DirectSum.decompose (SKM.SYM.elvCoefficientParity D cutoff) a p).property, ?_⟩
  rw [← coefficientPowerSpace_projection D cutoff L p a]
  exact (SVec.mem_part_iff _).mp hz

private theorem homogeneous_comm {p q : ZMod 2}
    {a b : CoefficientPowerQuotient (k := k) D cutoff L}
    (ha : a ∈ coefficientPowerParity D cutoff L p)
    (hb : b ∈ coefficientPowerParity D cutoff L q) :
    a * b = koszulSign p q • (b * a) := by
  obtain ⟨a0, ha0, ea⟩ := homogeneous_lift D cutoff L ha
  obtain ⟨b0, hb0, eb⟩ := homogeneous_lift D cutoff L hb
  rw [← ea, ← eb]
  have h := congrArg (coefficientProjection D cutoff L) (ELVPScalar.elv_comm D cutoff ha0 hb0)
  simpa only [map_mul, map_zsmul] using h

/-- Every actual higher moment on every coefficient vector is the original
left multiplication by its proved scalar value on 1. No bubble-value
hypothesis or ordinary commutativity of A/T is used. -/
theorem momentMap_apply (i : I) (hN : 0 < cutoff i) (n : ℕ)
    (z : CoefficientPowerQuotient (k := k) D cutoff L) :
    momentMap D Sc cutoff L i hN n z = signedMoment D Sc cutoff L i hN n * z := by
  have hvalue : signedMoment D Sc cutoff L i hN n ∈
      coefficientPowerParity D cutoff L ((n + (cutoff i - 1)) • D.parity i) := by
    have h := SVec.apply_mem_part (momentMap_mem D Sc cutoff L i hN n)
      (SetLike.one_mem_graded (coefficientPowerParity (k := k) D cutoff L))
    change signedMoment D Sc cutoff L i hN n ∈ coefficientPowerParity D cutoff L
      (0 + ((n + (cutoff i - 1)) • D.parity i)) at h
    simpa only [zero_add] using h
  have hh {p : ZMod 2} {a : CoefficientPowerQuotient (k := k) D cutoff L}
      (ha : a ∈ coefficientPowerParity D cutoff L p) :
      momentMap D Sc cutoff L i hN n a = signedMoment D Sc cutoff L i hN n * a := by
    obtain ⟨b, hb, rfl⟩ := homogeneous_lift D cutoff L ha
    have h := momentMap_coefficient D Sc cutoff L i hN n hb
    have hc := homogeneous_comm D cutoff L (coefficientPowerQuotient_mem D cutoff L hb) hvalue
    have hs : koszulSign ((n + (cutoff i - 1)) • D.parity i) p *
        koszulSign p ((n + (cutoff i - 1)) • D.parity i) = 1 := by
      rw [koszulSign_comm p _, koszulSign_mul_self]
    rw [hc, smul_smul, hs, one_smul] at h
    exact h
  have hz : z = (coefficientPowerSpace D cutoff L).proj 0 z +
      (coefficientPowerSpace D cutoff L).proj 1 z :=
    ((coefficientPowerSpace D cutoff L).proj_apply_add z).symm
  calc
    _ = momentMap D Sc cutoff L i hN n
        ((coefficientPowerSpace D cutoff L).proj 0 z + (coefficientPowerSpace D cutoff L).proj 1 z) :=
      congrArg (momentMap D Sc cutoff L i hN n) hz
    _ = _ := by
      rw [map_add, hh ((coefficientPowerSpace D cutoff L).proj_mem_part 0 z),
        hh ((coefficientPowerSpace D cutoff L).proj_mem_part 1 z), ← mul_add, ← hz]

/-- The same all-vector identity as an endomorphism equality, for use
when whiskering the source bubble map through a chosen word functor. -/
theorem momentMap_eq_mulLeft (i : I) (hN : 0 < cutoff i) (n : ℕ) :
    momentMap D Sc cutoff L i hN n = LinearMap.mulLeft k (signedMoment D Sc cutoff L i hN n) := by
  apply LinearMap.ext
  intro z
  exact momentMap_apply D Sc cutoff L i hN n z

/-- The complete even-index odd-colour reservoir series, as literal
endomorphisms on every vector of the actual power quotient. -/
theorem momentMap_even (i : I) (hi : D.parity i = 1) (hN : 0 < cutoff i) (r : ℕ) :
    momentMap D Sc cutoff L i hN (cutoff i - 1 + 2 * r) =
      LinearMap.mulLeft k (completeCoefficient D cutoff L i r) := by
  rw [momentMap_eq_mulLeft, signedMoment_even D Sc cutoff L i hi hN r]

/-- The complete odd-index reservoir series as literal endomorphisms,
retaining the original left exterior coefficient. -/
theorem momentMap_odd (i : I) (hi : D.parity i = 1) (hN : 0 < cutoff i) (r : ℕ) :
    momentMap D Sc cutoff L i hN (cutoff i - 1 + (2 * r + 1)) =
      LinearMap.mulLeft k ((-1 : k) ^ (cutoff i + 1) •
        (coefficientPowerQuotientMap D cutoff L (SKM.SYM.delta D k ⟨i, hi⟩) *
          completeCoefficient D cutoff L i r)) := by
  rw [momentMap_eq_mulLeft, signedMoment_odd D Sc cutoff L i hi hN r]

end OddMath.QuiverHecke.ELV.PowerVacuumCoefficient
end

end

section

/-! # Reservoir moments of an even moving colour on the power vacuum

The even-colour counterpart of `ELVCoefficientPowerOddSeries`
(`SwappedVacuumNonpositiveBubbles.md`, §2). For `D.parity i = 0` the signed
and raw moments agree, the actual one-strand relation is the reversed series
`E(-w) = Σₙ (-1)ⁿ eₙ wⁿ` (truncated by the cutoff relations of A/T), and the
higher reservoir moments are the coefficients of `1/E(-w)`:
`signedMoment (N - 1 + r) = completeCoefficient r`.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.PowerVacuumCoefficient
open CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (L : I × ℕ → ℕ)

private theorem coeff_monomial_mul_even {A : Type u} [Semiring A]
    (n l : ℕ) (a : A) (f : PowerSeries A) :
    PowerSeries.coeff l (PowerSeries.monomial n a * f) =
      if n ≤ l then a * PowerSeries.coeff (l - n) f else 0 := by
  change MvPowerSeries.coeff (Finsupp.single () l)
    (MvPowerSeries.monomial (Finsupp.single () n) a * f) = _
  rw [MvPowerSeries.coeff_monomial_mul]
  simp only [Finsupp.single_le_single, ← Finsupp.single_tsub]
  rfl

/-- For an even colour the triangular dot sign is trivial. -/
theorem even_signedMoment_rawMoment (i : I) (hi : D.parity i = 0) (hN : 0 < cutoff i) (n : ℕ) :
    signedMoment D Sc cutoff L i hN n = rawMoment D Sc cutoff L i hN 1 n := by
  rw [signedMoment_rawMoment, hi]
  simp only [inductionUnitDotSign, smul_zero, Supercategory.sign_zero, one_smul]

/-- The actual one-strand relation, with no Koszul sign for an even colour. -/
theorem even_rawMoment_recurrence (i : I) (hi : D.parity i = 0) (hN : 0 < cutoff i) (m : ℕ) :
    (∑ j : Fin (cutoff i + 1),
      (coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon.mkₐ k
        (singleCoefficient D cutoff i j) * rawMoment D Sc cutoff L i hN 1 (j.val + m)) = 0 := by
  have h := rawMoment_one_recurrence D Sc cutoff L i hN m
  rw [hi] at h
  simpa only [smul_zero, mul_zero, sub_zero, koszulSign_zero_left, one_smul] using h

/-- The low window of the actual even inverse row. -/
theorem even_rawMoment_window (i : I) (hi : D.parity i = 0) (hN : 0 < cutoff i)
    (n : ℕ) (hn : n < cutoff i) :
    rawMoment D Sc cutoff L i hN 1 n = if n + 1 = cutoff i then 1 else 0 := by
  rw [rawMoment_one_window D Sc cutoff L i hN n hn, hi]
  simp only [inductionUnitDotSign, smul_zero, Supercategory.sign_zero, one_smul]

/-- The even-colour top remainders at exponents N−1+l. -/
def evenRemainder (i : I) (hN : 0 < cutoff i) (l : ℕ) :
    CoefficientPowerQuotient (k := k) D cutoff L :=
  rawMoment D Sc cutoff L i hN 1 (cutoff i - 1 + l)

/-- Their complete series. -/
def evenRemainderSeries (i : I) (hN : 0 < cutoff i) :
    PowerSeries (CoefficientPowerQuotient (k := k) D cutoff L) :=
  PowerSeries.mk (evenRemainder D Sc cutoff L i hN)

theorem evenRemainder_zero (i : I) (hi : D.parity i = 0) (hN : 0 < cutoff i) :
    evenRemainder D Sc cutoff L i hN 0 = 1 := by
  have h := even_rawMoment_window D Sc cutoff L i hi hN (cutoff i - 1) (by omega)
  have ht : cutoff i - 1 + 1 = cutoff i := by omega
  simpa only [evenRemainder, Nat.add_zero, ite_eq_left ht] using h

theorem evenRemainder_recurrence (i : I) (hi : D.parity i = 0)
    (hN : 0 < cutoff i) (l : ℕ) (hl : 0 < l) :
    (∑ j : Fin (cutoff i + 1),
      (coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon.mkₐ k
        (singleCoefficient D cutoff i j) *
          (if cutoff i - j.val ≤ l then evenRemainder D Sc cutoff L i hN (l - (cutoff i - j.val))
           else 0)) = 0 := by
  calc
    _ = ∑ j : Fin (cutoff i + 1),
        (coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon.mkₐ k
          (singleCoefficient D cutoff i j) * rawMoment D Sc cutoff L i hN 1 (j.val + (l - 1)) := by
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      by_cases hj : cutoff i - j.val ≤ l
      · rw [ite_eq_left hj, evenRemainder]
        congr 1
        have hv := j.isLt
        omega
      · rw [ite_eq_right hj]
        have hv := j.isLt
        have he := even_rawMoment_window D Sc cutoff L i hi hN (j.val + (l - 1)) (by omega)
        have ht : ¬ j.val + (l - 1) + 1 = cutoff i := by omega
        simpa only [ite_eq_right ht] using he.symm
    _ = 0 := even_rawMoment_recurrence D Sc cutoff L i hi hN (l - 1)

/-- The reversed monic relation inverts the actual even remainder series. -/
theorem remainderPolynomial_mul_evenRemainderSeries (i : I) (hi : D.parity i = 0)
    (hN : 0 < cutoff i) :
    remainderPolynomial D cutoff L i * evenRemainderSeries D Sc cutoff L i hN = 1 := by
  classical
  apply PowerSeries.ext
  intro l
  simp only [remainderPolynomial, evenRemainderSeries, Finset.sum_mul, map_sum,
    coeff_monomial_mul_even, PowerSeries.coeff_mk, PowerSeries.coeff_one]
  by_cases hl : l = 0
  · subst l
    rw [ite_eq_left rfl]
    rw [Finset.sum_eq_single (Fin.last (cutoff i))]
    · simp only [Fin.val_last, Nat.sub_self, le_refl, ↓reduceIte,
        singleCoefficient_top, map_one, evenRemainder_zero D Sc cutoff L i hi hN, mul_one]
    · intro j _ hj
      have hne : j.val ≠ cutoff i := by
        intro h
        apply hj
        exact Fin.ext h
      have hv := j.isLt
      rw [ite_eq_right (by omega : ¬ cutoff i - j.val ≤ 0)]
    · simp
  · rw [ite_eq_right hl]
    simpa only [mul_ite, mul_zero] using evenRemainder_recurrence D Sc cutoff L i hi hN l (by omega)

private theorem even_reversed_coefficient (i : I) (hi : D.parity i = 0)
    (n : ℕ) (hn : n ≤ cutoff i) :
    (coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon.mkₐ k
      (singleCoefficient D cutoff i ⟨cutoff i - n, by omega⟩) =
      (-1 : k) ^ n • coefficientPowerQuotientMap (k := k) D cutoff L
        (SKM.SYM.evenCyclotomicCoefficient D k i n) := by
  have h1 : ¬ D.parity i = 1 := by rw [hi]; decide
  unfold singleCoefficient
  rw [dite_eq_right h1, SKM.SYM.evenMonicCoefficient, map_smul, map_smul]
  rw [show cutoff i - (cutoff i - n) = n by omega]
  rfl

private theorem even_coefficient_tail (i : I) (hi : D.parity i = 0)
    (n : ℕ) (hn : cutoff i < n) :
    coefficientPowerQuotientMap (k := k) D cutoff L
      (SKM.SYM.evenCyclotomicCoefficient D k i n) = 0 := by
  apply (coefficientPowerQuotientMap_eq_zero_iff D cutoff L _).mpr
  apply TwoSidedIdeal.mem_sup_left
  obtain ⟨r, rfl⟩ : ∃ r, n = r + 1 := ⟨n - 1, by omega⟩
  apply TwoSidedIdeal.subset_span
  refine Or.inl ⟨i, r, ?_, rfl⟩
  rw [SKM.SYM.elvElementaryRank, ite_eq_left hi]
  omega

private theorem polynomial_generatorCoeff_even (i : I) (n : ℕ) :
    polynomialToPower (k := k) D cutoff L (PowerSeries.coeff n (SKM.SYM.generatorSeries k i)) =
      coefficientPowerQuotientMap D cutoff L (SKM.SYM.evenCyclotomicCoefficient D k i n) := by
  cases n with
  | zero =>
    simp [SKM.SYM.generatorSeries, SKM.SYM.generatorCoeff, SKM.SYM.evenCyclotomicCoefficient]
  | succ n =>
    simp [SKM.SYM.generatorSeries, SKM.SYM.generatorCoeff, SKM.SYM.evenCyclotomicCoefficient,
      polynomialToPower, AlgHom.comp_apply]

/-- For an even colour the reversed actual monic relation is the mapped
series `E(-w)` of the commutative polynomial algebra; the coefficients beyond
the cutoff vanish by the defining relations of A/T. -/
theorem even_remainderPolynomial (i : I) (hi : D.parity i = 0) :
    remainderPolynomial (k := k) D cutoff L i =
      PowerSeries.map (polynomialToPower D cutoff L).toRingHom
        (PowerSeries.rescale (-1) (SKM.SYM.generatorSeries k i)) := by
  classical
  apply PowerSeries.ext
  intro n
  have hs : (-1 : MvPolynomial (I × ℕ) k) ^ n =
      (-1 : k) ^ n • (1 : MvPolynomial (I × ℕ) k) := by
    rw [Algebra.smul_def, mul_one, map_pow, map_neg, map_one]
  have hr : PowerSeries.coeff n (PowerSeries.map (polynomialToPower (k := k) D cutoff L).toRingHom
      (PowerSeries.rescale (-1) (SKM.SYM.generatorSeries k i))) =
      (-1 : k) ^ n • coefficientPowerQuotientMap D cutoff L
        (SKM.SYM.evenCyclotomicCoefficient D k i n) := by
    rw [PowerSeries.coeff_map, PowerSeries.coeff_rescale, hs, smul_mul_assoc, one_mul]
    change polynomialToPower (k := k) D cutoff L _ = _
    rw [map_smul, polynomial_generatorCoeff_even]
  rw [hr, remainderPolynomial, map_sum]
  by_cases hn : n ≤ cutoff i
  · let j : Fin (cutoff i + 1) := ⟨cutoff i - n, by omega⟩
    rw [Finset.sum_eq_single j]
    · rw [PowerSeries.coeff_monomial, ite_eq_left (by dsimp [j]; omega)]
      exact even_reversed_coefficient D cutoff L i hi n hn
    · intro b _ hb
      rw [PowerSeries.coeff_monomial, ite_eq_right]
      intro he
      apply hb
      apply Fin.ext
      have hv := b.isLt
      dsimp [j]
      omega
    · simp
  · rw [even_coefficient_tail D cutoff L i hi n (by omega), smul_zero]
    apply Finset.sum_eq_zero
    intro j _
    rw [PowerSeries.coeff_monomial, ite_eq_right (by have hv := j.isLt; omega)]

private theorem rescaled_generator_constantCoeff (i : I) :
    PowerSeries.constantCoeff (PowerSeries.rescale (-1 : MvPolynomial (I × ℕ) k)
      (SKM.SYM.generatorSeries k i)) = ((1 : (MvPolynomial (I × ℕ) k)ˣ) : _) := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_rescale, pow_zero,
    one_mul]
  simp [SKM.SYM.generatorSeries, SKM.SYM.generatorCoeff]

/-- The actual even remainder series is the mapped inverse of `E(-w)`. -/
theorem evenRemainderSeries_eq (i : I) (hi : D.parity i = 0) (hN : 0 < cutoff i) :
    evenRemainderSeries D Sc cutoff L i hN =
      PowerSeries.map (polynomialToPower D cutoff L).toRingHom
        (PowerSeries.invOfUnit (PowerSeries.rescale (-1) (SKM.SYM.generatorSeries k i)) 1) := by
  have hQP : PowerSeries.map (polynomialToPower (k := k) D cutoff L).toRingHom
        (PowerSeries.invOfUnit (PowerSeries.rescale (-1) (SKM.SYM.generatorSeries k i)) 1) *
      remainderPolynomial D cutoff L i = 1 := by
    rw [even_remainderPolynomial D cutoff L i hi, ← map_mul,
      PowerSeries.invOfUnit_mul _ _ (rescaled_generator_constantCoeff (k := k) i), map_one]
  calc
    _ = (PowerSeries.map (polynomialToPower (k := k) D cutoff L).toRingHom
          (PowerSeries.invOfUnit (PowerSeries.rescale (-1) (SKM.SYM.generatorSeries k i)) 1) *
        remainderPolynomial D cutoff L i) * evenRemainderSeries D Sc cutoff L i hN := by
      rw [hQP, one_mul]
    _ = _ := by
      rw [mul_assoc, remainderPolynomial_mul_evenRemainderSeries D Sc cutoff L i hi hN, mul_one]

/-- Every higher reservoir moment of an even colour is the actual mapped
coefficient of `1/E(-z)`. -/
theorem even_colour_signedMoment (i : I) (hi : D.parity i = 0) (hN : 0 < cutoff i) (r : ℕ) :
    signedMoment D Sc cutoff L i hN (cutoff i - 1 + r) =
      completeCoefficient D cutoff L i r := by
  rw [even_signedMoment_rawMoment D Sc cutoff L i hi hN]
  have h := congrArg (PowerSeries.coeff r) (evenRemainderSeries_eq D Sc cutoff L i hi hN)
  rw [evenRemainderSeries, PowerSeries.coeff_mk, PowerSeries.coeff_map] at h
  exact h

end OddMath.QuiverHecke.ELV.PowerVacuumCoefficient
end

end
