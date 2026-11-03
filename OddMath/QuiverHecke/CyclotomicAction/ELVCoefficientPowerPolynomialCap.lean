import OddMath.QuiverHecke.CyclotomicAction.ELVCoefficientPowerMomentMaps
import Mathlib.Data.Nat.Choose.Sum

/-! # Polynomial coefficient-extraction caps on the power vacuum

The candidate cap λg(y) in `SwappedVacuumNonpositiveBubbles.md`, §§3–4,
is evaluated using the original signed dot and the prescribed last inverse
row on literal A/T. Identification with the mixed inverse cap is separate.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.PowerVacuumCoefficient
open CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (L : I × ℕ → ℕ)

private abbrev polynomialCapTarget (i : I) :=
  mateTargetSpace D Sc cutoff i (coefficientPowerVacuum D Sc cutoff L) ⟨[]⟩
private def polynomialCapDot (i : I) : Module.End k (polynomialCapTarget D Sc cutoff L i) :=
  actualInductionDot D Sc cutoff i (coefficientPowerVacuum D Sc cutoff L)
    ((append D Sc cutoff i).obj ⟨[]⟩)

/-- The coefficient-extraction functional after the literal plus-one probe polynomial. -/
def polynomialCap (i : I) (hN : 0 < cutoff i) (M : ℕ) :
    polynomialCapTarget D Sc cutoff L i →ₗ[k] CoefficientPowerQuotient (k := k) D cutoff L :=
  (functional D Sc cutoff L i hN).comp ((polynomialCapDot D Sc cutoff L i ^ 2 + 1) ^ M)

/-- Its actual dotted unit closures on every quotient coefficient vector. -/
def polynomialCapMoment (i : I) (hN : 0 < cutoff i) (M n : ℕ) :
    Module.End k (CoefficientPowerQuotient (k := k) D cutoff L) :=
  (polynomialCap D Sc cutoff L i hN M).comp
    ((polynomialCapDot D Sc cutoff L i ^ n).comp (unit D Sc cutoff L i))

private def capMomentLinear (i : I) (hN : 0 < cutoff i) (n : ℕ) :
    Module.End k (polynomialCapTarget D Sc cutoff L i) →ₗ[k]
      Module.End k (CoefficientPowerQuotient (k := k) D cutoff L) where
  toFun f := (functional D Sc cutoff L i hN).comp
    (f.comp ((polynomialCapDot D Sc cutoff L i ^ n).comp (unit D Sc cutoff L i)))
  map_add' f g := by
    apply LinearMap.ext
    intro z
    simp only [LinearMap.comp_apply, LinearMap.add_apply, map_add]
  map_smul' r f := by
    apply LinearMap.ext
    intro z
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, map_smul, RingHom.id_apply]

private theorem capMomentLinear_pow (i : I) (hN : 0 < cutoff i) (n a : ℕ) :
    capMomentLinear D Sc cutoff L i hN n (polynomialCapDot D Sc cutoff L i ^ a) =
      momentMap D Sc cutoff L i hN (a + n) := by
  change (functional D Sc cutoff L i hN).comp
    ((polynomialCapDot D Sc cutoff L i ^ a).comp
      ((polynomialCapDot D Sc cutoff L i ^ n).comp (unit D Sc cutoff L i))) = _
  rw [← LinearMap.comp_assoc]
  change (functional D Sc cutoff L i hN).comp
    (((polynomialCapDot D Sc cutoff L i ^ a) * (polynomialCapDot D Sc cutoff L i ^ n)).comp
      (unit D Sc cutoff L i)) = _
  rw [← pow_add]
  rfl

/-- Ordered binomial moments are actual endomorphisms of A/T, including
all odd and inhomogeneous input vectors. -/
theorem polynomialCapMoment_sum (i : I) (hN : 0 < cutoff i) (M n : ℕ) :
    polynomialCapMoment D Sc cutoff L i hN M n =
      ∑ j ∈ Finset.range (M + 1), M.choose j • momentMap D Sc cutoff L i hN (2 * j + n) := by
  change capMomentLinear D Sc cutoff L i hN n
    ((polynomialCapDot D Sc cutoff L i ^ 2 + 1) ^ M) = _
  rw [(Commute.one_right (polynomialCapDot D Sc cutoff L i ^ 2)).add_pow]
  simp only [one_pow, mul_one, ← nsmul_eq_mul', ← pow_mul, map_sum, map_nsmul,
    capMomentLinear_pow]

private theorem momentMap_below_top_zero (i : I) (hN : 0 < cutoff i) (n : ℕ)
    (hn : n < cutoff i) (hne : n + 1 ≠ cutoff i) :
    momentMap D Sc cutoff L i hN n = 0 := by
  apply LinearMap.ext
  intro z
  change momentMap D Sc cutoff L i hN n z = 0
  have h := functional_dot_window D Sc cutoff L i hN n hn z
  change momentMap D Sc cutoff L i hN n z = if n + 1 = cutoff i then z else 0 at h
  simpa only [ite_eq_right hne] using h

/-- At zero external height the lower even probe powers are killed by the
actual coefficient window. The closure is the first higher moment map. -/
theorem polynomialCapMoment_zero_height (i : I) (hN : 0 < cutoff i) (M : ℕ)
    (hcut : cutoff i = 2 * M) :
    polynomialCapMoment D Sc cutoff L i hN M 0 = momentMap D Sc cutoff L i hN (cutoff i) := by
  rw [polynomialCapMoment_sum]
  calc
    _ = M.choose M • momentMap D Sc cutoff L i hN (2 * M + 0) := by
      apply Finset.sum_eq_single M
      · intro j hj hjM
        have hjle : j ≤ M := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
        have hjlt : j < M := by omega
        have hn : 2 * j + 0 < cutoff i := by omega
        have hne : 2 * j + 0 + 1 ≠ cutoff i := by omega
        rw [momentMap_below_top_zero D Sc cutoff L i hN _ hn hne, nsmul_zero]
      · simp
    _ = _ := by rw [Nat.choose_self, one_nsmul, Nat.add_zero, ← hcut]

/-- The actual zero-height polynomial-cap closure is minus the original
left exterior coefficient operator on every vector of literal A/T.
Its identification with the prescribed mixed inverse cap is separate. -/
theorem polynomialCapMoment_zero_height_odd (i : I) (hi : D.parity i = 1)
    (hN : 0 < cutoff i) (M : ℕ) (hcut : cutoff i = 2 * M) :
    polynomialCapMoment D Sc cutoff L i hN M 0 =
      LinearMap.mulLeft k (-(coefficientPowerQuotientMap D cutoff L
        (SKM.SYM.delta D k ⟨i, hi⟩))) := by
  rw [polynomialCapMoment_zero_height D Sc cutoff L i hN M hcut,
    momentMap_first_odd D Sc cutoff L i hi hN]
  have he : Even (cutoff i) := ⟨M, by omega⟩
  have hs : (-1 : k) ^ (cutoff i + 1) = -1 := by
    rw [pow_succ, he.neg_one_pow, one_mul]
  rw [hs]
  exact congrArg (LinearMap.mulLeft k)
    (neg_one_smul k (coefficientPowerQuotientMap D cutoff L (SKM.SYM.delta D k ⟨i, hi⟩)))

end OddMath.QuiverHecke.ELVOld.PowerVacuumCoefficient
