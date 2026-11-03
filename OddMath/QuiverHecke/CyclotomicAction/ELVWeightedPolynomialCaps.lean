import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedPowerMomentMaps
import OddMath.QuiverHecke.CyclotomicAction.ELVUnitDotComponents
import OddMath.QuiverHecke.CyclotomicAction.ELVEndEvaluation
import OddMath.QuiverHecke.CyclotomicAction.ELVCoefficientPowerNonpositiveCap

/-! # Polynomial caps of the actual weighted power vacuum

The coefficient cap lambda(D^2+1)^M in
`SwappedVacuumNonpositiveBubbles.md`, §§3–4, is a literal module map:
apply the polynomial in the given restricted module dot, then the
prescribed weighted inverse row. Its unit/dot closures are evaluated on
every A/T vector. Identification with the mixed inverse cap remains separate.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped BigOperators
namespace OddMath.QuiverHecke.ELVOld
open BalancedInduction CyclotomicCrossingTensor
universe u

private def componentMomentLinear {k U : Type u} [CommRing k]
    [AddCommGroup U] [Module k U] (V : SVec k) (cap : V →ₗ[k] U) (cup : U →ₗ[k] V) :
    (Module.End k V) →ₗ[k] Module.End k U where
  toFun f := cap ∘ₗ f ∘ₗ cup
  map_add' f g := by
    apply LinearMap.ext
    intro z
    simp only [LinearMap.comp_apply, LinearMap.add_apply, map_add]
  map_smul' r f := by
    apply LinearMap.ext
    intro z
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, map_smul, RingHom.id_apply]

private theorem even_end_power_mem
    {k C : Type*} [CommRing k] [Category* C] [Preadditive C] [Linear k C] [Supercategory k C]
    {X : C} (x : End X) (hx : x ∈ parity (R := k) X X 0) (m : ℕ) :
    x ^ m ∈ parity (R := k) X X 0 := by
  induction m with
  | zero => simpa only [pow_zero, End.one_def] using id_mem (R := k) X
  | succ m ih => simpa only [pow_succ, End.mul_def, zero_add] using comp_mem hx ih

private theorem square_plus_one_power_even
    {k C : Type*} [CommRing k] [Category* C] [Preadditive C] [Linear k C] [Supercategory k C]
    {X : C} (x : End X) {p : ZMod 2} (hx : x ∈ parity (R := k) X X p) (m : ℕ) :
    (x ^ 2 + 1) ^ m ∈ parity (R := k) X X 0 := by
  have h2 : x ^ 2 ∈ parity (R := k) X X 0 := by
    simpa only [pow_two, End.mul_def, SKM.zmod2_add_self] using comp_mem hx hx
  have h1 : (1 : End X) ∈ parity (R := k) X X 0 := id_mem (R := k) X
  exact even_end_power_mem _ ((parity (R := k) X X 0).add_mem h2 h1) m

private theorem unitDotColumn_post_dot_power
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    (J : C ⥤ C) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
    (M : Superfunctor k C (SVec k)) (a n : ℕ) :
    unitDotColumn J hα M n ≫ restrictedDotEnd J hα M ^ a = unitDotColumn J hα M (a + n) := by
  rw [unitDotColumn_eq_restrictedDotEnd, unitDotColumn_eq_restrictedDotEnd, Category.assoc]
  congr 1
  change restrictedDotEnd J hα M ^ a * restrictedDotEnd J hα M ^ n =
    restrictedDotEnd J hα M ^ (a + n)
  exact (pow_add _ _ _).symm

private theorem unitDotColumn_post_dot_power_apply
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    (J : C ⥤ C) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
    (M : Superfunctor k C (SVec k)) (a n : ℕ) (w : C) (b : M.obj w) :
    (restrictedDotEnd J hα M ^ a).total w ((unitDotColumn J hα M n).total w b) =
      (unitDotColumn J hα M (a + n)).total w b := by
  have h := congrArg (fun f => f.total w) (unitDotColumn_post_dot_power J hα M a n)
  rw [Superfunctor.comp_total] at h
  simpa only [SVec.comp_apply] using congrArg (fun f => f b) h

namespace PowerVacuumCoefficient
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  [Fintype I] (L : I × ℕ → ℕ)
local notation "bound" => SKM.SYM.elvPowerWeightBound D cutoff L + 1
local notation "WM" => weightedVacuum D Sc cutoff L
local notation "Q" => oldTruncateFunctor D Sc cutoff bound
local notation "Q₀" => contentInclusion D Sc cutoff bound (0 : Multiset I)
local notation "AQ" => CoefficientPowerQuotient (k := k) D cutoff L

/-- The given restricted dot, as an endomorphism of the actual weighted
F/E module before total evaluation. -/
abbrev weightedModuleDot (i : I) :=
  restrictedDotEnd (truncatedAppend D Sc cutoff bound [i])
    (truncatedDot_supernatural D Sc cutoff bound i) WM

/-- Apply a given native module endomorphism before the actual prescribed
coefficient cap. The cap and both endpoints remain fixed. -/
def weightedCapAfter (i : I) (hN : 0 < cutoff i)
    (f : End ((restriction (truncatedAppend D Sc cutoff bound [i])).obj
      ((induction (truncatedAppend D Sc cutoff bound [i])).obj WM))) :
    (restriction Q₀).obj ((restriction (truncatedAppend D Sc cutoff bound [i])).obj
      ((induction (truncatedAppend D Sc cutoff bound [i])).obj WM)) ⟶ (restriction Q₀).obj WM :=
  (restriction Q₀).map f ≫ weightedCoefficientCap D Sc cutoff i L hN

/-- The actual weighted module-cap polynomial lambda(D^2+1)^M. -/
def weightedPolynomialCap (i : I) (hN : 0 < cutoff i) (M : ℕ) :=
  weightedCapAfter D Sc cutoff L i hN ((weightedModuleDot D Sc cutoff L i ^ 2 + 1) ^ M)

/-- The actual polynomial cap retains the last inverse row's degree:
the given dot square and its plus-one polynomial are even module maps. -/
theorem weightedPolynomialCap_mem (i : I) (hN : 0 < cutoff i) (M : ℕ) :
    weightedPolynomialCap D Sc cutoff L i hN M ∈
      parity (R := k) _ _ ((cutoff i - 1) • D.parity i) := by
  have hp := square_plus_one_power_even (weightedModuleDot D Sc cutoff L i)
    (restrictedDotEnd_mem (truncatedAppend D Sc cutoff bound [i])
      (truncatedDot_supernatural D Sc cutoff bound i) WM) M
  have hr := map_mem (restriction Q₀) hp
  simpa only [weightedPolynomialCap, weightedCapAfter, zero_add] using
    comp_mem hr (weightedCoefficientCap_mem D Sc cutoff i L hN)

/-- Linear evaluation of the given cap after native module endomorphisms,
with its prescribed n-th unit/dot column and original A/T coordinate. -/
def weightedCapMomentLinear (i : I) (hN : 0 < cutoff i) (n : ℕ) :
    End ((restriction (truncatedAppend D Sc cutoff bound [i])).obj
      ((induction (truncatedAppend D Sc cutoff bound [i])).obj WM)) →ₗ[k] Module.End k AQ :=
  (componentMomentLinear
    (((restriction (truncatedAppend D Sc cutoff bound [i])).obj
      ((induction (truncatedAppend D Sc cutoff bound [i])).obj WM)).obj ((Q).obj ⟨[]⟩))
    (weightedFunctional D Sc cutoff L i hN)
    (SVec.toLinearMap ((unitDotColumn (truncatedAppend D Sc cutoff bound [i])
      (truncatedDot_supernatural D Sc cutoff bound i) WM n).total ((Q).obj ⟨[]⟩)) ∘ₗ
        (weightedEmptyEquiv D Sc cutoff L).toLinearMap)).comp
    ((svecEndEvaluation
      (((restriction (truncatedAppend D Sc cutoff bound [i])).obj
        ((induction (truncatedAppend D Sc cutoff bound [i])).obj WM)).obj ((Q).obj ⟨[]⟩))).toLinearMap.comp
      (supernaturalTotalLinearMap _ _ ((Q).obj ⟨[]⟩)))

/-- These evaluations are exactly the closures of the actual module cap,
including its canonical output restriction and original empty coordinate. -/
theorem weightedCapMomentLinear_capAfter (i : I) (hN : 0 < cutoff i) (n : ℕ)
    (f : End ((restriction (truncatedAppend D Sc cutoff bound [i])).obj
      ((induction (truncatedAppend D Sc cutoff bound [i])).obj WM))) (a : AQ) :
    weightedCapMomentLinear D Sc cutoff L i hN n f a =
      (weightedEmptyEquiv D Sc cutoff L).symm
        ((weightedCapAfter D Sc cutoff L i hN f).total
          (⟨⟨[]⟩, rfl⟩ : ContentCategory D Sc cutoff bound 0)
          ((unitDotColumn (truncatedAppend D Sc cutoff bound [i])
            (truncatedDot_supernatural D Sc cutoff bound i) WM n).total ((Q).obj ⟨[]⟩)
              (weightedEmptyEquiv D Sc cutoff L a))) := by
  rw [weightedCapAfter, Superfunctor.comp_total, SVec.comp_apply]
  exact weightedFunctional_coefficientCap D Sc cutoff i L hN _

/-- Powers of the same native restricted dot shift the actual weighted
moment exponent, with no independently specified component operator. -/
theorem weightedCapMomentLinear_pow (i : I) (hN : 0 < cutoff i) (n a : ℕ) :
    weightedCapMomentLinear D Sc cutoff L i hN n (weightedModuleDot D Sc cutoff L i ^ a) =
      weightedMomentMap D Sc cutoff L i hN (a + n) := by
  apply LinearMap.ext
  intro z
  have h := unitDotColumn_post_dot_power_apply (truncatedAppend D Sc cutoff bound [i])
    (truncatedDot_supernatural D Sc cutoff bound i) WM a n ((Q).obj ⟨[]⟩)
    (weightedEmptyEquiv D Sc cutoff L z)
  exact congrArg (weightedFunctional D Sc cutoff L i hN) h

/-- All dotted-unit closures of the actual plus-one polynomial module cap. -/
def weightedPolynomialCapMoment (i : I) (hN : 0 < cutoff i) (M n : ℕ) : Module.End k AQ :=
  weightedCapMomentLinear D Sc cutoff L i hN n ((weightedModuleDot D Sc cutoff L i ^ 2 + 1) ^ M)

/-- The closure operator is precisely the total component of the actual
polynomial module cap on the given unit/dot column, on every input. -/
theorem weightedPolynomialCapMoment_moduleCap (i : I) (hN : 0 < cutoff i) (M n : ℕ) (a : AQ) :
    weightedPolynomialCapMoment D Sc cutoff L i hN M n a =
      (weightedEmptyEquiv D Sc cutoff L).symm
        ((weightedPolynomialCap D Sc cutoff L i hN M).total
          (⟨⟨[]⟩, rfl⟩ : ContentCategory D Sc cutoff bound 0)
          ((unitDotColumn (truncatedAppend D Sc cutoff bound [i])
            (truncatedDot_supernatural D Sc cutoff bound i) WM n).total ((Q).obj ⟨[]⟩)
              (weightedEmptyEquiv D Sc cutoff L a))) :=
  weightedCapMomentLinear_capAfter D Sc cutoff L i hN n _ a

/-- Binomial expansion of the actual plus-one module cap, in terms of
the given all-power weighted moment maps and without rearranging coefficients. -/
theorem weightedPolynomialCapMoment_sum (i : I) (hN : 0 < cutoff i) (M n : ℕ) :
    weightedPolynomialCapMoment D Sc cutoff L i hN M n =
      ∑ j ∈ Finset.range (M + 1), M.choose j •
        weightedMomentMap D Sc cutoff L i hN (2 * j + n) := by
  change weightedCapMomentLinear D Sc cutoff L i hN n
    ((weightedModuleDot D Sc cutoff L i ^ 2 + 1) ^ M) = _
  rw [(Commute.one_right (weightedModuleDot D Sc cutoff L i ^ 2)).add_pow]
  simp only [one_pow, mul_one, ← nsmul_eq_mul', ← pow_mul, map_sum, map_nsmul,
    weightedCapMomentLinear_pow]

/-- All weighted polynomial-cap closure maps agree with the existing
literal-power calculation, now attached to actual module cap/dot fields. -/
theorem weightedPolynomialCapMoment_eq_polynomialCapMoment (i : I) (hN : 0 < cutoff i) (M n : ℕ) :
    weightedPolynomialCapMoment D Sc cutoff L i hN M n = polynomialCapMoment D Sc cutoff L i hN M n := by
  rw [weightedPolynomialCapMoment_sum, polynomialCapMoment_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [weightedMomentMap_eq_momentMap]

/-- The first normalized closure at zero or negative external height
is the actual weighted first higher moment on every coefficient vector. -/
theorem weightedPolynomialCapMoment_nonpositive_first (i : I) (hN : 0 < cutoff i) (M : ℕ)
    (hMN : 2 * M ≤ cutoff i) :
    weightedPolynomialCapMoment D Sc cutoff L i hN M (cutoff i - 2 * M) =
      weightedMomentMap D Sc cutoff L i hN (cutoff i) := by
  rw [weightedPolynomialCapMoment_eq_polynomialCapMoment,
    polynomialCapMoment_nonpositive_first D Sc cutoff L i hN M hMN,
    weightedMomentMap_eq_momentMap]

/-- Its odd-colour value keeps the original left exterior coefficient
and the prescribed reservoir-cutoff sign, at both nonpositive heights. -/
theorem weightedPolynomialCapMoment_nonpositive_first_odd (i : I) (hi : D.parity i = 1)
    (hN : 0 < cutoff i) (M : ℕ) (hMN : 2 * M ≤ cutoff i) :
    weightedPolynomialCapMoment D Sc cutoff L i hN M (cutoff i - 2 * M) =
      LinearMap.mulLeft k ((-1 : k) ^ (cutoff i + 1) •
        coefficientPowerQuotientMap D cutoff L (SKM.SYM.delta D k ⟨i, hi⟩)) := by
  rw [weightedPolynomialCapMoment_eq_polynomialCapMoment]
  exact polynomialCapMoment_nonpositive_first_odd D Sc cutoff L i hi hN M hMN

/-- The actual zero-height polynomial module cap gives minus the original
left exterior coefficient on every coefficient vector. The mixed inverse
identification is still separate. -/
theorem weightedPolynomialCapMoment_zero_height_odd (i : I) (hi : D.parity i = 1)
    (hN : 0 < cutoff i) (M : ℕ) (hcut : cutoff i = 2 * M) :
    weightedPolynomialCapMoment D Sc cutoff L i hN M 0 =
      LinearMap.mulLeft k (-(coefficientPowerQuotientMap D cutoff L (SKM.SYM.delta D k ⟨i, hi⟩))) := by
  rw [weightedPolynomialCapMoment_eq_polynomialCapMoment]
  exact polynomialCapMoment_zero_height_odd D Sc cutoff L i hi hN M hcut

omit [Fintype I] in
/-- The first complete coefficient is the original elementary chi_1;
this calculation occurs before its literal coefficient quotient. -/
theorem completeCoefficient_one (i : I) :
    completeCoefficient (k := k) D cutoff L i 1 =
      coefficientPowerQuotientMap D cutoff L (SKM.SYM.e D k i 0) := by
  have hc : PowerSeries.coeff 1 (PowerSeries.invOfUnit
      (PowerSeries.rescale (-1 : MvPolynomial (I × ℕ) k) (SKM.SYM.generatorSeries k i)) 1) =
      MvPolynomial.X (i, 0) := by
    have hd : Finset.HasAntidiagonal.antidiagonal (1 : ℕ) = {(0, 1), (1, 0)} := rfl
    rw [PowerSeries.coeff_invOfUnit, ite_eq_right (by decide : ¬ (1 : ℕ) = 0), hd]
    simp [PowerSeries.coeff_rescale, SKM.SYM.generatorSeries, SKM.SYM.generatorCoeff]
  rw [completeCoefficient, hc]
  simp only [polynomialToPower, AlgHom.comp_apply, SKM.SYM.polynomialInclude_X]

/-- The actual weighted moments have the full finite inverse-row window
as an operator equality on A/T. -/
theorem weightedMomentMap_window (i : I) (hN : 0 < cutoff i) (n : ℕ) (hn : n < cutoff i) :
    weightedMomentMap D Sc cutoff L i hN n = if n + 1 = cutoff i then 1 else 0 := by
  apply LinearMap.ext
  intro z
  have h := weightedFunctional_unitDotColumn D Sc cutoff L i hN n hn z
  by_cases htop : n + 1 = cutoff i
  · rw [ite_eq_left htop] at h ⊢
    exact h
  · rw [ite_eq_right htop] at h ⊢
    exact h

/-- The exponent-two plus-one cap closure in actual weighted moments. -/
theorem weightedPolynomialCapMoment_two (i : I) (hN : 0 < cutoff i) (n : ℕ) :
    weightedPolynomialCapMoment D Sc cutoff L i hN 2 n =
      weightedMomentMap D Sc cutoff L i hN (4 + n) +
        (2 : ℕ) • weightedMomentMap D Sc cutoff L i hN (2 + n) +
        weightedMomentMap D Sc cutoff L i hN n := by
  have hx : (weightedModuleDot D Sc cutoff L i ^ 2 + 1) ^ 2 =
      weightedModuleDot D Sc cutoff L i ^ 4 + (2 : ℕ) • weightedModuleDot D Sc cutoff L i ^ 2 + 1 := by
    generalize weightedModuleDot D Sc cutoff L i = x
    noncomm_ring
  change weightedCapMomentLinear D Sc cutoff L i hN n ((weightedModuleDot D Sc cutoff L i ^ 2 + 1) ^ 2) = _
  rw [hx, map_add, map_add, map_nsmul, weightedCapMomentLinear_pow, weightedCapMomentLinear_pow]
  have h1 : weightedCapMomentLinear D Sc cutoff L i hN n 1 =
      weightedMomentMap D Sc cutoff L i hN n := by
    simpa only [pow_zero, Nat.zero_add] using weightedCapMomentLinear_pow D Sc cutoff L i hN n 0
  rw [h1]

/-- The corresponding literal minus-one polynomial closure uses the same
actual dot and cap. It is retained only to distinguish the probe sign. -/
theorem weightedCapMomentLinear_minus_square (i : I) (hN : 0 < cutoff i) (n : ℕ) :
    weightedCapMomentLinear D Sc cutoff L i hN n ((weightedModuleDot D Sc cutoff L i ^ 2 - 1) ^ 2) =
      weightedMomentMap D Sc cutoff L i hN (4 + n) -
        (2 : ℕ) • weightedMomentMap D Sc cutoff L i hN (2 + n) +
        weightedMomentMap D Sc cutoff L i hN n := by
  have hx : (weightedModuleDot D Sc cutoff L i ^ 2 - 1) ^ 2 =
      weightedModuleDot D Sc cutoff L i ^ 4 - (2 : ℕ) • weightedModuleDot D Sc cutoff L i ^ 2 + 1 := by
    generalize weightedModuleDot D Sc cutoff L i = x
    noncomm_ring
  rw [hx, map_add, map_sub, map_nsmul, weightedCapMomentLinear_pow, weightedCapMomentLinear_pow]
  have h1 : weightedCapMomentLinear D Sc cutoff L i hN n 1 =
      weightedMomentMap D Sc cutoff L i hN n := by
    simpa only [pow_zero, Nat.zero_add] using weightedCapMomentLinear_pow D Sc cutoff L i hN n 0
  rw [h1]

/-- At reservoir cutoff four, the actual plus-one polynomial module cap
has second closure chi_1+2 on every coefficient vector. -/
theorem weightedPolynomialCapMoment_second_four (i : I) (hi : D.parity i = 1)
    (hN : 0 < cutoff i) (hcut : cutoff i = 4) :
    weightedPolynomialCapMoment D Sc cutoff L i hN 2 1 =
      LinearMap.mulLeft k (coefficientPowerQuotientMap D cutoff L (SKM.SYM.e D k i 0) + 2) := by
  have hlow := weightedMomentMap_window D Sc cutoff L i hN 1 (by omega)
  rw [ite_eq_right (by omega : 1 + 1 ≠ cutoff i)] at hlow
  have htop := weightedMomentMap_window D Sc cutoff L i hN 3 (by omega)
  rw [ite_eq_left (by omega : 3 + 1 = cutoff i)] at htop
  have hhigh := weightedMomentMap_even D Sc cutoff L i hi hN 1
  have hidx : cutoff i - 1 + 2 * 1 = 5 := by omega
  rw [hidx, completeCoefficient_one] at hhigh
  rw [weightedPolynomialCapMoment_two]
  change weightedMomentMap D Sc cutoff L i hN 5 +
    (2 : ℕ) • weightedMomentMap D Sc cutoff L i hN 3 +
    weightedMomentMap D Sc cutoff L i hN 1 = _
  rw [hlow, htop, hhigh, add_zero]
  apply LinearMap.ext
  intro z
  change coefficientPowerQuotientMap D cutoff L (SKM.SYM.e D k i 0) * z +
    (2 : ℕ) • z = (coefficientPowerQuotientMap D cutoff L (SKM.SYM.e D k i 0) + 2) * z
  simp only [two_smul]
  noncomm_ring

/-- Replacing the plus one by minus one gives chi_1-2 at the same actual
weighted fields. Their difference is not hidden by the first odd closure. -/
theorem weightedCapMomentLinear_minus_second_four (i : I) (hi : D.parity i = 1)
    (hN : 0 < cutoff i) (hcut : cutoff i = 4) :
    weightedCapMomentLinear D Sc cutoff L i hN 1 ((weightedModuleDot D Sc cutoff L i ^ 2 - 1) ^ 2) =
      LinearMap.mulLeft k (coefficientPowerQuotientMap D cutoff L (SKM.SYM.e D k i 0) - 2) := by
  have hlow := weightedMomentMap_window D Sc cutoff L i hN 1 (by omega)
  rw [ite_eq_right (by omega : 1 + 1 ≠ cutoff i)] at hlow
  have htop := weightedMomentMap_window D Sc cutoff L i hN 3 (by omega)
  rw [ite_eq_left (by omega : 3 + 1 = cutoff i)] at htop
  have hhigh := weightedMomentMap_even D Sc cutoff L i hi hN 1
  have hidx : cutoff i - 1 + 2 * 1 = 5 := by omega
  rw [hidx, completeCoefficient_one] at hhigh
  rw [weightedCapMomentLinear_minus_square]
  change weightedMomentMap D Sc cutoff L i hN 5 -
    (2 : ℕ) • weightedMomentMap D Sc cutoff L i hN 3 +
    weightedMomentMap D Sc cutoff L i hN 1 = _
  rw [hlow, htop, hhigh, add_zero]
  apply LinearMap.ext
  intro z
  change coefficientPowerQuotientMap D cutoff L (SKM.SYM.e D k i 0) * z -
    (2 : ℕ) • z = (coefficientPowerQuotientMap D cutoff L (SKM.SYM.e D k i 0) - 2) * z
  simp only [two_smul]
  noncomm_ring

end PowerVacuumCoefficient
end OddMath.QuiverHecke.ELVOld
