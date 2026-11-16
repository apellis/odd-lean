import OddMath.QuiverHecke.SwappedAssembly.Generators.CrossCoeffExistence
import OddMath.SKM.RouquierHomMixedRational

/-! # Evaluated finite expansions of the chosen mixed coefficient

`SwappedHomInversion.md` §3 (2)–(3): the prescribed crossing coefficient,
after a specified ring evaluation, has the finite signed expansion at
that component's reservoir bound. No whole-weight nilpotence bound is used.
-/
noncomputable section
open scoped BigOperators
namespace OddMath.QuiverHecke.SwappedAssembly
section Ring
variable {A : Type*} [Ring A]

/-- An evaluated inverse of `y-x` has the negative ordinary expansion. -/
theorem mixedCoefficient_even_expansion (x y a : A) (hx : IsUnit x)
    (hxy : Commute x y) (ha : a * (y - x) = 1) (n : ℕ) (hn : y ^ n = 0) :
    a = -∑ r ∈ Finset.range n, Ring.inverse x ^ (r + 1) * y ^ r := by
  obtain ⟨u, rfl⟩ := hx
  have hd := SKM.mixedEvenDenominator_isUnit u y hxy n hn
  have had : a * ((u : A) - y) = -1 := by
    rw [← neg_sub y (u : A), mul_neg, ha]
  have he : a = -Ring.inverse ((u : A) - y) := by
    calc
      a = a * (((u : A) - y) * Ring.inverse ((u : A) - y)) := by
        rw [Ring.mul_inverse_cancel _ hd, mul_one]
      _ = -Ring.inverse ((u : A) - y) := by rw [← mul_assoc, had, neg_one_mul]
  rw [he, SKM.mixedEvenInverse_expansion u y hxy n hn, Ring.inverse_unit]

/-- The odd square-denominator identity determines the ordered signed expansion. -/
theorem mixedCoefficient_odd_expansion (x y a : A) (hx : IsUnit x)
    (hxy : x * y = -(y * x)) (ha : a * (x ^ 2 - y ^ 2) = x - y)
    (n : ℕ) (hn : y ^ n = 0) :
    a = ∑ r ∈ Finset.range (2 * n), (-1 : A) ^ r * Ring.inverse x ^ (r + 1) * y ^ r := by
  obtain ⟨u, rfl⟩ := hx
  have hd := SKM.mixedOddDenominator_isUnit u y hxy n hn
  have he : a = ((u : A) - y) * Ring.inverse ((u : A) ^ 2 - y ^ 2) := by
    calc
      a = a * (((u : A) ^ 2 - y ^ 2) * Ring.inverse ((u : A) ^ 2 - y ^ 2)) := by
        rw [Ring.mul_inverse_cancel _ hd, mul_one]
      _ = ((u : A) - y) * Ring.inverse ((u : A) ^ 2 - y ^ 2) := by rw [← mul_assoc, ha]
  rw [he, SKM.mixedOddInverse_expansion u y hxy n hn, Ring.inverse_unit]
/-- The finite bound is required only after the specified ring evaluation. -/
theorem mixedCoefficient_even_map_expansion {R : Type*} [Ring R]
    (φ : R →+* A) (x y a : R) (hx : IsUnit (φ x)) (hxy : Commute x y)
    (ha : a * (y - x) = 1) (n : ℕ) (hn : φ y ^ n = 0) :
    φ a = -∑ r ∈ Finset.range n, Ring.inverse (φ x) ^ (r + 1) * φ y ^ r := by
  apply mixedCoefficient_even_expansion (φ x) (φ y) (φ a) hx (hxy.map φ) _ n hn
  simpa only [map_mul, map_sub, map_one] using congrArg φ ha

/-- Evaluation preserves the odd square-denominator identity and its ordered sum. -/
theorem mixedCoefficient_odd_map_expansion {R : Type*} [Ring R]
    (φ : R →+* A) (x y a : R) (hx : IsUnit (φ x)) (hxy : x * y = -(y * x))
    (ha : a * (x ^ 2 - y ^ 2) = x - y) (n : ℕ) (hn : φ y ^ n = 0) :
    φ a = ∑ r ∈ Finset.range (2 * n),
      (-1 : A) ^ r * Ring.inverse (φ x) ^ (r + 1) * φ y ^ r := by
  apply mixedCoefficient_odd_expansion (φ x) (φ y) (φ a) hx _ _ n hn
  · simpa only [map_mul, map_neg] using congrArg φ hxy
  · simpa only [map_mul, map_sub, map_pow] using congrArg φ ha

end Ring

open CategoryTheory StringDiagrams SKM BicategoryStruct Supercategory
universe u uB v w
variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type uB} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}
namespace ProbeReservoir
variable (P : ProbeReservoir k B D Sc) (c : P.CrossCoeff)
  (i : I) (t : Sector I) (hv : StepValid (true, i) false t)
  (Z : P.H (nextSector (true, i) true (nextSector (true, i) false t)))
  {A : Type*} [Ring A] (φ : End (P.rpObj i i t hv Z) →+* A)
local notation "x" => P.rpPreDot i t hv Z
local notation "y" => P.rpPostDot i t hv Z

/-- Evaluate the actual even crossing coefficient with a bound at this component. -/
theorem crossCoeff_even_evaluate (hc : c.IsInverse) (hp : D.parity i = 0)
    (hx : IsUnit (φ x)) (n : ℕ) (hn : φ y ^ n = 0) :
    φ (c.a i t hv Z) = -∑ r ∈ Finset.range n, Ring.inverse (φ x) ^ (r + 1) * φ y ^ r := by
  have he := P.rpPreDot_comp_rpPostDot i t hv Z
  simp only [hp, koszulSign_zero_left, one_smul, ← End.mul_def] at he
  have hi := (hc.even i hp t hv Z).2
  change c.a i t hv Z * (y - x) = 1 at hi
  exact mixedCoefficient_even_map_expansion φ x y (c.a i t hv Z) hx he.symm hi n hn

/-- Evaluate the actual odd crossing coefficient with its signed ordered expansion. -/
theorem crossCoeff_odd_evaluate (hc : c.IsInverse) (hp : D.parity i = 1)
    (hx : IsUnit (φ x)) (n : ℕ) (hn : φ y ^ n = 0) :
    φ (c.a i t hv Z) = ∑ r ∈ Finset.range (2 * n),
      (-1 : A) ^ r * Ring.inverse (φ x) ^ (r + 1) * φ y ^ r := by
  have he := P.rpPreDot_comp_rpPostDot i t hv Z
  simp only [hp, koszulSign_one_one, neg_one_smul, ← End.mul_def] at he
  have hi := (hc.odd i hp t hv Z).2
  change c.a i t hv Z * (x * x - y * y) = x - y at hi
  rw [← pow_two, ← pow_two] at hi
  exact mixedCoefficient_odd_map_expansion φ x y (c.a i t hv Z) hx
    (neg_eq_iff_eq_neg.mp he.symm) hi n hn

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly
