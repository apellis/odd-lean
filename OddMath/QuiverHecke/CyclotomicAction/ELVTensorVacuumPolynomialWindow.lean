import OddMath.QuiverHecke.CyclotomicAction.ELVTensorVacuumMomentMaps
import OddMath.QuiverHecke.SwappedVacuum.NegativeCapMoments
import Mathlib.Algebra.Polynomial.Expand

/-! # The native polynomial cap on the negative unit window

SwappedVacuumNonpositiveBubbles §2 (6)–(8): the given reservoir unit/dot
columns followed by the polynomial cap have the required final-coordinate
values. These are equalities of actual module maps, not assumed moments.
-/
noncomputable section
set_option quotPrecheck false
set_option autoImplicit false
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.PowerVacuumCoefficient
open BalancedInduction CyclotomicCrossingTensor
universe u v w

private theorem capPolynomial_square_add_one
    {k : Type u} {C : Type v} [CommRing k] [Category.{w} C] [Preadditive C] [Linear k C]
    {Y : C} (y : End Y) (M : ℕ) :
    SwappedVacuum.capPolynomial ((Polynomial.X ^ 2 + 1 : Polynomial k) ^ M).coeff (2 * M) y =
      (y ^ 2 + 1) ^ M := by
  have hb : (Polynomial.X ^ 2 + 1 : Polynomial k).natDegree ≤ 2 :=
    (Polynomial.natDegree_add_le _ _).trans
      (max_le (Polynomial.natDegree_X_pow_le 2) (by simp))
  have hd : ((Polynomial.X ^ 2 + 1 : Polynomial k) ^ M).natDegree ≤ 2 * M := by
    calc
      _ ≤ M * (Polynomial.X ^ 2 + 1 : Polynomial k).natDegree := Polynomial.natDegree_pow_le
      _ ≤ M * 2 := Nat.mul_le_mul_left M hb
      _ = 2 * M := Nat.mul_comm _ _
  rw [SwappedVacuum.capPolynomial, ← Polynomial.aeval_eq_sum_range' (Nat.lt_succ_of_le hd) y]
  simp only [map_pow, map_add, Polynomial.aeval_X, map_one]

private theorem square_add_one_monic {k : Type u} [CommRing k] (M : ℕ) :
    ((Polynomial.X ^ 2 + 1 : Polynomial k) ^ M).coeff (2 * M) = 1 := by
  have he : (Polynomial.X ^ 2 + 1 : Polynomial k) ^ M =
      Polynomial.expand k 2 ((Polynomial.X + 1) ^ M) := by
    simp only [map_pow, map_add, Polynomial.expand_X, map_one]
  rw [he, Polynomial.coeff_expand_mul' (by decide)]
  simpa only [Polynomial.C_1, Nat.choose_self, Nat.cast_one, Nat.sub_self, pow_zero, mul_one] using
    Polynomial.coeff_X_add_C_pow (1 : k) M M

private theorem polynomial_window
    {k : Type u} {C : Type v} [CommRing k] [Category.{w} C] [Preadditive C] [Linear k C]
    {V Y : C} (y : End Y) (unit : V ⟶ Y) (cap : Y ⟶ V) (N M : ℕ)
    (hw : ∀ a < N, unit ≫ (y ^ a) ≫ cap = if a + 1 = N then 𝟙 V else 0)
    (a : ℕ) (ha : a + 2 * M < N) :
    unit ≫ (y ^ a) ≫ ((y ^ 2 + 1) ^ M) ≫ cap =
      if a + 2 * M + 1 = N then 𝟙 V else 0 := by
  have h := SwappedVacuum.negative_cap_unit_window y unit cap N (2 * M)
    ((Polynomial.X ^ 2 + 1 : Polynomial k) ^ M).coeff (square_add_one_monic M) hw a ha
  rw [capPolynomial_square_add_one] at h
  exact h

variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m cutoff : I → ℕ)
  (L : I × ℕ → ℕ) (i : I)
local notation "bound" => SKM.SYM.elvPowerWeightBound D cutoff L + 1
local notation "K" => contentAppendTo D Sc cutoff bound (0 : Multiset I) [i]
  ((0 : Multiset I) + ([i] : Multiset I)) (contentBlockCanonicalSum 0 [i])
local notation "hDot" => contentBlockMatrixDot_supernatural D Sc cutoff bound 0 i
local notation "H" => VacuumTensor.probeFunctor D Sc m cutoff bound
  ((restriction (contentInclusion D Sc cutoff bound (0 : Multiset I))).obj
    (weightedVacuum D Sc cutoff L))
local notation "V" => (H).obj (probeOldVacuumRegular D Sc m)

/-- Every low native column has the actual polynomial cap's final-row
value as an equality on the entire tensor module. -/
theorem tensorPolynomialCap_unit_window (hN : 0 < cutoff i) (M a : ℕ)
    (ha : a + 2 * M < cutoff i) :
    tensorPolynomialClosure D Sc m cutoff L i hN M a =
      if a + 2 * M + 1 = cutoff i then 𝟙 V else 0 := by
  have hw (n : ℕ) (hn : n < cutoff i) :
      (adjunction K).unit.app V ≫ (restrictedDotEnd K hDot V ^ n) ≫
        tensorPowerVacuumCap D Sc m cutoff L i hN =
        if n + 1 = cutoff i then 𝟙 V else 0 :=
    tensorPowerVacuumCap_window D Sc m cutoff L i hN n hn
  have h := polynomial_window (k := k) (restrictedDotEnd K hDot V) ((adjunction K).unit.app V)
    (tensorPowerVacuumCap D Sc m cutoff L i hN) (cutoff i) M hw a ha
  unfold tensorPolynomialClosure tensorPolynomialCap
  rw [unitDotColumn_eq_restrictedDotEnd, Category.assoc]
  with_unfolding_all exact h

end OddMath.QuiverHecke.ELVOld.PowerVacuumCoefficient
