import OddMath.QuiverHecke.CyclotomicAction.ELVTensorVacuumCap
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeCentralSlide
import OddMath.QuiverHecke.SwappedVacuum.NegativeCapMoments
import Mathlib.Algebra.Polynomial.Expand

/-! # The polynomial cap kills the evaluated negative-height mixed bend

SwappedVacuumNonpositiveBubbles (9)–(10): use the given raw probe dot,
the evaluated A6 bend and its signed slide, and the prescribed inverse
coefficient cap on the same literal tensor-vacuum carrier.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open BalancedInduction CyclotomicCrossingTensor PowerVacuumCoefficient ProbeVacuumCap
universe u v w

private theorem capPolynomial_odd_pow
    {k : Type u} {C : Type v} [CommRing k] [Category.{w} C] [Preadditive C] [Linear k C]
    {V : C} (x : End V) (m : ℕ) :
    SwappedVacuum.capPolynomial ((Polynomial.X ^ 2 + 1 : Polynomial k) ^ m).coeff (2 * m) x =
      (x ^ 2 + 1) ^ m := by
  have hb : (Polynomial.X ^ 2 + 1 : Polynomial k).natDegree ≤ 2 :=
    (Polynomial.natDegree_add_le _ _).trans
      (max_le (Polynomial.natDegree_X_pow_le 2) (by simp))
  have hd : ((Polynomial.X ^ 2 + 1 : Polynomial k) ^ m).natDegree ≤ 2 * m := by
    calc
      _ ≤ m * (Polynomial.X ^ 2 + 1 : Polynomial k).natDegree := Polynomial.natDegree_pow_le
      _ ≤ m * 2 := Nat.mul_le_mul_left m hb
      _ = 2 * m := Nat.mul_comm _ _
  rw [SwappedVacuum.capPolynomial, ← Polynomial.aeval_eq_sum_range' (Nat.lt_succ_of_le hd) x]
  simp only [map_pow, map_add, Polynomial.aeval_X, map_one]

private theorem odd_probe_coefficient_sign {k : Type u} [CommRing k] (m n : ℕ) :
    ((Polynomial.X ^ 2 + 1 : Polynomial k) ^ m).coeff n * (-1 : k) ^ n =
      ((Polynomial.X ^ 2 + 1 : Polynomial k) ^ m).coeff n := by
  have he : (Polynomial.X ^ 2 + 1 : Polynomial k) ^ m =
      Polynomial.expand k 2 ((Polynomial.X + 1) ^ m) := by
    simp only [map_pow, map_add, Polynomial.expand_X, map_one]
  rw [he, Polynomial.coeff_expand (by decide)]
  by_cases hn : 2 ∣ n
  · rw [ite_eq_left hn, (even_iff_two_dvd.mpr hn : Even n).neg_one_pow, mul_one]
  · rw [ite_eq_right hn, zero_mul]

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) [Fintype I]
  (m : I → ℕ) (cutoff : I → ℕ) (L : I × ℕ → ℕ)
  (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)
local notation "bound" => SKM.SYM.elvPowerWeightBound D cutoff L + 1
local notation "W₀" => Functor.obj (restriction (contentInclusion D Sc cutoff bound (0 : Multiset I)))
  (weightedVacuum D Sc cutoff L)
local notation "H" => VacuumTensor.probeFunctor D Sc m cutoff bound W₀
local notation "R₀" => contentModuleTarget D Sc cutoff bound (0 : Multiset I)
local notation "N₀" => probeOldVacuumRegular D Sc m
local notation "V" => Superfunctor.obj H N₀
variable (i : I)
local notation "K" => contentAppend D Sc cutoff bound (0 : Multiset I) [i]

include sy hc in
/-- At negative height, the actual signed A6 mixed bend is annihilated
by the probe polynomial followed by the prescribed native inverse cap.
No mixed inverse, extractor window, or slide is assumed. -/
theorem evaluatedMixedBend_polynomialCap_zero
    (hi : D.parity i = 1) (hP : 0 < probeCutoff D m i)
    (hN : 0 < cutoff i) (hPN : 2 * m i < cutoff i) :
    evaluatedMixedBend D Sc m cutoff bound i hP H ≫
      ((evaluatedPostDot D Sc m cutoff bound i H ^ 2 + 1) ^ m i) ≫
      tensorPowerVacuumCap D Sc m cutoff L i hN = 0 := by
  have hs := evaluatedMixedBend_odd_slide D Sc m cutoff bound sy hc i hi hP H
  have hs' : evaluatedMixedBend D Sc m cutoff bound i hP H ≫
        evaluatedPostDot D Sc m cutoff bound i H -
      (-1 : k) • (shiftedPreDot D Sc m R₀ i H ≫
        evaluatedMixedBend D Sc m cutoff bound i hP H) =
      shiftedPreCap D Sc m R₀ i hP H ≫ (adjunction K).unit.app V := by
    simpa only [hi, koszulSign_one_one, neg_one_zsmul, neg_one_smul] using hs
  have hw (a : ℕ) (ha : a < cutoff i) :
      (adjunction K).unit.app V ≫ (evaluatedPostDot D Sc m cutoff bound i H ^ a) ≫
        tensorPowerVacuumCap D Sc m cutoff L i hN =
        if a + 1 = cutoff i then 𝟙 V else 0 :=
    tensorPowerVacuumCap_window D Sc m cutoff L i hN a ha
  have hp : SwappedVacuum.capPolynomial ((Polynomial.X ^ 2 + 1 : Polynomial k) ^ m i).coeff
      (2 * m i) (shiftedPreDot D Sc m R₀ i H) = 0 := by
    rw [capPolynomial_odd_pow]
    exact shiftedPreDot_odd_polynomial D Sc m R₀ i hi H
  have h := SwappedVacuum.negative_cap_annihilates_mate (k := k) (-1 : k)
    (shiftedPreDot D Sc m R₀ i H) (evaluatedPostDot D Sc m cutoff bound i H)
    (evaluatedMixedBend D Sc m cutoff bound i hP H) ((adjunction K).unit.app V)
    (shiftedPreCap D Sc m R₀ i hP H) (tensorPowerVacuumCap D Sc m cutoff L i hN)
    (cutoff i) (2 * m i) hPN ((Polynomial.X ^ 2 + 1 : Polynomial k) ^ m i).coeff
    (fun n _ => odd_probe_coefficient_sign (m i) n) hs' hw hp
  rw [capPolynomial_odd_pow] at h
  exact h

end OddMath.QuiverHecke.ELVOld
