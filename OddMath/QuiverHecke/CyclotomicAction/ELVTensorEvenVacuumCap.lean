import OddMath.QuiverHecke.CyclotomicAction.ELVTensorVacuumCap
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeEvenCentralSlide
import OddMath.QuiverHecke.SwappedVacuum.NegativeCapMoments

/-! # Even polynomial caps on the prescribed tensor vacuum

SwappedVacuumNonpositiveBubbles (8)–(10) with even moving colour:
the actual evaluated bend and normalized coefficient cap retain the
probe polynomial `(X-1)^m`, on the same full tensor-vacuum module.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open BalancedInduction CyclotomicCrossingTensor PowerVacuumCoefficient ProbeVacuumCap
universe u v w

private theorem capPolynomial_even_pow
    {k : Type u} {C : Type v} [CommRing k] [Category.{w} C] [Preadditive C] [Linear k C]
    {V : C} (x : End V) (m : ℕ) :
    SwappedVacuum.capPolynomial ((Polynomial.X - 1 : Polynomial k) ^ m).coeff m x =
      (x - 1) ^ m := by
  have hb : (Polynomial.X - 1 : Polynomial k).natDegree ≤ 1 :=
    (Polynomial.natDegree_sub_le _ _).trans (max_le Polynomial.natDegree_X_le (by simp))
  have hd : ((Polynomial.X - 1 : Polynomial k) ^ m).natDegree ≤ m := by
    calc
      _ ≤ m * (Polynomial.X - 1 : Polynomial k).natDegree := Polynomial.natDegree_pow_le
      _ ≤ m * 1 := Nat.mul_le_mul_left m hb
      _ = m := Nat.mul_one m
  rw [SwappedVacuum.capPolynomial, ← Polynomial.aeval_eq_sum_range' (Nat.lt_succ_of_le hd) x]
  simp only [map_pow, map_sub, Polynomial.aeval_X, map_one]

private theorem even_probe_coefficient_monic {k : Type u} [CommRing k] (m : ℕ) :
    ((Polynomial.X - 1 : Polynomial k) ^ m).coeff m = 1 := by
  have h := Polynomial.coeff_X_add_C_pow (-1 : k) m m
  simpa only [map_neg, map_one, sub_eq_add_neg, Nat.choose_self, Nat.cast_one,
    Nat.sub_self, pow_zero, mul_one] using h

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
theorem evaluatedMixedBend_even_polynomialCap_zero
    (hi : D.parity i = 0) (hP : 0 < probeCutoff D m i)
    (hN : 0 < cutoff i) (hPN : m i < cutoff i) :
    evaluatedMixedBend D Sc m cutoff bound i hP H ≫
      ((evaluatedPostDot D Sc m cutoff bound i H - 1) ^ m i) ≫
      tensorPowerVacuumCap D Sc m cutoff L i hN = 0 := by
  have hs := evaluatedMixedBend_even_slide D Sc m cutoff bound sy hc i hi hP H
  have hs' : evaluatedMixedBend D Sc m cutoff bound i hP H ≫
        evaluatedPostDot D Sc m cutoff bound i H -
      (1 : k) • (shiftedPreDot D Sc m R₀ i H ≫
        evaluatedMixedBend D Sc m cutoff bound i hP H) =
      shiftedPreCap D Sc m R₀ i hP H ≫ (adjunction K).unit.app V := by
    simpa only [hi, koszulSign_zero_left, one_smul] using hs
  have hw (a : ℕ) (ha : a < cutoff i) :
      (adjunction K).unit.app V ≫ (evaluatedPostDot D Sc m cutoff bound i H ^ a) ≫
        tensorPowerVacuumCap D Sc m cutoff L i hN =
        if a + 1 = cutoff i then 𝟙 V else 0 :=
    tensorPowerVacuumCap_window D Sc m cutoff L i hN a ha
  have hp : SwappedVacuum.capPolynomial ((Polynomial.X - 1 : Polynomial k) ^ m i).coeff
      (m i) (shiftedPreDot D Sc m R₀ i H) = 0 := by
    rw [capPolynomial_even_pow]
    exact shiftedPreDot_even_polynomial D Sc m R₀ i hi H
  have h := SwappedVacuum.negative_cap_annihilates_mate (k := k) (1 : k)
    (shiftedPreDot D Sc m R₀ i H) (evaluatedPostDot D Sc m cutoff bound i H)
    (evaluatedMixedBend D Sc m cutoff bound i hP H) ((adjunction K).unit.app V)
    (shiftedPreCap D Sc m R₀ i hP H) (tensorPowerVacuumCap D Sc m cutoff L i hN)
    (cutoff i) (m i) hPN ((Polynomial.X - 1 : Polynomial k) ^ m i).coeff
    (fun n _ => by simp only [one_pow, mul_one]) hs' hw hp
  rw [capPolynomial_even_pow] at h
  exact h


include sy hc in
/-- At equal levels, the polynomial cap of the actual A6 bend returns
exactly the prescribed shifted pre cap. All fields are the chosen native
maps; no mixed inverse or extraction premise is added. -/
theorem evaluatedMixedBend_even_polynomialCap_eq_preCap
    (hi : D.parity i = 0) (hP : 0 < probeCutoff D m i)
    (hN : 0 < cutoff i) (hPN : m i = cutoff i) :
    evaluatedMixedBend D Sc m cutoff bound i hP H ≫
      ((evaluatedPostDot D Sc m cutoff bound i H - 1) ^ m i) ≫
      tensorPowerVacuumCap D Sc m cutoff L i hN = shiftedPreCap D Sc m R₀ i hP H := by
  have hs := evaluatedMixedBend_even_slide D Sc m cutoff bound sy hc i hi hP H
  have hs' : evaluatedMixedBend D Sc m cutoff bound i hP H ≫
        evaluatedPostDot D Sc m cutoff bound i H -
      (1 : k) • (shiftedPreDot D Sc m R₀ i H ≫
        evaluatedMixedBend D Sc m cutoff bound i hP H) =
      shiftedPreCap D Sc m R₀ i hP H ≫ (adjunction K).unit.app V := by
    simpa only [hi, koszulSign_zero_left, one_smul] using hs
  have hw (a : ℕ) (ha : a < m i) :
      (adjunction K).unit.app V ≫ (evaluatedPostDot D Sc m cutoff bound i H ^ a) ≫
        tensorPowerVacuumCap D Sc m cutoff L i hN =
        if a + 1 = m i then 𝟙 V else 0 := by
    have hw := tensorPowerVacuumCap_window D Sc m cutoff L i hN a (by omega)
    exact hw.trans (if_congr (by omega) rfl rfl)
  have hp : SwappedVacuum.capPolynomial ((Polynomial.X - 1 : Polynomial k) ^ m i).coeff
      (m i) (shiftedPreDot D Sc m R₀ i H) = 0 := by
    rw [capPolynomial_even_pow]
    exact shiftedPreDot_even_polynomial D Sc m R₀ i hi H
  have h := SwappedVacuum.principal_cap_polynomial (k := k) (1 : k)
    (shiftedPreDot D Sc m R₀ i H) (evaluatedPostDot D Sc m cutoff bound i H)
    (evaluatedMixedBend D Sc m cutoff bound i hP H) ((adjunction K).unit.app V)
    (shiftedPreCap D Sc m R₀ i hP H) (tensorPowerVacuumCap D Sc m cutoff L i hN)
    (m i) (by omega) ((Polynomial.X - 1 : Polynomial k) ^ m i).coeff
    (even_probe_coefficient_monic (m i))
    (fun n _ => by simp) hs' hw hp
  rw [capPolynomial_even_pow] at h
  exact h


end OddMath.QuiverHecke.ELVOld
