import Mathlib.Tactic.Abel
import OddMath.QuiverHecke.CyclotomicAction.ProbeCentral
import OddMath.QuiverHecke.CyclotomicAction.ProbeVacuumBends
import OddMath.QuiverHecke.SwappedAssembly.Sigma.PaddedBendWordSeries
import OddMath.QuiverHecke.SwappedAssembly.Sigma.PointwiseBubbleEntry
import OddMath.QuiverHecke.SwappedAssembly.Sigma.PointwiseCupInverse
import OddMath.QuiverHecke.SwappedAssembly.Sigma.PointwiseRightBubbleEntry
import OddMath.QuiverHecke.SwappedAssembly.Sigma.VacuumCapInverseWindow

/-!
# Probe padded vacuum

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # The finite even vacuum bend

SwappedHomInversion §3 (A6), (3)–(5): on an even moving colour the chosen
mixed diagonal is `(Y-X)⁻¹`, hence the negative finite geometric series.
This evaluates the same post unit and shifted pre-cap used in the odd
calculation. Other colours of the datum may be odd.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV
open BalancedInduction CyclotomicCrossingTensor
universe u

private theorem inverse_neg_unit {R : Type*} [Ring R] (a : R) (ha : IsUnit a) :
    Ring.inverse (-a) = -Ring.inverse a := by
  calc
    Ring.inverse (-a) = Ring.inverse (-a) * 1 := (mul_one _).symm
    _ = Ring.inverse (-a) * ((-a) * (-Ring.inverse a)) := by
      rw [neg_mul_neg, Ring.mul_inverse_cancel _ ha]
    _ = -Ring.inverse a := by
      rw [← mul_assoc, Ring.inverse_mul_cancel _ ha.neg, one_mul]

private theorem negative_even_series {R : Type*} [Ring R] (x : Rˣ) (y : R)
    (hxy : Commute (x : R) y) (n : ℕ) (hn : y ^ n = 0) :
    Ring.inverse (y - (x : R)) =
      ∑ r ∈ Finset.range n, (-1 : ℤ) • (y ^ r * (↑x⁻¹ : R) ^ (r + 1)) := by
  rw [← neg_sub (x : R) y, inverse_neg_unit _ (SKM.mixedEvenDenominator_isUnit x y hxy n hn),
    SKM.mixedEvenInverse_expansion x y hxy n hn, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro r _
  rw [neg_one_zsmul, (hxy.units_inv_left.pow_pow (r + 1) r).eq]

private theorem map_inverse {A B : Type*} [Ring A] [Ring B]
    (f : A →* B) (x : A) (hx : IsUnit x) : f (Ring.inverse x) = Ring.inverse (f x) := by
  obtain ⟨v, rfl⟩ := hx
  change f (Ring.inverse (v : A)) = Ring.inverse ((Units.map f v : Bˣ) : B)
  simp only [Ring.inverse_unit, Units.coe_map_inv]

namespace ProbeVacuumCap
variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m cutoff : I → ℕ) (bound : ℕ)
local notation "R₀" => contentModuleTarget D Sc cutoff bound (0 : Multiset I)
local notation "N₀" => probeOldVacuumRegular D Sc m
local notation "J" => contentAppend D Sc cutoff bound (0 : Multiset I)

/-- The post-induced even probe dot is a unit on the selected mixed carrier. -/
theorem diagonalPreDot_even_isUnit (i : I) (hi : D.parity i = 0)
    (H : modulePiCategory D Sc m ⟶ R₀) : IsUnit (diagonalPreDot D Sc m cutoff bound i H) :=
  (shiftedPreDot_even_isUnit D Sc m R₀ i hi H).map ((induction (J [i])).mapEnd _)

/-- The literal even rational diagonal is the negative finite geometric series. -/
theorem evaluatedMixedDiagonal_even_expansion (i : I) (hi : D.parity i = 0)
    (H : modulePiCategory D Sc m ⟶ R₀) (n : ℕ)
    (hn : diagonalPostDot D Sc m cutoff bound i H ^ n = 0) :
    evaluatedMixedDiagonal D Sc m cutoff bound i H =
      ∑ r ∈ Finset.range n, (-1 : ℤ) •
        ((induction (J [i])).map (Ring.inverse (shiftedPreDot D Sc m R₀ i H) ^ (r + 1)) ≫
          diagonalPostDot D Sc m cutoff bound i H ^ r) := by
  rw [evaluatedMixedDiagonal, ite_eq_left hi]
  let x := diagonalPreDot D Sc m cutoff bound i H
  let y := diagonalPostDot D Sc m cutoff bound i H
  have hc : Commute x y := by
    have h := diagonal_dots_exchange D Sc m cutoff bound i H
    simp only [hi, koszulSign_zero_left, one_smul] at h
    exact h.symm
  obtain ⟨v, hv⟩ := diagonalPreDot_even_isUnit D Sc m cutoff bound i hi H
  change (v : End _) = x at hv
  have hs := negative_even_series v y (by simpa only [hv] using hc) n hn
  have hv' : (↑v⁻¹ : End _) = Ring.inverse x := by rw [← hv, Ring.inverse_unit]
  rw [hv, hv'] at hs
  rw [hs]
  apply Finset.sum_congr rfl
  intro r _
  congr 1
  have hmap := map_inverse ((induction (J [i])).mapEnd _)
    (shiftedPreDot D Sc m R₀ i H) (shiftedPreDot_even_isUnit D Sc m R₀ i hi H)
  change y ^ r * Ring.inverse x ^ (r + 1) = _
  rw [show Ring.inverse x = (induction (J [i])).mapEnd _
      (Ring.inverse (shiftedPreDot D Sc m R₀ i H)) from hmap.symm, ← map_pow]
  rfl

/-- The even cap/unit bend retains a constant negative coefficient in every term. -/
theorem evaluatedMixedBend_even_expansion (i : I) (hi : D.parity i = 0)
    (hP : 0 < probeCutoff D m i) (H : modulePiCategory D Sc m ⟶ R₀) (n : ℕ)
    (hn : diagonalPostDot D Sc m cutoff bound i H ^ n = 0) :
    evaluatedMixedBend D Sc m cutoff bound i hP H =
      ∑ r ∈ Finset.range n, (-1 : ℤ) •
        ((Ring.inverse (shiftedPreDot D Sc m R₀ i H) ^ (r + 1)) ≫
          shiftedPreCap D Sc m R₀ i hP H ≫ (adjunction (J [i])).unit.app (H.obj N₀) ≫
            evaluatedPostDot D Sc m cutoff bound i H ^ r) := by
  rw [evaluatedMixedBend, evaluatedMixedDiagonal_even_expansion D Sc m cutoff bound i hi H n hn]
  exact postBend_sum _ (contentAppendTo_supernatural D Sc cutoff bound rfl rfl (firstDot_parity D Sc i []))
    _ _ _ (shiftedPreCap_mem D Sc m R₀ i hP H)
    (fun r => Ring.inverse (shiftedPreDot D Sc m R₀ i H) ^ (r + 1)) (fun _ => -1) n

end ProbeVacuumCap
end OddMath.QuiverHecke.ELV
end

end

section

/-! # The ordered odd vacuum bend series

SwappedHomInversion §3 (4)–(5): the finite ordered series of prescribed
negative pre-caps and dotted post-units equals the evaluated A6 bend.

The hypothesis `[Fact Sc.PureNilpotent]` on declarations here is a route-only intermediate
hypothesis for parameters with pure terms: homogeneous parameters supply it
(`ScalarData.NoPure.pureNilpotent`) and truncated Rees parameters satisfy it
(`BWWReesParameters.truncated_pureNilpotent`).
-/
noncomputable section
set_option autoImplicit false
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELV.WeightTensorVacuum
open BalancedInduction CyclotomicAction
universe u
local instance bendSeriesHomPi {k : Type u} [CommRing k] (A B : PiSCat.{u,u,u+1} k) :
    PiSupercategory k (A ⟶ B) := PiTwoSupercategory.homPiLeft A B
variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m cutoff : I → ℕ) (bound : ℕ)
  (ΛP ΛR : X)
  (hcP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hcR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)
  (i : I) {muP nuR : X} (edgeP : -ΛP + D.α i = -muP)
  (edgeR : -ΛR + D.α i = nuR) (β : I →₀ ℕ)
variable (H : ProbeVacuumCap.modulePiCategory D Sc m ⟶ elvWeightSpace D Sc cutoff bound ΛR (-ΛR))
local instance bendSeriesProbeDotIso [Fact Sc.PureNilpotent] : IsIso (((probeOldRouquierFamily D Sc m ΛP hcP)).dot i edgeP) :=
  (isUnit_iff_isIso _).mp (probeOldRouquierFamily_dot_isUnit D Sc m ΛP hcP i edgeP)

/-- The given chronological series keeps each negative pre-cap and
post-unit as the prescribed Hom maps before regular-probe evaluation. -/
def vacuumBendWordSum [Fact Sc.PureNilpotent] (N : ℕ) :=
  -∑ r ∈ Finset.range N, (koszulSign (D.parity i) (D.parity i)) ^ (r + 1) •
    (((SKM.homPreNegativeCap (probeOldRouquierFamily D Sc m ΛP hcP) (elvWeightSpace D Sc cutoff bound ΛR) i (-ΛR) edgeP (r + 1) (preCapInput D Sc m ΛP hcP (elvWeightSpace D Sc cutoff bound ΛR) (-ΛR) H) ≫
      SKM.homContentPostCup ((probeOldRouquierFamily D Sc m ΛP hcP)).obj (elvRouquierFamily D Sc cutoff bound ΛR hcR) i β ΛP edgeR r (preCapInput D Sc m ΛP hcP (elvWeightSpace D Sc cutoff bound ΛR) (-ΛR) H)).total (regularProbe D Sc m ΛP)) (emptyBlock D ΛR))

private theorem odd_coefficient (r : ℕ) :
    -((koszulSign (1 : ZMod 2) 1) ^ (r + 1)) = (-1 : ℤ) ^ r := by
  rw [koszulSign_one_one, pow_succ]
  ring

/-- At any given native reservoir nilpotence exponent, the actual
finite pre-cap/post-unit word sum is exactly the evaluated odd A6 bend.
The raw shifted pre-dot and raw reservoir unit/dot are retained. -/
theorem vacuumBendWordSum_odd [Fact Sc.PureNilpotent] (hP : 0 < probeCutoff D m i) (hi : D.parity i = 1)
    (n : ℕ)
    (hn : ProbeVacuumCap.diagonalPostDot D Sc m cutoff bound i (vacuumBendBlock D Sc m cutoff bound ΛR H) ^ n = 0) :
    vacuumBendWordSum D Sc m cutoff bound ΛP ΛR hcP hcR i edgeP edgeR β H (2 * n) ≫
      (vacuumPostTarget D Sc m cutoff bound ΛP ΛR hcP hcR i edgeR β H).hom =
    (vacuumPreBlockSourceIso D Sc m cutoff bound ΛP ΛR hcP i edgeP H).hom ≫
      ProbeVacuumCap.evaluatedMixedBend D Sc m cutoff bound i hP (vacuumBendBlock D Sc m cutoff bound ΛR H) := by
  rw [ProbeVacuumCap.evaluatedMixedBend_odd_expansion D Sc m cutoff bound i hi hP (vacuumBendBlock D Sc m cutoff bound ΛR H) n hn]
  simp only [vacuumBendWordSum, Preadditive.neg_comp, Preadditive.sum_comp,
    Preadditive.zsmul_comp, Preadditive.comp_sum, Preadditive.comp_zsmul,
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  rw [vacuumBendMonomial_eq D Sc m cutoff bound ΛP ΛR hcP hcR i edgeP edgeR β H hP hi (r + 1) r]
  have hs : -((koszulSign (D.parity i) (D.parity i)) ^ (r + 1)) = (-1 : ℤ) ^ r := by
    rw [hi, odd_coefficient]
  rw [← neg_zsmul, hs]
  congr 1

/-- Even colour: at any given native reservoir nilpotence exponent `n`, the actual
finite pre-cap/post-unit word sum of length `n` is exactly the evaluated even A6 bend. -/
theorem vacuumBendWordSum_even [Fact Sc.PureNilpotent] (hP : 0 < probeCutoff D m i) (hi : D.parity i = 0)
    (n : ℕ)
    (hn : ProbeVacuumCap.diagonalPostDot D Sc m cutoff bound i (vacuumBendBlock D Sc m cutoff bound ΛR H) ^ n = 0) :
    vacuumBendWordSum D Sc m cutoff bound ΛP ΛR hcP hcR i edgeP edgeR β H n ≫
      (vacuumPostTarget D Sc m cutoff bound ΛP ΛR hcP hcR i edgeR β H).hom =
    (vacuumPreBlockSourceIso D Sc m cutoff bound ΛP ΛR hcP i edgeP H).hom ≫
      ProbeVacuumCap.evaluatedMixedBend D Sc m cutoff bound i hP (vacuumBendBlock D Sc m cutoff bound ΛR H) := by
  rw [ProbeVacuumCap.evaluatedMixedBend_even_expansion D Sc m cutoff bound i hi hP (vacuumBendBlock D Sc m cutoff bound ΛR H) n hn]
  simp only [vacuumBendWordSum, Preadditive.neg_comp, Preadditive.sum_comp,
    Preadditive.zsmul_comp, Preadditive.comp_sum, Preadditive.comp_zsmul,
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  rw [vacuumBendMonomial_even D Sc m cutoff bound ΛP ΛR hcP hcR i edgeP edgeR β H hP hi (r + 1) r]
  have hs : -((koszulSign (D.parity i) (D.parity i)) ^ (r + 1)) = (-1 : ℤ) := by
    rw [hi, koszulSign_zero_left, one_pow]
  rw [← neg_zsmul, hs]
  congr 1

end OddMath.QuiverHecke.ELV.WeightTensorVacuum
end

end
