import OddMath.QuiverHecke.CyclotomicAction.ELVProbeEvenVacuumPolynomial
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeCentralBend

/-! # The finite even vacuum bend

SwappedHomInversion §3 (A6), (3)–(5): on an even moving colour the chosen
mixed diagonal is `(Y-X)⁻¹`, hence the negative finite geometric series.
This evaluates the same post unit and shifted pre-cap used in the odd
calculation. Other colours of the datum may be odd.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
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
end OddMath.QuiverHecke.ELVOld
