import OddMath.QuiverHecke.CyclotomicAction.ELVProbeEvenCentralBend
import Mathlib.Tactic.Abel

/-! # The even slide of the evaluated mixed bend

SwappedVacuumNonpositiveBubbles §1 (1), with moving parity zero.
The chosen even finite series telescopes on the actual probe/reservoir
carrier, retaining the prescribed cap and post unit.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open BalancedInduction CyclotomicCrossingTensor
universe u
section Series
variable {C : Type*} [Category* C] [Preadditive C] {X Y : C}
private theorem inverse_power_cancel (x : End X) (hx : IsUnit x) (r : ℕ) :
    x ≫ Ring.inverse x ^ (r + 1) = Ring.inverse x ^ r := by
  change Ring.inverse x ^ (r + 1) * x = Ring.inverse x ^ r
  rw [pow_succ, mul_assoc, Ring.inverse_mul_cancel _ hx, mul_one]
private def evenSeries (x : End X) (y : End Y) (t : X ⟶ Y) (n : ℕ) : X ⟶ Y :=
  ∑ r ∈ Finset.range n, (-1 : ℤ) • ((Ring.inverse x ^ (r + 1)) ≫ t ≫ y ^ r)
private theorem evenSeries_boundary (x : End X) (hx : IsUnit x)
    (y : End Y) (t : X ⟶ Y) (n : ℕ) :
    evenSeries x y t n ≫ y - x ≫ evenSeries x y t n =
      t - ((Ring.inverse x ^ n) ≫ t ≫ y ^ n) := by
  induction n with
  | zero => simp only [evenSeries, Finset.sum_range_zero, pow_zero, End.one_def,
      Category.id_comp, Category.comp_id, sub_self, Limits.zero_comp, Limits.comp_zero]
  | succ n ih =>
    have hs : evenSeries x y t (n + 1) = evenSeries x y t n -
        ((Ring.inverse x ^ (n + 1)) ≫ t ≫ y ^ n) := by
      rw [evenSeries, Finset.sum_range_succ, neg_one_zsmul, sub_eq_add_neg]
      rfl
    have hY : ((Ring.inverse x ^ (n + 1)) ≫ t ≫ y ^ n) ≫ y =
        (Ring.inverse x ^ (n + 1)) ≫ t ≫ y ^ (n + 1) := by
      simp only [pow_succ' y n, End.mul_def, Category.assoc]
    have hX : x ≫ ((Ring.inverse x ^ (n + 1)) ≫ t ≫ y ^ n) =
        (Ring.inverse x ^ n) ≫ t ≫ y ^ n := by
      rw [← Category.assoc, ← Category.assoc, inverse_power_cancel x hx n]
      exact Category.assoc _ _ _
    rw [hs, Preadditive.sub_comp, Preadditive.comp_sub, hY, hX]
    calc
      _ = (evenSeries x y t n ≫ y - x ≫ evenSeries x y t n) +
          ((Ring.inverse x ^ n) ≫ t ≫ y ^ n) -
          ((Ring.inverse x ^ (n + 1)) ≫ t ≫ y ^ (n + 1)) := by abel
      _ = _ := by rw [ih]; abel
private theorem evenSeries_slide (x : End X) (hx : IsUnit x)
    (y : End Y) (t : X ⟶ Y) (n : ℕ) (hn : y ^ n = 0) :
    evenSeries x y t n ≫ y - x ≫ evenSeries x y t n = t := by
  rw [evenSeries_boundary x hx y t n, hn, Limits.comp_zero, Limits.comp_zero, sub_zero]
end Series
namespace ProbeVacuumCap
variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m cutoff : I → ℕ) (bound : ℕ)
  (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)
local notation "R₀" => contentModuleTarget D Sc cutoff bound (0 : Multiset I)
local notation "N₀" => probeOldVacuumRegular D Sc m

/-- The parity-zero mate slide on the prescribed evaluated bend, with no slide premise. -/
theorem evaluatedMixedBend_even_slideOf
    (hdot : TruncatedAppendDotNilpotent D Sc cutoff bound) (i : I) (hi : D.parity i = 0)
    (hP : 0 < probeCutoff D m i) (H : modulePiCategory D Sc m ⟶ R₀) :
    evaluatedMixedBend D Sc m cutoff bound i hP H ≫ evaluatedPostDot D Sc m cutoff bound i H -
      koszulSign (D.parity i) (D.parity i) •
        (shiftedPreDot D Sc m R₀ i H ≫ evaluatedMixedBend D Sc m cutoff bound i hP H) =
      shiftedPreCap D Sc m R₀ i hP H ≫
        (adjunction (contentAppend D Sc cutoff bound (0 : Multiset I) [i])).unit.app (H.obj N₀) := by
  obtain ⟨n, _, hd⟩ := diagonalPostDot_pow_zero D Sc m cutoff bound hdot i
  obtain ⟨l, _, hy⟩ := evaluatedPostDot_pow_zero D Sc m cutoff bound hdot i
  have hd' : diagonalPostDot D Sc m cutoff bound i H ^ (n + l) = 0 :=
    pow_eq_zero_of_le (by omega) (hd H)
  have hy' : evaluatedPostDot D Sc m cutoff bound i H ^ (n + l) = 0 :=
    pow_eq_zero_of_le (by omega) (hy H)
  have he := evaluatedMixedBend_even_expansion D Sc m cutoff bound i hi hP H (n + l) hd'
  have hs : evaluatedMixedBend D Sc m cutoff bound i hP H =
      evenSeries (shiftedPreDot D Sc m R₀ i H) (evaluatedPostDot D Sc m cutoff bound i H)
        (shiftedPreCap D Sc m R₀ i hP H ≫
          (adjunction (contentAppend D Sc cutoff bound (0 : Multiset I) [i])).unit.app (H.obj N₀))
        (n + l) := by
    simpa only [evenSeries, Category.assoc] using he
  rw [hs, hi, koszulSign_zero_left, one_smul]
  exact evenSeries_slide _ (shiftedPreDot_even_isUnit D Sc m R₀ i hi H) _ _ _ hy'

include sy hc in
/-- For homogeneous parameters: the parity-zero mate slide on the prescribed evaluated bend,
with no slide premise. -/
theorem evaluatedMixedBend_even_slide (i : I) (hi : D.parity i = 0)
    (hP : 0 < probeCutoff D m i) (H : modulePiCategory D Sc m ⟶ R₀) :
    evaluatedMixedBend D Sc m cutoff bound i hP H ≫ evaluatedPostDot D Sc m cutoff bound i H -
      koszulSign (D.parity i) (D.parity i) •
        (shiftedPreDot D Sc m R₀ i H ≫ evaluatedMixedBend D Sc m cutoff bound i hP H) =
      shiftedPreCap D Sc m R₀ i hP H ≫
        (adjunction (contentAppend D Sc cutoff bound (0 : Multiset I) [i])).unit.app (H.obj N₀) :=
  evaluatedMixedBend_even_slideOf D Sc m cutoff bound
    (truncatedAppendDotNilpotent D Sc cutoff sy hc bound) i hi hP H

end ProbeVacuumCap
end OddMath.QuiverHecke.ELVOld
