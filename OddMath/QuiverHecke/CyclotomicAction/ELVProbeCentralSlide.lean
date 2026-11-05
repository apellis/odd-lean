import OddMath.QuiverHecke.CyclotomicAction.ELVProbeCentralBend
import Mathlib.Tactic.Abel

/-! # The signed slide of the evaluated mixed bend

SwappedVacuumNonpositiveBubbles §1 (1) for the actual evaluated A6 bend.
The finite central series telescopes using its raw regular-probe dot unit
and the given fixed-content reservoir nilpotence. No slide for an arbitrary
map is assumed.
-/
noncomputable section
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
namespace OddMath.QuiverHecke.ELVOld
open BalancedInduction CyclotomicCrossingTensor
universe u
section Series
variable {C : Type*} [Category* C] [Preadditive C] {X Y : C}
private theorem inverse_power_cancel (x : End X) (hx : IsUnit x) (m : ℕ) :
    x ≫ (Ring.inverse x ^ (m + 1)) = Ring.inverse x ^ m := by
  change Ring.inverse x ^ (m + 1) * x = Ring.inverse x ^ m
  rw [pow_succ, mul_assoc, Ring.inverse_mul_cancel _ hx, mul_one]
private def series (x : End X) (y : End Y) (t : X ⟶ Y) (m : ℕ) : X ⟶ Y :=
  ∑ r ∈ Finset.range m, (-1 : ℤ) ^ r • ((Ring.inverse x ^ (r + 1)) ≫ t ≫ (y ^ r))
private theorem series_slide_boundary (x : End X) (hx : IsUnit x) (y : End Y) (t : X ⟶ Y) (m : ℕ) :
    series x y t m ≫ y + x ≫ series x y t m =
      t - (-1 : ℤ) ^ m • ((Ring.inverse x ^ m) ≫ t ≫ (y ^ m)) := by
  induction m with
  | zero => simp only [series, Finset.sum_range_zero, pow_zero, End.one_def, Category.id_comp,
      Category.comp_id, one_zsmul, sub_self, Limits.zero_comp, Limits.comp_zero, zero_add]
  | succ m ih =>
    have hs : series x y t (m + 1) = series x y t m +
        (-1 : ℤ) ^ m • ((Ring.inverse x ^ (m + 1)) ≫ t ≫ (y ^ m)) := by
      rw [series, Finset.sum_range_succ]
      rfl
    have hY : ((Ring.inverse x ^ (m + 1)) ≫ t ≫ (y ^ m)) ≫ y =
        (Ring.inverse x ^ (m + 1)) ≫ t ≫ (y ^ (m + 1)) := by
      simp only [pow_succ' y m, End.mul_def, Category.assoc]
    have hX : x ≫ ((Ring.inverse x ^ (m + 1)) ≫ t ≫ (y ^ m)) =
        (Ring.inverse x ^ m) ≫ t ≫ (y ^ m) := by
      rw [← Category.assoc, ← Category.assoc, inverse_power_cancel x hx m]
      exact Category.assoc _ _ _
    rw [hs, Preadditive.add_comp, Preadditive.comp_add, Preadditive.zsmul_comp,
      Preadditive.comp_zsmul, hY, hX]
    calc
      _ = (series x y t m ≫ y + x ≫ series x y t m) +
          (-1 : ℤ) ^ m • ((Ring.inverse x ^ (m + 1)) ≫ t ≫ (y ^ (m + 1))) +
          (-1 : ℤ) ^ m • ((Ring.inverse x ^ m) ≫ t ≫ (y ^ m)) := by abel
      _ = _ := by
        rw [ih, show (-1 : ℤ) ^ (m + 1) = -((-1 : ℤ) ^ m) by rw [pow_succ, mul_neg_one],
          neg_smul, sub_neg_eq_add]
        abel
private theorem series_slide (x : End X) (hx : IsUnit x) (y : End Y) (t : X ⟶ Y)
    (m : ℕ) (hy : y ^ m = 0) :
    series x y t m ≫ y + x ≫ series x y t m = t := by
  rw [series_slide_boundary x hx y t m, hy, Limits.comp_zero, Limits.comp_zero,
    smul_zero, sub_zero]
end Series
namespace ProbeVacuumCap
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) [Fintype I] (m : I → ℕ)
  (reservoirCutoff : I → ℕ) (bound : ℕ) (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)
local notation "R₀" => contentModuleTarget D Sc reservoirCutoff bound (0 : Multiset I)
local notation "N₀" => probeOldVacuumRegular D Sc m

/-- The signed mate slide on the actual regular-probe evaluated mixed
bend. All its maps are the given raw dot, shifted cap and reservoir unit. -/
theorem evaluatedMixedBend_odd_slideOf
    (hdot : TruncatedAppendDotNilpotent D Sc reservoirCutoff bound) (i : I) (hi : D.parity i = 1)
    (hP : 0 < probeCutoff D m i) (H : modulePiCategory D Sc m ⟶ R₀) :
    evaluatedMixedBend D Sc m reservoirCutoff bound i hP H ≫
        evaluatedPostDot D Sc m reservoirCutoff bound i H -
      koszulSign (D.parity i) (D.parity i) •
        (shiftedPreDot D Sc m R₀ i H ≫ evaluatedMixedBend D Sc m reservoirCutoff bound i hP H) =
      shiftedPreCap D Sc m R₀ i hP H ≫
        (adjunction (contentAppend D Sc reservoirCutoff bound (0 : Multiset I) [i])).unit.app (H.obj N₀) := by
  obtain ⟨n, hn, hd⟩ := diagonalPostDot_pow_zero D Sc m reservoirCutoff bound hdot i
  obtain ⟨l, hl, hy⟩ := evaluatedPostDot_pow_zero D Sc m reservoirCutoff bound hdot i
  have hd' : diagonalPostDot D Sc m reservoirCutoff bound i H ^ (n + l) = 0 :=
    pow_eq_zero_of_le (by omega) (hd H)
  have hy' : evaluatedPostDot D Sc m reservoirCutoff bound i H ^ (2 * (n + l)) = 0 :=
    pow_eq_zero_of_le (by omega) (hy H)
  have he := evaluatedMixedBend_odd_expansion D Sc m reservoirCutoff bound i hi hP H (n + l) hd'
  have hs : evaluatedMixedBend D Sc m reservoirCutoff bound i hP H =
      series (shiftedPreDot D Sc m R₀ i H) (evaluatedPostDot D Sc m reservoirCutoff bound i H)
        (shiftedPreCap D Sc m R₀ i hP H ≫
          (adjunction (contentAppend D Sc reservoirCutoff bound (0 : Multiset I) [i])).unit.app (H.obj N₀))
        (2 * (n + l)) := by
    simpa only [series, Category.assoc] using he
  rw [hs, hi, koszulSign_one_one, neg_one_zsmul, sub_neg_eq_add]
  exact series_slide _ (shiftedPreDot_isUnit D Sc m R₀ i hi H) _ _ _ hy'

include sy hc in
/-- For homogeneous parameters: the signed mate slide on the actual regular-probe evaluated mixed
bend. All its maps are the given raw dot, shifted cap and reservoir unit. -/
theorem evaluatedMixedBend_odd_slide (i : I) (hi : D.parity i = 1)
    (hP : 0 < probeCutoff D m i) (H : modulePiCategory D Sc m ⟶ R₀) :
    evaluatedMixedBend D Sc m reservoirCutoff bound i hP H ≫
        evaluatedPostDot D Sc m reservoirCutoff bound i H -
      koszulSign (D.parity i) (D.parity i) •
        (shiftedPreDot D Sc m R₀ i H ≫ evaluatedMixedBend D Sc m reservoirCutoff bound i hP H) =
      shiftedPreCap D Sc m R₀ i hP H ≫
        (adjunction (contentAppend D Sc reservoirCutoff bound (0 : Multiset I) [i])).unit.app (H.obj N₀) :=
  evaluatedMixedBend_odd_slideOf D Sc m reservoirCutoff bound
    (truncatedAppendDotNilpotent D Sc reservoirCutoff sy hc bound) i hi hP H

end ProbeVacuumCap
end OddMath.QuiverHecke.ELVOld
