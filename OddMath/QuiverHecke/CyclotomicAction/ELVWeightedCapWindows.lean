import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedPolynomialCaps

/-! # Weighted cap windows as module identities

The inverse-row window in SwappedVacuumNonpositiveBubbles §2 is an identity
of module maps at content zero. This attaches the given weighted unit/dot
columns to the prescribed cap before Hom postcomposition. The polynomial
cap is the same module map used in that note's negative-height inverse row.
No mixed mate or extractor is supplied as a hypothesis.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open BalancedInduction CyclotomicCrossingTensor
universe u

private theorem if_identity_total_apply
    {k C : Type u} [CommRing k] [Category.{u} C] [Preadditive C]
    [Linear k C] [Supercategory k C] (F : Superfunctor k C (SVec k))
    (b : Prop) [Decidable b] (w : C) (z : F.obj w) :
    ((if b then 𝟙 F else 0) : F ⟶ F).total w z = if b then z else 0 := by
  split_ifs
  · simp only [SuperNatTrans.total, Superfunctor.id_app_zero, Superfunctor.id_app_one,
      add_zero, SVec.id_apply]
  · simp only [SuperNatTrans.total, Superfunctor.zero_app, zero_add]
    rfl

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

private theorem emptyContent_eq (N : ℕ) (w : ContentCategory D Sc cutoff N 0) :
    w = ⟨⟨[]⟩, rfl⟩ := by
  rcases w with ⟨⟨w⟩, hw⟩
  have he : w = [] := by simpa only [Multiset.coe_eq_zero] using hw
  subst w
  rfl

private theorem emptyContent_total_injective (N : ℕ)
    (F G : Superfunctor k (ContentCategory D Sc cutoff N 0) (SVec k)) :
    Function.Injective (fun f : F ⟶ G => f.total ⟨⟨[]⟩, rfl⟩) := by
  intro f g h
  apply FiniteSupermodule.hom_ext_total
  intro w
  rw [emptyContent_eq D Sc cutoff N w]
  exact h

namespace PowerVacuumCoefficient
variable [Fintype I] (L : I × ℕ → ℕ)
local notation "bound" => SKM.SYM.elvPowerWeightBound D cutoff L + 1
local notation "WM" => weightedVacuum D Sc cutoff L
local notation "Q₀" => contentInclusion D Sc cutoff bound (0 : Multiset I)

/-- Restrict the given n-th unit/dot column to content zero. -/
def weightedUnitColumn (i : I) (n : ℕ) :=
  (restriction Q₀).map
    (unitDotColumn (truncatedAppend D Sc cutoff bound [i])
      (truncatedDot_supernatural D Sc cutoff bound i) WM n)

/-- The given column followed by the prescribed weighted cap is exactly
the finite inverse-row window as a module morphism, including odd inputs. -/
theorem weightedUnitColumn_cap (i : I) (hN : 0 < cutoff i)
    (n : ℕ) (hn : n < cutoff i) :
    weightedUnitColumn D Sc cutoff L i n ≫ weightedCoefficientCap D Sc cutoff i L hN =
      if n + 1 = cutoff i then 𝟙 ((restriction Q₀).obj WM) else 0 := by
  apply emptyContent_total_injective D Sc cutoff bound
  apply LinearMap.ext
  intro z
  obtain ⟨a, rfl⟩ := (weightedEmptyEquiv D Sc cutoff L).surjective z
  apply (weightedEmptyEquiv D Sc cutoff L).symm.injective
  dsimp only
  rw [Superfunctor.comp_total]
  change (weightedEmptyEquiv D Sc cutoff L).symm
    ((weightedCoefficientCap D Sc cutoff i L hN).total ⟨⟨[]⟩, rfl⟩
      ((unitDotColumn (truncatedAppend D Sc cutoff bound [i])
        (truncatedDot_supernatural D Sc cutoff bound i) WM n).total
          ((oldTruncateFunctor D Sc cutoff bound).obj ⟨[]⟩)
            (weightedEmptyEquiv D Sc cutoff L a))) = _
  rw [← weightedFunctional_coefficientCap]
  rw [weightedFunctional_unitDotColumn D Sc cutoff L i hN n hn a]
  rw [if_identity_total_apply]
  split_ifs
  · exact ((weightedEmptyEquiv D Sc cutoff L).symm_apply_apply a).symm
  · exact ((weightedEmptyEquiv D Sc cutoff L).symm.map_zero).symm


/-- Below the reservoir cutoff, the monic polynomial cap extracts exactly
its final low-unit column. This is an operator equality on every A/T input. -/
theorem weightedPolynomialCapMoment_window (i : I) (hN : 0 < cutoff i)
    (M n : ℕ) (hn : 2 * M + n < cutoff i) :
    weightedPolynomialCapMoment D Sc cutoff L i hN M n =
      if 2 * M + n + 1 = cutoff i then 1 else 0 := by
  rw [weightedPolynomialCapMoment_sum]
  calc
    _ = M.choose M • weightedMomentMap D Sc cutoff L i hN (2 * M + n) := by
      apply Finset.sum_eq_single M
      · intro j hj hjM
        have hjle : j ≤ M := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
        have hjlt : j < M := by omega
        rw [weightedMomentMap_window D Sc cutoff L i hN _ (by omega),
          ite_eq_right (by omega : 2 * j + n + 1 ≠ cutoff i), nsmul_zero]
      · simp
    _ = _ := by
      rw [Nat.choose_self, one_nsmul, weightedMomentMap_window D Sc cutoff L i hN _ hn]

/-- The same polynomial-window identity holds for the given unit column
and polynomial cap as entire content-zero module maps. -/
theorem weightedUnitColumn_polynomialCap (i : I) (hN : 0 < cutoff i)
    (M n : ℕ) (hn : 2 * M + n < cutoff i) :
    weightedUnitColumn D Sc cutoff L i n ≫ weightedPolynomialCap D Sc cutoff L i hN M =
      if 2 * M + n + 1 = cutoff i then 𝟙 ((restriction Q₀).obj WM) else 0 := by
  apply emptyContent_total_injective D Sc cutoff bound
  apply LinearMap.ext
  intro z
  obtain ⟨a, rfl⟩ := (weightedEmptyEquiv D Sc cutoff L).surjective z
  apply (weightedEmptyEquiv D Sc cutoff L).symm.injective
  dsimp only
  rw [Superfunctor.comp_total]
  change (weightedEmptyEquiv D Sc cutoff L).symm
    ((weightedPolynomialCap D Sc cutoff L i hN M).total ⟨⟨[]⟩, rfl⟩
      ((unitDotColumn (truncatedAppend D Sc cutoff bound [i])
        (truncatedDot_supernatural D Sc cutoff bound i) WM n).total
          ((oldTruncateFunctor D Sc cutoff bound).obj ⟨[]⟩)
            (weightedEmptyEquiv D Sc cutoff L a))) = _
  rw [← weightedPolynomialCapMoment_moduleCap,
    weightedPolynomialCapMoment_window D Sc cutoff L i hN M n hn, if_identity_total_apply]
  split_ifs
  · exact ((weightedEmptyEquiv D Sc cutoff L).symm_apply_apply a).symm
  · exact ((weightedEmptyEquiv D Sc cutoff L).symm.map_zero).symm

end PowerVacuumCoefficient
end OddMath.QuiverHecke.ELVOld
