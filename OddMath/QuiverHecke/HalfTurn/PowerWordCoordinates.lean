import OddMath.QuiverHecke.CyclotomicAction.ELVPowerWordCoordinates
import OddMath.QuiverHecke.HalfTurn.OldQuotient

/-! # Bounded half-turn coordinates in actual regular-power word values

SwappedVacuumCoordinates §§2–6. These are coordinates in actual induction
of the literal regular A/T vacuum, on reversed words at the twisted
parameters. The presentation kernel is computed, including unchanged
coefficient powers. Identifying the chosen SKM action evaluation with these
coordinates remains a separate generator-comparison task.
-/
noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (L : I × ℕ → ℕ)

/-- The signed source coordinate in an actual word value of regular A/T. -/
def powerWordHalfTurnCoordinate (s t : List I) :
    (coefficientObj D Sc s ⟶ coefficientObj D Sc t) →ₗ[k]
      (ELVOld.powerWordModule D (parameterTwist D Sc) cutoff L t.reverse).obj
        (⟨s.reverse⟩ : ELVOld.OldCategory D (parameterTwist D Sc) cutoff) :=
  (ELVOld.powerWordSourceMap D (parameterTwist D Sc) cutoff L t.reverse ⟨s.reverse⟩).comp
    (htCoef D Sc s t)

/-- The intermediate map is the literal old Hom half-turn, followed by its
original balanced coend unit h tensor 1. -/
theorem powerWordHalfTurnCoordinate_eq (s t : List I) :
    powerWordHalfTurnCoordinate D Sc cutoff L s t =
      (ELVOld.powerWordGenerator D (parameterTwist D Sc) cutoff L t.reverse ⟨s.reverse⟩).comp
        (halfTurnOldHom D Sc cutoff s t) := by
  unfold powerWordHalfTurnCoordinate ELVOld.powerWordSourceMap halfTurnOldHom
  exact LinearMap.comp_assoc _ _ _

/-- Exact source kernel, including the paper's literal elementary powers. -/
theorem powerWordHalfTurnCoordinate_ker (s t : List I) :
    LinearMap.ker (powerWordHalfTurnCoordinate D Sc cutoff L s t) =
      TransformedIdeal D Sc cutoff
        (Set.range fun j : I × ℕ => SKM.SYM.e D k j.1 j.2 ^ L j) s t := by
  rw [powerWordHalfTurnCoordinate, LinearMap.ker_comp, ELVOld.powerWordSourceMap_ker,
    ← ELVOld.comap_oldIdeal_sup_elementaryPowers D (parameterTwist D Sc) cutoff L t.reverse s.reverse,
    ← Submodule.comap_comp]
  exact halfTurn_oldElementaryPowers_preimage D Sc cutoff L s t

private theorem elementaryPowers_weight {N : ℕ}
    (hL : ∀ j, N ≤ L j * SKM.SYM.elementaryWeight D j) :
    ∀ a ∈ (Set.range fun j : I × ℕ => SKM.SYM.e D k j.1 j.2 ^ L j),
      a ∈ SKM.SYM.CoefficientAtLeast D k N := by
  rintro a ⟨j, rfl⟩
  exact SKM.SYM.coefficientAtLeast_antitone D k (hL j)
    (SKM.SYM.elementary_pow_mem_coefficientAtLeast D k j (L j))

/-- Actual word values detect the full coefficient/PBW window under the
explicit cutoff and literal power inequalities, with no kernel premise. -/
theorem powerWordHalfTurnCoordinate_injective_on_extendedAtMost
    {s t : List I} {d N : ℕ} (hN : ∀ i, N ≤ cutoff i)
    (hL : ∀ j, N ≤ L j * SKM.SYM.elementaryWeight D j)
    (hd : d + 2 * s.length.choose 2 < N) :
    Function.Injective (fun x : ExtendedAtMost D Sc s t d =>
      powerWordHalfTurnCoordinate D Sc cutoff L s t x.val) := by
  intro x y hxy
  apply transformedIdeal_quotient_injective_on_extendedAtMost D Sc hN
    (elementaryPowers_weight D L hL) hd
  apply (Submodule.Quotient.eq _).mpr
  rw [← powerWordHalfTurnCoordinate_ker D Sc cutoff L s t]
  change powerWordHalfTurnCoordinate D Sc cutoff L s t (x.val - y.val) = 0
  rw [map_sub]
  exact sub_eq_zero.mpr hxy

/-- The actual-coordinate kernel satisfies the prescribed vacuum window
bound for the literal reservoir schedule. -/
theorem powerWordHalfTurnCoordinate_kernel_le_vacuumWindow
    (μ : X) (s t : List I) (d : ℕ)
    (hL : ∀ j, vacuumCutoff s d ≤ L j * SKM.SYM.elementaryWeight D j) :
    LinearMap.ker (powerWordHalfTurnCoordinate D Sc (reservoirLevel D μ s d) L s t) ≤
      ExtendedAtLeast D Sc s t ((vacuumCutoff s d : ℤ) - 2 * s.length.choose 2) := by
  rw [powerWordHalfTurnCoordinate_ker]
  exact transformedIdeal_le_vacuumWindow D Sc μ s t d (elementaryPowers_weight D L hL)

/-- Bounded detection in the actual word values at the prescribed schedule. -/
theorem powerWordHalfTurnCoordinate_reservoir_injective (μ : X) (s t : List I) (d : ℕ)
    (hL : ∀ j, vacuumCutoff s d ≤ L j * SKM.SYM.elementaryWeight D j) :
    Function.Injective (fun x : ExtendedAtMost D Sc s t d =>
      powerWordHalfTurnCoordinate D Sc (reservoirLevel D μ s d) L s t x.val) :=
  powerWordHalfTurnCoordinate_injective_on_extendedAtMost D Sc _ L
    (vacuumCutoff_le_reservoirLevel D μ s d) hL (by simp [vacuumCutoff])

end OddMath.QuiverHecke
