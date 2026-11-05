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

end OddMath.QuiverHecke
