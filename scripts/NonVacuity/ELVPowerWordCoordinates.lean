import OddMath.QuiverHecke.CyclotomicAction.ELVPowerWordCoordinates
import OddMath.QuiverHecke.HalfTurn.PowerWordCoordinates
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters

/-! Actual regular A/T word induction with both odd coefficient colours.
A nonempty two-strand coordinate carrying their exterior product survives.
These tests do not assume or assert a chosen SKM-action evaluation identity.
-/
noncomputable section
namespace NonVacuity.ELVPowerWordCoordinates
open CategoryTheory StringDiagrams OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
private abbrev D := CyclotomicAction.AsymmetricParameters.datum
private abbrev Sc := CyclotomicAction.AsymmetricParameters.scalars
private def cutoff (_ : Bool) : ℕ := 8
private def L (_ : Bool × ℕ) : ℕ := 3
private def ν : List Bool := [false, true]

example (w : OldCategory D Sc cutoff) :
    Function.Surjective (powerWordGenerator D Sc cutoff L ν w) :=
  powerWordGenerator_surjective D Sc cutoff L ν w

example (w : OldCategory D Sc cutoff) :
    LinearMap.ker (powerWordGenerator D Sc cutoff L ν w) =
      powerWordRelationSpan D Sc cutoff L ν w := powerWordGenerator_ker D Sc cutoff L ν w

example : powerWordModule D Sc cutoff L [] = coefficientPowerVacuum D Sc cutoff L :=
  powerWordModule_nil D Sc cutoff L

example (i : Bool) := powerWordAppendIso D Sc cutoff L ν i
example (w : OldCategory D Sc cutoff) :=
  powerWordRelationSpan_eq_elementaryPowerImage D Sc cutoff L ν w
example (w : OldCategory D Sc cutoff) := powerWordSourceMap_ker D Sc cutoff L ν w

/-- These actual word values belong to the literal power-module category. -/
example : CoefficientPowerModules D Sc cutoff (elementaryCoefficients (k := ℚ) D cutoff) L :=
  powerWordObject D Sc cutoff L ν

private theorem powers_heavy (j : Bool × ℕ) : 6 ≤ L j * SKM.SYM.elementaryWeight D j := by
  change 6 ≤ 3 * (2 * (j.2 + 1))
  omega

/-- The source coordinate kernel is computed in the actual word value. -/
example := powerWordHalfTurnCoordinate_ker D Sc cutoff L ν ν

example (μ : Bool → ℤ) := powerWordHalfTurnCoordinate_kernel_le_vacuumWindow D Sc L μ ν ν 2
  (fun j => Nat.le_trans (by decide : vacuumCutoff ν 2 ≤ 6) (powers_heavy j))

example (μ : Bool → ℤ) := powerWordHalfTurnCoordinate_reservoir_injective D Sc L μ ν ν 2
  (fun j => Nat.le_trans (by decide : vacuumCutoff ν 2 ≤ 6) (powers_heavy j))

private theorem bounded_injective :
    Function.Injective (fun x : ExtendedAtMost D Sc ν ν 2 =>
      powerWordHalfTurnCoordinate D Sc cutoff L ν ν x.val) :=
  powerWordHalfTurnCoordinate_injective_on_extendedAtMost D Sc cutoff L
    (fun _ => (by decide : 6 ≤ 8)) powers_heavy (by decide)

private def identityNF : NFIdx ν ν := by
  have hc : Categorification.TypeA.canWord ν.length (1 : Equiv.Perm (Fin ν.length)) = [] := by
    apply List.length_eq_zero_iff.mp
    rw [Categorification.TypeA.length_canWord, Categorification.TypeA.length_one]
  refine ⟨([], 1), by simp, by simp, ?_⟩
  simp only [List.map_nil, hc, cw, List.reverse_nil, List.nil_append, pl, SChain]

private def oddIndex : SKM.SYM.CoefficientIndex D := (0, {⟨false, rfl⟩, ⟨true, rfl⟩})

private def occupied : ExtendedAtMost D Sc ν ν 2 :=
  ⟨extensionBasis D Sc ν ν (oddIndex, identityNF),
    Submodule.subset_span ⟨(oddIndex, identityNF), by decide, rfl⟩⟩


/-- Occupied nonempty actual induction: the PBW coordinate with BOTH odd
exterior generators is nonzero after all old and literal power relations. -/
example : powerWordHalfTurnCoordinate D Sc cutoff L ν ν occupied.val ≠ 0 := by
  intro hz
  have hh : occupied = (0 : ExtendedAtMost D Sc ν ν 2) := by
    apply bounded_injective
    change powerWordHalfTurnCoordinate D Sc cutoff L ν ν occupied.val =
      powerWordHalfTurnCoordinate D Sc cutoff L ν ν 0
    exact hz.trans (map_zero _).symm
  exact (extensionBasis D Sc ν ν).ne_zero (oddIndex, identityNF) (congrArg Subtype.val hh)

/-- The codomain is a component of actual regular-power word induction,
with the prescribed reversal and parameter twist retained literally. -/
example (x : coefficientObj D Sc ν ⟶ coefficientObj D Sc ν) :
    (powerWordModule D (parameterTwist D Sc) cutoff L ν.reverse).obj
      (⟨ν.reverse⟩ : OldCategory D (parameterTwist D Sc) cutoff) :=
  powerWordHalfTurnCoordinate D Sc cutoff L ν ν x

end NonVacuity.ELVPowerWordCoordinates

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for owner in #[`OddMath.QuiverHecke.CyclotomicAction.ELVPowerWordCoordinates,
      `OddMath.QuiverHecke.HalfTurn.PowerWordCoordinates] do
    let some idx := env.header.moduleNames.idxOf? owner
      | throwError "Module was not imported: {owner}"
    let names := env.header.moduleData[idx]!.constNames
    unless names.size > 0 do throwError "Empty owned declaration inventory"
    for name in names do
      for ax in ← Lean.collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {name}"
    logInfo m!"Audited ALL {names.size} owned declarations in {owner}, including private/generated"
