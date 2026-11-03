import OddMath.QuiverHecke.CyclotomicAction.ELVReservoirWordValue
import OddMath.QuiverHecke.HalfTurn.PowerWordCoordinates
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath OddMath.SKM OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction OddMath.QuiverHecke.SwappedAssembly
namespace NonVacuity.ELVReservoirWordValue

private abbrev D := AsymmetricParameters.datum
private abbrev originalSc := AsymmetricParameters.scalars
private abbrev Sc := parameterTwist D originalSc
private def cutoff (_ : Bool) : ℕ := 20
private def L (_ : Bool × ℕ) : ℕ := 10
private abbrev N := PowerWordContent.powerBound D cutoff L
private def Λ : Bool → ℤ := fun _ => 20

private def labels : List (Col Bool (Bool → ℤ)) := wd D 0 [(true, false), (true, true)]
private theorem upward : ∀ a ∈ labels, a.l.1 = true := by simp [labels, wd]

/-- The selected native reservoir value is the reversed chosen E-word
value on its literal regular-power empty-word family. -/
example := ReservoirWordValue.reservoirPath_value_heq D Λ Sc cutoff L labels upward
example := ReservoirWordValue.pathChart_hom_mem D Λ Sc cutoff L labels upward

private abbrev ν : List Bool := [true, false]
private abbrev σ : List Bool := ν.reverse
private def w : ContentCategory D Sc cutoff N (ν : Multiset Bool) := ⟨⟨ν⟩, rfl⟩

private theorem powers_high (j : Bool × ℕ) : 16 ≤ L j * SKM.SYM.elementaryWeight D j := by
  change 16 ≤ 10 * (2 * (j.2 + 1))
  omega
private theorem bounded_injective :
    Function.Injective (fun x : ExtendedAtMost D originalSc σ σ 2 =>
      powerWordHalfTurnCoordinate D originalSc cutoff L σ σ x.val) :=
  powerWordHalfTurnCoordinate_injective_on_extendedAtMost D originalSc cutoff L
    (fun _ => (by decide : 16 ≤ 20)) powers_high (by decide)
private def identityNF : NFIdx σ σ := by
  have hc : Categorification.TypeA.canWord σ.length (1 : Equiv.Perm (Fin σ.length)) = [] := by
    apply List.length_eq_zero_iff.mp
    rw [Categorification.TypeA.length_canWord, Categorification.TypeA.length_one]
  refine ⟨([], 1), by simp, by simp, ?_⟩
  simp only [List.map_nil, hc, cw, List.reverse_nil, List.nil_append, pl, SChain]
private def oddIndex : SKM.SYM.CoefficientIndex D := (0, {⟨false, rfl⟩, ⟨true, rfl⟩})
private def occupied : ExtendedAtMost D originalSc σ σ 2 :=
  ⟨extensionBasis D originalSc σ σ (oddIndex, identityNF),
    Submodule.subset_span ⟨(oddIndex, identityNF), by decide, rfl⟩⟩

private def contentVector : (PowerWordWeight.wordAt D Sc cutoff L ν (ν : Multiset Bool)).obj w :=
  powerWordHalfTurnCoordinate D originalSc cutoff L σ σ occupied.val
private theorem contentVector_ne_zero : contentVector ≠ 0 := by
  intro hz
  have hh : occupied = (0 : ExtendedAtMost D originalSc σ σ 2) := by
    apply bounded_injective
    change powerWordHalfTurnCoordinate D originalSc cutoff L σ σ occupied.val =
      powerWordHalfTurnCoordinate D originalSc cutoff L σ σ 0
    exact hz.trans (map_zero _).symm
  exact (extensionBasis D originalSc σ σ).ne_zero (oddIndex, identityNF) (congrArg Subtype.val hh)

private abbrev wordUnit := PowerWordContentCyclicity.wordUnit D Sc cutoff L ν (ν : Multiset Bool) rfl
private theorem wordUnit_ne_zero : wordUnit ≠ 0 := by
  intro hz
  obtain ⟨g, hg⟩ := PowerWordContentCyclicity.generator_surjective D Sc cutoff L ν (ν : Multiset Bool) w
    contentVector
  have hu := PowerWordContentCyclicity.generator_as_map_unit D Sc cutoff L ν (ν : Multiset Bool) rfl w g
  rw [hz, map_zero] at hu
  exact contentVector_ne_zero (hg.symm.trans hu.symm)

private abbrev β := PowerWordWeight.wordBlock D Λ ν
private abbrev WO := PowerWordContentCyclicity.wordObject D Sc cutoff L ν (ν : Multiset Bool) rfl
private abbrev pathEquiv := moduleIsoLinearEquiv
  (Pi.isoApp (ReservoirWordValue.pathChart D Λ Sc cutoff L labels upward) β) WO
private def pathVector := pathEquiv.symm wordUnit
private def pathCoefficient := pathEquiv.symm contentVector

/-- The independent product of two odd coefficients survives in the
literal native path value itself, through its prescribed even chart. -/
example : pathCoefficient ≠ 0 := by
  intro hz
  apply contentVector_ne_zero
  have hh := congrArg pathEquiv hz
  simpa only [pathCoefficient, LinearEquiv.apply_symm_apply, map_zero] using hh

/-- The actual native reservoir path value is occupied: its cyclic unit
survives through the same chart as the independent two-odd coefficient. -/
example : pathVector ≠ 0 := by
  intro hz
  apply wordUnit_ne_zero
  have hh := congrArg pathEquiv hz
  simpa only [pathVector, LinearEquiv.apply_symm_apply, map_zero] using hh

end NonVacuity.ELVReservoirWordValue

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for owner in #[`OddMath.QuiverHecke.CyclotomicAction.ELVReservoirWordValue,
      `OddMath.QuiverHecke.SwappedAssembly.ReservoirWordFunctor] do
    let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owned module {owner}"
    let names := env.header.moduleData[idx]!.constNames
    if names.isEmpty then throwError "Empty owned module {owner}"
    for name in names do
      for ax in ← Lean.collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {name}"
    logInfo m!"Audited all {names.size} owned declarations of {owner}"
