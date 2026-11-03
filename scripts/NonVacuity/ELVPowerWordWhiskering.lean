import OddMath.QuiverHecke.CyclotomicAction.ELVPowerWordWhiskering
import OddMath.QuiverHecke.HalfTurn.PowerWordCoordinates
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

/-! Chosen append comparisons for old-Hom maps in a right context on
an occupied three-strand A/T module with both odd coefficient colours. -/
noncomputable section
namespace NonVacuity.ELVPowerWordWhiskering
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open CyclotomicCrossingTensor
private abbrev D := CyclotomicAction.AsymmetricParameters.datum
private abbrev originalSc := CyclotomicAction.AsymmetricParameters.scalars
private abbrev Sc := parameterTwist D originalSc
private def cutoff (_ : Bool) : ℕ := 20
private def L (_ : Bool × ℕ) : ℕ := 10
private abbrev ν : List Bool := [false, true]
private abbrev τ : List Bool := ν ++ [false]
private abbrev σ : List Bool := τ.reverse
private abbrev C := OldCategory D Sc cutoff
private abbrev target := powerWordModule D Sc cutoff L τ

/-- An arbitrary old arrow, with BOTH parity components, on this occupied
three-strand append module. No homogeneity premise remains. -/
example (g : (⟨ν⟩ : C) ⟶ (⟨ν⟩ : C)) :=
  PowerWordWhiskering.append_fromArrow_all D Sc cutoff L ν ν false g

/-- A literal odd dot in the middle position after a right append. -/
example := PowerWordWhiskering.append_fromArrow D Sc cutoff L [false, true] [false, true] false
  (oldAppendDotComponent D Sc cutoff true (⟨[false]⟩ : C))
  ((oldAppendDot_supernatural D Sc cutoff true).mem (⟨[false]⟩ : C))

/-- The independently chosen positive crossing gets a right context. -/
example := PowerWordWhiskering.append_fromArrow D Sc cutoff L [false, true] [true, false] false
  (Distinct.crossComponent D Sc cutoff false true (⟨[]⟩ : C))
  ((Distinct.cross_supernatural D Sc cutoff false true).mem (⟨[]⟩ : C))

/-- The equal-colour underlying arrow also admits the same context; its
separately chosen action crossing retains the checked extra minus. -/
example := PowerWordWhiskering.append_fromArrow D Sc cutoff L [false, false] [false, false] true
  (equalCrossComponent D Sc cutoff false (⟨[]⟩ : C))
  ((equalCross_supernatural D Sc cutoff false).mem (⟨[]⟩ : C))

private def oddCoefficient : SKM.SYM.ELVCoefficientAlgebra (k := ℚ) D cutoff :=
  SKM.SYM.elvCoefficientQuotient D cutoff (SKM.SYM.delta D ℚ ⟨false, rfl⟩)

/-- Explicit even-plus-odd coefficient input uses the literal coefficient
endomorphism, with no commutativity or parity premise. -/
example := PowerWordWhiskering.append_fromArrow_all D Sc cutoff L ν ν false
  (𝟙 (⟨ν⟩ : C) + coefficientEndomorphism D Sc cutoff ν oddCoefficient)

/-- The chart in this square retains arbitrary full coefficients inside
its total parity twist. -/
example (g h : (⟨ν⟩ : C) ⟶ (⟨ν⟩ : C))
    (a : SKM.SYM.ELVCoefficientAlgebra (k := ℚ) D cutoff) :=
  PowerWordMorphisms.fromArrow_generator D Sc cutoff L ν ν g 1 (⟨ν⟩ : C)
    (coefficientEndomorphism D Sc cutoff ν a ≫ h)

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

/-- The SAME actual target of the selected append square contains
an independent two-colour exterior coefficient vector that survives. -/
example : (show target.obj (⟨τ⟩ : C) from
    powerWordHalfTurnCoordinate D originalSc cutoff L σ σ occupied.val) ≠ 0 := by
  intro hz
  have hh : occupied = (0 : ExtendedAtMost D originalSc σ σ 2) := by
    apply bounded_injective
    change powerWordHalfTurnCoordinate D originalSc cutoff L σ σ occupied.val =
      powerWordHalfTurnCoordinate D originalSc cutoff L σ σ 0
    exact hz.trans (map_zero _).symm
  exact (extensionBasis D originalSc σ σ).ne_zero (oddIndex, identityNF) (congrArg Subtype.val hh)

end NonVacuity.ELVPowerWordWhiskering
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let some idx := env.header.moduleNames.idxOf?
      `OddMath.QuiverHecke.CyclotomicAction.ELVPowerWordWhiskering | throwError "Module not imported"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "No owned declarations"
  for name in names do
    for axiomName in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
  logInfo m!"Audited {names.size} owned declarations: standard axioms only"
