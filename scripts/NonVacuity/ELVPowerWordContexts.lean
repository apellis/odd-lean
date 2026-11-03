import OddMath.QuiverHecke.CyclotomicAction.ELVPowerWordContexts
import OddMath.QuiverHecke.HalfTurn.PowerWordCoordinates
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

/-! Chosen induction comparisons for arbitrary right contexts on
an occupied four-strand A/T module with both odd coefficient colours. -/
noncomputable section
namespace NonVacuity.ELVPowerWordContexts
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open CyclotomicCrossingTensor
private abbrev D := CyclotomicAction.AsymmetricParameters.datum
private abbrev originalSc := CyclotomicAction.AsymmetricParameters.scalars
private abbrev Sc := parameterTwist D originalSc
private def cutoff (_ : Bool) : ℕ := 20
private def L (_ : Bool × ℕ) : ℕ := 10
private abbrev ν : List Bool := [false, true]
private abbrev τ : List Bool := ν ++ [false, true]
private abbrev σ : List Bool := τ.reverse
private abbrev C := OldCategory D Sc cutoff
private abbrev target := powerWordModule D Sc cutoff L τ

/-- The recursive endpoints are the literal word concatenations. -/
example : PowerWordContexts.extendedWord ν [false, true] = ν ++ [false, true] :=
  PowerWordContexts.extendedWord_eq ν [false, true]

/-- Arbitrary suffix and arbitrary old arrow, retaining both parity
components. No hypothesis on the chosen action maps is supplied. -/
example (η : List Bool) (g : (⟨ν⟩ : C) ⟶ (⟨ν⟩ : C)) :=
  PowerWordContexts.context_fromArrow D Sc cutoff L ν ν η g

/-- A literal odd dot in an interior position of a four-strand word. -/
example := PowerWordContexts.context_fromArrow D Sc cutoff L [false, true] [false, true] [false, true]
  (oldAppendDotComponent D Sc cutoff true (⟨[false]⟩ : C))

/-- The chosen positive crossing gets a two-letter right context. -/
example := PowerWordContexts.context_fromArrow D Sc cutoff L [false, true] [true, false] [true, false]
  (Distinct.crossComponent D Sc cutoff false true (⟨[]⟩ : C))

/-- The underlying equal-colour arrow gets the same nonempty context. -/
example := PowerWordContexts.context_fromArrow D Sc cutoff L [false, false] [false, false] [true, false]
  (equalCrossComponent D Sc cutoff false (⟨[]⟩ : C))

private def oddCoefficient : SKM.SYM.ELVCoefficientAlgebra (k := ℚ) D cutoff :=
  SKM.SYM.elvCoefficientQuotient D cutoff (SKM.SYM.delta D ℚ ⟨false, rfl⟩)

/-- Inhomogeneous coefficient endomorphism under the literal chosen
composite functor; all exterior coefficients remain available. -/
example := PowerWordContexts.context_fromArrow D Sc cutoff L ν ν [false, true]
  (𝟙 (⟨ν⟩ : C) + coefficientEndomorphism D Sc cutoff ν oddCoefficient)

/-- The full-coefficient chart used by the context square. -/
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

/-- The SAME actual target of the selected context square contains
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

end NonVacuity.ELVPowerWordContexts
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let some idx := env.header.moduleNames.idxOf?
      `OddMath.QuiverHecke.CyclotomicAction.ELVPowerWordContexts | throwError "Module not imported"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "No owned declarations"
  for name in names do
    for axiomName in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
  logInfo m!"Audited {names.size} owned declarations: standard axioms only"
