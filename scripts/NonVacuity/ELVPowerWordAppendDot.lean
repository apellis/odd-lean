import OddMath.QuiverHecke.CyclotomicAction.ELVPowerWordAppendDot
import OddMath.QuiverHecke.HalfTurn.PowerWordCoordinates
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

/-! Selected word append and actual odd-dot square with arbitrary coefficient
vectors, on an occupied three-strand all-odd regular-power module. -/
noncomputable section
namespace NonVacuity.ELVPowerWordAppendDot
open CategoryTheory StringDiagrams OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open CyclotomicCrossingTensor
private abbrev D := CyclotomicAction.AsymmetricParameters.datum
private abbrev originalSc := CyclotomicAction.AsymmetricParameters.scalars
private abbrev Sc := parameterTwist D originalSc
private def cutoff (_ : Bool) : ℕ := 12
private def L (_ : Bool × ℕ) : ℕ := 6
private def ν : List Bool := [false, true]
private abbrev C := OldCategory D Sc cutoff

/-- The map in the square is literally the selected isomorphism's total. -/
example (w : C) : PowerWordAppend.appendLinear D Sc cutoff L ν false w =
    (powerWordAppendIso D Sc cutoff L ν false).hom.total w := rfl

example (w : C) :
    PowerWordAppend.appendLinear D Sc cutoff L ν false w ∘ₗ
      actualInductionDot D Sc cutoff false (powerWordModule D Sc cutoff L ν) w =
    (PowerWordAppend.nativeDot D Sc cutoff L ν false).app 1 w ∘ₗ
      PowerWordAppend.appendLinear D Sc cutoff L ν false w :=
  PowerWordAppend.appendLinear_dot D Sc cutoff L ν false w

example (s w : C) (g : (append D Sc cutoff false).obj s ⟶ w)
    (h : (OldCategory.mk ν : C) ⟶ s)
    (a : CoefficientPowerQuotient (k := ℚ) D cutoff L) :=
  PowerWordAppend.appendLinear_dot_tensor D Sc cutoff L ν false s w g h a

/-- The square also retains an inhomogeneous vector containing both odd
coefficient colours and the regular quotient unit. -/
example (s w : C) (g : (append D Sc cutoff false).obj s ⟶ w)
    (h : (OldCategory.mk ν : C) ⟶ s) :=
  PowerWordAppend.appendLinear_dot_tensor D Sc cutoff L ν false s w g h
    (coefficientPowerQuotientMap (k := ℚ) D cutoff L (SKM.SYM.delta D ℚ ⟨false, rfl⟩) +
      coefficientPowerQuotientMap (k := ℚ) D cutoff L (SKM.SYM.delta D ℚ ⟨true, rfl⟩) + 1)

private def τ : List Bool := [false, true, false]
private theorem powers_high (j : Bool × ℕ) : 10 ≤ L j * SKM.SYM.elementaryWeight D j := by
  change 10 ≤ 6 * (2 * (j.2 + 1))
  omega
private theorem bounded_injective :
    Function.Injective (fun x : ExtendedAtMost D originalSc τ τ 2 =>
      powerWordHalfTurnCoordinate D originalSc cutoff L τ τ x.val) :=
  powerWordHalfTurnCoordinate_injective_on_extendedAtMost D originalSc cutoff L
    (fun _ => (by decide : 10 ≤ 12)) powers_high (by decide)
private def identityNF : NFIdx τ τ := by
  have hc : Categorification.TypeA.canWord τ.length (1 : Equiv.Perm (Fin τ.length)) = [] := by
    apply List.length_eq_zero_iff.mp
    rw [Categorification.TypeA.length_canWord, Categorification.TypeA.length_one]
  refine ⟨([], 1), by simp, by simp, ?_⟩
  simp only [List.map_nil, hc, cw, List.reverse_nil, List.nil_append, pl, SChain]
private def oddIndex : SKM.SYM.CoefficientIndex D := (0, {⟨false, rfl⟩, ⟨true, rfl⟩})
private def occupied : ExtendedAtMost D originalSc τ τ 2 :=
  ⟨extensionBasis D originalSc τ τ (oddIndex, identityNF),
    Submodule.subset_span ⟨(oddIndex, identityNF), by decide, rfl⟩⟩

/-- A two-colour exterior coordinate survives in the SAME actual next-word
module on which the selected odd-dot square was tested. -/
example : (show (powerWordModule D Sc cutoff L (ν ++ [false])).obj
    (⟨ν ++ [false]⟩ : C) from
      powerWordHalfTurnCoordinate D originalSc cutoff L τ τ occupied.val) ≠ 0 := by
  intro hz
  have hh : occupied = (0 : ExtendedAtMost D originalSc τ τ 2) := by
    apply bounded_injective
    change powerWordHalfTurnCoordinate D originalSc cutoff L τ τ occupied.val =
      powerWordHalfTurnCoordinate D originalSc cutoff L τ τ 0
    exact hz.trans (map_zero _).symm
  exact (extensionBasis D originalSc τ τ).ne_zero (oddIndex, identityNF) (congrArg Subtype.val hh)

end NonVacuity.ELVPowerWordAppendDot
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let some idx := env.header.moduleNames.idxOf?
      `OddMath.QuiverHecke.CyclotomicAction.ELVPowerWordAppendDot | throwError "Module not imported"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "No owned declarations"
  for name in names do
    for axiomName in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
  logInfo m!"Audited {names.size} owned declarations: standard axioms only"
