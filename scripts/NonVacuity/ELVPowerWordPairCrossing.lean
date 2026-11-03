import OddMath.QuiverHecke.CyclotomicAction.ELVPowerWordPairCrossing
import OddMath.QuiverHecke.HalfTurn.PowerWordCoordinates
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

/-! Exact selected pair comparison and the signed equal-colour crossing on
an occupied actual four-strand A/T module with both odd coefficient colours. -/
noncomputable section
namespace NonVacuity.ELVPowerWordPairCrossing
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open CyclotomicCrossingTensor
private abbrev D := CyclotomicAction.AsymmetricParameters.datum
private abbrev originalSc := CyclotomicAction.AsymmetricParameters.scalars
private abbrev Sc := parameterTwist D originalSc
private def cutoff (_ : Bool) : ℕ := 20
private def L (_ : Bool × ℕ) : ℕ := 10
private abbrev ν : List Bool := [false, true]
private abbrev τ : List Bool := ν ++ [false] ++ [false]
private abbrev σ : List Bool := τ.reverse
private abbrev C := OldCategory D Sc cutoff
private abbrev target := powerWordModule D Sc cutoff L τ
private abbrev native := PowerWordPair.nativeCross D Sc cutoff L ν false

/-- Both single comparisons are the original selected comparisons. -/
example := PowerWordPair.selectedAppend_eq D Sc cutoff L ν false
example := PowerWordPair.selectedAppend_eq D Sc cutoff L (ν ++ [false]) false
example := PowerWordPair.selectedPair_hom_eq D Sc cutoff L ν false
example := PowerWordPair.collapsed_cross D Sc cutoff L ν false
example := PowerWordPair.selected_signed_cross D Sc cutoff L ν false

/-- The native map is literally the full old-Hom chart. -/
example : native = PowerWordMorphisms.fromArrow D Sc cutoff L τ τ
    (equalCrossComponent D Sc cutoff false (⟨ν⟩ : C)) :=
  PowerWordPair.nativeCross_eq_fromArrow D Sc cutoff L ν false

/-- The literal crossing has the required odd parity. -/
example : proj ℚ 1 (equalCrossComponent D Sc cutoff false (⟨ν⟩ : C)) =
    equalCrossComponent D Sc cutoff false (⟨ν⟩ : C) :=
  proj_of_mem ((equalCross_supernatural D Sc cutoff false).mem (⟨ν⟩ : C))

/-- The native chart just identified above retains arbitrary full
coefficients INSIDE the total parity twist, including both exterior colours. -/
example (w : C) (h : (⟨τ⟩ : C) ⟶ w)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := ℚ) D cutoff) :=
  PowerWordMorphisms.fromArrow_generator D Sc cutoff L τ τ
    (equalCrossComponent D Sc cutoff false (⟨ν⟩ : C)) 1 w
    (coefficientEndomorphism D Sc cutoff τ a ≫ h)

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

/-- The SAME actual target of the selected signed-crossing square contains
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

end NonVacuity.ELVPowerWordPairCrossing
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let some idx := env.header.moduleNames.idxOf?
      `OddMath.QuiverHecke.CyclotomicAction.ELVPowerWordPairCrossing | throwError "Module not imported"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "No owned declarations"
  for name in names do
    for axiomName in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
  logInfo m!"Audited {names.size} owned declarations: standard axioms only"
