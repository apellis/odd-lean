import OddMath.QuiverHecke.CyclotomicAction.ELVPowerWordChartParity
import OddMath.QuiverHecke.HalfTurn.PowerWordCoordinates
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import OddMath.QuiverHecke.CyclotomicAction.ELVContentSingleLetterRelations
import Lean.Util.CollectAxioms

/-! Actual chosen weight dot in scheduled full-coefficient word coordinates on
an occupied three-strand A/T module with both odd coefficient colours. -/
noncomputable section
namespace NonVacuity.ELVPowerWordChartParity
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open CyclotomicCrossingTensor
open OddMath.QuiverHecke.CyclotomicAction
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

private abbrev N := PowerWordContent.powerBound D cutoff L
private abbrev Λ : Bool → ℤ := 0
private abbrev δ := blockSucc D Λ false (PowerWordWeight.wordWeight_append D Λ ν false)
  (PowerWordWeight.wordBlock D Λ ν)
private def w : ContentCategory D Sc cutoff N δ.1 := ⟨⟨τ⟩, by
  change ((ν ++ [false] : List Bool) : Multiset Bool) = {false} + (ν : Multiset Bool)
  rw [← Multiset.coe_add]
  exact add_comm _ _⟩

/-- Both original content and whole weight charts have their required even parity. -/
example := PowerWordChartParity.content_append_to_even D Sc cutoff L ν false
  (ν : Multiset Bool) δ.1 rfl
  (elvBlockSucc_content_eq D false Λ (PowerWordWeight.wordWeight_append D Λ ν false)
    (PowerWordWeight.wordBlock D Λ ν))
example := PowerWordChartParity.weight_append_even D Sc cutoff L ν false Λ

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
private theorem coordinate_ne_zero : (show target.obj (⟨τ⟩ : C) from
    powerWordHalfTurnCoordinate D originalSc cutoff L σ σ occupied.val) ≠ 0 := by
  intro hz
  have hh : occupied = (0 : ExtendedAtMost D originalSc σ σ 2) := by
    apply bounded_injective
    change powerWordHalfTurnCoordinate D originalSc cutoff L σ σ occupied.val =
      powerWordHalfTurnCoordinate D originalSc cutoff L σ σ 0
    exact hz.trans (map_zero _).symm
  exact (extensionBasis D originalSc σ σ).ne_zero (oddIndex, identityNF) (congrArg Subtype.val hh)

private def contentVector : (PowerWordWeight.wordAt D Sc cutoff L τ δ.1).obj w :=
  powerWordHalfTurnCoordinate D originalSc cutoff L σ σ occupied.val
private theorem contentVector_ne_zero : contentVector ≠ 0 := coordinate_ne_zero

private abbrev chosenEquiv := moduleIsoLinearEquiv
  (PowerWordWeight.weightAppendComponentIso D Sc cutoff L Λ ν false) w
private def chosenVector := chosenEquiv.symm contentVector

/-- A nonzero vector in the independently chosen original-weight E component itself,
transported through the prescribed comparison, not a zero formal module. -/
example : chosenVector ≠ 0 := by
  intro hz
  apply contentVector_ne_zero
  have he := congrArg chosenEquiv hz
  simpa only [chosenVector, LinearEquiv.apply_symm_apply, map_zero] using he

private abbrev chosenChart := (PowerWordWeight.weightAppendIso D Sc cutoff L Λ ν false).hom δ
/-- The odd component vanishes on a proved nonzero actual E input carrying
both exterior coefficient colours. -/
example : chosenChart.app 1 w chosenVector = 0 := by
  have he := PowerWordChartParity.weight_append_even D Sc cutoff L ν false Λ δ
  rw [Superfunctor.app_eq_zero_of_mem he (by decide : (1 : ZMod 2) ≠ 0) w]
  rfl
/-- No restriction on the parity or coefficient tail of the input is used. -/
example (v : (((elvE D Sc cutoff N false Λ (PowerWordWeight.wordWeight_append D Λ ν false)).obj
    (PowerWordWeight.wordFamily D Sc cutoff L Λ (PowerWordWeight.wordWeight D Λ ν) ν)) δ).obj w) :
    chosenChart.app 1 w v = 0 := by
  have he := PowerWordChartParity.weight_append_even D Sc cutoff L ν false Λ δ
  rw [Superfunctor.app_eq_zero_of_mem he (by decide : (1 : ZMod 2) ≠ 0) w]
  rfl

end NonVacuity.ELVPowerWordChartParity
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let some idx := env.header.moduleNames.idxOf?
      `OddMath.QuiverHecke.CyclotomicAction.ELVPowerWordChartParity | throwError "Module not imported"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "No owned declarations"
  for name in names do
    for axiomName in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
  logInfo m!"Audited {names.size} owned declarations: standard axioms only"
