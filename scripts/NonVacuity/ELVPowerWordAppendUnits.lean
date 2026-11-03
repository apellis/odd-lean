import OddMath.QuiverHecke.CyclotomicAction.ELVPowerWordAppendUnits
import OddMath.QuiverHecke.HalfTurn.PowerWordCoordinates
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import OddMath.QuiverHecke.CyclotomicAction.ELVContentSingleLetterRelations
import Lean.Util.CollectAxioms

/-! Selected append unit tails on
an occupied three-strand A/T module with both odd coefficient colours. -/
noncomputable section
namespace NonVacuity.ELVPowerWordAppendUnits
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

private abbrev N := PowerWordContent.powerBound D cutoff L
private def w : ContentCategory D Sc cutoff N (τ : Multiset Bool) := ⟨⟨τ⟩, rfl⟩

/-- Arbitrary full coefficient arrows are retained in both chosen comparisons. -/
example (a : SKM.SYM.ELVCoefficientAlgebra (k := ℚ) D cutoff) :=
  PowerWordAppendUnits.weighted_append_tensor_unit D Sc cutoff L ν false (⟨τ⟩ : C)
    (coefficientEndomorphism D Sc cutoff τ a)
example (a : SKM.SYM.ELVCoefficientAlgebra (k := ℚ) D cutoff) :=
  PowerWordAppendUnits.content_append_tensor_unit D Sc cutoff L ν false w
    (coefficientEndomorphism D Sc cutoff τ a)

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

private def contentVector : (PowerWordContent.contentWord D Sc cutoff L τ).obj w :=
  powerWordHalfTurnCoordinate D originalSc cutoff L σ σ occupied.val
private theorem contentVector_ne_zero : contentVector ≠ 0 := coordinate_ne_zero

private def tailArrow : (⟨τ⟩ : C) ⟶ (⟨τ⟩ : C) :=
  halfTurnOldHom D originalSc cutoff σ σ occupied.val

private def chosenUnitTensor :
    BalancedInduction.Obj
      (contentAppendTo D Sc cutoff N (ν : Multiset Bool) [false] (τ : Multiset Bool)
        (Multiset.coe_add ν [false]))
      (PowerWordContent.contentWord D Sc cutoff L ν).toFunctor w :=
  BalancedInduction.tensor
    (contentAppendTo D Sc cutoff N (ν : Multiset Bool) [false] (τ : Multiset Bool)
      (Multiset.coe_add ν [false]))
    (PowerWordContent.contentWord D Sc cutoff L ν).toFunctor
    (PowerWordContentCyclicity.wordObject D Sc cutoff L ν (ν : Multiset Bool) rfl)
    (truncateOld D Sc cutoff N τ τ tailArrow)
    (PowerWordContentCyclicity.wordUnit D Sc cutoff L ν (ν : Multiset Bool) rfl)

private theorem chosenUnitTensor_image :
    (PowerWordContent.contentAppendIso D Sc cutoff L ν false).hom.total w chosenUnitTensor =
      contentVector := by
  have hh := PowerWordAppendUnits.content_append_tensor_unit D Sc cutoff L ν false w tailArrow
  have hc := LinearMap.congr_fun (powerWordHalfTurnCoordinate_eq D originalSc cutoff L σ σ) occupied.val
  convert hh.trans hc.symm using 1
  · apply congrArg ((PowerWordContent.contentAppendIso D Sc cutoff L ν false).hom.total w)
    rfl
  · rfl

/-- The actual chosen input tensor is nonzero, since its comparison image
is the independently surviving two-colour exterior coefficient vector. -/
example : chosenUnitTensor ≠ 0 := by
  intro hz
  apply contentVector_ne_zero
  rw [← chosenUnitTensor_image, hz, map_zero]

example :
    (PowerWordContent.contentAppendIso D Sc cutoff L ν false).hom.total w chosenUnitTensor =
      contentVector := chosenUnitTensor_image

end NonVacuity.ELVPowerWordAppendUnits
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let some idx := env.header.moduleNames.idxOf?
      `OddMath.QuiverHecke.CyclotomicAction.ELVPowerWordAppendUnits | throwError "Module not imported"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "No owned declarations"
  for name in names do
    for axiomName in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
  logInfo m!"Audited {names.size} owned declarations: standard axioms only"
