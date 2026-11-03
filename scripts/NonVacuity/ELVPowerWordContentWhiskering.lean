import OddMath.QuiverHecke.CyclotomicAction.ELVPowerWordContentWhiskering
import OddMath.QuiverHecke.HalfTurn.PowerWordCoordinates
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import OddMath.QuiverHecke.CyclotomicAction.ELVContentSingleLetterRelations
import Lean.Util.CollectAxioms

/-! Selected append unit tails on
an occupied three-strand A/T module with both odd coefficient colours. -/
noncomputable section
namespace NonVacuity.ELVPowerWordContentWhiskering
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

private def sourceIso := PowerWordWeight.contentAppendIsoTo D Sc cutoff L ν false
  (ν : Multiset Bool) (τ : Multiset Bool) rfl (Multiset.coe_add ν [false])
private abbrev source := BalancedInduction.induced
  (contentAppendTo D Sc cutoff N (ν : Multiset Bool) [false] (τ : Multiset Bool)
    (Multiset.coe_add ν [false])) (PowerWordWeight.wordAt D Sc cutoff L ν (ν : Multiset Bool))
private def chosenVector : source.obj w := (moduleIsoLinearEquiv sourceIso w).symm contentVector
private theorem chosenVector_ne_zero : chosenVector ≠ 0 := by
  intro hz
  apply contentVector_ne_zero
  have hh := congrArg (moduleIsoLinearEquiv sourceIso w) hz
  simpa only [chosenVector, LinearEquiv.apply_symm_apply, map_zero] using hh

/-- Every coefficient, including inhomogeneous tails, is passed through the
chosen append comparison on an occupied input. -/
example (a : SKM.SYM.ELVCoefficientAlgebra (k := ℚ) D cutoff) :=
  congrArg (fun f : source ⟶ PowerWordWeight.wordAt D Sc cutoff L τ (τ : Multiset Bool) =>
    f.total w chosenVector)
    (PowerWordContentWhiskering.append_word_arrow D Sc cutoff L ν ν false
      (ν : Multiset Bool) (τ : Multiset Bool) rfl rfl (Multiset.coe_add ν [false])
      (coefficientEndomorphism D Sc cutoff ν a))
example : chosenVector ≠ 0 := chosenVector_ne_zero

private abbrev κ : List Bool := [true, false]
private theorem hκ : (κ : Multiset Bool) = (ν : Multiset Bool) := by decide
/-- A full coefficient tail on an arbitrary arrow between different word orders. -/
example (a : SKM.SYM.ELVCoefficientAlgebra (k := ℚ) D cutoff)
    (h : (OldCategory.mk κ : OldCategory D Sc cutoff) ⟶ OldCategory.mk ν) :=
  congrArg (fun f : source ⟶ PowerWordWeight.wordAt D Sc cutoff L (κ ++ [false]) (τ : Multiset Bool) =>
    f.total w chosenVector)
    (PowerWordContentWhiskering.append_word_arrow D Sc cutoff L ν κ false
      (ν : Multiset Bool) (τ : Multiset Bool) rfl hκ (Multiset.coe_add ν [false])
      (coefficientEndomorphism D Sc cutoff κ a ≫ h))

end NonVacuity.ELVPowerWordContentWhiskering
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let some idx := env.header.moduleNames.idxOf?
      `OddMath.QuiverHecke.CyclotomicAction.ELVPowerWordContentWhiskering | throwError "Module not imported"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "No owned declarations"
  for name in names do
    for axiomName in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
  logInfo m!"Audited {names.size} owned declarations: standard axioms only"
