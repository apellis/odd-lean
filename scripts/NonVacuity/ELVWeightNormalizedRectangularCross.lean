import OddMath.QuiverHecke.CyclotomicAction.ELVWeightNormalizedRectangularCross
import OddMath.QuiverHecke.CyclotomicAction.ELVPowerWordWeight
import OddMath.QuiverHecke.HalfTurn.PowerWordCoordinates
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

/-! The existing chosen weight crossing, equal and distinct, on nonzero vectors
in its actual two-E source. Both independent odd coefficient colours survive. -/
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath
open OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction
namespace NonVacuity.ELVWeightNormalizedRectangularCross
private abbrev D := CyclotomicAction.AsymmetricParameters.datum
private abbrev originalSc := CyclotomicAction.AsymmetricParameters.scalars
private abbrev Sc := parameterTwist D originalSc
private def cutoff (_ : Bool) : ℕ := 20
private def L (_ : Bool × ℕ) : ℕ := 10
private abbrev N := PowerWordContent.powerBound D cutoff L
private abbrev Λ : Bool → ℤ := 0
private abbrev τ (i j : Bool) : List Bool := [j,i]
private abbrev σ (i j : Bool) : List Bool := (τ i j).reverse
private abbrev C := OldCategory D Sc cutoff
private abbrev x₀ := PowerWordWeight.wordWeight D Λ []
private abbrev h₁ (j : Bool) := PowerWordWeight.wordWeight_append D Λ [] j
private abbrev h₂ (i j : Bool) := PowerWordWeight.wordWeight_append D Λ [j] i
private abbrev β := PowerWordWeight.wordBlock D Λ []
private abbrev ε (i j : Bool) := blockSucc₂ D i j Λ (h₁ j) (h₂ i j) β
private theorem h₄ (i j : Bool) :
    (x₀ + D.α i) + D.α j = PowerWordWeight.wordWeight D Λ (τ i j) := by
  calc
    (x₀ + D.α i) + D.α j = (x₀ + D.α j) + D.α i := by abel
    _ = PowerWordWeight.wordWeight D Λ [j] + D.α i := congrArg (fun x => x + D.α i) (h₁ j)
    _ = PowerWordWeight.wordWeight D Λ (τ i j) := h₂ i j
private abbrev M := PowerWordWeight.wordFamily D Sc cutoff L Λ x₀ []
private def w (i j : Bool) : ContentCategory D Sc cutoff N (ε i j).1 := ⟨⟨τ i j⟩, by
  change (([j,i] : List Bool) : Multiset Bool) = (([i,j] : List Bool) : Multiset Bool)
  exact Multiset.coe_eq_coe.mpr (List.Perm.swap i j [])⟩

private def chosenPairIso (i j : Bool) :=
  (elvEFunctor D Sc cutoff N i Λ (h₂ i j)).mapIso
      (PowerWordWeight.weightAppendIso D Sc cutoff L Λ [] j) ≪≫
    PowerWordWeight.weightAppendIso D Sc cutoff L Λ [j] i
private def componentIso (i j : Bool) :=
  (elvBlockEval D Sc cutoff N Λ (ε i j)).toFunctor.mapIso (chosenPairIso i j)
private abbrev chosenEquiv (i j : Bool) := moduleIsoLinearEquiv (componentIso i j) (w i j)

private theorem powers_high (q : Bool × ℕ) : 16 ≤ L q * SKM.SYM.elementaryWeight D q := by
  change 16 ≤ 10 * (2 * (q.2 + 1))
  omega
private theorem bounded_injective (i j : Bool) :
    Function.Injective (fun x : ExtendedAtMost D originalSc (σ i j) (σ i j) 2 =>
      powerWordHalfTurnCoordinate D originalSc cutoff L (σ i j) (σ i j) x.val) :=
  powerWordHalfTurnCoordinate_injective_on_extendedAtMost D originalSc cutoff L
    (fun _ => (by decide : 16 ≤ 20)) powers_high (by change 2 + 2 * (2 : ℕ).choose 2 < 16; decide)
private def identityNF (i j : Bool) : NFIdx (σ i j) (σ i j) := by
  have hc : Categorification.TypeA.canWord (σ i j).length (1 : Equiv.Perm (Fin (σ i j).length)) = [] := by
    apply List.length_eq_zero_iff.mp
    rw [Categorification.TypeA.length_canWord, Categorification.TypeA.length_one]
  refine ⟨([], 1), by simp, by simp, ?_⟩
  simp only [List.map_nil, hc, cw, List.reverse_nil, List.nil_append, pl, SChain]
private def oddIndex : SKM.SYM.CoefficientIndex D := (0, {⟨false, rfl⟩, ⟨true, rfl⟩})
private def occupied (i j : Bool) : ExtendedAtMost D originalSc (σ i j) (σ i j) 2 :=
  ⟨extensionBasis D originalSc (σ i j) (σ i j) (oddIndex, identityNF i j),
    Submodule.subset_span ⟨(oddIndex, identityNF i j), by cases i <;> cases j <;> decide, rfl⟩⟩
private def contentVector (i j : Bool) :
    (PowerWordWeight.wordAt D Sc cutoff L (τ i j) (ε i j).1).obj (w i j) :=
  powerWordHalfTurnCoordinate D originalSc cutoff L (σ i j) (σ i j) (occupied i j).val
private theorem contentVector_ne_zero (i j : Bool) : contentVector i j ≠ 0 := by
  intro hz
  have hh : occupied i j = (0 : ExtendedAtMost D originalSc (σ i j) (σ i j) 2) := by
    apply bounded_injective i j
    change powerWordHalfTurnCoordinate D originalSc cutoff L (σ i j) (σ i j) (occupied i j).val =
      powerWordHalfTurnCoordinate D originalSc cutoff L (σ i j) (σ i j) 0
    exact hz.trans (map_zero _).symm
  exact (extensionBasis D originalSc (σ i j) (σ i j)).ne_zero (oddIndex, identityNF i j)
    (congrArg Subtype.val hh)
private def chosenVector (i j : Bool) := (chosenEquiv i j).symm (contentVector i j)
private theorem chosenVector_ne_zero (i j : Bool) : chosenVector i j ≠ 0 := by
  intro hz
  apply contentVector_ne_zero i j
  have he := congrArg (chosenEquiv i j) hz
  simpa only [chosenVector, LinearEquiv.apply_symm_apply, map_zero] using he

private def evaluateSource (i j : Bool)
    (f : (elvEFunctor D Sc cutoff N j Λ (h₁ j) ⋙
        (elvInductionComponent D Sc cutoff N i Λ (h₂ i j) (ε i j)).toFunctor).obj M ⟶
      (elvEFunctor D Sc cutoff N i Λ (by rfl : x₀ + D.α i = x₀ + D.α i) ⋙
        (elvInductionComponent D Sc cutoff N j Λ (h₄ i j) (ε i j)).toFunctor).obj M) :=
  f.total (w i j) (chosenVector i j)

/-- Actual chosen equal-colour field on a surviving two-odd-coefficient source vector. -/
example := congrArg (evaluateSource false false)
  (elvWeightCrossVia_normalized_rectangular D Sc cutoff N false false Λ
    (h₁ false) (h₂ false false) β (ε false false) rfl rfl (h₄ false false) M)
/-- Actual chosen distinct-colour field, with its positive normalization. -/
example := congrArg (evaluateSource false true)
  (elvWeightCrossVia_normalized_rectangular D Sc cutoff N false true Λ
    (h₁ true) (h₂ false true) β (ε false true) rfl rfl (h₄ false true) M)
example : chosenVector false false ≠ 0 := chosenVector_ne_zero false false
example : chosenVector false true ≠ 0 := chosenVector_ne_zero false true
end NonVacuity.ELVWeightNormalizedRectangularCross
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for mod in #[`OddMath.QuiverHecke.CyclotomicAction.ELVNormalizedContentRectangularCross,
      `OddMath.QuiverHecke.CyclotomicAction.ELVWeightNormalizedRectangularCross] do
    let some idx := env.header.moduleNames.idxOf? mod | throwError "Module not imported: {mod}"
    let names := env.header.moduleData[idx]!.constNames
    if names.isEmpty then throwError "No owned declarations"
    for name in names do
      for axiomName in ← Lean.collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
          throwError "Disallowed axiom {axiomName} in {name}"
    logInfo m!"Audited {names.size} owned declarations in {mod}: standard axioms only"
