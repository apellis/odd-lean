import OddMath.QuiverHecke.CyclotomicAction.ELVPowerWordWeightContexts
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
namespace NonVacuity.ELVPowerWordWeightContexts
private abbrev D := CyclotomicAction.AsymmetricParameters.datum
private abbrev originalSc := CyclotomicAction.AsymmetricParameters.scalars
private abbrev Sc := parameterTwist D originalSc
private def cutoff (_ : Bool) : ℕ := 20
private def L (_ : Bool × ℕ) : ℕ := 10
private abbrev N := PowerWordContent.powerBound D cutoff L
private abbrev Λ : Bool → ℤ := 0
private abbrev ν : List Bool := []
private abbrev η : List Bool := [false, true]
private abbrev ρ (i j : Bool) : List Bool := (ν ++ [j]) ++ [i]
private abbrev τ (i j : Bool) : List Bool := PowerWordContexts.extendedWord (ρ i j) η
private abbrev σ (i j : Bool) : List Bool := (τ i j).reverse
private abbrev C := OldCategory D Sc cutoff
private abbrev x₀ := PowerWordWeight.wordWeight D Λ ν
private abbrev h₁ (j : Bool) := PowerWordWeight.wordWeight_append D Λ ν j
private abbrev h₂ (i j : Bool) := PowerWordWeight.wordWeight_append D Λ (ν ++ [j]) i
private abbrev β := PowerWordWeight.wordBlock D Λ ν
private abbrev finalWeight (i j : Bool) :=
  PowerWordWeightContexts.contextWeight D (PowerWordWeight.wordWeight D Λ (ρ i j)) η
private def ε (i j : Bool) : WeightBlocks D Λ (finalWeight i j) :=
  ⟨τ i j, (PowerWordWeightContexts.context_weight_word D Λ (ρ i j) η
    (PowerWordWeight.wordWeight D Λ (ρ i j)) rfl).symm⟩
private theorem h₄ (i j : Bool) :
    (x₀ + D.α i) + D.α j = PowerWordWeight.wordWeight D Λ (ρ i j) := by
  calc
    (x₀ + D.α i) + D.α j = (x₀ + D.α j) + D.α i := by abel
    _ = PowerWordWeight.wordWeight D Λ (ν ++ [j]) + D.α i := congrArg (fun x => x + D.α i) (h₁ j)
    _ = PowerWordWeight.wordWeight D Λ (ρ i j) := h₂ i j
private abbrev M := PowerWordEvaluation.value D Sc cutoff L Λ ν
private def w (i j : Bool) : ContentCategory D Sc cutoff N (ε i j).1 := ⟨⟨τ i j⟩, rfl⟩
private abbrev nativeSource (i j : Bool) :=
  (PowerWordWeightContexts.contextFunctor D Sc cutoff L Λ (PowerWordWeight.wordWeight D Λ (ρ i j)) η).obj
    ((elvE D Sc cutoff N i Λ (h₂ i j)).obj ((elvE D Sc cutoff N j Λ (h₁ j)).obj M))
private abbrev targetWord (i j : Bool) := PowerWordContexts.extendedWord ((ν ++ [i]) ++ [j]) η
private def chosenPairIso (i j : Bool) :=
  PowerWordWeightContexts.contextChart D Sc cutoff L Λ (ρ i j) η
    (PowerWordWeight.wordWeight D Λ (ρ i j)) rfl
    (PowerWordEvaluation.pairChart D Sc cutoff L Λ ν i j (h₁ j) (h₂ i j))
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
    (fun _ => (by decide : 16 ≤ 20)) powers_high (by change 2 + 2 * (4 : ℕ).choose 2 < 16; decide)
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
    (f : nativeSource i j ⟶ PowerWordWeight.wordFamily D Sc cutoff L Λ (finalWeight i j) (targetWord i j)) :=
  (f (ε i j)).total (w i j) (chosenVector i j)

/-- Actual equal and distinct chosen crossings inside a two-E right context,
on nonzero literal FOUR-E vacuum inputs. -/
example := congrArg (evaluateSource false false)
  (PowerWordWeightContexts.cross_in_context D Sc cutoff L Λ ν η false false
    (h₁ false) (h₂ false false) rfl (h₄ false false))
example := congrArg (evaluateSource false true)
  (PowerWordWeightContexts.cross_in_context D Sc cutoff L Λ ν η false true
    (h₁ true) (h₂ false true) rfl (h₄ false true))
example : chosenVector false false ≠ 0 := chosenVector_ne_zero false false
example : chosenVector false true ≠ 0 := chosenVector_ne_zero false true
example (i j : Bool) (ε' : WeightBlocks D Λ (finalWeight i j))
    (z : ContentCategory D Sc cutoff N ε'.1) (v : ((nativeSource i j) ε').obj z) :=
  congrArg (fun f : nativeSource i j ⟶
      PowerWordWeight.wordFamily D Sc cutoff L Λ (finalWeight i j) (targetWord i j) => (f ε').total z v)
    (PowerWordWeightContexts.cross_in_context D Sc cutoff L Λ ν η i j (h₁ j) (h₂ i j) rfl (h₄ i j))

private abbrev s : List Bool := [false, true]
private abbrev t : List Bool := [true, false]
private theorem hst : (s : Multiset Bool) = (t : Multiset Bool) := by decide
/-- An arbitrary full coefficient tail on an arbitrary old arrow is retained
through the same chosen right-context functors. -/
example (a : SKM.SYM.ELVCoefficientAlgebra (k := ℚ) D cutoff)
    (g : (OldCategory.mk t : C) ⟶ OldCategory.mk s) :=
  PowerWordWeightContexts.context_family_arrow D Sc cutoff L Λ s t η
    (PowerWordWeight.wordWeight D Λ s) rfl (congrArg (blockWeight D Λ) hst) hst
    (coefficientEndomorphism D Sc cutoff t a ≫ g)

namespace Dot
private abbrev baseWord : List Bool := [false]
private abbrev τ : List Bool := PowerWordContexts.extendedWord baseWord η
private abbrev σ : List Bool := τ.reverse
private abbrev x := PowerWordWeight.wordWeight D Λ baseWord
private abbrev finalWeight := PowerWordWeightContexts.contextWeight D x η
private def δ : WeightBlocks D Λ finalWeight :=
  ⟨τ, (PowerWordWeightContexts.context_weight_word D Λ baseWord η x rfl).symm⟩
private def w : ContentCategory D Sc cutoff N δ.1 := ⟨⟨τ⟩, rfl⟩
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
private def occupied : ExtendedAtMost D originalSc σ σ 2 :=
  ⟨extensionBasis D originalSc σ σ (oddIndex, identityNF),
    Submodule.subset_span ⟨(oddIndex, identityNF), by decide, rfl⟩⟩
private def contentVector : (PowerWordWeight.wordAt D Sc cutoff L τ δ.1).obj w :=
  powerWordHalfTurnCoordinate D originalSc cutoff L σ σ occupied.val
private theorem contentVector_ne_zero : contentVector ≠ 0 := by
  intro hz
  have hh : occupied = (0 : ExtendedAtMost D originalSc σ σ 2) := by
    apply bounded_injective
    change powerWordHalfTurnCoordinate D originalSc cutoff L σ σ occupied.val =
      powerWordHalfTurnCoordinate D originalSc cutoff L σ σ 0
    exact hz.trans (map_zero _).symm
  exact (extensionBasis D originalSc σ σ).ne_zero (oddIndex, identityNF) (congrArg Subtype.val hh)
private def chosenChart := PowerWordWeightContexts.contextChart D Sc cutoff L Λ baseWord η x rfl
  (PowerWordEvaluation.appendChart D Sc cutoff L Λ ν false)
private abbrev chosenEquiv := moduleIsoLinearEquiv
  ((elvBlockEval D Sc cutoff N Λ δ).toFunctor.mapIso chosenChart) w
private def chosenVector := chosenEquiv.symm contentVector
example : chosenVector ≠ 0 := by
  intro hz
  apply contentVector_ne_zero
  have he := congrArg chosenEquiv hz
  simpa only [chosenVector, LinearEquiv.apply_symm_apply, map_zero] using he
private abbrev nativeSource := (PowerWordWeightContexts.contextFunctor D Sc cutoff L Λ x η).obj
  ((elvE D Sc cutoff N false Λ (PowerWordWeight.wordWeight_append D Λ ν false)).obj M)
/-- The chosen dot inside the same two-E right context on a nonzero
literal THREE-E value of the actual regular-power vacuum. -/
example := congrArg (fun f : nativeSource ⟶ PowerWordWeight.wordFamily D Sc cutoff L Λ finalWeight τ =>
  (f δ).total w chosenVector) (PowerWordWeightContexts.dot_in_context D Sc cutoff L Λ ν η false)
end Dot
end NonVacuity.ELVPowerWordWeightContexts
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let some idx := env.header.moduleNames.idxOf?
      `OddMath.QuiverHecke.CyclotomicAction.ELVPowerWordWeightContexts | throwError "Module not imported"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "No owned declarations"
  for name in names do
    for axiomName in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
  logInfo m!"Audited {names.size} owned declarations: standard axioms only"
