import OddMath.QuiverHecke.CyclotomicAction.ELVPowerWordEvaluation
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
namespace NonVacuity.ELVPowerWordEvaluation
private abbrev D := CyclotomicAction.AsymmetricParameters.datum
private abbrev originalSc := CyclotomicAction.AsymmetricParameters.scalars
private abbrev Sc := parameterTwist D originalSc
private def cutoff (_ : Bool) : ℕ := 20
private def L (_ : Bool × ℕ) : ℕ := 10
private abbrev N := PowerWordContent.powerBound D cutoff L
private abbrev Λ : Bool → ℤ := 0
private abbrev ν : List Bool := [false, true]
private abbrev τ (i j : Bool) : List Bool := (ν ++ [j]) ++ [i]
private abbrev σ (i j : Bool) : List Bool := (τ i j).reverse
private abbrev C := OldCategory D Sc cutoff
private abbrev x₀ := PowerWordWeight.wordWeight D Λ ν
private abbrev h₁ (j : Bool) := PowerWordWeight.wordWeight_append D Λ ν j
private abbrev h₂ (i j : Bool) := PowerWordWeight.wordWeight_append D Λ (ν ++ [j]) i
private abbrev β := PowerWordWeight.wordBlock D Λ ν
private abbrev ε (i j : Bool) := blockSucc₂ D i j Λ (h₁ j) (h₂ i j) β
private theorem h₄ (i j : Bool) :
    (x₀ + D.α i) + D.α j = PowerWordWeight.wordWeight D Λ (τ i j) := by
  calc
    (x₀ + D.α i) + D.α j = (x₀ + D.α j) + D.α i := by abel
    _ = PowerWordWeight.wordWeight D Λ (ν ++ [j]) + D.α i := congrArg (fun x => x + D.α i) (h₁ j)
    _ = PowerWordWeight.wordWeight D Λ (τ i j) := h₂ i j
private abbrev M := PowerWordEvaluation.value D Sc cutoff L Λ ν
private def w (i j : Bool) : ContentCategory D Sc cutoff N (ε i j).1 := ⟨⟨τ i j⟩, by
  change (((ν ++ [j]) ++ [i] : List Bool) : Multiset Bool) = {i} + ({j} + (ν : Multiset Bool))
  rw [← Multiset.coe_add, ← Multiset.coe_add]
  ac_rfl⟩
private def chosenPairIso (i j : Bool) :=
  PowerWordEvaluation.pairChart D Sc cutoff L Λ ν i j (h₁ j) (h₂ i j)
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
    (f : (elvE D Sc cutoff N i Λ (h₂ i j)).obj
        ((elvE D Sc cutoff N j Λ (h₁ j)).obj M) ⟶
      PowerWordWeight.wordFamily D Sc cutoff L Λ
        (PowerWordWeight.wordWeight D Λ (τ i j)) ((ν ++ [i]) ++ [j])) :=
  (f (ε i j)).total (w i j) (chosenVector i j)

/-- The whole chosen equal-colour field on a surviving exterior input. -/
example := congrArg (evaluateSource false false)
  (PowerWordEvaluation.cross_pair_value D Sc cutoff L Λ ν false false
    (h₁ false) (h₂ false false) rfl (h₄ false false))
/-- The whole chosen distinct-colour field, with its positive normalization. -/
example := congrArg (evaluateSource false true)
  (PowerWordEvaluation.cross_pair_value D Sc cutoff L Λ ν false true
    (h₁ true) (h₂ false true) rfl (h₄ false true))
example : chosenVector false false ≠ 0 := chosenVector_ne_zero false false
example : chosenVector false true ≠ 0 := chosenVector_ne_zero false true
/-- Every full coefficient vector is covered, rather than only a chosen basis vector. -/
example (i j : Bool) (ε' : WeightBlocks D Λ (PowerWordWeight.wordWeight D Λ (τ i j)))
    (z : ContentCategory D Sc cutoff N ε'.1)
    (v : (((elvE D Sc cutoff N i Λ (h₂ i j)).obj
      ((elvE D Sc cutoff N j Λ (h₁ j)).obj M)) ε').obj z) :=
  congrArg (fun f : (elvE D Sc cutoff N i Λ (h₂ i j)).obj
      ((elvE D Sc cutoff N j Λ (h₁ j)).obj M) ⟶
      PowerWordWeight.wordFamily D Sc cutoff L Λ
        (PowerWordWeight.wordWeight D Λ (τ i j)) ((ν ++ [i]) ++ [j]) => (f ε').total z v)
    (PowerWordEvaluation.cross_pair_value D Sc cutoff L Λ ν i j
      (h₁ j) (h₂ i j) rfl (h₄ i j))
example := PowerWordEvaluation.dot_append_value D Sc cutoff L Λ ν false
example := PowerWordEvaluation.chart_even D Sc cutoff L Λ ν

namespace Dot
private abbrev τ : List Bool := ν ++ [false]
private abbrev σ : List Bool := τ.reverse
private abbrev C := OldCategory D Sc cutoff
private abbrev target := powerWordModule D Sc cutoff L τ
private abbrev δ := blockSucc D Λ false (PowerWordWeight.wordWeight_append D Λ ν false)
  (PowerWordWeight.wordBlock D Λ ν)
private def w : ContentCategory D Sc cutoff N δ.1 := ⟨⟨τ⟩, by
  change ((ν ++ [false] : List Bool) : Multiset Bool) = {false} + (ν : Multiset Bool)
  rw [← Multiset.coe_add]
  exact add_comm _ _⟩
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
private abbrev chosenEquiv := moduleIsoLinearEquiv
  ((elvBlockEval D Sc cutoff N Λ δ).toFunctor.mapIso
    (PowerWordEvaluation.appendChart D Sc cutoff L Λ ν false)) w
private def chosenVector := chosenEquiv.symm contentVector
/-- The chosen dot is tested on a nonzero literal THREE-E value of the vacuum. -/
example : chosenVector ≠ 0 := by
  intro hz
  apply contentVector_ne_zero
  have he := congrArg chosenEquiv hz
  simpa only [chosenVector, LinearEquiv.apply_symm_apply, map_zero] using he
example := congrArg (fun f : (elvE D Sc cutoff N false Λ
    (PowerWordWeight.wordWeight_append D Λ ν false)).obj M ⟶
    PowerWordWeight.wordFamily D Sc cutoff L Λ (PowerWordWeight.wordWeight D Λ τ) τ =>
      (f δ).total w chosenVector) (PowerWordEvaluation.dot_append_value D Sc cutoff L Λ ν false)
end Dot

end NonVacuity.ELVPowerWordEvaluation
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for mod in #[`OddMath.QuiverHecke.CyclotomicAction.ELVPowerWordEvaluation] do
    let some idx := env.header.moduleNames.idxOf? mod | throwError "Module not imported: {mod}"
    let names := env.header.moduleData[idx]!.constNames
    if names.isEmpty then throwError "No owned declarations"
    for name in names do
      for axiomName in ← Lean.collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
          throwError "Disallowed axiom {axiomName} in {name}"
    logInfo m!"Audited {names.size} owned declarations in {mod}: standard axioms only"
