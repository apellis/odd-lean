import OddMath.QuiverHecke.CyclotomicAction.ELVPowerWordContentCross
import OddMath.QuiverHecke.HalfTurn.PowerWordCoordinates
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

/-! Chosen content crossings on occupied equal- and distinct-colour pairs,
retaining arbitrary full coefficient arrows. -/
noncomputable section
namespace NonVacuity.ELVPowerWordContentCross
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open CyclotomicCrossingTensor
private abbrev D := CyclotomicAction.AsymmetricParameters.datum
private abbrev originalSc := CyclotomicAction.AsymmetricParameters.scalars
private abbrev Sc := parameterTwist D originalSc
private def cutoff (_ : Bool) : ℕ := 20
private def L (_ : Bool × ℕ) : ℕ := 10
private abbrev N := PowerWordContent.powerBound D cutoff L
private abbrev ν : List Bool := [false, true]
private abbrev ρ (i j : Bool) : List Bool := (ν ++ [j]) ++ [i]
private abbrev τ (i j : Bool) : List Bool := (ν ++ [i]) ++ [j]
private abbrev σ (i j : Bool) : List Bool := (ρ i j).reverse
private abbrev β : Multiset Bool := ν
private abbrev δ (i : Bool) : Multiset Bool := ([i] : Multiset Bool) + β
private abbrev γ (i j : Bool) : Multiset Bool := ρ i j
private theorem hj (j : Bool) : β + ([j] : Multiset Bool) = δ j := add_comm _ _
private theorem hSource (i j : Bool) : δ j + ([i] : Multiset Bool) = γ i j := by
  change ([j] : Multiset Bool) + (ν : Multiset Bool) + [i] = ((ν ++ [j]) ++ [i] : List Bool)
  rw [← Multiset.coe_add, ← Multiset.coe_add]
  ac_rfl
private theorem hTarget (i j : Bool) : δ i + ([j] : Multiset Bool) = γ i j := by
  change ([i] : Multiset Bool) + (ν : Multiset Bool) + [j] = ((ν ++ [j]) ++ [i] : List Bool)
  rw [← Multiset.coe_add, ← Multiset.coe_add]
  ac_rfl
private def sourceIso (i j : Bool) :=
  PowerWordContentCross.pairIsoTo D Sc cutoff L ν i j β (δ j) (γ i j) rfl (hj j) (hSource i j)
private abbrev sourceModule (i j : Bool) :=
  BalancedInduction.induced (contentAppendTo D Sc cutoff N (δ j) [i] (γ i j) (hSource i j))
    (BalancedInduction.induced (contentAppendTo D Sc cutoff N β [j] (δ j) (hj j))
      (PowerWordWeight.wordAt D Sc cutoff L ν β))
private abbrev targetModule (i j : Bool) := PowerWordWeight.wordAt D Sc cutoff L (τ i j) (γ i j)
private def w (i j : Bool) : ContentCategory D Sc cutoff N (γ i j) := ⟨⟨ρ i j⟩, rfl⟩

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
    (PowerWordWeight.wordAt D Sc cutoff L (ρ i j) (γ i j)).obj (w i j) :=
  powerWordHalfTurnCoordinate D originalSc cutoff L (σ i j) (σ i j) (occupied i j).val
private theorem contentVector_ne_zero (i j : Bool) : contentVector i j ≠ 0 := by
  intro hz
  have hh : occupied i j = (0 : ExtendedAtMost D originalSc (σ i j) (σ i j) 2) := by
    apply bounded_injective i j
    change powerWordHalfTurnCoordinate D originalSc cutoff L (σ i j) (σ i j) (occupied i j).val =
      powerWordHalfTurnCoordinate D originalSc cutoff L (σ i j) (σ i j) 0
    exact hz.trans (map_zero _).symm
  exact (extensionBasis D originalSc (σ i j) (σ i j)).ne_zero
    (oddIndex, identityNF i j) (congrArg Subtype.val hh)
private def chosenVector (i j : Bool) : (sourceModule i j).obj (w i j) :=
  (moduleIsoLinearEquiv (sourceIso i j) (w i j)).symm (contentVector i j)
private theorem chosenVector_ne_zero (i j : Bool) : chosenVector i j ≠ 0 := by
  intro hz
  apply contentVector_ne_zero i j
  have he := (moduleIsoLinearEquiv (sourceIso i j) (w i j)).apply_symm_apply (contentVector i j)
  rw [show (moduleIsoLinearEquiv (sourceIso i j) (w i j)).symm (contentVector i j) = 0 from hz,
    map_zero] at he
  exact he.symm

/-- Test the original selected content crossing on arbitrary full coefficient tails. -/
example (i j : Bool) (z : ContentCategory D Sc cutoff N (γ i j))
    (a : SKM.SYM.ELVCoefficientAlgebra (k := ℚ) D cutoff)
    (h : (OldCategory.mk (ρ i j) : OldCategory D Sc cutoff) ⟶ OldCategory.mk z.obj.word) :=
  congrArg (fun f : sourceModule i j ⟶ targetModule i j => f.total z
    ((sourceIso i j).inv.total z
      (PowerWordContentCyclicity.generator D Sc cutoff L (ρ i j) (γ i j) z
        (coefficientEndomorphism D Sc cutoff (ρ i j) a ≫ h))))
    (PowerWordContentCross.chosen_pair_cross D Sc cutoff L ν β rfl i j
      (δ j) (δ i) (γ i j) (hj j) (hj i) (hSource i j) (hTarget i j))

/-- Equal-colour minus on a surviving two-colour exterior input. -/
example : chosenVector false false ≠ 0 := chosenVector_ne_zero false false
example := congrArg (fun f : sourceModule false false ⟶ targetModule false false =>
  f.total (w false false) (chosenVector false false))
  (PowerWordContentCross.chosen_pair_cross D Sc cutoff L ν β rfl false false
    (δ false) (δ false) (γ false false) (hj false) (hj false)
    (hSource false false) (hTarget false false))
/-- Distinct-colour crossing on a surviving two-colour exterior input. -/
example : chosenVector false true ≠ 0 := chosenVector_ne_zero false true
example := congrArg (fun f : sourceModule false true ⟶ targetModule false true =>
  f.total (w false true) (chosenVector false true))
  (PowerWordContentCross.chosen_pair_cross D Sc cutoff L ν β rfl false true
    (δ true) (δ false) (γ false true) (hj true) (hj false)
    (hSource false true) (hTarget false true))
end NonVacuity.ELVPowerWordContentCross
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let some idx := env.header.moduleNames.idxOf?
      `OddMath.QuiverHecke.CyclotomicAction.ELVPowerWordContentCross | throwError "Module not imported"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "No owned declarations"
  for name in names do
    for axiomName in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
  logInfo m!"Audited {names.size} owned declarations: standard axioms only"
