import OddMath.QuiverHecke.CyclotomicAction.ELVTensorVacuumGenerators
import OddMath.QuiverHecke.HalfTurn.PowerWordCoordinates
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction OddMath.QuiverHecke.SwappedAssembly
namespace NonVacuity.ELVTensorVacuumGenerators
private abbrev D := AsymmetricParameters.datum
private abbrev originalSc := AsymmetricParameters.scalars
private abbrev Sc := parameterTwist D originalSc
private def cutoff (_ : Bool) : ℕ := 20
private def L (_ : Bool × ℕ) : ℕ := 10
private def m (i : Bool) : ℕ := if i then 2 else 1
private def Λ : Bool → ℤ := fun _ => 20
private abbrev N := PowerWordContent.powerBound D cutoff L
private abbrev x₀ := ReservoirWord.weight D Λ 0
private abbrev Z := WeightTensorVacuum.selectedHom D Sc m cutoff Λ Λ L
private abbrev R := WeightTensorVacuum.regularProbe D Sc m Λ
private abbrev W := elvRouquierData D Sc cutoff N Λ
private abbrev τ (i j : Bool) : List Bool := [j, i]
private abbrev σ (i j : Bool) : List Bool := (τ i j).reverse
private theorem h₄ (i j : Bool) : (x₀ + D.α i) + D.α j = (x₀ + D.α j) + D.α i := by abel
private def β (i j : Bool) : WeightBlocks D Λ ((x₀ + D.α j) + D.α i) :=
  ⟨τ i j, by simp [τ, blockWeight, ReservoirWord.weight]; abel⟩
private def w (i j : Bool) : ContentCategory D Sc cutoff N (β i j).1 := ⟨⟨τ i j⟩, rfl⟩
private abbrev chart (i j : Bool) := TensorVacuumGenerators.pairChart D Sc m cutoff L Λ Λ i j rfl rfl
private abbrev chosenEquiv (i j : Bool) := moduleIsoLinearEquiv (Pi.isoApp (chart i j) (β i j)) (w i j)
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
    (PowerWordWeight.wordAt D Sc cutoff L (τ i j) (β i j).1).obj (w i j) :=
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

/-- Equal and distinct odd crossings are evaluated on nonzero vectors in
the literal two-E image of the tensor-vacuum Hom at its regular probe. -/
example := TensorVacuumGenerators.cross_apply D Sc m cutoff L Λ Λ false false rfl rfl rfl
  (h₄ false false) (β false false) (w false false) (chosenVector false false)
example := TensorVacuumGenerators.cross_apply D Sc m cutoff L Λ Λ false true rfl rfl rfl
  (h₄ false true) (β false true) (w false true) (chosenVector false true)
example : chosenVector false false ≠ 0 := chosenVector_ne_zero false false
example : chosenVector false true ≠ 0 := chosenVector_ne_zero false true
example (i j : Bool) := TensorVacuumGenerators.cross D Sc m cutoff L Λ Λ i j rfl rfl rfl (h₄ i j)

namespace Dot
private abbrev ν : List Bool := [false]
private def β : WeightBlocks D Λ (x₀ + D.α false) :=
  ⟨ν, by simp [ν, blockWeight, ReservoirWord.weight]; abel⟩
private def w : ContentCategory D Sc cutoff N β.1 := ⟨⟨ν⟩, rfl⟩
private abbrev chart := TensorVacuumGenerators.dotChart D Sc m cutoff L Λ Λ false rfl
private abbrev chosenEquiv := moduleIsoLinearEquiv (Pi.isoApp chart β) w
private theorem bounded_injective :
    Function.Injective (fun x : ExtendedAtMost D originalSc ν ν 2 =>
      powerWordHalfTurnCoordinate D originalSc cutoff L ν ν x.val) :=
  powerWordHalfTurnCoordinate_injective_on_extendedAtMost D originalSc cutoff L
    (fun _ => (by decide : 16 ≤ 20)) powers_high (by decide)
private def identityNF : NFIdx ν ν := by
  have hc : Categorification.TypeA.canWord ν.length (1 : Equiv.Perm (Fin ν.length)) = [] := by
    apply List.length_eq_zero_iff.mp
    rw [Categorification.TypeA.length_canWord, Categorification.TypeA.length_one]
  refine ⟨([], 1), by simp, by simp, ?_⟩
  simp only [List.map_nil, hc, cw, List.reverse_nil, List.nil_append, pl, SChain]
private def occupied : ExtendedAtMost D originalSc ν ν 2 :=
  ⟨extensionBasis D originalSc ν ν (oddIndex, identityNF),
    Submodule.subset_span ⟨(oddIndex, identityNF), by decide, rfl⟩⟩
private def contentVector : (PowerWordWeight.wordAt D Sc cutoff L ν β.1).obj w :=
  powerWordHalfTurnCoordinate D originalSc cutoff L ν ν occupied.val
private theorem contentVector_ne_zero : contentVector ≠ 0 := by
  intro hz
  have hh : occupied = (0 : ExtendedAtMost D originalSc ν ν 2) := by
    apply bounded_injective
    change powerWordHalfTurnCoordinate D originalSc cutoff L ν ν occupied.val =
      powerWordHalfTurnCoordinate D originalSc cutoff L ν ν 0
    exact hz.trans (map_zero _).symm
  exact (extensionBasis D originalSc ν ν).ne_zero (oddIndex, identityNF) (congrArg Subtype.val hh)
private def chosenVector := chosenEquiv.symm contentVector
example : chosenVector ≠ 0 := by
  intro hz
  apply contentVector_ne_zero
  have he := congrArg chosenEquiv hz
  simpa only [chosenVector, LinearEquiv.apply_symm_apply, map_zero] using he
/-- The literal whiskered dot has its prescribed signed old-Hom value on
the same nonzero exterior coefficient input. -/
example := TensorVacuumGenerators.dot_apply D Sc m cutoff L Λ Λ false rfl β w chosenVector
example := TensorVacuumGenerators.dot D Sc m cutoff L Λ Λ false rfl
end Dot

/-- The formulas cover every vector of every original-weight component. -/
example (i : Bool) (β' : WeightBlocks D Λ (x₀ + D.α i))
    (c : ContentCategory D Sc cutoff N β'.1) (z : (((Z ≫ W.E i rfl).obj R) β').obj c) :=
  TensorVacuumGenerators.dot_apply D Sc m cutoff L Λ Λ i rfl β' c z
example (i j : Bool) (β' : WeightBlocks D Λ ((x₀ + D.α j) + D.α i))
    (c : ContentCategory D Sc cutoff N β'.1)
    (z : (((Z ≫ W.E j rfl ≫ W.E i rfl).obj R) β').obj c) :=
  TensorVacuumGenerators.cross_apply D Sc m cutoff L Λ Λ i j rfl rfl rfl (h₄ i j) β' c z
end NonVacuity.ELVTensorVacuumGenerators
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVTensorVacuumGenerators
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing module: {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module: {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited {names.size} owned declarations in {owner}: standard axioms"
