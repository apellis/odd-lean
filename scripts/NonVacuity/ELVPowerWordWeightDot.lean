import OddMath.QuiverHecke.CyclotomicAction.ELVPowerWordWeightDot
import OddMath.QuiverHecke.HalfTurn.PowerWordCoordinates
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import OddMath.QuiverHecke.CyclotomicAction.ELVContentSingleLetterRelations
import Lean.Util.CollectAxioms

/-! Actual chosen weight dot in scheduled full-coefficient word coordinates on
an occupied three-strand A/T module with both odd coefficient colours. -/
noncomputable section
namespace NonVacuity.ELVPowerWordWeightDot
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

/-- The independently chosen dot on the occupied component and the
whole original-weight family; all coefficient vectors are unrestricted. -/
example := PowerWordWeightDot.weight_dot_component D Sc cutoff L Λ ν false
example := PowerWordWeightDot.weight_append_dot D Sc cutoff L Λ ν false
example := PowerWordWeightDot.weight_append_dot D Sc cutoff L Λ (ν ++ [false]) true

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

private abbrev chosenDot := elvWeightDotComponent D Sc cutoff N false Λ
  (PowerWordWeight.wordWeight_append D Λ ν false) 1
  (PowerWordWeight.wordFamily D Sc cutoff L Λ (PowerWordWeight.wordWeight D Λ ν) ν) δ
private abbrev appIso := PowerWordWeight.weightAppendComponentIso D Sc cutoff L Λ ν false
private abbrev nextDot := PowerWordWeightDot.wordDotAt D Sc cutoff L ν false δ.1

/-- The native whole-map equation evaluated on the proved nonzero actual
weight E vector. Its particular dot image need not be nonzero. -/
example : ((chosenDot ≫ appIso.hom).total w) chosenVector =
    ((appIso.hom ≫ nextDot).total w) chosenVector :=
  congrArg (fun f => f.total w chosenVector) (PowerWordWeightDot.weight_dot_component D Sc cutoff L Λ ν false)

end NonVacuity.ELVPowerWordWeightDot
namespace NonVacuity.ELVPowerWordWeightDotCollision
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction
private def collisionDatum : SKM.Datum Bool (Bool → ℤ) where
  cd :=
    { root := fun j i => if i = j then 2 else -2
      coroot := fun i => LinearMap.proj i
      coroot_root_self := fun i => by simp }
  isGCM :=
    { diag := fun i => by simp [CartanDatum.cartanMatrix_apply]
      offDiag_nonpos := fun i j h => by simp [CartanDatum.cartanMatrix_apply, h]
      zero_comm := fun i j => by simp [CartanDatum.cartanMatrix_apply, eq_comm] }
  parity := fun _ => 1
  even_of_odd := by
    intro i j _
    change Even (if i = j then (2 : ℤ) else -2)
    split
    · exact ⟨1, by norm_num⟩
    · exact ⟨-1, by norm_num⟩

private def collisionScalars : SKM.Scalars collisionDatum ℚ where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := fun _ => isUnit_iff_ne_zero.mpr (by norm_num)

private abbrev D := collisionDatum
private abbrev Sc := parameterTwist D collisionScalars
private def cutoff (_ : Bool) : ℕ := 20
private def L (_ : Bool × ℕ) : ℕ := 10
private abbrev Λ : Bool → ℤ := 0
private abbrev ν : List Bool := [true, true]
private abbrev step := PowerWordWeight.wordWeight_append D Λ ν false
private def missing : WeightBlocks D Λ (PowerWordWeight.wordWeight D Λ (ν ++ [false])) :=
  ⟨[true], by
    ext b
    cases b <;> norm_num [PowerWordWeight.wordWeight, blockWeight,
      collisionDatum, SKM.Datum.α]⟩
private def other : WeightBlocks D Λ (PowerWordWeight.wordWeight D Λ ν) :=
  ⟨[false, true, true, true], by
    ext b
    cases b <;> norm_num [PowerWordWeight.wordWeight, blockWeight,
      collisionDatum, SKM.Datum.α]⟩
private abbrev selected := blockSucc D Λ false step (PowerWordWeight.wordBlock D Λ ν)
private theorem missing_ne : missing ≠ selected := by
  intro he
  have hc := congrArg (fun β => β.1.card) he
  change (1 : ℕ) = 3 at hc
  omega
private theorem other_ne : blockSucc D Λ false step other ≠ selected := by
  intro he
  have hc := congrArg (fun β => β.1.card) he
  change (5 : ℕ) = 3 at hc
  omega

/-- Actual absent predecessor at the same original target weight. -/
example : ¬ ∃ β, blockSucc D Λ false step β = missing := by
  intro ⟨β, he⟩
  have hm := (exists_blockSucc_iff D Λ false step missing).mp ⟨β, he⟩
  simp only [missing, Multiset.mem_coe, List.mem_singleton, Bool.false_eq_true] at hm
example := PowerWordWeight.weightAppend_isZero D Sc cutoff L Λ ν false missing missing_ne

/-- A genuinely present predecessor outside support at that same weight. -/
example : ∃ β, blockSucc D Λ false step β = blockSucc D Λ false step other := ⟨other, rfl⟩
example := PowerWordWeight.weightAppend_isZero D Sc cutoff L Λ ν false
  (blockSucc D Λ false step other) other_ne
/-- Whole dot compatibility includes the actual absent and present
unsupported components at this same original weight. -/
example := congrArg (fun f => f missing) (PowerWordWeightDot.weight_append_dot D Sc cutoff L Λ ν false)
example := congrArg (fun f => f (blockSucc D Λ false step other))
  (PowerWordWeightDot.weight_append_dot D Sc cutoff L Λ ν false)
end NonVacuity.ELVPowerWordWeightDotCollision

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let some idx := env.header.moduleNames.idxOf?
      `OddMath.QuiverHecke.CyclotomicAction.ELVPowerWordWeightDot | throwError "Module not imported"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "No owned declarations"
  for name in names do
    for axiomName in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
  logInfo m!"Audited {names.size} owned declarations: standard axioms only"
