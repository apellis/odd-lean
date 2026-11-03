import OddMath.QuiverHecke.CyclotomicAction.ELVWeightTensorVacuum
import OddMath.QuiverHecke.HalfTurn.PowerWordCoordinates
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath OddMath.SKM OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction OddMath.QuiverHecke.SwappedAssembly
namespace NonVacuity.ELVWeightTensorVacuum

private abbrev D := AsymmetricParameters.datum
private abbrev originalSc := AsymmetricParameters.scalars
private abbrev Sc := parameterTwist D originalSc
private def cutoff (_ : Bool) : ℕ := 20
private def L (_ : Bool × ℕ) : ℕ := 10
private def m (i : Bool) : ℕ := if i then 2 else 1
private def Λ : Bool → ℤ := fun _ => 20
private abbrev N := PowerWordContent.powerBound D cutoff L
private abbrev W := ReservoirWordValue.initialValue D Λ Sc cutoff L
private abbrev Z := WeightTensorVacuum.selectedHom D Sc m cutoff Λ Λ L
private abbrev M := WeightTensorVacuum.regularProbe D Sc m Λ
private abbrev e := WeightTensorVacuum.selectedIso D Sc m cutoff Λ Λ L
private def β : WeightBlocks D Λ (ReservoirWord.weight D Λ 0) :=
  ⟨0, by simp [ReservoirWord.weight]⟩
private def star : ContentCategory D Sc cutoff N (0 : Multiset Bool) := ⟨⟨[]⟩, rfl⟩

/-- The source and target really are the complete original-weight products. -/
example : probeOldWeightSpace D Sc m Λ (-Λ) ⟶
    elvWeightSpace D Sc cutoff N Λ (ReservoirWord.weight D Λ 0) := Z
example : Z.obj M ≅ W := e
example := WeightTensorVacuum.emptyProbe_regular D Sc m Λ
example := WeightTensorVacuum.regularIso_hom_mem D Sc m cutoff N Λ Λ W
example := WeightTensorVacuum.regularIso_inv_mem D Sc m cutoff N Λ Λ W
example (γ : WeightBlocks D Λ (-Λ)) (h : γ.1 ≠ 0) : Limits.IsZero (M γ) :=
  WeightTensorVacuum.regularProbe_isZero D Sc m Λ γ h

private theorem powers_high (j : Bool × ℕ) : 16 ≤ L j * SKM.SYM.elementaryWeight D j := by
  change 16 ≤ 10 * (2 * (j.2 + 1))
  omega
private theorem bounded_injective :
    Function.Injective (fun x : ExtendedAtMost D originalSc [] [] 2 =>
      powerWordHalfTurnCoordinate D originalSc cutoff L [] [] x.val) :=
  powerWordHalfTurnCoordinate_injective_on_extendedAtMost D originalSc cutoff L
    (fun _ => (by decide : 16 ≤ 20)) powers_high (by decide)
private def identityNF : NFIdx ([] : List Bool) [] := by
  have hc : Categorification.TypeA.canWord 0 (1 : Equiv.Perm (Fin 0)) = [] := by
    apply List.length_eq_zero_iff.mp
    rw [Categorification.TypeA.length_canWord, Categorification.TypeA.length_one]
  refine ⟨([], 1), by simp, by simp, ?_⟩
  simp only [List.map_nil, List.length_nil, hc, cw, List.reverse_nil, List.nil_append, pl,
    QuiverHecke.SChain]
private def oddIndex : SKM.SYM.CoefficientIndex D := (0, {⟨false, rfl⟩, ⟨true, rfl⟩})
private def occupied : ExtendedAtMost D originalSc [] [] 2 :=
  ⟨extensionBasis D originalSc [] [] (oddIndex, identityNF),
    Submodule.subset_span ⟨(oddIndex, identityNF), by decide, rfl⟩⟩
private def coefficient : (W β).obj star :=
  powerWordHalfTurnCoordinate D originalSc cutoff L [] [] occupied.val
private theorem coefficient_ne_zero : coefficient ≠ 0 := by
  intro hz
  have hh : occupied = (0 : ExtendedAtMost D originalSc [] [] 2) := by
    apply bounded_injective
    change powerWordHalfTurnCoordinate D originalSc cutoff L [] [] occupied.val =
      powerWordHalfTurnCoordinate D originalSc cutoff L [] [] 0
    exact hz.trans (map_zero _).symm
  exact (extensionBasis D originalSc [] []).ne_zero (oddIndex, identityNF) (congrArg Subtype.val hh)

private def tensorCoefficient : ((Z.obj M) β).obj star :=
  WeightTensorVacuum.tensorVector D Sc m cutoff N Λ Λ W β star coefficient
private theorem tensorCoefficient_image : (e.hom β).total star tensorCoefficient = coefficient :=
  WeightTensorVacuum.regularIso_hom_tensorVector D Sc m cutoff N Λ Λ W β star coefficient

/-- A product of the two independent odd coefficients occupies the actual
full-product Hom input at its regular probe, and survives unchanged. -/
example : (e.hom β).total star tensorCoefficient = coefficient := tensorCoefficient_image
example : tensorCoefficient ≠ 0 := by
  intro hz
  have h := tensorCoefficient_image
  rw [hz, map_zero] at h
  exact coefficient_ne_zero h.symm

/-- Every reservoir vector has the same exact tensor-vacuum formula. -/
example (γ : WeightBlocks D Λ (ReservoirWord.weight D Λ 0))
    (c : ContentCategory D Sc cutoff N γ.1) (v : (W γ).obj c) :
    (e.hom γ).total c
      (WeightTensorVacuum.tensorVector D Sc m cutoff N Λ Λ W γ c v) = v :=
  WeightTensorVacuum.regularIso_hom_tensorVector D Sc m cutoff N Λ Λ W γ c v
example (γ : WeightBlocks D Λ (ReservoirWord.weight D Λ 0))
    (c : ContentCategory D Sc cutoff N γ.1) (z : ((Z.obj M) γ).obj c) :
    (e.hom γ).total c z =
      VacuumTensor.scalarTensorEquiv ((W γ).obj c)
        ((probeOldVacuumRegular D Sc m).obj (probeOldVacuumObject D Sc m))
        (probeVacuumScalarEquiv D Sc m).symm
        ((eqToHom (WeightTensorVacuum.regularBlock_eq D Sc m cutoff N Λ Λ W γ)).total c z) :=
  WeightTensorVacuum.regularIso_hom_apply D Sc m cutoff N Λ Λ W γ c z
example : e.hom ≫ e.inv = 𝟙 _ := e.hom_inv_id
example : e.inv ≫ e.hom = 𝟙 _ := e.inv_hom_id

end NonVacuity.ELVWeightTensorVacuum
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVWeightTensorVacuum
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing module: {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module: {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited {names.size} owned declarations in {owner}: standard axioms"
