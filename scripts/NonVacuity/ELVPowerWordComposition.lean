import OddMath.QuiverHecke.CyclotomicAction.ELVPowerWordComposition
import OddMath.QuiverHecke.HalfTurn.PowerWordCoordinates
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

/-! Signed whole-map composition and source half-turn evaluation on
an occupied two-strand A/T module with both odd coefficient colours. -/
noncomputable section
namespace NonVacuity.ELVPowerWordComposition
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open CyclotomicCrossingTensor
private abbrev D := CyclotomicAction.AsymmetricParameters.datum
private abbrev originalSc := CyclotomicAction.AsymmetricParameters.scalars
private abbrev Sc := parameterTwist D originalSc
private def cutoff (_ : Bool) : ℕ := 20
private def L (_ : Bool × ℕ) : ℕ := 10
private abbrev ν : List Bool := [false, true]
private abbrev τ : List Bool := ν.reverse
private abbrev σ : List Bool := τ.reverse
private abbrev C := OldCategory D Sc cutoff
private abbrev target := powerWordModule D Sc cutoff L τ

private def sourceOdd (i : Bool) : coefficientObj D originalSc ν ⟶ coefficientObj D originalSc ν :=
  sourceCoefficientHom D originalSc (SKM.SYM.delta D ℚ ⟨i, rfl⟩) (𝟙 _)
private theorem sourceOdd_mem (i : Bool) : sourceOdd i ∈ parity (R := ℚ) _ _ 1 := by
  simpa only [sourceOdd, add_zero] using
    sourceCoefficientHom_mem_parity D originalSc
      (SKM.SYM.polynomialExterior_delta_mem_odd D ℚ ⟨i, rfl⟩) (id_mem _)
private def oldOdd (i : Bool) : (⟨τ⟩ : C) ⟶ (⟨τ⟩ : C) :=
  halfTurnOldHom D originalSc cutoff ν ν (sourceOdd i)
private theorem oldOdd_mem (i : Bool) : oldOdd i ∈ parity (R := ℚ) _ _ 1 :=
  PowerWordComposition.halfTurnOldHom_mem D originalSc cutoff (sourceOdd_mem i)

/-- The old word chart has the odd-odd super-opposite sign in both orders. -/
example := PowerWordComposition.fromArrow_comp D Sc cutoff L τ τ τ
  (oldOdd false) (oldOdd true) (oldOdd_mem false) (oldOdd_mem true)
example := PowerWordComposition.fromArrow_comp D Sc cutoff L τ τ τ
  (oldOdd true) (oldOdd false) (oldOdd_mem true) (oldOdd_mem false)
example := PowerWordComposition.fromArrow_comp D Sc cutoff L τ τ τ
  (𝟙 (⟨τ⟩ : C)) (oldOdd false) (id_mem _) (oldOdd_mem false)
example := PowerWordComposition.fromArrow_comp D Sc cutoff L τ τ τ
  (oldOdd false) (𝟙 (⟨τ⟩ : C)) (oldOdd_mem false) (id_mem _)

/-- The signed U map gives ordinary source composition, on the entire
actual module. Both exterior orders are retained. -/
example := PowerWordComposition.sourceMap_comp_homogeneous D originalSc cutoff L
  (sourceOdd_mem false) (sourceOdd_mem true)
example := PowerWordComposition.sourceMap_comp_homogeneous D originalSc cutoff L
  (sourceOdd_mem true) (sourceOdd_mem false)

/-- Arbitrary source arrows, including inhomogeneous coefficient inputs. -/
example (f g : coefficientObj D originalSc ν ⟶ coefficientObj D originalSc ν) :=
  PowerWordComposition.sourceMap_comp D originalSc cutoff L f g
example := PowerWordComposition.sourceMap_comp D originalSc cutoff L
  (𝟙 _ + sourceOdd false) (𝟙 _ + sourceOdd true)
example := PowerWordComposition.sourceMap_evaluate D originalSc cutoff L ν ν
  (sourceOdd false ≫ sourceOdd true)
example := PowerWordComposition.fromArrow_smul D Sc cutoff L τ τ (2 : ℚ) (oldOdd false)

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
example : (show target.obj (⟨τ⟩ : C) from
    powerWordHalfTurnCoordinate D originalSc cutoff L σ σ occupied.val) ≠ 0 := by
  intro hz
  have hh : occupied = (0 : ExtendedAtMost D originalSc σ σ 2) := by
    apply bounded_injective
    change powerWordHalfTurnCoordinate D originalSc cutoff L σ σ occupied.val =
      powerWordHalfTurnCoordinate D originalSc cutoff L σ σ 0
    exact hz.trans (map_zero _).symm
  exact (extensionBasis D originalSc σ σ).ne_zero (oddIndex, identityNF) (congrArg Subtype.val hh)

/-- The actual source-module map on this two-exterior PBW vector is
nonzero, as its checked unit evaluation is the surviving coordinate. -/
example : PowerWordComposition.sourceMap D originalSc cutoff L σ σ occupied.val ≠ 0 := by
  intro hz
  have he := PowerWordComposition.sourceMap_evaluate D originalSc cutoff L σ σ occupied.val
  rw [hz, map_zero] at he
  have hh : occupied = (0 : ExtendedAtMost D originalSc σ σ 2) := by
    apply bounded_injective
    change powerWordHalfTurnCoordinate D originalSc cutoff L σ σ occupied.val =
      powerWordHalfTurnCoordinate D originalSc cutoff L σ σ 0
    exact he.symm.trans (map_zero _).symm
  exact (extensionBasis D originalSc σ σ).ne_zero (oddIndex, identityNF) (congrArg Subtype.val hh)

end NonVacuity.ELVPowerWordComposition
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let some idx := env.header.moduleNames.idxOf?
      `OddMath.QuiverHecke.CyclotomicAction.ELVPowerWordComposition | throwError "Module not imported"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "No owned declarations"
  for name in names do
    for axiomName in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
  logInfo m!"Audited {names.size} owned declarations: standard axioms only"
