import OddMath.QuiverHecke.CyclotomicAction.ELVPowerWordHomCoordinates
import OddMath.QuiverHecke.HalfTurn.PowerWordCoordinates
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import OddMath.QuiverHecke.CyclotomicAction.ELVContentSingleLetterRelations
import Lean.Util.CollectAxioms

/-! Full-coefficient cyclicity on the scheduled word module with
an occupied three-strand A/T module with both odd coefficient colours. -/
noncomputable section
namespace NonVacuity.ELVPowerWordHomCoordinates
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open CyclotomicCrossingTensor
private abbrev D := CyclotomicAction.AsymmetricParameters.datum
private abbrev originalSc := CyclotomicAction.AsymmetricParameters.scalars
private abbrev Sc := parameterTwist D originalSc
private def cutoff (_ : Bool) : ℕ := 20
private def L (_ : Bool × ℕ) : ℕ := 10
private abbrev ν : List Bool := [false, true]
private abbrev τ : List Bool := ν
private abbrev Λ : Bool → ℤ := 0
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

private abbrev coordinates := PowerWordHomCoordinates.homEquiv D Sc cutoff L Λ ν ν
private def nativeHom := coordinates.symm contentVector
/-- The full native Hom space is occupied by an independently surviving
exterior two-colour coordinate. -/
example : nativeHom ≠ 0 := by
  intro hz
  apply contentVector_ne_zero
  have hh := congrArg coordinates hz
  simpa only [nativeHom, LinearEquiv.apply_symm_apply, map_zero] using hh

private abbrev β := PowerWordWeight.wordBlock D Λ ν
private abbrev WO := PowerWordContentCyclicity.wordObject D Sc cutoff L ν (ν : Multiset Bool) rfl
private theorem coordinate_image :
    (nativeHom β).total WO (PowerWordHomCoordinates.unitVector D Sc cutoff L Λ ν) = contentVector :=
  coordinates.apply_symm_apply contentVector

/-- Its actual cyclic unit is nonzero as well. -/
example : PowerWordHomCoordinates.unitVector D Sc cutoff L Λ ν ≠ 0 := by
  intro hz
  apply contentVector_ne_zero
  have hh := coordinate_image
  rw [hz, map_zero] at hh
  exact hh.symm
example :
    (nativeHom β).total WO (PowerWordHomCoordinates.unitVector D Sc cutoff L Λ ν) = contentVector :=
  coordinate_image

private abbrev κ : List Bool := [true, false]
/-- A different same-weight target word, with its genuine crossing arrow. -/
example := PowerWordHomCoordinates.homEquiv_from_old D Sc cutoff L Λ ν κ
  (PowerWordContentCross.normalizedOldCross D Sc cutoff [] true false)

private def deltaCoefficient (i : Bool) : SKM.SYM.ELVCoefficientAlgebra (k := ℚ) D cutoff :=
  SKM.SYM.elvCoefficientQuotient D cutoff (SKM.SYM.delta D ℚ ⟨i, rfl⟩)
/-- Genuine native coefficient insertion, including independent odd colours
and inhomogeneous coefficients, has the asserted full Hom coordinate. -/
example := PowerWordHomCoordinates.homEquiv_coefficient D Sc cutoff L Λ ν
  (deltaCoefficient false * deltaCoefficient true)
example := PowerWordHomCoordinates.homEquiv_coefficient D Sc cutoff L Λ ν (1 + deltaCoefficient false)
/-- The independently chosen odd dot on a literal three-E value. -/
example := PowerWordHomCoordinates.homEquiv_dot D Sc cutoff L Λ ν false

private theorem h₄ (i j : Bool) :
    PowerWordWeight.wordWeight D Λ ([] ++ [i]) + D.α j =
      PowerWordWeight.wordWeight D Λ (([] ++ [j]) ++ [i]) := by
  calc
    PowerWordWeight.wordWeight D Λ ([] ++ [i]) + D.α j =
        (PowerWordWeight.wordWeight D Λ [] + D.α i) + D.α j :=
      congrArg (fun x => x + D.α j) (PowerWordWeight.wordWeight_append D Λ [] i).symm
    _ = (PowerWordWeight.wordWeight D Λ [] + D.α j) + D.α i := by abel
    _ = PowerWordWeight.wordWeight D Λ ([] ++ [j]) + D.α i :=
      congrArg (fun x => x + D.α i) (PowerWordWeight.wordWeight_append D Λ [] j)
    _ = PowerWordWeight.wordWeight D Λ (([] ++ [j]) ++ [i]) :=
      PowerWordWeight.wordWeight_append D Λ ([] ++ [j]) i
/-- The given equal crossing includes its required extra minus. -/
example := PowerWordHomCoordinates.homEquiv_cross D Sc cutoff L Λ [] false false (h₄ false false)
/-- The given distinct crossing retains its original positive convention. -/
example := PowerWordHomCoordinates.homEquiv_cross D Sc cutoff L Λ [] false true (h₄ false true)

end NonVacuity.ELVPowerWordHomCoordinates
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let some idx := env.header.moduleNames.idxOf?
      `OddMath.QuiverHecke.CyclotomicAction.ELVPowerWordHomCoordinates | throwError "Module not imported"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "No owned declarations"
  for name in names do
    for axiomName in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
  logInfo m!"Audited {names.size} owned declarations: standard axioms only"
