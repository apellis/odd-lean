import OddMath.QuiverHecke.SwappedAssembly.SupportedTensorCoefficientAction
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.SKM
open OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction OddMath.QuiverHecke.SwappedAssembly
open SupportedSectors
namespace NonVacuity.SupportedTensorCoefficientAction
private abbrev D := AsymmetricParameters.datum
private abbrev Sc := AsymmetricParameters.scalars
private def cutoff (_ : Bool) : ℕ := 20
private def m (i : Bool) : ℕ := if i then 2 else 1
private def L (_ : Bool × ℕ) : ℕ := 10
private abbrev Λ : Bool → ℤ := 0
private abbrev N := PowerWordContent.powerBound D cutoff L
private abbrev Tw := parameterTwist D Sc
private abbrev Z := tensorVacuum D Sc m cutoff L Λ Λ
private abbrev action := tensorVacuumCoefficientAction D Sc m cutoff L Λ Λ
private abbrev OddColour := {i : Bool // D.parity i = 1}
private def i₀ : OddColour := ⟨false, rfl⟩
private def i₁ : OddColour := ⟨true, rfl⟩

example : SYM D ℚ →ₐ[ℚ] End Z := action
example (a b : SYM D ℚ) : action (a * b) = action a * action b := map_mul _ a b
example : action (SYM.delta D ℚ i₀ * SYM.delta D ℚ i₁) =
    -action (SYM.delta D ℚ i₁ * SYM.delta D ℚ i₀) := by
  rw [SYM.delta_anticommute, map_neg]
example (s : List Bool) : SYM D ℚ →ₐ[ℚ] End (tensorSourceObject D Sc m cutoff Λ Λ L s) :=
  tensorSourceCoefficientAction D Sc m cutoff L Λ Λ s

example {l : List (Col Bool (Bool → ℤ))} {s : Sector Bool}
    (p : SPath l s (0,0)) (G : H D Tw m cutoff N Λ Λ s)
    (a : SYM D ℚ) (f : G ⟶ (pathFunctor D Tw m cutoff N Λ Λ p).obj Z) :
    tensorWordHomCoefficientAction D Sc m cutoff L Λ Λ p G a f =
      f ≫ tensorPathCoefficientAction D Sc m cutoff L Λ Λ p a :=
  tensorWordHomCoefficientAction_apply D Sc m cutoff L Λ Λ p G a f

/-- The induced word-Hom action preserves the original multiplication,
including products of independent odd source coefficients. -/
example {l : List (Col Bool (Bool → ℤ))} {s : Sector Bool}
    (p : SPath l s (0,0)) (G : H D Tw m cutoff N Λ Λ s) (a b : SYM D ℚ) :
    tensorWordHomCoefficientAction D Sc m cutoff L Λ Λ p G (a * b) =
      tensorWordHomCoefficientAction D Sc m cutoff L Λ Λ p G a *
        tensorWordHomCoefficientAction D Sc m cutoff L Λ Λ p G b := map_mul _ a b
end NonVacuity.SupportedTensorCoefficientAction
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.SwappedAssembly.SupportedTensorCoefficientAction
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing module: {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module: {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited {names.size} owned declarations in {owner}: standard axioms"
