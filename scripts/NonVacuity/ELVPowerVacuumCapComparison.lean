import OddMath.QuiverHecke.CyclotomicAction.ELVPowerVacuumCapComparison
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import OddMath.SKM.BubbleSubstitution
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
open BalancedInduction CyclotomicCrossingTensor PowerVacuumCoefficient
namespace NonVacuity.ELVPowerVacuumCapComparison
private theorem nonzero_of_extracts {k V W : Type*} [CommRing k]
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (f : V →ₗ[k] W) (v : V) (w : W) (hw : w ≠ 0) (h : f v = w) : v ≠ 0 := by
  intro hv
  exact hw (h.symm.trans ((congrArg f hv).trans f.map_zero))

private abbrev D := CyclotomicAction.AsymmetricParameters.datum
private abbrev Sc := CyclotomicAction.AsymmetricParameters.scalars
private def cutoff (_ : Bool) : ℕ := 4
private def L (_ : Bool × ℕ) : ℕ := 4
private abbrev AQ := CoefficientPowerQuotient (k := ℚ) D cutoff L
private abbrev M := coefficientPowerVacuum D Sc cutoff L
private abbrev W := weightedVacuum D Sc cutoff L
private abbrev bound := SKM.SYM.elvPowerWeightBound D cutoff L + 1
private abbrev T (i : Bool) := truncatedAppend D Sc cutoff bound [i]
private abbrev s := (oldTruncateFunctor D Sc cutoff bound).obj (⟨[]⟩ : OldCategory D Sc cutoff)
private def topVector (i : Bool) (a : AQ) :=
  (unitDotColumn (T i) (truncatedDot_supernatural D Sc cutoff bound i) W 3).total s
    (weightedEmptyEquiv D Sc cutoff L a)

private theorem powers_high (a : Bool × ℕ) :
    4 ≤ L a * SKM.SYM.elementaryWeight D a := by
  change 4 ≤ 4 * SKM.SYM.elementaryWeight D a
  have hw : 0 < SKM.SYM.elementaryWeight D a := by
    unfold SKM.SYM.elementaryWeight
    split_ifs <;> omega
  omega
private def deltaClass (j : Bool) : AQ :=
  coefficientPowerQuotientMap (k := ℚ) D cutoff L (SKM.SYM.delta D ℚ ⟨j, rfl⟩)
private theorem deltaClass_ne_zero (j : Bool) : deltaClass j ≠ 0 := by
  intro hz
  have hi := coefficientPowerQuotient_injective (k := ℚ) D cutoff L 1 4 (by norm_num [cutoff])
    (fun _ => by rfl) powers_high
  have he := hi (a₁ := ⟨_, SKM.SYM.delta_mem_coefficientAtMost D ℚ ⟨j, rfl⟩⟩)
    (a₂ := 0) (by simpa only [deltaClass, ZeroMemClass.coe_zero, map_zero] using hz)
  have hδ : SKM.SYM.delta D ℚ ⟨j, rfl⟩ ≠ 0 := by
    rw [← SKM.SYM.coefficientBasis_delta]
    exact (SKM.SYM.coefficientBasis D ℚ).ne_zero _
  exact hδ (congrArg Subtype.val he)

/-- The selected weighted inverse row, not a fresh extractor, gives the
actual old λ on every literal A/T induction vector. -/
example (i : Bool) (z : mateTargetSpace D Sc cutoff i M ⟨[]⟩) :
    weightedFunctional D Sc cutoff L i (by norm_num [cutoff])
      (weightedTargetChart D Sc cutoff L i z) =
    functional D Sc cutoff L i (by norm_num [cutoff]) z :=
  weightedFunctional_compare D Sc cutoff L i (by norm_num [cutoff]) z

/-- Every coefficient of the literal power quotient is recovered by the
actual weighted unit/dot field on the unchanged vacuum. -/
private theorem extracts_top (i : Bool) (a : AQ) :
    weightedFunctional D Sc cutoff L i (by norm_num [cutoff]) (topVector i a) = a := by
  exact weightedFunctional_unitDotColumn D Sc cutoff L i (by norm_num [cutoff])
    3 (by norm_num [cutoff]) a

/-- Each independent odd colour remains occupied after weighted descent
and the prescribed dotted unit. -/
example (i j : Bool) : topVector i (deltaClass j) ≠ 0 := by
  exact nonzero_of_extracts (weightedFunctional D Sc cutoff L i (by norm_num [cutoff]))
    (topVector i (deltaClass j)) (deltaClass j) (deltaClass_ne_zero j) (extracts_top i (deltaClass j))

example (i : Bool) (a : AQ) :
    weightedFunctional D Sc cutoff L i (by norm_num [cutoff])
      ((unitDotColumn (T i) (truncatedDot_supernatural D Sc cutoff bound i) W 2).total s
        (weightedEmptyEquiv D Sc cutoff L a)) = 0 :=
  weightedFunctional_unitDotColumn D Sc cutoff L i (by norm_num [cutoff])
    2 (by norm_num [cutoff]) a
end NonVacuity.ELVPowerVacuumCapComparison
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for owner in #[`OddMath.QuiverHecke.CyclotomicAction.ELVWeightedCoefficientRows,
      `OddMath.QuiverHecke.CyclotomicAction.ELVPowerVacuumCapComparison] do
    let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing module: {owner}"
    let names := env.header.moduleData[idx]!.constNames
    if names.isEmpty then throwError "Empty owned module: {owner}"
    for name in names do
      for ax in ← Lean.collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {name}"
    logInfo m!"Audited {names.size} owned declarations in {owner}: standard axioms"
