import OddMath.QuiverHecke.CyclotomicAction.ELVCoefficientPowerVacuum
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import OddMath.SKM.BubbleSubstitution
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
namespace NonVacuity.ELVCoefficientPowerVacuum
private abbrev D := CyclotomicAction.AsymmetricParameters.datum
private abbrev Sc := CyclotomicAction.AsymmetricParameters.scalars
private def cutoff (_ : Bool) : ℕ := 4
private def L (_ : Bool × ℕ) : ℕ := 4
private abbrev J := powerCoefficientEmbedding (k := ℚ) D Sc cutoff
private abbrev R := liftedPowerRegular (k := ℚ) D cutoff L
private abbrev s := powerCoefficientStar (k := ℚ) D cutoff

/-- The comparison is the chosen ordinary induction unit. -/
example : (coefficientPowerVacuumUnitIso D Sc cutoff L).hom =
    (BalancedInduction.adjunctionUnit J).app R :=
  BalancedInduction.fullyFaithfulUnitIso_hom J R

/-- Both maps use the actual balanced quotient and its prescribed
fully faithful unit inverse. -/
example (x : R.obj s) :
    BalancedInduction.fullyFaithfulUnitInverse J R.toFunctor s
      (BalancedInduction.unit J R.toFunctor s x) = x :=
  LinearMap.congr_fun (BalancedInduction.fullyFaithfulUnitInverse_unit J R.toFunctor
    s) x

/-- The exact full coefficient corner is decoded without removing any
odd coefficient direction or imposing a monic-basis assumption. -/
example (a : SKM.SYM.ELVCoefficientAlgebra (k := ℚ) D cutoff) :
    emptyCoefficientDecoder D Sc cutoff (emptyCoefficientEncoder D Sc cutoff a) = a :=
  emptyCoefficientDecoder_encoder D Sc cutoff a

/-- All nonempty old words vanish in the literal power vacuum. -/
example (i : Bool) (t : OldCategory D Sc cutoff)
    (z : ((BalancedInduction.restriction (CyclotomicCrossingTensor.append D Sc cutoff i)).obj
      (coefficientPowerVacuum D Sc cutoff L)).obj t) : z = 0 :=
  coefficientPowerVacuum_support D Sc cutoff L _ (by change t.word ++ [i] ≠ []; simp) z

/-- Every element of the whole defining ideal kills every old component. -/
example (a : SKM.SYM.ELVCoefficientAlgebra (k := ℚ) D cutoff)
    (ha : a ∈ coefficientPowerIdeal D cutoff (elementaryCoefficients (k := ℚ) D cutoff) L) :
    KillsCoefficient D Sc cutoff (coefficientPowerVacuum D Sc cutoff L) a :=
  (mem_coefficientAnnihilator D Sc cutoff _ a).mp
    ((coefficientPowerVacuumObject D Sc cutoff L).property ha)

private theorem powers_high (a : Bool × ℕ) :
    4 ≤ L a * SKM.SYM.elementaryWeight D a := by
  change 4 ≤ 4 * SKM.SYM.elementaryWeight D a
  have hw : 0 < SKM.SYM.elementaryWeight D a := by
    unfold SKM.SYM.elementaryWeight
    split_ifs <;> omega
  omega

private theorem deltaClass_ne_zero (i : Bool) :
    coefficientPowerQuotientMap (k := ℚ) D cutoff L (SKM.SYM.delta D ℚ ⟨i, rfl⟩) ≠ 0 := by
  intro hz
  have hi := coefficientPowerQuotient_injective (k := ℚ) D cutoff L 1 4 (by decide)
    (fun _ => by rfl) powers_high
  have he := hi (a₁ := ⟨_, SKM.SYM.delta_mem_coefficientAtMost D ℚ ⟨i, rfl⟩⟩)
    (a₂ := 0) (by simpa only [ZeroMemClass.coe_zero, map_zero] using hz)
  have hδ : SKM.SYM.delta D ℚ ⟨i, rfl⟩ ≠ 0 := by
    rw [← SKM.SYM.coefficientBasis_delta]
    exact (SKM.SYM.coefficientBasis D ℚ).ne_zero _
  exact hδ (congrArg Subtype.val he)

/-- Both independent odd coefficient vectors survive in the ACTUAL old
vacuum, transported by its chosen balanced unit. -/
example (i : Bool) : coefficientPowerVacuumEmptyEquiv D Sc cutoff L
    (coefficientPowerQuotientMap (k := ℚ) D cutoff L (SKM.SYM.delta D ℚ ⟨i, rfl⟩)) ≠ 0 := by
  intro h
  apply deltaClass_ne_zero i
  apply (coefficientPowerVacuumEmptyEquiv D Sc cutoff L).injective
  simpa only [map_zero] using h

/-- The same occupied old-vacuum coefficient vectors retain odd parity
through the literal even unit comparison. -/
example (i : Bool) : coefficientPowerVacuumEmptyEquiv D Sc cutoff L
      (coefficientPowerQuotientMap (k := ℚ) D cutoff L (SKM.SYM.delta D ℚ ⟨i, rfl⟩)) ∈
    ((coefficientPowerVacuum D Sc cutoff L).obj (⟨[]⟩ : OldCategory D Sc cutoff)).part 1 := by
  have h := SKM.SYM.elvModelQuotient_mem D (cutoff := cutoff)
    (SKM.SYM.polynomialExterior_delta_mem_odd D (k := ℚ) ⟨i, rfl⟩)
  have ha : SKM.SYM.elvCoefficientQuotient D cutoff (SKM.SYM.delta D ℚ ⟨i, rfl⟩) ∈
      SKM.SYM.elvCoefficientParity D cutoff 1 := by
    simpa only [SKM.SYM.elvModelQuotient, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
      AlgEquiv.symm_apply_apply] using h
  exact coefficientPowerVacuumEmptyEquiv_mem D Sc cutoff L
    (coefficientPowerQuotient_mem D cutoff L ha)

end NonVacuity.ELVCoefficientPowerVacuum

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for owner in #[`OddMath.QuiverHecke.CyclotomicAction.ELVEmptyCoefficientEmbedding,
      `OddMath.QuiverHecke.CyclotomicAction.ELVCoefficientPowerVacuum] do
    let some idx := env.header.moduleNames.idxOf? owner | throwError "Module not imported: {owner}"
    let names := env.header.moduleData[idx]!.constNames
    if names.isEmpty then throwError "No owned declarations: {owner}"
    for name in names do
      for axiomName in ← Lean.collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
          throwError "Disallowed axiom {axiomName} in {name}"
    logInfo m!"Audited {names.size} owned declarations in {owner}: standard axioms only"
