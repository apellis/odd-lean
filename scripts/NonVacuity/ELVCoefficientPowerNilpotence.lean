import OddMath.QuiverHecke.CyclotomicAction.ELVCoefficientPowerNilpotence
import OddMath.QuiverHecke.CyclotomicAction.ELVCoefficientPowerRows
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import OddMath.SKM.BubbleSubstitution
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
open CyclotomicCrossingTensor PowerVacuumCoefficient
namespace NonVacuity.ELVCoefficientPowerNilpotence
private abbrev D := CyclotomicAction.AsymmetricParameters.datum
private abbrev Sc := CyclotomicAction.AsymmetricParameters.scalars
private def cutoff (_ : Bool) : ℕ := 4
private def L (_ : Bool × ℕ) : ℕ := 4
private theorem powers_high (a : Bool × ℕ) :
    4 ≤ L a * SKM.SYM.elementaryWeight D a := by
  change 4 ≤ 4 * SKM.SYM.elementaryWeight D a
  have hw : 0 < SKM.SYM.elementaryWeight D a := by
    unfold SKM.SYM.elementaryWeight
    split_ifs <;> omega
  omega

private def deltaA (i : Bool) : SKM.SYM.ELVCoefficientAlgebra (k := ℚ) D cutoff :=
  SKM.SYM.elvCoefficientQuotient D cutoff (SKM.SYM.delta D ℚ ⟨i, rfl⟩)
private theorem deltaA_mem (i : Bool) :
    deltaA i ∈ SKM.SYM.elvCoefficientParity D cutoff 1 := by
  have h := SKM.SYM.elvModelQuotient_mem D (cutoff := cutoff)
    (SKM.SYM.polynomialExterior_delta_mem_odd D (k := ℚ) ⟨i, rfl⟩)
  simpa only [SKM.SYM.elvModelQuotient, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    AlgEquiv.symm_apply_apply, deltaA] using h

private theorem deltaClass_ne_zero (i : Bool) :
    coefficientPowerQuotientMap (k := ℚ) D cutoff L (SKM.SYM.delta D ℚ ⟨i, rfl⟩) ≠ 0 := by
  intro hz
  have hi := coefficientPowerQuotient_injective (k := ℚ) D cutoff L 1 4 (by norm_num [cutoff])
    (fun _ => by rfl) powers_high
  have he := hi (a₁ := ⟨_, SKM.SYM.delta_mem_coefficientAtMost D ℚ ⟨i, rfl⟩⟩)
    (a₂ := 0) (by simpa only [ZeroMemClass.coe_zero, map_zero] using hz)
  have hδ : SKM.SYM.delta D ℚ ⟨i, rfl⟩ ≠ 0 := by
    rw [← SKM.SYM.coefficientBasis_delta]
    exact (SKM.SYM.coefficientBasis D ℚ).ne_zero _
  exact hδ (congrArg Subtype.val he)



private abbrev AQ := CoefficientPowerQuotient (k := ℚ) D cutoff L
private abbrev M := coefficientPowerVacuum D Sc cutoff L
private def dot (i : Bool) : Module.End ℚ (mateTargetSpace D Sc cutoff i M ⟨[]⟩) :=
  actualInductionDot D Sc cutoff i M ((append D Sc cutoff i).obj ⟨[]⟩)
private def deltaClass (j : Bool) : AQ :=
  coefficientPowerQuotientMap (k := ℚ) D cutoff L (SKM.SYM.delta D ℚ ⟨j, rfl⟩)

/-- The derived positive exponent works simultaneously for every literal
power-annihilated module at the prescribed successor content. -/
example (ν : List Bool) (i : Bool) :
    ∃ e : ℕ, 0 < e ∧ ∀ P : CoefficientPowerModules D Sc cutoff
        (elementaryCoefficients (k := ℚ) D cutoff) L,
      ∀ (w : OldCategory D Sc cutoff), w.word.Perm (ν ++ [i]) →
        actualInductionDot D Sc cutoff i P.obj w ^ e = 0 :=
  coefficientPowerInductionDot_pow_zero D Sc cutoff
    CyclotomicAction.AsymmetricParameters.symmetrizer
    CyclotomicAction.AsymmetricParameters.homogeneous L ν i

private theorem top_occupied (i j : Bool) :
    (dot i ^ 3) (unit D Sc cutoff L i (deltaClass j)) ≠ 0 := by
  intro hz
  have h := functional_dot_window D Sc cutoff L i (by norm_num [cutoff])
    3 (by norm_num [cutoff]) (deltaClass j)
  change functional D Sc cutoff L i (by norm_num [cutoff])
    ((dot i ^ 3) (unit D Sc cutoff L i (deltaClass j))) = deltaClass j at h
  rw [hz, map_zero] at h
  exact deltaClass_ne_zero j h.symm

/-- On the actual old regular A/T vacuum the signed induction dot is
nilpotent, while its third power still acts nontrivially on an occupied
odd coefficient vector. The resulting exponent must exceed three. -/
example (i : Bool) : ∃ e : ℕ, 3 < e ∧ dot i ^ e = 0 := by
  obtain ⟨e, _, hp⟩ := coefficientPowerInductionDot_pow_zero D Sc cutoff
    CyclotomicAction.AsymmetricParameters.symmetrizer
    CyclotomicAction.AsymmetricParameters.homogeneous L [] i
  have hz : dot i ^ e = 0 := hp (coefficientPowerVacuumObject D Sc cutoff L)
    ((append D Sc cutoff i).obj ⟨[]⟩) (List.Perm.refl _)
  refine ⟨e, ?_, hz⟩
  by_contra he
  have he3 : e ≤ 3 := by omega
  have he0 : (dot i ^ e) (unit D Sc cutoff L i (deltaClass false)) = 0 :=
    LinearMap.congr_fun hz _
  exact top_occupied i false (Module.End.pow_map_zero_of_le he3 he0)

end NonVacuity.ELVCoefficientPowerNilpotence

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVCoefficientPowerNilpotence
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Module not imported: {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "No owned declarations: {owner}"
  for name in names do
    for axiomName in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
  logInfo m!"Audited {names.size} owned declarations in {owner}: standard axioms only"
