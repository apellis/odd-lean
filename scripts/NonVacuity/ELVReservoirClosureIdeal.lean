import NonVacuity.ELVWeightedAppendFixture
import OddMath.QuiverHecke.CyclotomicAction.ELVReservoirClosureIdeal
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightCentreBlocks
import OddMath.QuiverHecke.CyclotomicAction.ELVTruncatedDetection
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath OddMath.QuiverHecke ELVOld
open OddMath.QuiverHecke.CyclotomicAction
namespace NonVacuity.ELVReservoirClosureIdeal
private def D : SKM.Datum Unit ℤ where
  cd := {
    root := fun _ => 2
    coroot := fun _ => LinearMap.id
    coroot_root_self := fun _ => rfl }
  isGCM := {
    diag := fun _ => rfl
    offDiag_nonpos := fun i j h => absurd (Subsingleton.elim i j) h
    zero_comm := fun _ _ => Iff.rfl }
  parity := fun _ => 1
  even_of_odd := fun _ _ _ => even_two
private def Sc : SKM.Scalars D ℚ where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := fun _ => isUnit_iff_ne_zero.mpr (by norm_num)
private def cutoff (_ : Unit) : ℕ := 2
private def Λ : ℤ := 2
private theorem cutoff_match (i : Unit) : (cutoff i : ℤ) = D.h i Λ := rfl
private theorem h₁ : (-2 : ℤ) + D.α () = 0 := by decide
private theorem h₂ : (0 : ℤ) + D.α () = 2 := by decide
private def β : WeightBlocks D Λ 0 := ⟨[()],by decide⟩
private def v : ContentCategory D Sc cutoff 3 β.1 := ⟨⟨[()]⟩,rfl⟩
private def R := contentRepresentable D Sc cutoff 3 β.1 v
private def M : ELVWeightProduct D Sc cutoff 3 Λ 0 := (WeightCentreBlocks.extension D Sc cutoff 3 Λ β).obj R
private def z : R.obj v := truncatedSingle D Sc cutoff 3 () (SKM.SYM.delta D ℚ ⟨(),rfl⟩) 0
private theorem z_ne_zero : z ≠ 0 := truncatedSingle_delta_ne_zero D Sc rfl
private theorem identity_ne_zero : (𝟙 v : v ⟶ v) ≠ 0 := by
  intro h
  have hz := congrArg (fun f : v ⟶ v => f ≫ z) h
  rw [Category.id_comp, Limits.zero_comp] at hz
  exact z_ne_zero hz
private def chart := moduleIsoLinearEquiv (eqToIso (WeightCentreBlocks.extension_obj D Sc cutoff 3 Λ β R)) v
private def occupied : (M β).obj v := chart.symm z
private theorem occupied_ne_zero : occupied ≠ 0 := by
  intro h
  apply z_ne_zero
  have hh := congrArg chart h
  simpa only [occupied,LinearEquiv.apply_symm_apply,map_zero] using hh

private def sy : SKM.Symmetrizer D where
  d := fun _ => 1
  pos := fun _ => by decide
  symm := fun _ _ => rfl
private theorem hc : Sc.Homogeneous := fun _ _ _ _ _ _ _ _ h => absurd rfl h
private abbrev C := contentModuleTarget D Sc cutoff 3 β.1

example (r s : ℕ) := ReservoirClosures.positiveContent_mem_coeffGrading
  D Sc cutoff 3 Λ cutoff_match () h₁ h₂ β sy hc (by decide) r s
example (r s : ℕ) := ReservoirClosures.negativeContent_mem_coeffGrading
  D Sc cutoff 3 Λ cutoff_match () h₁ h₂ β sy hc (by decide) r s

-- The arbitrary surrounding transformations may be odd or inhomogeneous.
example (r s : ℕ) (a b : (𝟙 C) ⟶ (𝟙 C)) := ReservoirClosures.positiveContent_sandwich_mem
  D Sc cutoff 3 Λ cutoff_match () h₁ h₂ β sy hc C (by decide) r s a b
example (r s : ℕ) (a b : (𝟙 C) ⟶ (𝟙 C)) := ReservoirClosures.negativeContent_sandwich_mem
  D Sc cutoff 3 Λ cutoff_match () h₁ h₂ β sy hc C (by decide) r s a b

private abbrev W := elvWeightSpace D Sc cutoff 3 Λ 0
example (r s : ℕ) (a b : (𝟙 W) ⟶ (𝟙 W)) := ReservoirClosures.positiveAction_evaluate_mem
  D Sc cutoff 3 Λ cutoff_match () h₁ h₂ β sy hc W (by decide) r s a b
example (r s : ℕ) (a b : (𝟙 W) ⟶ (𝟙 W)) := ReservoirClosures.negativeAction_evaluate_mem
  D Sc cutoff 3 Λ cutoff_match () h₁ h₂ β sy hc W (by decide) r s a b

example (r s : ℕ) (a b : (𝟙 W) ⟶ (𝟙 W)) := ReservoirClosures.positiveNativeClosure_evaluate_mem
  D Sc cutoff 3 Λ cutoff_match () h₁ h₂ β sy hc (fun _ => W) (Finsupp.single () 1) 0
  (by decide) r s a b
example (r s : ℕ) (a b : (𝟙 W) ⟶ (𝟙 W)) := ReservoirClosures.negativeNativeClosure_evaluate_mem
  D Sc cutoff 3 Λ cutoff_match () h₁ h₂ β sy hc (fun _ => W) (Finsupp.single () 1) 0
  (by decide) r s a b

-- The module category and its identity action are occupied by a nonzero odd vector.
example : z ≠ 0 := z_ne_zero
example : occupied ≠ 0 := occupied_ne_zero
example : (𝟙 v : v ⟶ v) ≠ 0 := identity_ne_zero
end NonVacuity.ELVReservoirClosureIdeal

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVReservoirClosureIdeal
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Module not imported: {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "No owned declarations: {owner}"
  for name in names do
    for axiomName in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
  logInfo m!"Audited {names.size} owned declarations in {owner}: standard axioms only"
