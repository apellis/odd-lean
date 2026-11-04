import OddMath.QuiverHecke.CyclotomicAction.ELVModuleCentreTotalDegree
import OddMath.QuiverHecke.CyclotomicAction.ELVTruncatedDetection
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
namespace NonVacuity.ModuleCentreTotalDegree
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
private def sy : SKM.Symmetrizer D where
  d := fun _ => 1
  pos := fun _ => by decide
  symm := fun _ _ => rfl
private theorem hc : Sc.Homogeneous := by
  intro _ _ _ _ _ _ _ _ h
  exact (h rfl).elim
private def cutoff (_ : Unit) : ℕ := 2
private abbrev β : Multiset Unit := [()]
private abbrev C := ContentCategory D Sc cutoff 3 β
private def c : ContentCoefficient D Sc cutoff 3 β := 𝟙 _
private def η : ModuleCentre.Centre D Sc cutoff 3 β := contentRealize D Sc cutoff 3 β c
private def v : C := ⟨⟨[()]⟩,rfl⟩
private def z : v ⟶ v := truncatedSingle D Sc cutoff 3 () (SKM.SYM.delta D ℚ ⟨(),rfl⟩) 0
private theorem z_ne_zero : z ≠ 0 := truncatedSingle_delta_ne_zero D Sc rfl

private theorem total_degree (w : C) :
    (η.total (contentRepresentable D Sc cutoff 3 β w)).total w (𝟙 w) ∈
      truncatedDegree D Sc cutoff sy hc 3 w.obj.word w.obj.word 0 := by
  rw [← ModuleCentre.reconstruct_total_evaluate]
  change (ModuleCentre.reconstruct D Sc cutoff 3 β (contentRealize D Sc cutoff 3 β c)).total w ∈ _
  rw [ModuleCentre.reconstruct_realize]
  change (𝟙 w : w ⟶ w) + 0 ∈ _
  rw [add_zero]
  exact (contentGradedSupercategory D Sc cutoff 3 sy hc β).id_mem_degree w
example : ModuleCentre.reconstruct D Sc cutoff 3 β η ∈
    contentCoefficientDegree D Sc cutoff 3 β sy hc 0 :=
  ModuleCentre.reconstruct_mem_degree_of_total_evaluation D Sc cutoff 3 β sy hc η 0 total_degree
example (w : C) := ModuleCentre.reconstruct_total_evaluate D Sc cutoff 3 β η w
example (p : ZMod 2) (w : C) := ModuleCentre.reconstruct_app_eq_proj_total D Sc cutoff 3 β η p w

-- The representable input has an independently detected nonzero odd vector.
example : z ≠ 0 := z_ne_zero
example : (𝟙 v : v ⟶ v) ≠ 0 := by
  intro h
  apply z_ne_zero
  calc
    z = (𝟙 v) ≫ z := (Category.id_comp z).symm
    _ = 0 := by rw [h, Limits.zero_comp]
end NonVacuity.ModuleCentreTotalDegree

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVModuleCentreTotalDegree
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations in {owner}"
