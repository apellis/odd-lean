import OddMath.QuiverHecke.CyclotomicAction.ELVModuleCentreDegree
import OddMath.QuiverHecke.CyclotomicAction.ELVTruncatedDetection
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
namespace NonVacuity.ELVModuleCentreDegree
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
  intro i j p q _ _ _ _ h
  exact False.elim (h rfl)
private def cutoff (_ : Unit) : ℕ := 2
private abbrev β : Multiset Unit := [()]
private abbrev C := ContentCategory D Sc cutoff 3 β
private def c : ContentCoefficient D Sc cutoff 3 β := 𝟙 _
private def η : ModuleCentre.Centre D Sc cutoff 3 β := contentRealize D Sc cutoff 3 β c
private def v : C := ⟨⟨[()]⟩,rfl⟩
private def z : v ⟶ v := truncatedSingle D Sc cutoff 3 () (SKM.SYM.delta D ℚ ⟨(),rfl⟩) 0
private theorem z_ne_zero : z ≠ 0 := truncatedSingle_delta_ne_zero D Sc rfl
private theorem source_degree : c ∈ contentCoefficientDegree D Sc cutoff 3 β sy hc 0 := by
  let := contentGradedSupercategory D Sc cutoff 3 sy hc β
  intro p w
  change (if p = 0 then 𝟙 w else 0) ∈ GradedSupercategory.degree (R := ℚ) w w 0
  split_ifs
  · exact GradedSupercategory.id_mem_degree w
  · exact Submodule.zero_mem _
private theorem represented_degree (w : C) (p : ZMod 2) :
    ModuleYoneda.evaluate D Sc cutoff 3 β (contentRepresentable D Sc cutoff 3 β w)
      (η.app p (contentRepresentable D Sc cutoff 3 β w)) ∈
        truncatedDegree D Sc cutoff sy hc 3 w.obj.word w.obj.word 0 := by
  rw [← ModuleCentre.reconstruct_app_evaluate]
  change (ModuleCentre.reconstruct D Sc cutoff 3 β (contentRealize D Sc cutoff 3 β c)).app p w ∈ _
  rw [ModuleCentre.reconstruct_realize]
  exact source_degree p w

-- The headline witness has a concrete nonzero module-centre input at positive
-- content; this is a degree-zero test, not the still-needed closure degree proof.
example : ∃ a : ContentCoefficient D Sc cutoff 3 β,
    a ∈ contentCoefficientDegree D Sc cutoff 3 β sy hc 0 ∧
      contentRealize D Sc cutoff 3 β a = η :=
  ModuleCentre.exists_coefficient_of_represented_degree D Sc cutoff 3 β sy hc η 0 represented_degree
example : ModuleCentre.reconstruct D Sc cutoff 3 β η ∈
    contentCoefficientDegree D Sc cutoff 3 β sy hc 0 :=
  (ModuleCentre.reconstruct_mem_degree_iff D Sc cutoff 3 β sy hc η 0).mpr represented_degree
example (w : C) (p : ZMod 2) := ModuleCentre.reconstruct_app_evaluate D Sc cutoff 3 β η p w

private theorem identity_nonzero : (𝟙 v : v ⟶ v) ≠ 0 := by
  intro h
  apply z_ne_zero
  calc
    z = (𝟙 v) ≫ z := (Category.id_comp z).symm
    _ = 0 := by rw [h,Limits.zero_comp]
example : ModuleCentre.reconstruct D Sc cutoff 3 β η ≠ 0 := by
  rw [show η = contentRealize D Sc cutoff 3 β c from rfl,ModuleCentre.reconstruct_realize]
  intro h
  have he := congrArg (fun a : ContentCoefficient D Sc cutoff 3 β => a.app 0 v) h
  change (𝟙 v : v ⟶ v) = 0 at he
  exact identity_nonzero he
example : η ≠ 0 := by
  intro h
  have he := congrArg (ModuleCentre.reconstruct D Sc cutoff 3 β) h
  rw [show η = contentRealize D Sc cutoff 3 β c from rfl,ModuleCentre.reconstruct_realize] at he
  have hz : ModuleCentre.reconstruct D Sc cutoff 3 β (0 : ModuleCentre.Centre D Sc cutoff 3 β) = 0 := by
    apply contentRealize_injective D Sc cutoff 3 β
    rw [ModuleCentre.realize_reconstruct]
    exact (map_zero (contentRealizeLinear D Sc cutoff 3 β)).symm
  rw [hz] at he
  have hh := congrArg (fun a : ContentCoefficient D Sc cutoff 3 β => a.app 0 v) he
  change (𝟙 v : v ⟶ v) = 0 at hh
  exact identity_nonzero hh
example : z ≠ 0 := z_ne_zero
end NonVacuity.ELVModuleCentreDegree

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVModuleCentreDegree
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Module not imported: {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "No owned declarations: {owner}"
  for name in names do
    for axiomName in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
  logInfo m!"Audited {names.size} owned declarations in {owner}: standard axioms only"
