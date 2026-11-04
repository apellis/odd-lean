import OddMath.QuiverHecke.CyclotomicAction.ELVReservoirClosures
import OddMath.QuiverHecke.SwappedAssembly.CentralInverse.FactorClosures
import OddMath.QuiverHecke.CyclotomicAction.ELVTruncatedDetection
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath OddMath.QuiverHecke ELVOld
open OddMath.QuiverHecke.CyclotomicAction
namespace NonVacuity.FactorClosures
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
private def chart := moduleIsoLinearEquiv (eqToIso (WeightCentreBlocks.extension_obj D Sc cutoff 3 Λ β R)) v
private def occupied : (M β).obj v := chart.symm z
private theorem occupied_ne_zero : occupied ≠ 0 := by
  intro h
  apply z_ne_zero
  have hh := congrArg chart h
  simpa only [occupied,LinearEquiv.apply_symm_apply,map_zero] using hh

open OddMath.SKM OddMath.QuiverHecke.SwappedAssembly
local instance factorClosureHomPi (A B : PiSCat.{0,0,1} ℚ) : PiSupercategory ℚ (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B
private def W := elvRouquierFamily D Sc cutoff 3 Λ cutoff_match
private def T (ν : ℤ) (_ : ℤ) := W.obj ν
private def Z (ν : ℤ) : homWeightSector (T ν) W.obj 0 ν := 𝟙 (W.obj ν)
private def βP : Unit →₀ ℕ := Finsupp.single () 1
private theorem lower (ν : ℤ) : ν - 2 + D.α () = ν := by change ν - 2 + 2 = ν; omega
private theorem upper (ν : ℤ) : ν + D.α () = ν + 2 := rfl

-- Both nonempty finite windows and both height-zero principal choices.
example (r s : ℕ) := postCapInverse_closure (T 2) W () βP 0 (lower 2) (upper 2)
  (by decide) (Z 2) r s
example (r s : ℕ) := postCupInverse_closure (T (-2)) W () βP 0 (lower (-2)) (upper (-2))
  (by decide) (Z (-2)) r s
example (r s : ℕ) := postCapInverse_closure (T 0) W () βP 0 (lower 0) (upper 0)
  (by decide) (Z 0) r s
example (r s : ℕ) := postCupInverse_closure (T 0) W () βP 0 (lower 0) (upper 0)
  (by decide) (Z 0) r s
example (j r : ℕ) := postCapInverse_boundary (T 2) W () βP 0 (lower 2) (upper 2)
  (by decide) (Z 2) j r
example (r j : ℕ) := postCupInverse_boundary (T (-2)) W () βP 0 (lower (-2)) (upper (-2))
  (by decide) (Z (-2)) r j
-- The constructed family has a positive-content module with a nonzero odd vector.
example : occupied ≠ 0 := occupied_ne_zero
end NonVacuity.FactorClosures

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.SwappedAssembly.CentralInverse.FactorClosures
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Module not imported: {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "No owned declarations: {owner}"
  for name in names do
    for axiomName in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
  logInfo m!"Audited {names.size} owned declarations in {owner}: standard axioms only"
