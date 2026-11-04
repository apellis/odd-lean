import NonVacuity.ELVWeightedAppendFixture
import OddMath.QuiverHecke.CyclotomicAction.ELVAbsentWindowInverseCoordinates
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightCentreBlocks
import OddMath.QuiverHecke.CyclotomicAction.ELVReservoirBoundaries
import OddMath.QuiverHecke.CyclotomicAction.ELVTruncatedDetection
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath OddMath.QuiverHecke ELVOld
open OddMath.QuiverHecke.CyclotomicAction
namespace NonVacuity.ELVAbsentWindowInverseCoordinates
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
private theorem h₁ : (-4 : ℤ) + D.α () = -2 := by decide
private theorem h₂ : (-2 : ℤ) + D.α () = 0 := by decide
private def δ : WeightBlocks D Λ (-2) := ⟨0,by decide⟩
private def v : ContentCategory D Sc cutoff 3 δ.1 := ⟨⟨[]⟩,rfl⟩
private def R := contentRepresentable D Sc cutoff 3 δ.1 v
private def M : ELVWeightProduct D Sc cutoff 3 Λ (-2) :=
  (WeightCentreBlocks.extension D Sc cutoff 3 Λ δ).obj R
private theorem absent : ¬ ∃ β, blockSucc D Λ () h₁ β = δ := by
  intro h
  have hi := (exists_blockSucc_iff D Λ () h₁ δ).mp h
  simpa only [δ, Multiset.not_mem_zero] using hi

-- Both finite rows of the absent unit window are retained by the chosen inverse.
example (j : Fin (-D.h () (-2 : ℤ)).toNat) :=
  elvChosenAbsentUnitWindow_coordinates D Sc cutoff 3 Λ cutoff_match () h₁ h₂ M δ
    absent (by decide) j.val j.isLt
example (j : Fin (CyclotomicCrossingTensor.contentUnitCount D cutoff () δ.1)) :=
  contentAbsentUnitTargetInverse_window D Sc cutoff 3 δ.1
    (blockSucc D Λ () h₂ δ).1 () (elvBlockSucc_content_eq D () Λ h₂ δ) (M δ)
    (elvContentAbsentUnitInverseAtWeight D Sc cutoff 3 Λ () h₁ h₂ M δ absent)
    (by decide) j.val j.isLt
example : CyclotomicCrossingTensor.contentUnitCount D cutoff () δ.1 = 2 := by decide

private def strand : TruncatedCategory D Sc cutoff 3 := ⟨[()]⟩
private theorem strand_identity_ne_zero : (𝟙 strand : strand ⟶ strand) ≠ 0 := by
  have hz := truncatedSingle_delta_ne_zero D Sc rfl
  intro h
  apply hz
  calc
    _ = (𝟙 strand) ≫ truncatedSingle D Sc cutoff 3 () (SKM.SYM.delta D ℚ ⟨(),rfl⟩) 0 :=
      (Category.id_comp _).symm
    _ = 0 := by rw [h, Limits.zero_comp]
private theorem vacuum_identity_ne_zero : (𝟙 v : v ⟶ v) ≠ 0 := by
  intro h
  apply strand_identity_ne_zero
  have he := congrArg (truncatedAppend D Sc cutoff 3 [()]).map h
  simpa only [Functor.map_id, Functor.map_zero] using he
private def chart := moduleIsoLinearEquiv
  (eqToIso (WeightCentreBlocks.extension_obj D Sc cutoff 3 Λ δ R)) v
private def occupied : (M δ).obj v := chart.symm (𝟙 v)
private theorem occupied_ne_zero : occupied ≠ 0 := by
  intro h
  apply vacuum_identity_ne_zero
  have he := congrArg chart h
  simpa only [occupied, LinearEquiv.apply_symm_apply, map_zero] using he

-- The absent diagonal unit boundary is identity, so this branch cannot be discarded.
private theorem diagonal_boundary :
    ReservoirBoundaries.negative D Sc cutoff 3 Λ cutoff_match () h₁ h₂ (by decide) 0 0 =
      𝟙 (Superfunctor.id ℚ (ELVWeightProduct D Sc cutoff 3 Λ (-2))) :=
  ((elvRouquierFamily D Sc cutoff 3 Λ cutoff_match).loc () h₁ h₂).boundaryNeg_eq
    (by decide) 0 0 (by decide) (by decide)
example : occupied ≠ 0 := occupied_ne_zero
example :
    (((ReservoirBoundaries.negative D Sc cutoff 3 Λ cutoff_match () h₁ h₂ (by decide) 0 0).total M δ).total v)
      occupied ≠ 0 := by
  rw [diagonal_boundary]
  simpa only [SuperNatTrans.id_total, CategoryTheory.Pi.id_apply, SVec.id_apply] using occupied_ne_zero
end NonVacuity.ELVAbsentWindowInverseCoordinates

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVAbsentWindowInverseCoordinates
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Module not imported: {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "No owned declarations: {owner}"
  for name in names do
    for axiomName in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
  logInfo m!"Audited {names.size} owned declarations in {owner}: standard axioms only"
