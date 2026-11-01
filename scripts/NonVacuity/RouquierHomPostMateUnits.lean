import OddMath.SKM.RouquierHomPostMateUnits
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightSuperAdjunction
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import StringDiagrams.Super.PiTwo
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath.SKM OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction
namespace NonVacuity.RouquierHomPostMateUnits

private abbrev D := AsymmetricParameters.datum
private abbrev Sc := AsymmetricParameters.scalars
private abbrev X := Bool → ℤ
private theorem step : (0 : X) + D.α false = D.α false := zero_add _
private abbrev P := elvE D Sc (fun _ => 12) 12 false (0 : X) step
private abbrev Q := elvF D Sc (fun _ => 12) 12 false (0 : X) step
private abbrev V := elvWeightSpace D Sc (fun _ => 12) 12 (0 : X) (D.α false)
private abbrev E : V ⟶ V := 𝟙 V
private abbrev H : V ⟶ V := 𝟙 V
private abbrev adj := elvActionAdjunction D Sc (fun _ => 12) 12 false (0 : X) step

local instance homPi {A B : PiSCat.{0, 0, 1} ℚ} : PiSupercategory ℚ (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B

private abbrev target := E ≫ (homParityShift (k := ℚ) 1).obj
  (((homParityShift (k := ℚ) 1).obj H ≫ Q) ≫ P)
private abbrev source := E ≫ ((homParityShift (k := ℚ) 1).obj H ≫ Q)

private theorem target_pre :
    mixedPostTargetPreDot (k := ℚ) E 1 H (E' := P) (F' := Q) (𝟙 E) =
      (1 : End target) :=
  (homPost (k := ℚ) _).map_id E

private theorem target_post :
    mixedPostTargetPostDot (k := ℚ) E 1 H (F' := Q) (0 : P ⟶ P) = 0 := by
  rw [mixedPostTargetPostDot, whiskerLeft_zero' (k := ℚ),
    (homParityShift (k := ℚ) (C := V ⟶ V) 1).map_zero, whiskerLeft_zero' (k := ℚ)]

private theorem source_post :
    mixedPostSourcePostDot (k := ℚ) E 1 H adj (0 : P ⟶ P) = 0 := by
  have hz : SuperAdjunction.rightTranspose adj adj (0 : P ⟶ P) = 0 :=
    (SuperAdjunction.rightTransposeLinear adj adj).map_zero
  rw [mixedPostSourcePostDot, hz, whiskerLeft_zero' (k := ℚ), whiskerLeft_zero' (k := ℚ)]

/-- A nonidentity crossing on the actual asymmetric ELV adjunction,
with both parity shifts nontrivial, satisfies the explicit source-unit criterion. -/
example : IsIso (homDistinctMixedMateDot E adj 1 1 H (-1 : End target)) := by
  have hL : IsUnit ((mixedPostSourcePreDot (k := ℚ) E 1 H (F' := Q) (𝟙 E) -
      mixedPostSourcePostDot (k := ℚ) E 1 H adj (0 : P ⟶ P)) ^ 2 : End source) := by
    rw [source_post, sub_zero]
    exact ((isUnit_one : IsUnit (1 : End E)).map ((homPost (k := ℚ) _).mapEnd E)).pow 2
  apply homDistinctMixedMateDot_isIso_of_square_sub_units E adj 1 1 H
    (id_mem E) (zero_mem _) (-1 : End target)
    ((Commute.one_left _).neg_left) ((Commute.one_left _).neg_left)
    (-1 : ℚ) 0 0
  · rw [target_pre, target_post, sub_zero, one_pow, pow_zero,
      zero_smul, add_zero, neg_one_smul]
    exact Category.id_comp _
  · exact hL
  · simpa using (isUnit_one : IsUnit (1 : End source)).neg

end NonVacuity.RouquierHomPostMateUnits

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.SKM.RouquierHomPostMateUnits
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Module was not imported: {owner}"
  let names := env.header.moduleData[idx]!.constNames
  unless names.size > 0 do throwError "Empty owned declaration inventory"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited ALL {names.size} owned declarations, including private/generated"

