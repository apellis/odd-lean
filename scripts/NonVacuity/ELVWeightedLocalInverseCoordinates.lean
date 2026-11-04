import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedLocalInverseCoordinates
import NonVacuity.ELVWeightedAppendFixture
import OddMath.QuiverHecke.CyclotomicAction.ELVTruncatedDetection
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory Opposite StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.ELVOld
namespace WeightedLocalInverseCoordinateConsumer
private def D : SKM.Datum Bool (Bool → ℤ) := WeightedAppendFixture.datum
private def Sc : SKM.Scalars D ℚ := WeightedAppendFixture.scalars
private abbrev cut : Bool → ℕ := fun _ => 8
private abbrev Q := oldTruncateFunctor D Sc cut 8
private abbrev s : OldCategory D Sc cut := ⟨[false, true]⟩
private def M : Superfunctor ℚ (TruncatedCategory D Sc cut 8) (SVec ℚ) :=
  WeightedAppendFixture.truncatedRepresentable D Sc cut 8 (Q.obj s)
private abbrev J (i : Bool) := CyclotomicCrossingTensor.append D Sc cut i

private abbrev T (i : Bool) := truncatedAppend D Sc cut 8 [i]
private theorem hDot (i : Bool) : IsSupernatural ℚ (D.parity i)
    (truncatedAppendComponent D Sc cut 8 (dotE D Sc [i] 0)) :=
  truncatedAppendComponent_supernatural D Sc cut 8 (by
    simpa only [pow_one, one_nsmul] using firstDot_pow_parity D Sc i [] 1)

private theorem positive (i : Bool) :
    0 ≤ CyclotomicCrossingTensor.contentCrossingHeight D cut i (s.word : Multiset Bool) := by
  cases i <;> decide
example (i : Bool) := weightedContentLocalInverseFrom_principal_total D Sc cut 8 i M
  (s.word : Multiset Bool) (positive i) ⟨Q.obj s,rfl⟩
example (i : Bool) := weightedUnitInverse_coordinates D Sc cut 8 i M s (positive i)
example (i : Bool) := weightedUnitInverse_none D Sc cut 8 i M s (positive i)
example (i : Bool) := weightedContentUnitInverse_atWord D Sc cut 8 i M s (positive i)
example (i : Bool) := weightedContentUnitInverse_component D Sc cut 8 i M
  (s.word : Multiset Bool) (positive i) ⟨Q.obj s,rfl⟩
example (i : Bool) := weightedUnitPrincipalInverseValue_tensor D Sc cut 8 i M s (positive i)
  s (𝟙 _) (𝟙 (Q.obj s))
example : CyclotomicCrossingTensor.contentUnitCount D cut false (s.word : Multiset Bool) = 8 := by decide
example : CyclotomicCrossingTensor.contentUnitCount D cut true (s.word : Multiset Bool) = 10 := by decide

private abbrev cutOne : Bool → ℕ := fun _ => 1
private abbrev Qone := oldTruncateFunctor D Sc cutOne 4
private abbrev oneWord (i : Bool) : OldCategory D Sc cutOne := ⟨[i]⟩
private def oneModule (i : Bool) : Superfunctor ℚ (TruncatedCategory D Sc cutOne 4) (SVec ℚ) :=
  WeightedAppendFixture.truncatedRepresentable D Sc cutOne 4 (Qone.obj (oneWord i))
private theorem negative (i : Bool) :
    CyclotomicCrossingTensor.contentCrossingHeight D cutOne i ((oneWord i).word : Multiset Bool) ≤ 0 := by
  cases i <;> decide
example (i : Bool) := weightedContentLocalInverseTo_principal_total D Sc cutOne 4 i (oneModule i)
  ((oneWord i).word : Multiset Bool) (negative i) ⟨Qone.obj (oneWord i),rfl⟩
example (i : Bool) := weightedCapInverse_coordinates D Sc cutOne 4 i (oneModule i)
  (oneWord i) (negative i)
example (i : Bool) := weightedContentCapInverse_atWord D Sc cutOne 4 i (oneModule i)
  (oneWord i) (negative i)
example (i : Bool) := weightedContentCapInverse_component D Sc cutOne 4 i (oneModule i)
  ((oneWord i).word : Multiset Bool) (negative i) ⟨Qone.obj (oneWord i),rfl⟩
example (i : Bool) := weightedCapPrincipalInverseValue_tensor D Sc cutOne 4 i (oneModule i)
  (oneWord i) (negative i) (oneWord i) (𝟙 _) (𝟙 (Qone.obj (oneWord i)))
example (i : Bool) : CyclotomicCrossingTensor.contentCapCount D cutOne i ((oneWord i).word : Multiset Bool) = 1 := by
  cases i <;> decide

private abbrev cutTwo : Bool → ℕ := fun _ => 2
private abbrev Qtwo := oldTruncateFunctor D Sc cutTwo 4
private abbrev zeroWord (i : Bool) : OldCategory D Sc cutTwo := ⟨[i]⟩
private def zeroModule (i : Bool) : Superfunctor ℚ (TruncatedCategory D Sc cutTwo 4) (SVec ℚ) :=
  WeightedAppendFixture.truncatedRepresentable D Sc cutTwo 4 (Qtwo.obj (zeroWord i))
private theorem zero_positive (i : Bool) :
    0 ≤ CyclotomicCrossingTensor.contentCrossingHeight D cutTwo i ((zeroWord i).word : Multiset Bool) := by
  cases i <;> decide
private theorem zero_negative (i : Bool) :
    CyclotomicCrossingTensor.contentCrossingHeight D cutTwo i ((zeroWord i).word : Multiset Bool) ≤ 0 := by
  cases i <;> decide
example (i : Bool) := weightedContentLocalInverseFrom_principal_total D Sc cutTwo 4 i (zeroModule i)
  ((zeroWord i).word : Multiset Bool) (zero_positive i) ⟨Qtwo.obj (zeroWord i),rfl⟩
example (i : Bool) := weightedContentLocalInverseTo_principal_total D Sc cutTwo 4 i (zeroModule i)
  ((zeroWord i).word : Multiset Bool) (zero_negative i) ⟨Qtwo.obj (zeroWord i),rfl⟩
example (i : Bool) := weightedContentUnitInverse_atWord D Sc cutTwo 4 i (zeroModule i) (zeroWord i) (zero_positive i)
example (i : Bool) := weightedContentCapInverse_atWord D Sc cutTwo 4 i (zeroModule i) (zeroWord i) (zero_negative i)
example (i : Bool) : CyclotomicCrossingTensor.contentUnitCount D cutTwo i ((zeroWord i).word : Multiset Bool) = 0 := by
  cases i <;> decide
example (i : Bool) : CyclotomicCrossingTensor.contentCapCount D cutTwo i ((zeroWord i).word : Multiset Bool) = 0 := by
  cases i <;> decide

private abbrev vacuum : OldCategory D Sc cut := ⟨[]⟩
private def vacuumModule : Superfunctor ℚ (TruncatedCategory D Sc cut 8) (SVec ℚ) :=
  WeightedAppendFixture.truncatedRepresentable D Sc cut 8 (Q.obj vacuum)
private theorem vacuum_positive (i : Bool) :
    0 ≤ CyclotomicCrossingTensor.contentCrossingHeight D cut i (vacuum.word : Multiset Bool) := by
  cases i <;> decide
example (i : Bool) := weightedContentUnitInverse_atWord D Sc cut 8 i vacuumModule vacuum (vacuum_positive i)
example (i : Bool) := weightedUnitPrincipalInverseValue_tensor D Sc cut 8 i vacuumModule vacuum (vacuum_positive i) vacuum (𝟙 _) (𝟙 (Q.obj vacuum))
example : D.parity true = 1 := by decide
example : D.parity false = 0 := by decide
private def O : SKM.Datum Unit ℤ where
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
private def Os : SKM.Scalars O ℚ where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := fun _ => isUnit_iff_ne_zero.mpr (by norm_num)
private abbrev Oc : Unit → ℕ := fun _ => 2
private abbrev Ov : OldCategory O Os Oc := ⟨[]⟩
private abbrev OQ := oldTruncateFunctor O Os Oc 3
private abbrev Ot := OQ.obj Ov
private abbrev OT := truncatedAppend O Os Oc 3 [()]
private abbrev OM := WeightedAppendFixture.truncatedRepresentable O Os Oc 3 Ot
private abbrev ORM := weightedRestriction O Os Oc 3 OM
private theorem Opositive : 0 ≤ CyclotomicCrossingTensor.contentCrossingHeight O Oc ()
    (Ov.word : Multiset Unit) := by decide
private theorem occupied_identity : (𝟙 Ot : Ot ⟶ Ot) ≠ 0 := by
  have hz := truncatedSingle_delta_ne_zero O Os rfl
  have hs : (𝟙 (OT.obj Ot) : OT.obj Ot ⟶ OT.obj Ot) ≠ 0 := by
    intro h
    apply hz
    calc
      _ = (𝟙 (OT.obj Ot)) ≫ truncatedSingle O Os Oc 3 ()
        (SKM.SYM.delta O ℚ ⟨(),rfl⟩) 0 := (Category.id_comp _).symm
      _ = 0 := by rw [h, Limits.zero_comp]
  intro h
  apply hs
  calc
    𝟙 (OT.obj Ot) = OT.map (𝟙 Ot) := (CategoryTheory.Functor.map_id OT Ot).symm
    _ = 0 := by rw [h, CategoryTheory.Functor.map_zero]
private def oldPoint : CyclotomicCrossingTensor.unitMatrixSourceSpace O Os Oc () ORM
    (CyclotomicCrossingTensor.contentUnitCount O Oc () (Ov.word : Multiset Unit)) Ov :=
  Pi.single (some ⟨0,by decide⟩) (𝟙 Ot)
private theorem oldPoint_nonzero : oldPoint ≠ 0 := by
  intro h
  have he : oldPoint (some ⟨0,by decide⟩) = 0 := by rw [h]; rfl
  have hi : (𝟙 Ot : Ot ⟶ Ot) = 0 := by
    simpa only [oldPoint, Pi.single_eq_same] using he
  exact occupied_identity hi
private abbrev chart := weightedUnitMatrixValueEquiv O Os Oc 3 () OM
  (CyclotomicCrossingTensor.contentUnitCount O Oc () (Ov.word : Multiset Unit)) Ov
private def weightedPoint := chart oldPoint
private theorem weightedPoint_nonzero : weightedPoint ≠ 0 := by
  intro hz
  exact oldPoint_nonzero (chart.map_eq_zero_iff.mp hz)
/-- An actual weighted inverse has an independently detected nonzero value. -/
example : (weightedUnitMatrixComponentIso O Os Oc 3 () OM Ov Opositive).inv
    ((weightedUnitMatrixComponentIso O Os Oc 3 () OM Ov Opositive).hom weightedPoint) ≠ 0 := by
  have hi := congrArg (fun f => f weightedPoint)
    (weightedUnitMatrixComponentIso O Os Oc 3 () OM Ov Opositive).hom_inv_id
  intro h
  have hp : weightedPoint = 0 := by
    simpa only [SVec.comp_apply, SVec.id_apply] using hi.symm.trans h
  exact weightedPoint_nonzero hp

-- This application is occupied by the preceding identity detection.
example : weightedPoint ≠ 0 := weightedPoint_nonzero
end WeightedLocalInverseCoordinateConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVWeightedLocalInverseCoordinates
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"
