import OddMath.QuiverHecke.CyclotomicAction.ELVUnitCoefficientRows
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
open ELVOld.CyclotomicCrossingTensor ELVOld.CyclotomicCrossingTensor.TensorMatrixCoordinates
open CyclotomicAction.AsymmetricParameters
namespace NonVacuity.ELVUnitCoefficientRows

private def mixedDatum : SKM.Datum Bool (Bool → ℤ) :=
  { datum with
    parity := fun i => if i then 1 else 0
    even_of_odd := fun i j _ => datum.even_of_odd i j rfl }
private def mixedScalars : SKM.Scalars mixedDatum ℚ where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := by intro _; norm_num

private def cutoff (_ : Bool) : ℕ := 2
private abbrev C := OldCategory mixedDatum mixedScalars cutoff
private def emptyWord : C := ⟨[]⟩
private def vacuum := oldRepresentable mixedDatum mixedScalars cutoff emptyWord

private theorem height (i : Bool) :
    0 ≤ contentCrossingHeight mixedDatum cutoff i (emptyWord.word : Multiset Bool) := by
  simp [contentCrossingHeight, emptyWord, cutoff]
private theorem count (i : Bool) :
    contentUnitCount mixedDatum cutoff i (emptyWord.word : Multiset Bool) = 2 := by
  simp [contentUnitCount, contentCrossingHeight, emptyWord, cutoff]
private def lowSlot (i : Bool) :
    Fin (contentUnitCount mixedDatum cutoff i (emptyWord.word : Multiset Bool)) :=
  ⟨0, by rw [count]; decide⟩
private def topSlot (i : Bool) :
    Fin (contentUnitCount mixedDatum cutoff i (emptyWord.word : Multiset Bool)) :=
  ⟨1, by rw [count]; decide⟩

/-- Both moving parities extract the literal top ordinary unit/dot column
at the vacuum representable, retaining its canonical source shift. -/
example (i : Bool) (z : vacuum.obj emptyWord) :
    moduleUnitCoefficient mixedDatum mixedScalars cutoff vacuum i emptyWord (height i) (topSlot i)
      ((moduleUnitColumn mixedDatum mixedScalars cutoff i vacuum (topSlot i).val).total
        emptyWord z) = z :=
  moduleUnitCoefficient_column mixedDatum mixedScalars cutoff vacuum i emptyWord (height i)
    (topSlot i) z

example (i : Bool) (z : vacuum.obj emptyWord) :
    moduleUnitCoefficient mixedDatum mixedScalars cutoff vacuum i emptyWord (height i) (topSlot i)
      ((moduleUnitColumn mixedDatum mixedScalars cutoff i vacuum (lowSlot i).val).total
        emptyWord z) = 0 := by
  exact moduleUnitCoefficient_column_ne mixedDatum mixedScalars cutoff vacuum i emptyWord (height i)
    (topSlot i) (lowSlot i) (by intro h; have hv : (1 : ℕ) = 0 := congrArg Fin.val h; exact Nat.one_ne_zero hv) z

/-- The literal shifted extraction coordinate is even before removing its
selected parity comparison. -/
example (i : Bool) :
    moduleUnitCoefficientRow mixedDatum mixedScalars cutoff vacuum i emptyWord (height i)
      (some (topSlot i)) ∈ parity (R := ℚ)
        (mateTargetSpace mixedDatum mixedScalars cutoff i vacuum emptyWord)
        ((unitMatrixFamily mixedDatum mixedScalars cutoff i vacuum
          (contentUnitCount mixedDatum cutoff i (emptyWord.word : Multiset Bool))
          (some (topSlot i))).obj emptyWord) 0 :=
  moduleUnitCoefficientRow_even mixedDatum mixedScalars cutoff vacuum i emptyWord (height i) _

/-- Removing the top shift retains the prescribed odd/even functional parity. -/
example (i : Bool) :
    moduleUnitCoefficient mixedDatum mixedScalars cutoff vacuum i emptyWord (height i) (topSlot i) ∈
      parity (R := ℚ) (mateTargetSpace mixedDatum mixedScalars cutoff i vacuum emptyWord)
        (vacuum.obj emptyWord) (mixedDatum.parity i) := by
  simpa only [topSlot, one_nsmul] using
    moduleUnitCoefficient_mem mixedDatum mixedScalars cutoff vacuum i emptyWord (height i) (topSlot i)

private def oddIndex : SKM.SYM.CoefficientIndex mixedDatum :=
  (0, {⟨true, rfl⟩})
private def oddCoefficient : emptyWord ⟶ emptyWord :=
  (ideal mixedDatum mixedScalars cutoff [] []).mkQ
    (coefficientIdentity mixedDatum mixedScalars cutoff []
      (SKM.SYM.coefficientBasis mixedDatum ℚ oddIndex))
private theorem oddCoefficient_mem : oddCoefficient ∈ parity (R := ℚ) emptyWord emptyWord 1 := by
  have hp : coefficientIdentity mixedDatum mixedScalars cutoff []
      (SKM.SYM.coefficientBasis mixedDatum ℚ oddIndex) ∈
      parity (R := ℚ) (obj mixedDatum mixedScalars cutoff [])
        (obj mixedDatum mixedScalars cutoff []) 1 := by
    simpa only [oddIndex, Finset.card_singleton, Nat.cast_one] using
      coefficientIdentity_basis_parity mixedDatum mixedScalars cutoff [] oddIndex
  change (ideal mixedDatum mixedScalars cutoff [] []).mkQ
    (coefficientIdentity mixedDatum mixedScalars cutoff []
      (SKM.SYM.coefficientBasis mixedDatum ℚ oddIndex)) ∈
        oldParity mixedDatum mixedScalars cutoff [] [] 1
  exact Submodule.mem_map_of_mem hp

/-- A literal full-coefficient old endomorphism supplies the odd
superlinearity check on the selected top row. -/
example :
    (moduleUnitCoefficient mixedDatum mixedScalars cutoff vacuum true emptyWord (height true)
      (topSlot true)).comp
      (SVec.toLinearMap (((BalancedInduction.restriction (append mixedDatum mixedScalars cutoff true)).obj
        ((BalancedInduction.induction (append mixedDatum mixedScalars cutoff true)).obj vacuum)).map
          oddCoefficient)) =
      -((SVec.toLinearMap (vacuum.map oddCoefficient)).comp
        (moduleUnitCoefficient mixedDatum mixedScalars cutoff vacuum true emptyWord (height true)
          (topSlot true))) := by
  have hs : (topSlot true).val • mixedDatum.parity true = (1 : ZMod 2) := rfl
  simpa only [hs, koszulSign_one_one, neg_smul, one_smul] using
    moduleUnitCoefficient_end_naturality mixedDatum mixedScalars cutoff vacuum true emptyWord
      (height true) (topSlot true) oddCoefficient oddCoefficient_mem

/-- The actual empty-word representable has no append-restriction source. -/
example (i : Bool) (t : C)
    (z : mateSourceSpace mixedDatum mixedScalars cutoff i
      (VacuumCoefficient.coefficientModule mixedDatum mixedScalars cutoff) t) : z = 0 :=
  VacuumCoefficient.indRes_eq_zero mixedDatum mixedScalars cutoff i t z

/-- The constructed vacuum functional kills the undotted unit and is 1 on
the first signed dot at cutoff two, for both moving parities. -/
example (i : Bool)
    (z : (VacuumCoefficient.coefficientModule mixedDatum mixedScalars cutoff).obj
      (⟨[]⟩ : C)) :
    VacuumCoefficient.functional mixedDatum mixedScalars cutoff i (by simp [cutoff])
      ((((BalancedInduction.adjunction (append mixedDatum mixedScalars cutoff i)).unit.app
        (VacuumCoefficient.coefficientModule mixedDatum mixedScalars cutoff)).total ⟨[]⟩) z) = 0 := by
  have h := VacuumCoefficient.functional_dot_window mixedDatum mixedScalars cutoff i
    (by change 0 < 2; decide) 0 (by change 0 < 2; decide) z
  have hz : (0 + 1 : ℕ) ≠ cutoff i := by change (1 : ℕ) ≠ 2; decide
  rw [ite_eq_right hz] at h
  simpa only [pow_zero, Module.End.one_apply] using h

example (i : Bool) :
    VacuumCoefficient.functional mixedDatum mixedScalars cutoff i (by simp [cutoff]) ∈
      parity (R := ℚ)
        (mateTargetSpace mixedDatum mixedScalars cutoff i
          (VacuumCoefficient.coefficientModule mixedDatum mixedScalars cutoff) ⟨[]⟩)
        ((VacuumCoefficient.coefficientModule mixedDatum mixedScalars cutoff).obj ⟨[]⟩)
        (mixedDatum.parity i) := by
  have hs : (cutoff i - 1) • mixedDatum.parity i = mixedDatum.parity i := by
    change 1 • mixedDatum.parity i = mixedDatum.parity i
    exact one_nsmul _
  simpa only [hs] using
    VacuumCoefficient.functional_mem mixedDatum mixedScalars cutoff i (by change 0 < 2; decide)

/-- At zero finite count the first inverse row still extracts the mate
coordinate; no finite slot or inhabited lower-content corner is assumed. -/
example (i : Bool) :
    let c0 := fun _ : Bool => 0
    let t : OldCategory mixedDatum mixedScalars c0 := ⟨[]⟩
    let M := oldRepresentable mixedDatum mixedScalars c0 t
    ∀ z : (unitMatrixFamily mixedDatum mixedScalars c0 i M
      (contentUnitCount mixedDatum c0 i (t.word : Multiset Bool)) none).obj t,
      moduleUnitCoefficientRow mixedDatum mixedScalars c0 M i t
        (by simp [contentCrossingHeight, t, c0]) none
        ((unitMatrixEntry mixedDatum mixedScalars c0 i M
          (contentUnitCount mixedDatum c0 i (t.word : Multiset Bool)) none).total t z) = z := by
  dsimp only
  intro z
  exact moduleUnitCoefficientRow_entry _ _ _ _ _ _ _ _ z

end NonVacuity.ELVUnitCoefficientRows

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let some idx := env.header.moduleNames.idxOf?
      `OddMath.QuiverHecke.CyclotomicAction.ELVUnitCoefficientRows | throwError "Module not imported"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "No owned declarations"
  for name in names do
    for axiomName in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
  logInfo m!"Audited {names.size} owned declarations: standard axioms only"
