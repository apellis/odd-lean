import OddMath.QuiverHecke.CyclotomicAction.ELVContentCoefficientMaps
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeExtensionRows
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.ELVOld OddMath.QuiverHecke.ELVOld.BalancedInduction
open OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
universe u
private theorem iso_total_nonzero
    {k C : Type u} [CommRing k] [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
    {F G : Superfunctor k C (SVec k)} (e : F ≅ G) (w : C) (v : F.obj w) (hv : v ≠ 0) :
    e.hom.total w v ≠ 0 := by
  intro hz
  exact hv ((moduleIsoLinearEquiv e w).injective
    (hz.trans (map_zero (moduleIsoLinearEquiv e w)).symm))

namespace NonVacuity.ELVContentCoefficientMaps
private abbrev D := CyclotomicAction.AsymmetricParameters.datum
private abbrev Sc := CyclotomicAction.AsymmetricParameters.scalars
private def m (i : Bool) : ℕ := if i then 2 else 1
private theorem positive (i : Bool) : 0 < probeCutoff D m i := by cases i <;> decide
private abbrev N := probeOldVacuumRegular D Sc m
private abbrev J := oldContentInclusion D Sc (probeCutoff D m) []
private abbrev L := induced J N
private abbrev s := probeOldVacuumObject D Sc m
private abbrev t := OldContentCategory.obj s
private theorem height (i : Bool) :
    0 ≤ contentCrossingHeight D (probeCutoff D m) i (([] : List Bool) : Multiset Bool) := by
  simp [contentCrossingHeight]
private def top (i : Bool) :
    Fin (contentUnitCount D (probeCutoff D m) i (([] : List Bool) : Multiset Bool)) :=
  ⟨probeCutoff D m i - 1, by rw [VacuumCoefficient.count]; have hp := positive i; omega⟩
private abbrev V (i : Bool) := mateTargetSpace D Sc (probeCutoff D m) i L t

/-- A genuine inverse-row module morphism has a nonzero component
on the prescribed regular probe extension, at both positive odd levels. -/
example (i : Bool) : ∃ z,
    (contentUnitCoefficientMap D Sc (probeCutoff D m) L i [] (height i) (top i)).total s z ≠ 0 := by
  let e := oldContentExtensionUnitIso D Sc (probeCutoff D m) [] N
  have hv : e.hom.total s (probeOldVacuumVector D Sc m) ≠ 0 :=
    iso_total_nonzero e s _ (probeOldVacuumVector_ne_zero D Sc m)
  obtain ⟨z, hz⟩ := contentUnitCoefficientMap_total_surjective D Sc (probeCutoff D m) L i []
    (height i) (top i) s (e.hom.total s (probeOldVacuumVector D Sc m))
  exact ⟨z, hz ▸ hv⟩

example (i : Bool)
    (z : mateTargetSpace D Sc (probeCutoff D m) i L (⟨[]⟩ : OldCategory D Sc (probeCutoff D m))) :
    (contentUnitCoefficientMap D Sc (probeCutoff D m) L i [] (height i) (top i)).total
      (⟨⟨[]⟩, List.Perm.refl _⟩ : OldContentCategory D Sc (probeCutoff D m) []) z =
    TensorMatrixCoordinates.moduleUnitCoefficient D Sc (probeCutoff D m) L i ⟨[]⟩
      (height i) (top i) z :=
  contentUnitCoefficientMap_vacuum_total D Sc (probeCutoff D m) L i (height i) (top i) z

example (i : Bool) :
    contentUnitCoefficientMap D Sc (probeCutoff D m) L i [] (height i) (top i) ∈
      parity (R := ℚ) _ _ ((top i).val • D.parity i) :=
  contentUnitCoefficientMap_mem D Sc (probeCutoff D m) L i [] (height i) (top i)

end NonVacuity.ELVContentCoefficientMaps

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVContentCoefficientMaps
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Module not imported: {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "No owned declarations: {owner}"
  for name in names do
    for axiomName in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
  logInfo m!"Audited {names.size} owned declarations in {owner}: standard axioms only"
