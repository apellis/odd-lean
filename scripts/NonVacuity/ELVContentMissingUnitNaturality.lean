import OddMath.QuiverHecke.CyclotomicAction.ELVContentMissingUnitNaturality
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeVacuumVector
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.ELVOld OddMath.QuiverHecke.ELVOld.BalancedInduction
open OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
namespace NonVacuity.ContentMissingUnitNaturality
private theorem identity_ne_zero_of_vector
    {k C : Type} [CommRing k] [Category.{0} C] [Preadditive C] [Linear k C] [Supercategory k C]
    (M : Superfunctor k C (SVec k)) (s : C) (b : M.obj s) (hb : b ≠ 0) : (𝟙 s : s ⟶ s) ≠ 0 := by
  intro h
  have hi : M.map (𝟙 s) = 𝟙 (M.obj s) := M.toFunctor.map_id s
  have hz : M.map (0 : s ⟶ s) = 0 := M.toFunctor.map_zero s s
  have he := congrArg (fun f => M.map f b) h
  rw [hi, hz, SVec.id_apply, SVec.zero_apply] at he
  exact hb he
private theorem iso_hom_nonzero_of_value
    {k C : Type} [CommRing k] [Category.{0} C] [Preadditive C] [Linear k C] [Supercategory k C]
    {F G : Superfunctor k C (SVec k)} (e : F ≅ G) (w : C) (b : G.obj w) (hb : b ≠ 0) : e.hom ≠ 0 := by
  intro h
  have hi := e.inv_hom_id
  rw [h, Limits.comp_zero] at hi
  have he := congrArg (fun f : G ⟶ G => f.total w b) hi
  have hid : (𝟙 G : G ⟶ G).total w = 𝟙 (G.obj w) := SuperNatTrans.id_total G.toFunctor w
  rw [hid, SVec.id_apply] at he
  simp only [SuperNatTrans.total, Superfunctor.zero_app, zero_add, SVec.zero_apply] at he
  exact hb he.symm
private abbrev D := WeightedAppendFixture.datum
private abbrev Sc := WeightedAppendFixture.scalars
private def m (i : Bool) : ℕ := if i then 2 else 3
private abbrev cut := probeCutoff D m
private abbrev w : OldContentCategory D Sc cut [] :=
  OldContentCategory.mk (OldCategory.mk []) (List.Perm.refl [])
private def N := (restriction (oldContentInclusion D Sc cut [])).obj
  (oldRepresentable D Sc cut (OldCategory.mk []))
private def ground : N.obj w := 𝟙 (OldCategory.mk [] : OldCategory D Sc cut)
private theorem ground_ne_zero : ground ≠ 0 := by
  exact identity_ne_zero_of_vector (probeOldVacuumRegular D Sc m) w
    (probeOldVacuumVector D Sc m) (probeOldVacuumVector_ne_zero D Sc m)
local instance missingInverseInputPi :
    PiSupercategory ℚ (Superfunctor ℚ (OldContentCategory D Sc cut []) (SVec ℚ)) := supermodulePiSupercategory
/-- The odd input map is an actual nonzero canonical parity comparison. -/
example : ((SKM.homParityShiftDatum (k := ℚ) 1).iso N).hom ≠ 0 :=
  iso_hom_nonzero_of_value ((SKM.homParityShiftDatum (k := ℚ) 1).iso N) w ground ground_ne_zero
/-- All finite rows retain their signed naturality on this actual odd input map. -/
example (i : Bool) (r : Fin (contentUnitCount D cut i (0 : Multiset Bool))) :=
  (contentMissingUnitRow_supernatural D Sc cut [] i (by simp) r).naturality
    ((SKM.homParityShiftDatum (k := ℚ) 1).hom_mem N)
/-- Even identity input maps are also covered by the same constructed family. -/
example (i : Bool) (r : Fin (contentUnitCount D cut i (0 : Multiset Bool))) :=
  (contentMissingUnitRow_supernatural D Sc cut [] i (by simp) r).naturality (id_mem N)
example (i : Bool) (r : Fin (contentUnitCount D cut i (0 : Multiset Bool))) :=
  contentMissingUnitRowTransformation_total D Sc cut [] i (by simp) r N
private def oddTop : Fin (contentUnitCount D cut true (0 : Multiset Bool)) := ⟨3, by decide⟩
/-- At the odd top row and odd input map the prescribed sign is explicitly minus. -/
example :
    (induction (oldContentAppend D Sc cut [] true) ⋙ restriction (oldContentAppend D Sc cut [] true)).map
        ((SKM.homParityShiftDatum (k := ℚ) 1).iso N).hom ≫
      contentMissingUnitRow D Sc cut [] true (by simp) N oddTop =
    -(contentMissingUnitRow D Sc cut [] true (by simp)
        ((SKM.homParityShift (k := ℚ) 1).obj N) oddTop ≫
      ((SKM.homParityShiftDatum (k := ℚ) 1).iso N).hom) := by
  have h := (contentMissingUnitRow_supernatural D Sc cut [] true (by simp) oddTop).naturality
    ((SKM.homParityShiftDatum (k := ℚ) 1).hom_mem N)
  have hp : (oddTop.val • D.parity true) * (1 : ZMod 2) = 1 := by decide
  simpa only [hp, Supercategory.sign_one, neg_one_smul, CategoryTheory.Functor.id_map, Preadditive.neg_comp] using h
end NonVacuity.ContentMissingUnitNaturality
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for owner in #[`OddMath.QuiverHecke.CyclotomicAction.ELVInductionUnitInverseNaturality,
      `OddMath.QuiverHecke.CyclotomicAction.ELVContentMissingUnitNaturality] do
    let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
    let names := env.header.moduleData[idx]!.constNames
    if names.isEmpty then throwError "Empty owner {owner}"
    for name in names do
      for ax in ← Lean.collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {name}"
    logInfo m!"Audited all {names.size} owned declarations in {owner}"
