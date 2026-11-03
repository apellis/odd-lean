import OddMath.QuiverHecke.CyclotomicAction.ELVContentMissingUnitModules
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeVacuumVector
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.ELVOld OddMath.QuiverHecke.ELVOld.BalancedInduction
open OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
namespace NonVacuity.ContentMissingUnitModules
private theorem identity_ne_zero_of_vector
    {k C : Type} [CommRing k] [Category.{0} C] [Preadditive C] [Linear k C] [Supercategory k C]
    (M : Superfunctor k C (SVec k)) (s : C) (b : M.obj s) (hb : b ≠ 0) : (𝟙 s : s ⟶ s) ≠ 0 := by
  intro h
  have hi : M.map (𝟙 s) = 𝟙 (M.obj s) := M.toFunctor.map_id s
  have hz : M.map (0 : s ⟶ s) = 0 := M.toFunctor.map_zero s s
  have he := congrArg (fun f => M.map f b) h
  rw [hi, hz, SVec.id_apply, SVec.zero_apply] at he
  exact hb he
private theorem moduleIso_hom_nonzero
    {k C : Type} [CommRing k] [Category.{0} C] [Preadditive C] [Linear k C] [Supercategory k C]
    {F G : Superfunctor k C (SVec k)} (e : F ≅ G) (w : C) (x : F.obj w) (hx : x ≠ 0) :
    e.hom.total w x ≠ 0 := by
  intro h
  have he := congrArg (fun f : F ⟶ F => f.total w x) e.hom_inv_id
  rw [Superfunctor.comp_total, SVec.comp_apply, h, map_zero] at he
  have hi : (𝟙 F : F ⟶ F).total w = 𝟙 (F.obj w) := SuperNatTrans.id_total F.toFunctor w
  rw [hi, SVec.id_apply] at he
  exact hx he.symm
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
private def chosen (i : Bool) := contentMissingUnitModuleIso D Sc cut [] i (by simp) N
private def first (i : Bool) : Fin (contentUnitCount D cut i (0 : Multiset Bool)) :=
  ⟨0, by cases i <;> decide⟩
private def source (i : Bool) :
    (OddMath.FiniteSupermodule.product (unitColumnModuleFamily (D.parity i) N
      (contentUnitCount D cut i (0 : Multiset Bool)))).obj w :=
  Pi.single (first i) ground
private theorem source_ne_zero (i : Bool) : source i ≠ 0 := by
  intro h
  have he := congrFun h (first i)
  simp only [source, Pi.single_eq_same] at he
  exact ground_ne_zero he
/-- Both moving parities retain occupied full-old coefficient module values. -/
example (i : Bool) : (chosen i).hom.total w (source i) ≠ 0 :=
  moduleIso_hom_nonzero (chosen i) w (source i) (source_ne_zero i)
example (i : Bool) := (chosen i).hom_inv_id
example (i : Bool) := (chosen i).inv_hom_id
example (i : Bool) := contentMissingUnitModuleIso_hom D Sc cut [] i (by simp) N
example (i : Bool) := contentMissingUnitModuleIso_inv_mem D Sc cut [] i (by simp) N
/-- Cutoff zero is covered by the same specified finite matrix. -/
example (i : Bool) (M : Superfunctor ℚ (OldContentCategory D Sc (fun _ => 0) []) (SVec ℚ))
    := (contentMissingUnitModuleIso D Sc (fun _ => 0) [] i (by simp) M).hom_inv_id
end NonVacuity.ContentMissingUnitModules
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for owner in #[`OddMath.QuiverHecke.CyclotomicAction.ELVInductionUnitColumnModules,
      `OddMath.QuiverHecke.CyclotomicAction.ELVContentMissingUnitModules] do
    let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
    let names := env.header.moduleData[idx]!.constNames
    if names.isEmpty then throwError "Empty owner {owner}"
    for name in names do
      for ax in ← Lean.collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {name}"
    logInfo m!"Audited all {names.size} owned declarations in {owner}"
