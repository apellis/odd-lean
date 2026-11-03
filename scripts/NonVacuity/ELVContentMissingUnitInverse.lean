import OddMath.QuiverHecke.CyclotomicAction.ELVContentMissingUnitInverse
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeVacuumVector
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.ELVOld OddMath.QuiverHecke.ELVOld.BalancedInduction
open OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
namespace NonVacuity.ContentMissingUnitInverse
private theorem identity_ne_zero_of_vector
    {k C : Type} [CommRing k] [Category C] [Preadditive C] [Linear k C] [Supercategory k C]
    (M : Superfunctor k C (SVec k)) (s : C) (b : M.obj s) (hb : b ≠ 0) : (𝟙 s : s ⟶ s) ≠ 0 := by
  intro h
  have hi : M.map (𝟙 s) = 𝟙 (M.obj s) := M.toFunctor.map_id s
  have hz : M.map (0 : s ⟶ s) = 0 := M.toFunctor.map_zero s s
  have he := congrArg (fun f => M.map f b) h
  rw [hi, hz, SVec.id_apply, SVec.zero_apply] at he
  exact hb he
private theorem iso_hom_nonzero {k : Type} [CommRing k] {V W : SVec k}
    (e : V ≅ W) (x : V) (hx : x ≠ 0) : e.hom x ≠ 0 := by
  intro h
  have he := congrArg (fun f : V ⟶ V => f x) e.hom_inv_id
  rw [SVec.comp_apply, h, map_zero, SVec.id_apply] at he
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
private def chosen (i : Bool) := contentMissingUnitMatrixIso D Sc cut [] i (by simp) N w
private def first (i : Bool) : Fin (contentUnitCount D cut i (0 : Multiset Bool)) :=
  ⟨0, by cases i <;> decide⟩
private def source (i : Bool) : unitColumnSourceSpace (D.parity i) N
    (contentUnitCount D cut i (0 : Multiset Bool)) w :=
  Pi.single (first i) ground
private theorem source_ne_zero (i : Bool) : source i ≠ 0 := by
  intro h
  have he := congrFun h (first i)
  simp only [source, Pi.single_eq_same] at he
  exact ground_ne_zero he
/-- Both moving parities retain occupied full-old coefficient module values. -/
example (i : Bool) : (chosen i).hom (source i) ≠ 0 :=
  iso_hom_nonzero (chosen i) (source i) (source_ne_zero i)
example (i : Bool) := (chosen i).hom_inv_id
example (i : Bool) := (chosen i).inv_hom_id
example (i : Bool) := contentMissingUnitMatrixIso_hom D Sc cut [] i (by simp) N w
example (i : Bool) := contentMissingUnitMatrixIso_inv_mem D Sc cut [] i (by simp) N w
/-- Cutoff zero is covered by the same specified finite matrix. -/
example (i : Bool) (M : Superfunctor ℚ (OldContentCategory D Sc (fun _ => 0) []) (SVec ℚ))
    (t : OldContentCategory D Sc (fun _ => 0) []) :=
  (contentMissingUnitMatrixIso D Sc (fun _ => 0) [] i (by simp) M t).hom_inv_id
end NonVacuity.ContentMissingUnitInverse
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVContentMissingUnitInverse
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"
