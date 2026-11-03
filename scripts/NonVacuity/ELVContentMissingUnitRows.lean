import OddMath.QuiverHecke.CyclotomicAction.ELVContentMissingUnitRows
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeVacuumVector
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.ELVOld OddMath.QuiverHecke.ELVOld.BalancedInduction
open OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
namespace NonVacuity.ContentMissingUnitRows
private theorem identity_ne_zero_of_vector
    {k C : Type} [CommRing k] [Category.{0} C] [Preadditive C] [Linear k C] [Supercategory k C]
    (M : Superfunctor k C (SVec k)) (s : C) (b : M.obj s) (hb : b ≠ 0) : (𝟙 s : s ⟶ s) ≠ 0 := by
  intro h
  have hi : M.map (𝟙 s) = 𝟙 (M.obj s) := M.toFunctor.map_id s
  have hz : M.map (0 : s ⟶ s) = 0 := M.toFunctor.map_zero s s
  have he := congrArg (fun f => M.map f b) h
  rw [hi, hz, SVec.id_apply, SVec.zero_apply] at he
  exact hb he
private theorem inverse_column_apply
    {k C : Type} [CommRing k] [Category.{0} C] [Preadditive C] [Linear k C] [Supercategory k C]
    {M T : Superfunctor k C (SVec k)} (u : M ⟶ T) (v : T ⟶ M) (h : u ≫ v = 𝟙 M)
    (w : C) (b : M.obj w) : v.total w (u.total w b) = b := by
  have he := congrArg (fun f : M ⟶ M => f.total w b) h
  rw [Superfunctor.comp_total, SVec.comp_apply] at he
  have hi : (𝟙 M : M ⟶ M).total w = 𝟙 (M.obj w) := SuperNatTrans.id_total M.toFunctor w
  rw [hi, SVec.id_apply] at he
  exact he
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
private def chosenRow (i : Bool) (r : Fin (contentUnitCount D cut i (0 : Multiset Bool))) :=
  contentMissingUnitRow D Sc cut [] i (by simp) N r
/-- Every finite row extracts a nonzero vector of the full old representable,
with both moving parities and no scalar-evaluation assumption. -/
example (i : Bool) (r : Fin (contentUnitCount D cut i (0 : Multiset Bool))) :
    (chosenRow i r).total w
      ((unitDotColumn (oldContentAppend D Sc cut [] i)
        (oldContentAppendDot_supernatural D Sc cut [] i) N r.val).total w ground) ≠ 0 := by
  have h := contentMissingUnitColumn_row D Sc cut [] i (by simp) N r r
  rw [ite_eq_left rfl] at h
  have he := inverse_column_apply _ _ h w ground
  unfold chosenRow
  rw [he]
  exact ground_ne_zero
example (i : Bool) (r : Fin (contentUnitCount D cut i (0 : Multiset Bool))) :=
  contentMissingUnitRow_mem D Sc cut [] i (by simp) N r
example (i : Bool) (a r : Fin (contentUnitCount D cut i (0 : Multiset Bool))) :=
  contentMissingUnitColumn_row D Sc cut [] i (by simp) N a r
example (i : Bool) := contentMissingUnitRow_total D Sc cut [] i (by simp) N
/-- The zero-cutoff finite sum gives the same boundary identity. -/
example (i : Bool) (M : Superfunctor ℚ (OldContentCategory D Sc (fun _ => 0) []) (SVec ℚ)) :=
  contentMissingUnitRow_total D Sc (fun _ => 0) [] i (by simp) M
end NonVacuity.ContentMissingUnitRows
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for owner in #[`OddMath.QuiverHecke.CyclotomicAction.ELVInductionUnitInverseRows,
      `OddMath.QuiverHecke.CyclotomicAction.ELVContentMissingUnitRows] do
    let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
    let names := env.header.moduleData[idx]!.constNames
    if names.isEmpty then throwError "Empty owner {owner}"
    for name in names do
      for ax in ← Lean.collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {name}"
    logInfo m!"Audited all {names.size} owned declarations in {owner}"
