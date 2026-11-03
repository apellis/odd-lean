import OddMath.QuiverHecke.CyclotomicAction.ELVContentAbsentColour
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.ELVOld OddMath.QuiverHecke.ELVOld.BalancedInduction
open OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
namespace ContentAbsentColourConsumer
private abbrev D := WeightedAppendFixture.datum
private abbrev Sc := WeightedAppendFixture.scalars
private def cut : Bool → ℕ := fun _ => 8
private abbrev γ (i : Bool) : List Bool := [!i]
private abbrev t (i : Bool) : OldContentCategory D Sc cut (γ i) :=
  oldContentObject D Sc cut (γ i) ⟨γ i,List.Perm.refl _⟩
private def N (i : Bool) := (restriction (oldContentInclusion D Sc cut (γ i))).obj
  (oldRepresentable D Sc cut (t i).obj)
private def G (i : Bool) := induced (oldContentInclusion D Sc cut (γ i)) (N i)
private abbrev J (i : Bool) := append D Sc cut i
private theorem missing (i : Bool) : i ∉ γ i := by cases i <;> decide

/-- Both moving parities, with a nonempty output block of the OTHER colour. -/
example (i : Bool) := contentCrossingHeight_nonneg_of_not_mem D cut (γ i) i (missing i)
example (i : Bool) (v : OldCategory D Sc cut) :=
  oldContentAppend_offContent_of_not_mem D Sc cut (γ i) i (missing i) v
example (i : Bool) (v : OldCategory D Sc cut) :=
  oldContentRestriction_subsingleton_of_not_mem D Sc cut (γ i) i (missing i) (N i) v
example (i : Bool) (v : OldCategory D Sc cut) :=
  oldContentIndRes_subsingleton_of_not_mem D Sc cut (γ i) i (missing i) (N i) v
example (i : Bool) (b : ℕ) (v : OldCategory D Sc cut) :=
  oldContentUnitPrincipal_subsingleton_of_not_mem D Sc cut (γ i) i (missing i) (N i) b v

/-- The input-value coend vanishing lemma is used on the actual restricted
full-content extension, with every zero-value hypothesis proved. -/
example (i : Bool) (v : OldCategory D Sc cut) :=
  obj_subsingleton_of_values_subsingleton (J i) ((restriction (J i)).obj (G i)).toFunctor
    (oldContentRestriction_subsingleton_of_not_mem D Sc cut (γ i) i (missing i) (N i)) v

private abbrev vacuum : OldContentCategory D Sc cut [] :=
  oldContentObject D Sc cut [] ⟨[],List.Perm.refl _⟩
private def N0 := (restriction (oldContentInclusion D Sc cut [])).obj
  (oldRepresentable D Sc cut vacuum.obj)
private theorem missing0 (i : Bool) : i ∉ ([] : List Bool) := by simp

/-- Genuine EMPTY OUTPUT, separate from empty predecessor/output[i]. -/
example (i : Bool) := contentCrossingHeight_nonneg_of_not_mem D cut [] i (missing0 i)
example (i : Bool) (v : OldCategory D Sc cut) :=
  oldContentRestriction_subsingleton_of_not_mem D Sc cut [] i (missing0 i) N0 v
example (i : Bool) :=
  oldContentIndRes_subsingleton_of_not_mem D Sc cut [] i (missing0 i) N0 vacuum.obj
example (i : Bool) (b : ℕ) :=
  oldContentUnitPrincipal_subsingleton_of_not_mem D Sc cut [] i (missing0 i) N0 b vacuum.obj

end ContentAbsentColourConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVContentAbsentColour
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing owned module {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited {names.size} declarations in {owner}."
