import OddMath.QuiverHecke.CyclotomicAction.ELVContentMissingColourMatrix
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.ELVOld OddMath.QuiverHecke.ELVOld.BalancedInduction
open OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
open OddMath.FiniteSuperspace
namespace ContentMissingColourMatrixConsumer
private abbrev D := WeightedAppendFixture.datum
private abbrev Sc := WeightedAppendFixture.scalars
private def cut : Bool → ℕ := fun _ => 8
private abbrev γ (i : Bool) : List Bool := [!i]
private abbrev t (i : Bool) : OldContentCategory D Sc cut (γ i) :=
  oldContentObject D Sc cut (γ i) ⟨γ i,List.Perm.refl _⟩
private def N (i : Bool) := (restriction (oldContentInclusion D Sc cut (γ i))).obj
  (oldRepresentable D Sc cut (t i).obj)
private def G (i : Bool) := induced (oldContentInclusion D Sc cut (γ i)) (N i)
private theorem missing (i : Bool) : i ∉ γ i := by cases i <;> decide
private def V (i : Bool) (m : ℕ) : Option (Fin m) → SVec ℚ :=
  fun a => (unitMatrixFamily D Sc cut i (G i) m a).obj (t i).obj
private theorem zeroPrincipal (i : Bool) (m : ℕ) : Subsingleton (V i m none) :=
  oldContentUnitPrincipal_subsingleton_of_not_mem D Sc cut (γ i) i (missing i) (N i) m (t i).obj

/-- Drop and reinsert the actual vanished E/F coordinate for both parities. -/
example (i : Bool) (m : ℕ) := dropZeroPrincipalEquiv (V i m) (zeroPrincipal i m)
example (i : Bool) (m : ℕ) (x : product (V i m)) (r : Fin m) :=
  dropZeroPrincipalEquiv_apply (V i m) (zeroPrincipal i m) x r
example (i : Bool) (m : ℕ) (x : withoutPrincipal (V i m)) :=
  dropZeroPrincipalEquiv_symm_none (V i m) (zeroPrincipal i m) x
example (i : Bool) (m : ℕ) (x : withoutPrincipal (V i m)) (r : Fin m) :=
  dropZeroPrincipalEquiv_symm_some (V i m) (zeroPrincipal i m) x r
example (i : Bool) (m : ℕ) := dropZeroPrincipalEquiv_hom_mem (V i m) (zeroPrincipal i m)
example (i : Bool) (m : ℕ) := dropZeroPrincipalEquiv_inv_mem (V i m) (zeroPrincipal i m)
example (i : Bool) (m : ℕ) := dropZeroPrincipalEquiv_columns (V i m) (zeroPrincipal i m)
  (mateTargetSpace D Sc cut i (G i) (t i).obj)
  (fun a => (unitMatrixEntry D Sc cut i (G i) m a).total (t i).obj)

/-- The GIVEN inverse has exactly the prescribed remaining forward columns. -/
example (i : Bool) := missingColourUnitMatrixIso D Sc cut (γ i) i (missing i) (N i) (t i)
example (i : Bool) := missingColourUnitMatrixIso_hom D Sc cut (γ i) i (missing i) (N i) (t i)
example (i : Bool) := missingColourUnitMatrixIso_hom_mem D Sc cut (γ i) i (missing i) (N i) (t i)
example (i : Bool) := missingColourUnitMatrixIso_inv_mem D Sc cut (γ i) i (missing i) (N i) (t i)
example (i : Bool) := (missingColourUnitMatrixIso D Sc cut (γ i) i (missing i) (N i) (t i)).hom_inv_id
example (i : Bool) := (missingColourUnitMatrixIso D Sc cut (γ i) i (missing i) (N i) (t i)).inv_hom_id

private abbrev vacuum : OldContentCategory D Sc cut [] :=
  oldContentObject D Sc cut [] ⟨[],List.Perm.refl _⟩
private def N0 := (restriction (oldContentInclusion D Sc cut [])).obj
  (oldRepresentable D Sc cut vacuum.obj)
private theorem missing0 (i : Bool) : i ∉ ([] : List Bool) := by simp
/-- Genuine empty output has the same prescribed inverse, with no predecessor. -/
example (i : Bool) := missingColourUnitMatrixIso D Sc cut [] i (missing0 i) N0 vacuum
example (i : Bool) := missingColourUnitMatrixIso_hom D Sc cut [] i (missing0 i) N0 vacuum
example (i : Bool) := missingColourUnitMatrixIso_hom_mem D Sc cut [] i (missing0 i) N0 vacuum
example (i : Bool) := missingColourUnitMatrixIso_inv_mem D Sc cut [] i (missing0 i) N0 vacuum
example (i : Bool) := (missingColourUnitMatrixIso D Sc cut [] i (missing0 i) N0 vacuum).hom_inv_id
example (i : Bool) := (missingColourUnitMatrixIso D Sc cut [] i (missing0 i) N0 vacuum).inv_hom_id
end ContentMissingColourMatrixConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for owner in #[`OddMath.Algebra.FiniteZeroCoordinate,
      `OddMath.QuiverHecke.CyclotomicAction.ELVContentMissingColourMatrix] do
    let some idx := env.header.moduleNames.idxOf? owner
      | throwError "Missing owned module {owner}"
    let names := env.header.moduleData[idx]!.constNames
    if names.isEmpty then throwError "Empty owned module {owner}"
    for name in names do
      for ax in ← Lean.collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {name}"
    logInfo m!"Audited {names.size} declarations in {owner}."
