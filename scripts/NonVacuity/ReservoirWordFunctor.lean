import OddMath.QuiverHecke.SwappedAssembly.ReservoirWordFunctor
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import OddMath.QuiverHecke.CyclotomicAction.PiWeightSpaces
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath.SKM OddMath.QuiverHecke.SwappedAssembly
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ReservoirWordFunctorExamples

private abbrev C := Bool → SVec ℚ
private instance : PiSupercategory ℚ C := productPiSupercategory _

private def duplicate : C ⥤ C where
  obj M _ := M false
  map f _ := f false
private instance : duplicate.Additive where
  map_add := by intros; rfl
private instance : duplicate.Linear ℚ where
  map_smul := by intros; rfl
private instance : IsSuperfunctor ℚ duplicate where
  map_mem hf _ := hf false

private def swap : C ⥤ C where
  obj M i := M (!i)
  map f i := f (!i)
private instance : swap.Additive where
  map_add := by intros; rfl
private instance : swap.Linear ℚ where
  map_smul := by intros; rfl
private instance : IsSuperfunctor ℚ swap where
  map_mem hf i := hf (!i)

/-- Noncommuting upward generator data, without a full-action assertion. -/
private def W : RouquierData (k := ℚ) (B := PiSCat.{0,0,1} ℚ) AsymmetricParameters.datum where
  obj _ := PiSCat.of ℚ C
  E i _ _ _ := if i then ⟨swap⟩ else ⟨duplicate⟩
  dot _ _ _ _ := 0
  dot_mem _ _ _ _ := Submodule.zero_mem _
  cross _ _ _ _ _ _ _ _ _ _ := 0
  cross_mem _ _ _ _ _ _ _ _ _ _ := Submodule.zero_mem _

private def letters : List (Col Bool (Bool → ℤ)) :=
  [⟨(true, false), 0⟩, ⟨(true, true), 0⟩]
private theorem upward : ∀ a ∈ letters, a.l.1 = true := by simp [letters]
private def path := SPath.reservoirPath letters upward 0
private def M : C := fun _ => SVec.unit
private def f : M ⟶ M := fun i => (if i then (3 : ℚ) else 2) • 𝟙 _

/-- The tail (swap) acts first, followed by the head (duplicate). -/
private theorem nativeWord_eq : ReservoirWord.word W 0 path upward =
    (⟨swap ⋙ duplicate⟩ : Superfunctor ℚ C C) := by
  simp [ReservoirWord.word, path, SPath.reservoirPath, SPath.wordContent, letters, W]

example : (ReservoirWord.word W 0 path upward).obj M = M := by
  rw [nativeWord_eq]
  rfl

example : (ReservoirWord.word W 0 path upward).map f =
    fun _ => (3 : ℚ) • 𝟙 _ := by
  rw [nativeWord_eq]
  rfl

/-- Scalar 3 survives and distinguishes the chosen order from scalar 2. -/
example : ((((⟨swap ⋙ duplicate⟩ : Superfunctor ℚ C C).map f) false) (1 : ℚ)) = 3 := by
  rfl

end OddMath.QuiverHecke.ReservoirWordFunctorExamples

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.SwappedAssembly.ReservoirWordFunctor
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owned module"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"
