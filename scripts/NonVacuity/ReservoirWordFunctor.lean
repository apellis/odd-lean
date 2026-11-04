import OddMath.QuiverHecke.SwappedAssembly.ReservoirWordFunctor
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import OddMath.QuiverHecke.CyclotomicAction.PiWeightSpaces
import OddMath.QuiverHecke.CyclotomicAction.ELVRouquierMulticolour
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

/-- Read any occupied two-letter path before supplying the canonical path;
this keeps content transports out of the noncommuting operator test. -/
private theorem nativeWord_two {c d : Bool →₀ ℕ}
    (p : SPath letters (0, c) (0, d)) : ReservoirWord.word W 0 p upward =
    (⟨swap ⋙ duplicate⟩ : Superfunctor ℚ C C) := by
  cases p with
  | cons _ side _ hv₁ p =>
    have hs := SPath.side_eq_false_of_upward_probe_zero false side p (by simp) rfl
    subst side
    cases p with
    | cons _ side _ hv₂ p =>
      have hs := SPath.side_eq_false_of_upward_probe_zero true side p (by simp) rfl
      subst side
      cases p
      have h₁ : 1 ≤ c false := hv₁
      have h₂ : 1 ≤ (c - Finsupp.single false 1 : Bool →₀ ℕ) true := hv₂
      erw [ReservoirWord.word_cons W 0 false 0 (c := c) h₁ _ (by simp)]
      erw [ReservoirWord.word_cons W 0 true 0 (c := c - Finsupp.single false 1) h₂ _ (by simp)]
      erw [ReservoirWord.word_nil]
      rfl

private theorem nativeWord_eq : ReservoirWord.word W 0 path upward =
    (⟨swap ⋙ duplicate⟩ : Superfunctor ℚ C C) := nativeWord_two path

example : (ReservoirWord.word W 0 path upward).obj M = M := by
  rw [nativeWord_eq]
  rfl

example : (ReservoirWord.word W 0 path upward).map f =
    fun _ => (3 : ℚ) • 𝟙 _ := by
  rw [nativeWord_eq]
  rfl

/-- Scalar 3 survives and distinguishes the chosen order from scalar 2. -/
example : (show SVec.unit ⟶ SVec.unit from
    ((⟨swap ⋙ duplicate⟩ : Superfunctor ℚ C C).map f) false) (1 : ℚ) = (3 : ℚ) := by
  change (3 : ℚ) * 1 = 3
  norm_num

example : (show SVec.unit ⟶ SVec.unit from
    ((⟨duplicate ⋙ swap⟩ : Superfunctor ℚ C C).map f) false) (1 : ℚ) = (2 : ℚ) := by
  change (2 : ℚ) * 1 = 2
  norm_num

end OddMath.QuiverHecke.ReservoirWordFunctorExamples

namespace NonVacuity.ReservoirWordFunctorELV
open OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
private abbrev D := AsymmetricParameters.datum
private abbrev originalSc := AsymmetricParameters.scalars
private abbrev Sc := parameterTwist D originalSc
private def cutoff (_ : Bool) : ℕ := 4
private def Λ : Bool → ℤ := fun _ => 4
private theorem cutoff_pairing : ∀ i, (cutoff i : ℤ) = D.h i Λ := by intro i; rfl
private def T := elvRouquierFamily D Sc cutoff 12 Λ cutoff_pairing
private instance homPi (A B : PiSCat.{0,0,1} ℚ) : PiSupercategory ℚ (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B

/-- Both factors and every relation field are constructed. This fixture
does not assert that the identical factors form a separating model. -/
private def P : ProbeReservoir ℚ (PiSCat.{0,0,1} ℚ) D originalSc where
  T := T
  W := T
  leftAdj := T.leftAdjoints
  probeRel := elvRouquierMulticolour D originalSc cutoff 12 Λ cutoff_pairing
  reservoirRel := elvRouquierMulticolour D originalSc cutoff 12 Λ cutoff_pairing
  ΛP := Λ
  ΛR := Λ

private def labels : List (Col Bool (Bool → ℤ)) := wd D 0 [(true, false), (true, true)]
private theorem upward : ∀ a ∈ labels, a.l.1 = true := by simp [labels, wd]
private def path := SPath.reservoirPath labels upward 0

/-- The entire path-functor comparison receives a real full factor pair
and an occupied two-colour path, without a factor-existence premise. -/
example := P.reservoirWordFunctorIso path upward

private def identityInput : P.H (0, 0) := by
  change elvWeightSpace D Sc cutoff 12 Λ (-(Λ - contentWeight D 0)) ⟶
    elvWeightSpace D Sc cutoff 12 Λ (-Λ + contentWeight D 0)
  simp only [map_zero, sub_zero, add_zero]
  exact 𝟙 _

example := P.reservoirWordFunctorIso_hom_mem path upward identityInput

example := P.reservoirWordFunctorIso_nil_hom_heq 0 identityInput

private def oneOddContent : Bool →₀ ℕ := Finsupp.single true 1
private theorem oneOdd_height : 1 ≤ oneOddContent true := by simp [oneOddContent]
private def oddTail : SPath (X := Bool → ℤ) [] (0,oneOddContent - Finsupp.single true 1) (0,0) := by
  simp only [oneOddContent,tsub_self]
  exact SPath.nil _
example := P.reservoirWordFunctorIso_cons_hom_heq true 0 oneOdd_height oddTail (by simp) identityInput

end NonVacuity.ReservoirWordFunctorELV

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
