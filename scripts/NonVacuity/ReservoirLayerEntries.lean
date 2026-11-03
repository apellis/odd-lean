import OddMath.QuiverHecke.SwappedAssembly.ReservoirLayerEntries
import OddMath.QuiverHecke.SwappedAssembly.Generators.Dot
import OddMath.QuiverHecke.SwappedAssembly.ReservoirPaths
import OddMath.QuiverHecke.CyclotomicAction.ELVRouquierMulticolour
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath OddMath.SKM OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction OddMath.QuiverHecke.SwappedAssembly
namespace NonVacuity.ReservoirLayerEntries
private abbrev D := AsymmetricParameters.datum
private abbrev originalSc := AsymmetricParameters.scalars
private abbrev Sc := parameterTwist D originalSc
private def cutoff (_ : Bool) : ℕ := 4
private def Λ : Bool → ℤ := fun _ => 4
private theorem cutoff_pairing : ∀ i, (cutoff i : ℤ) = D.h i Λ := by intro i; rfl
private def T := elvRouquierFamily D Sc cutoff 12 Λ cutoff_pairing
private instance homPi (A B : PiSCat.{0,0,1} ℚ) : PiSupercategory ℚ (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B
private def P : ProbeReservoir ℚ (PiSCat.{0,0,1} ℚ) D originalSc where
  T := T
  W := T
  leftAdj := T.leftAdjoints
  probeRel := elvRouquierMulticolour D originalSc cutoff 12 Λ cutoff_pairing
  reservoirRel := elvRouquierMulticolour D originalSc cutoff 12 Λ cutoff_pairing
  ΛP := Λ
  ΛR := Λ
private def zeroFunctor (x y : Bool → ℤ) :
    elvWeightSpace D Sc cutoff 12 Λ x ⥤ elvWeightSpace D Sc cutoff 12 Λ y :=
  Functor.pi' fun β => (elvZeroFunctor D Sc cutoff 12 (C := elvWeightSpace D Sc cutoff 12 Λ x) β.1)
private instance (x y : Bool → ℤ) : (zeroFunctor x y).Additive where
  map_add {_X _Y f g} := funext fun β =>
    (elvZeroFunctor D Sc cutoff 12 (C := elvWeightSpace D Sc cutoff 12 Λ x) β.1).map_add (f := f) (g := g)
private instance (x y : Bool → ℤ) : (zeroFunctor x y).Linear ℚ where
  map_smul f r := funext fun β => (elvZeroFunctor D Sc cutoff 12 (C := elvWeightSpace D Sc cutoff 12 Λ x) β.1).map_smul r f
private instance (x y : Bool → ℤ) : IsSuperfunctor ℚ (zeroFunctor x y) where
  map_mem hf β := IsSuperfunctor.map_mem (F := elvZeroFunctor D Sc cutoff 12 (C := elvWeightSpace D Sc cutoff 12 Λ x) β.1) hf
private def zeroHom (s : Sector Bool) : P.H s := by
  change elvWeightSpace D Sc cutoff 12 Λ (-P.muP s) ⟶ elvWeightSpace D Sc cutoff 12 Λ (P.muM s)
  exact ⟨zeroFunctor _ _⟩
private def identityInput : P.H (0,0) := by
  change elvWeightSpace D Sc cutoff 12 Λ (-(Λ - contentWeight D 0)) ⟶
    elvWeightSpace D Sc cutoff 12 Λ (-Λ + contentWeight D 0)
  simp only [map_zero, sub_zero, add_zero]
  exact 𝟙 _
private def Ys (s : Sector Bool) : P.H s :=
  if h : s = (0,0) then (by subst s; exact identityInput) else zeroHom s
private def L : Layer (SKM.sig D) := SKM.lay D 0 [] (.dot false) []
private theorem valid : L.Valid := lay_valid D 0 [] (.dot false) []
private theorem upward : ∀ a ∈ L.dom.word, a.l.1 = true := by
  change ∀ a ∈ ([⟨(true,false),0⟩] : List (Col Bool (Bool → ℤ))), a.l.1 = true
  simp
private abbrev sl : Sector Bool := (0, SPath.wordContent L.dom.word + 0)
private def p : SPath L.dom.word sl (0,0) := SPath.reservoirPath L.dom.word upward 0
private def Gs (s : Sector Bool) : P.H s :=
  if h : s = sl then (by subst s; exact (P.pathFunctor p).obj (Ys (0,0))) else zeroHom s
private theorem source_eq : Gs sl = (P.pathFunctor p).obj (Ys (0,0)) := by simp [Gs]
private def sr : {s : Sector Bool // P.wt s = L.dom.endR} := ⟨(0,0), by
  change P.wt (0,0) = 0
  simp [ProbeReservoir.wt, ProbeReservoir.muP, ProbeReservoir.muM, P]⟩
private def x : P.Mod Gs Ys L.dom := fun s t q =>
  if hs : s = sl then (by
    subst s
    exact if ht : t = sr then (by
      subst t
      have hq : q = p :=
        (SPath.subsingleton_of_upward_probe_zero (s := sl) (t := (0,0)) upward rfl).elim q p
      subst q
      exact eqToHom source_eq) else 0) else 0
private theorem selected_entry : x sl sr p = eqToHom source_eq := by simp [x]
private def gens : P.Generators where
  dot := P.dotImage
  cross := fun _ _ _ _ _ _ => 0
  cup := fun _ _ _ _ _ => 0
  cap := fun _ _ _ _ _ => 0
  lcross := fun _ _ _ _ _ _ => 0
  dcup := fun _ _ _ _ _ _ => 0
  dcap := fun _ _ _ _ _ _ => 0
/-- The input is a supported identity Hom entry on a nonempty reservoir
path in a supplied complete ELV factor pair. Only the tested dot field is
specified; no relation assertion for this generator record is made. -/
example : x sl sr p = eqToHom source_eq := selected_entry
example : SPath.wordContent L.dom.word = Finsupp.single false 1 := by
  change Finsupp.single false 1 + 0 = Finsupp.single false 1
  simp
example := P.layerMap_reservoir gens L valid upward x sl sr rfl p p
example := P.layerMap_reservoir_append gens L valid
  (by change ∀ a ∈ ([⟨(true,false),0⟩] : List (Col Bool (Bool → ℤ))), a.l.1 = true; simp)
  (by simp [L, SKM.lay, SKM.wd]) x (SPath.nil sl) p p (SPath.nil (0,0)) sr.2 rfl
/-- The same literal matrix formula applies to every input family. -/
example (v : P.Mod Gs Ys L.dom) := P.layerMap_reservoir gens L valid upward v sl sr rfl p p
end NonVacuity.ReservoirLayerEntries
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.SwappedAssembly.ReservoirLayerEntries
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing module: {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module: {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited {names.size} owned declarations in {owner}: standard axioms"
