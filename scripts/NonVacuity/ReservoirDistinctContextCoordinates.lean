import OddMath.QuiverHecke.SwappedAssembly.ReservoirDistinctContextCoordinates
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
namespace NonVacuity.ReservoirDistinctContextCoordinates
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
private def L : Layer (SKM.sig D) := SKM.lay D 0 [up true] (.cross false true) [up true]
private theorem valid : L.Valid := lay_valid D 0 [up true] (.cross false true) [up true]
private theorem right_upward : ∀ a ∈ L.right, a.l.1 = true := by
  change ∀ a ∈ ([⟨(true,true),0⟩] : List (Col Bool (Bool → ℤ))), a.l.1 = true
  simp
private theorem left_upward : ∀ a ∈ L.left, a.l.1 = true := by
  change ∀ a ∈ ([⟨(true,true),_⟩] : List (Col Bool (Bool → ℤ))), a.l.1 = true
  simp
private abbrev c : Bool →₀ ℕ := Finsupp.single false 1 + (Finsupp.single true 1 + SPath.wordContent L.right)
private abbrev sl : Sector Bool := (0, SPath.wordContent L.left + c)
private theorem middle_valid : StepValid (true,false) false (0,c) := by
  change 1 ≤ (Finsupp.single false 1 + (Finsupp.single true 1 + SPath.wordContent L.right) : Bool →₀ ℕ) false
  simp
private theorem inner_valid : StepValid (true,true) false (nextSector (true,false) false (0,c)) := by
  change 1 ≤ ((Finsupp.single false 1 + (Finsupp.single true 1 + SPath.wordContent L.right) -
    Finsupp.single false 1 : Bool →₀ ℕ) true)
  simp
private theorem target_outer_valid : StepValid (true,true) false (0,c) := by
  change 1 ≤ (Finsupp.single false 1 + (Finsupp.single true 1 + SPath.wordContent L.right) : Bool →₀ ℕ) true
  simp
private theorem target_inner_valid : StepValid (true,false) false (nextSector (true,true) false (0,c)) := by
  change 1 ≤ ((Finsupp.single false 1 + (Finsupp.single true 1 + SPath.wordContent L.right) -
    Finsupp.single true 1 : Bool →₀ ℕ) false)
  simp
private theorem hs : nextSector (true,true) false (nextSector (true,false) false (0,c)) =
    nextSector (true,false) false (nextSector (true,true) false (0,c)) := by
  simp only [nextSector, tsub_right_comm]
private def pu : SPath L.left sl (0,c) := SPath.reservoirPath L.left left_upward c
private def pv : SPath L.right (nextSector (true,false) false (nextSector (true,true) false (0,c))) (0,0) := by
  have he : nextSector (true,false) false (nextSector (true,true) false (0,c)) = (0, SPath.wordContent L.right + 0) := by
    simp only [nextSector, c]
    rw [tsub_right_comm (a := c) (b := Finsupp.single true 1) (c := Finsupp.single false 1),
      add_tsub_cancel_left, add_tsub_cancel_left, add_zero]
  rw [he]
  exact SPath.reservoirPath L.right right_upward 0
private def pg : SPath ((SKM.sig D).dom L.gen) (0,c)
    (nextSector (true,false) false (nextSector (true,true) false (0,c))) :=
  SPath.two (c₁ := ⟨up false, SKM.wt D (SKM.wt D 0 [up true]) [up true]⟩)
    (c₂ := ⟨up true, SKM.wt D 0 [up true]⟩) false false middle_valid inner_valid hs
private def p : SPath L.dom.word sl (0,0) := (pu.append pg).append pv
private theorem upward : ∀ a ∈ L.dom.word, a.l.1 = true := by
  change ∀ a ∈ ([⟨(true,true),_⟩,⟨(true,false),_⟩,⟨(true,true),_⟩,⟨(true,true),_⟩] : List (Col Bool (Bool → ℤ))), a.l.1 = true
  simp
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
private def coeff : P.CrossCoeff := ⟨fun _ _ _ _ => 0⟩

/-- A supplied complete factor pair, two nonempty contexts, and an
identity transport at the occupied four-letter reservoir path. No
inverse assertion for the unused mixed coefficient is needed. -/
example : x sl sr p = eqToHom source_eq := selected_entry
example := P.layerMap_reservoir_cross_ne_word coeff 0 [up true] [up true] false true (by decide)
  x middle_valid inner_valid target_outer_valid target_inner_valid hs pu left_upward pv right_upward sr.2

/-- The matrix square is a whole-Hom-map identity for arbitrary input
families in the same supplied factor pair. -/
example (z : P.Mod Gs Ys L.dom) := P.layerMap_reservoir_cross_ne_word coeff 0 [up true] [up true] false true (by decide)
  z middle_valid inner_valid target_outer_valid target_inner_valid hs pu left_upward pv right_upward sr.2
example := P.reservoirLayerCrossSourceWordIso 0 [up true] [up true] false true middle_valid inner_valid hs pu left_upward pv right_upward (Ys (0,0))
end NonVacuity.ReservoirDistinctContextCoordinates
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.SwappedAssembly.ReservoirDistinctContextCoordinates
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing module: {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module: {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited {names.size} owned declarations in {owner}: standard axioms"
