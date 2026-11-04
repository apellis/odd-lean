import OddMath.QuiverHecke.SwappedAssembly.SupportedTensorCrossEntries
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeDenominatorUnits
import OddMath.QuiverHecke.HalfTurn.PowerWordCoordinates
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath OddMath.SKM OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction OddMath.QuiverHecke.SwappedAssembly
namespace NonVacuity.SupportedTensorCrossEntries
private theorem coordinate_ne_zero (D : SKM.Datum Bool (Bool → ℤ)) (Sc : SKM.Scalars D ℚ)
    (cutoff : Bool → ℕ) (L : Bool × ℕ → ℕ) (s t : List Bool)
    (v : (powerWordModule D (parameterTwist D Sc) cutoff L t.reverse).obj (OldCategory.mk s.reverse))
    (hv : v ≠ 0) : PowerWordQuotientCoordinates.coordinate D Sc cutoff L s t v ≠ 0 := by
  intro h
  let e := PowerWordQuotientCoordinates.quotientEquiv D Sc cutoff L s t
  have hh := congrArg e h
  change e (e.symm v) = e 0 at hh
  rw [LinearEquiv.apply_symm_apply,map_zero] at hh
  exact hv hh
local instance tensorHomPi (A C : PiSCat.{0,0,1} ℚ) : PiSupercategory ℚ (A ⟶ C) :=
  PiTwoSupercategory.homPiLeft A C
private def collisionDatum : SKM.Datum Bool (Bool → ℤ) where
  cd :=
    { root := fun j i => if i = j then 2 else -2
      coroot := fun i => LinearMap.proj i
      coroot_root_self := fun i => by simp }
  isGCM :=
    { diag := fun i => by simp [CartanDatum.cartanMatrix_apply]
      offDiag_nonpos := fun i j h => by simp [CartanDatum.cartanMatrix_apply, h]
      zero_comm := fun i j => by simp [CartanDatum.cartanMatrix_apply, eq_comm] }
  parity := fun _ => 1
  even_of_odd := by
    intro i j _
    change Even (if i = j then (2 : ℤ) else -2)
    split
    · exact ⟨1, by norm_num⟩
    · exact ⟨-1, by norm_num⟩

private def collisionScalars : SKM.Scalars collisionDatum ℚ where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := fun _ => isUnit_iff_ne_zero.mpr (by norm_num)


private abbrev D := collisionDatum
private abbrev originalSc := collisionScalars
private abbrev Sc := parameterTwist D originalSc
private def cutoff (_ : Bool) : ℕ := 40
private def L (_ : Bool × ℕ) : ℕ := 40
private def m (_ : Bool) : ℕ := 20
private def Λ : Bool → ℤ := fun _ => 40
private abbrev N := PowerWordContent.powerBound D cutoff L
local notation "R" => WeightTensorVacuum.regularProbe D (parameterTwist D originalSc) m Λ
private abbrev W := elvRouquierData D Sc cutoff N Λ
private def rightLabels : List (Col Bool (Bool → ℤ)) := wd D 0 [up true,up false]
private def leftLabels : List (Col Bool (Bool → ℤ)) := wd D 0 [up false]
private theorem right_up : ∀ a ∈ rightLabels, a.l.1 = true := by simp [rightLabels,wd]
private theorem left_up : ∀ a ∈ leftLabels, a.l.1 = true := by simp [leftLabels,wd]
private abbrev cR : Bool →₀ ℕ := SPath.wordContent rightLabels + 0
private def pR : SPath rightLabels (0,cR) (0,0) := SPath.reservoirPath rightLabels right_up 0
private def pL (cM : Bool →₀ ℕ) := SPath.reservoirPath leftLabels left_up cM
private abbrev ν : List Bool := [false,true]
private abbrev η : List Bool := [false]
private theorem weight_add (c : Bool →₀ ℕ) (i : Bool) :
    ReservoirWord.weight D Λ (c + Finsupp.single i 1) = ReservoirWord.weight D Λ c + D.α i := by
  simp only [ReservoirWord.weight,map_add,contentWeight,Finsupp.weight_single,one_nsmul]
  abel
private theorem powers_high (q : Bool × ℕ) : 32 ≤ L q * SKM.SYM.elementaryWeight D q := by
  have hw : 0 < SKM.SYM.elementaryWeight D q := by
    unfold SKM.SYM.elementaryWeight
    split_ifs <;> omega
  change 32 ≤ 40 * SKM.SYM.elementaryWeight D q
  omega
private def identityNF (s : List Bool) : NFIdx s s := by
  have hc : Categorification.TypeA.canWord s.length (1 : Equiv.Perm (Fin s.length)) = [] := by
    apply List.length_eq_zero_iff.mp
    rw [Categorification.TypeA.length_canWord,Categorification.TypeA.length_one]
  refine ⟨([],1),by simp,by simp,?_⟩
  simp only [List.map_nil,hc,cw,List.reverse_nil,List.nil_append,pl,QuiverHecke.SChain]
private def oddIndex : SKM.SYM.CoefficientIndex D := (0,{⟨false,rfl⟩,⟨true,rfl⟩})
private def occupied (s : List Bool) : ExtendedAtMost D originalSc s s 2 :=
  ⟨extensionBasis D originalSc s s (oddIndex,identityNF s),
    Submodule.subset_span ⟨(oddIndex,identityNF s),by
      change SKM.SYM.coefficientWeight D oddIndex + 0 ≤ 2
      decide,rfl⟩⟩
private def rawVector (s : List Bool) := powerWordHalfTurnCoordinate D originalSc cutoff L s s (occupied s).val
private theorem rawVector_ne_zero (s : List Bool) (hb : 2 + 2 * s.length.choose 2 < 32) : rawVector s ≠ 0 := by
  intro hz
  have hinj := powerWordHalfTurnCoordinate_injective_on_extendedAtMost D originalSc cutoff L (s := s) (t := s)
    (fun _ => (by decide : 32 ≤ 40)) powers_high hb
  have hh : occupied s = (0 : ExtendedAtMost D originalSc s s 2) := by
    apply hinj
    change powerWordHalfTurnCoordinate D originalSc cutoff L s s (occupied s).val =
      powerWordHalfTurnCoordinate D originalSc cutoff L s s 0
    exact hz.trans (map_zero _).symm
  exact (extensionBasis D originalSc s s).ne_zero (oddIndex,identityNF s) (congrArg Subtype.val hh)
private theorem probePairing (i : Bool) : (probeCutoff D m i : ℤ) = D.h i Λ := by
  cases i <;> norm_num [probeCutoff, probeDotExponent, m, D, collisionDatum, SKM.Datum.h, Λ]
private theorem reservoirPairing (i : Bool) : (cutoff i : ℤ) = D.h i Λ := rfl
private abbrev P := elvProbeReservoir D originalSc m cutoff N Λ Λ probePairing reservoirPairing
private def sy : SKM.Symmetrizer D where
  d := fun _ => 1
  pos := by intro _; norm_num
  symm := by intro i j; cases i <;> cases j <;> rfl
private theorem homogeneous : originalSc.Homogeneous := by
  intro _ _ _ _ _ _ _ _ h
  exact (h rfl).elim
private def coefficient :=
  elvProbeCrossCoeff D originalSc m cutoff N Λ Λ probePairing reservoirPairing sy homogeneous
private def crossLayer (i j : Bool) := SKM.lay D 0 [up false] (.cross i j) [up true,up false]
private abbrev crossContent (i j : Bool) : Bool →₀ ℕ := cR + (Finsupp.single i 1 + Finsupp.single j 1)
private theorem firstValid (i j : Bool) : StepValid (true,i) false (0,crossContent i j) := by
  change 1 ≤ (crossContent i j) i
  simp only [crossContent,Finsupp.add_apply,Finsupp.single_eq_same]
  omega
private theorem secondValid (i j : Bool) :
    StepValid (true,j) false (nextSector (true,i) false (0,crossContent i j)) := by
  have hc : crossContent i j - Finsupp.single i 1 = cR + Finsupp.single j 1 := by
    dsimp [crossContent]
    rw [add_comm (Finsupp.single i 1), ← add_assoc, add_tsub_cancel_right]
  change 1 ≤ (crossContent i j - Finsupp.single i 1 : Bool →₀ ℕ) j
  rw [hc]
  simp
private theorem swapContent (i j : Bool) : crossContent i j = crossContent j i := by
  dsimp [crossContent]
  rw [add_comm (Finsupp.single i 1)]
private theorem targetFirst (i j : Bool) : StepValid (true,j) false (0,crossContent i j) := by
  rw [swapContent i j]
  exact firstValid j i
private theorem targetSecond (i j : Bool) :
    StepValid (true,i) false (nextSector (true,j) false (0,crossContent i j)) := by
  rw [swapContent i j]
  exact secondValid j i
private theorem endpoints (i j : Bool) :
    nextSector (true,j) false (nextSector (true,i) false (0,crossContent i j)) =
      nextSector (true,i) false (nextSector (true,j) false (0,crossContent i j)) := by
  change (0,crossContent i j - Finsupp.single i 1 - Finsupp.single j 1) =
    ((0,crossContent i j - Finsupp.single j 1 - Finsupp.single i 1) : Sector Bool)
  rw [tsub_tsub,tsub_tsub,add_comm (Finsupp.single i 1)]
private theorem crossLeft_up (i j : Bool) : ∀ a ∈ (crossLayer i j).left, a.l.1 = true := by
  simp [crossLayer,SKM.lay,wd]
private theorem crossRight_up (i j : Bool) : ∀ a ∈ (crossLayer i j).right, a.l.1 = true := by
  simp [crossLayer,SKM.lay,wd]
private def crossLeft (i j : Bool) :=
  SPath.reservoirPath (crossLayer i j).left (crossLeft_up i j) (crossContent i j)
private def crossRight (i j : Bool) : SPath (crossLayer i j).right
    (0,crossContent i j - Finsupp.single j 1 - Finsupp.single i 1) (0,0) := by
  simpa only [crossLayer,SKM.lay,crossContent,tsub_tsub,add_comm (Finsupp.single j 1),
    add_tsub_cancel_right,rightLabels] using pR
example (i : Bool) := SupportedSectors.tensorLayerSameCrossIso D originalSc m cutoff L Λ Λ
  probePairing reservoirPairing 0 [up false] [up true,up false] i (firstValid i i) (secondValid i i)
  (crossLeft i i) (crossLeft_up i i) (crossRight i i) (crossRight_up i i)
example (i : Bool) := SupportedSectors.tensorLayerSameCross_square D originalSc m cutoff L Λ Λ
  probePairing reservoirPairing 0 [up false] [up true,up false] i (firstValid i i) (secondValid i i)
  (crossLeft i i) (crossLeft_up i i) (crossRight i i) (crossRight_up i i) coefficient
example (i j : Bool) (hij : i ≠ j) := SupportedSectors.tensorLayerCross_square D originalSc m cutoff L Λ Λ
  probePairing reservoirPairing 0 [up false] [up true,up false] i j
  (firstValid i j) (secondValid i j) (targetFirst i j) (targetSecond i j) (endpoints i j)
  (crossLeft i j) (crossLeft_up i j) (crossRight i j) (crossRight_up i j) coefficient hij
end NonVacuity.SupportedTensorCrossEntries
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.SwappedAssembly.SupportedTensorCrossEntries
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owned module"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"
