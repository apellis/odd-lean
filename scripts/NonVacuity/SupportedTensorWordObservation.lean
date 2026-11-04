import OddMath.QuiverHecke.SwappedAssembly.SupportedTensorWordObservation
import OddMath.QuiverHecke.HalfTurn.PowerWordCoordinates
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath OddMath.SKM OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction OddMath.QuiverHecke.SwappedAssembly
namespace NonVacuity.SupportedTensorWordObservation
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
private def cutoff (_ : Bool) : ℕ := 20
private def L (_ : Bool × ℕ) : ℕ := 20
private def m (_ : Bool) : ℕ := 10
private def Λ : Bool → ℤ := fun _ => 20
private abbrev N := PowerWordContent.powerBound D cutoff L
private def labels : List (Col Bool (Bool → ℤ)) := wd D (Λ - Λ) [up true,up false]
private theorem upward : ∀ a ∈ labels, a.l.1 = true := by simp [labels,wd]
private def path := SPath.reservoirPath labels upward 0
private abbrev ν : List Bool := [false,true]
private abbrev σ : List Bool := ν.reverse
private abbrev β := PowerWordWeight.wordBlock D Λ ν
private def w : ContentCategory D Sc cutoff N β.1 := ⟨⟨ν⟩,rfl⟩
private abbrev chosenEquiv := moduleIsoLinearEquiv
  (Pi.isoApp (TensorReservoirWords.valueChart D Sc m cutoff L Λ Λ path upward) β) w
private theorem powers_high (q : Bool × ℕ) : 16 ≤ L q * SKM.SYM.elementaryWeight D q := by
  have hw : 0 < SKM.SYM.elementaryWeight D q := by
    unfold SKM.SYM.elementaryWeight
    split_ifs <;> omega
  change 16 ≤ 20 * SKM.SYM.elementaryWeight D q
  omega
private theorem bounded_injective :
    Function.Injective (fun x : ExtendedAtMost D originalSc σ σ 2 =>
      powerWordHalfTurnCoordinate D originalSc cutoff L σ σ x.val) :=
  powerWordHalfTurnCoordinate_injective_on_extendedAtMost D originalSc cutoff L
    (fun _ => (by decide : 16 ≤ 20)) powers_high (by decide)
private def identityNF : NFIdx σ σ := by
  have hc : Categorification.TypeA.canWord σ.length (1 : Equiv.Perm (Fin σ.length)) = [] := by
    apply List.length_eq_zero_iff.mp
    rw [Categorification.TypeA.length_canWord, Categorification.TypeA.length_one]
  refine ⟨([],1),by simp,by simp,?_⟩
  simp only [List.map_nil,hc,cw,List.reverse_nil,List.nil_append,pl,QuiverHecke.SChain]
private def oddIndex : SKM.SYM.CoefficientIndex D := (0,{⟨false,rfl⟩,⟨true,rfl⟩})
private def occupied : ExtendedAtMost D originalSc σ σ 2 :=
  ⟨extensionBasis D originalSc σ σ (oddIndex,identityNF),
    Submodule.subset_span ⟨(oddIndex,identityNF),by decide,rfl⟩⟩
private def contentVector : (PowerWordWeight.wordAt D Sc cutoff L ν β.1).obj w :=
  powerWordHalfTurnCoordinate D originalSc cutoff L σ σ occupied.val
private theorem contentVector_ne_zero : contentVector ≠ 0 := by
  intro hz
  have hh : occupied = (0 : ExtendedAtMost D originalSc σ σ 2) := by
    apply bounded_injective
    change powerWordHalfTurnCoordinate D originalSc cutoff L σ σ occupied.val =
      powerWordHalfTurnCoordinate D originalSc cutoff L σ σ 0
    exact hz.trans (map_zero _).symm
  exact (extensionBasis D originalSc σ σ).ne_zero (oddIndex,identityNF) (congrArg Subtype.val hh)
private def chosenVector := chosenEquiv.symm contentVector
private theorem chosenVector_ne_zero : chosenVector ≠ 0 := by
  intro hz
  apply contentVector_ne_zero
  have he := congrArg chosenEquiv hz
  simpa only [chosenVector,LinearEquiv.apply_symm_apply,map_zero] using he

/-- Whole actual selected tensor-Hom functors agree, including all source
morphisms, at the proved original-weight presentation. -/
example := TensorReservoirWords.pathHomAt_eq_wordHom D Sc m cutoff L Λ Λ path upward
example := TensorReservoirWords.path_weight D Λ path upward
example {c : Bool →₀ ℕ} (p : SPath labels (0,c) (0,0)) :=
  TensorReservoirWords.pathHom_heq D Sc m cutoff L Λ Λ p upward
example := TensorReservoirWords.pathHomAt_eq_wordHom D Sc m cutoff L Λ Λ
  (SPath.nil (0,0)) (by simp)
example (M N₀ : probeOldWeightSpace D Sc m Λ (-Λ)) (f : M ⟶ N₀) :
    HEq ((TensorReservoirWords.pathHomAt D Sc m cutoff L Λ Λ path upward).map f)
      ((TensorVacuumWords.wordHom D Sc m cutoff L Λ Λ ν).map f) := by
  rw [TensorReservoirWords.pathHomAt_eq_wordHom]
  rfl
example := TensorReservoirWords.valueChart_hom_mem D Sc m cutoff L Λ Λ path upward
example : chosenVector ≠ 0 := chosenVector_ne_zero
example : chosenEquiv chosenVector = contentVector := chosenEquiv.apply_symm_apply _

private theorem probePairing (i : Bool) : (probeCutoff D m i : ℤ) = D.h i Λ := by
  cases i <;> norm_num [probeCutoff, probeDotExponent, m, D, collisionDatum, SKM.Datum.h, Λ]
private theorem reservoirPairing (i : Bool) : (cutoff i : ℤ) = D.h i Λ := rfl
private def vacuum := SupportedSectors.tensorVacuum D originalSc m cutoff L Λ Λ
private def supportedPath :=
  (SupportedSectors.pathFunctor D Sc m cutoff N Λ Λ path).obj vacuum
example := SupportedSectors.tensorVacuum_obj D originalSc m cutoff L Λ Λ
example := SupportedSectors.tensorVacuumPathIso D originalSc m cutoff L Λ Λ
  probePairing reservoirPairing path upward
example := SupportedSectors.tensorVacuumPathIso_hom_mem D originalSc m cutoff L Λ Λ
  probePairing reservoirPairing path upward
example := SupportedSectors.tensorVacuumPathIso D originalSc m cutoff L Λ Λ
  probePairing reservoirPairing (SPath.nil (0,0)) (by simp)

private theorem source_transport_isZero {x y z : Bool → ℤ} (h : x = y)
    (F : probeOldWeightSpace D Sc m Λ x ⟶ elvWeightSpace D Sc cutoff N Λ z)
    (hz : Limits.IsZero (h ▸ F : probeOldWeightSpace D Sc m Λ y ⟶
      elvWeightSpace D Sc cutoff N Λ z)) : Limits.IsZero F := by
  subst y
  exact hz

private theorem target_transport_isZero {x y : Bool → ℤ} (h : x = y)
    (F : probeOldWeightSpace D Sc m Λ (-Λ) ⟶ elvWeightSpace D Sc cutoff N Λ x)
    (hz : Limits.IsZero F) : Limits.IsZero (h ▸ F :
      probeOldWeightSpace D Sc m Λ (-Λ) ⟶ elvWeightSpace D Sc cutoff N Λ y) := by
  subst y
  exact hz

/-- The supported two-letter path is occupied by a product of the two
independent odd coefficients, even though its root weight is zero. -/
private theorem supportedPath_nonzero : ¬ Limits.IsZero supportedPath.obj := by
  intro hz
  have hn := hz.of_iso (SupportedSectors.tensorVacuumPathIso D originalSc m cutoff L Λ Λ
    probePairing reservoirPairing path upward).symm
  have hp : Limits.IsZero (TensorReservoirWords.pathHom D Sc m cutoff L Λ Λ path upward) :=
    source_transport_isZero (SupportedSectors.probeWeight_vacuum D Λ).symm _ hn
  have ha : Limits.IsZero (TensorReservoirWords.pathHomAt D Sc m cutoff L Λ Λ path upward) :=
    target_transport_isZero (TensorReservoirWords.path_weight D Λ path upward) _ hp
  have he := (Limits.IsZero.iff_id_eq_zero _).mp ha
  have hh := congrArg (fun f : End (TensorReservoirWords.pathHomAt D Sc m cutoff L Λ Λ path upward) =>
    (f.app 0 (WeightTensorVacuum.regularProbe D Sc m Λ)) β) he
  change (𝟙 _ : End (((TensorReservoirWords.pathHomAt D Sc m cutoff L Λ Λ path upward).obj
    (WeightTensorVacuum.regularProbe D Sc m Λ)) β)) = 0 at hh
  have hv := (Limits.IsZero.iff_id_eq_zero _).mpr hh
  have hw := hv.of_iso (Pi.isoApp (TensorReservoirWords.valueChart D Sc m cutoff L Λ Λ path upward) β).symm
  have hi := (Limits.IsZero.iff_id_eq_zero _).mp hw
  have hh' := congrArg (fun f : End (PowerWordWeight.wordFamily D Sc cutoff L Λ
    (PowerWordWeight.wordWeight D Λ ν) ν β) => f.app 0 w contentVector) hi
  exact contentVector_ne_zero hh'

example : ¬ Limits.IsZero supportedPath.obj := supportedPath_nonzero

private abbrev sourceWord : List Bool := [true,false]
private abbrev sourceSector : Sector Bool :=
  (0,SupportedSectors.tensorSourceContent D Λ Λ sourceWord)
example := SupportedSectors.tensorTargetFamily_zero D originalSc m cutoff Λ Λ L
example := SupportedSectors.tensorSourceFamily_source D originalSc m cutoff Λ Λ L sourceWord
example := SupportedSectors.tensorSourceFamily_source D originalSc m cutoff Λ Λ L [false,true]
example := SupportedSectors.tensorSourceObjectIso D originalSc m cutoff Λ Λ L
  probePairing reservoirPairing sourceWord
example := SupportedSectors.tensorSourceObjectIso_hom_mem D originalSc m cutoff Λ Λ L
  probePairing reservoirPairing sourceWord
example := SupportedSectors.tensorVacuumWeight D originalSc m cutoff Λ Λ L probePairing reservoirPairing
private theorem sourceSector_ne_zero : sourceSector ≠ (0,0) := by
  intro h
  have hh := congrArg (fun t : Sector Bool => t.2 true) h
  norm_num [sourceSector,sourceWord,SupportedSectors.tensorSourceContent,
    SupportedSectors.tensorSourceLabels,upWord,wd,SPath.wordContent] at hh
private theorem sourceContentWeight_zero : contentWeight D sourceSector.2 = 0 := by
  simp only [sourceWord,SupportedSectors.tensorSourceContent,
    SupportedSectors.tensorSourceLabels,upWord,List.map_cons,List.map_nil,wd_cons,wd_nil,
    SPath.wordContent,add_zero]
  simp only [map_add,contentWeight,Finsupp.weight_single,one_nsmul]
  ext i
  cases i <;> norm_num [D,collisionDatum,SKM.Datum.α]
example : contentWeight D sourceSector.2 = 0 := sourceContentWeight_zero
example : Limits.IsZero (SupportedSectors.tensorTargetFamily D originalSc m cutoff Λ Λ L sourceSector) :=
  SupportedSectors.tensorTargetFamily_isZero D originalSc m cutoff Λ Λ L sourceSector sourceSector_ne_zero
example : Limits.IsZero (SupportedSectors.tensorSourceFamily D originalSc m cutoff Λ Λ L sourceWord (0,0)) :=
  SupportedSectors.tensorSourceFamily_isZero D originalSc m cutoff Λ Λ L sourceWord (0,0)
    (Ne.symm sourceSector_ne_zero)
private theorem sourceObject_nonzero :
    ¬ Limits.IsZero (SupportedSectors.tensorSourceObject D originalSc m cutoff Λ Λ L sourceWord).obj := by
  change ¬ Limits.IsZero supportedPath.obj
  exact supportedPath_nonzero
example : ¬ Limits.IsZero (SupportedSectors.tensorSourceObject D originalSc m cutoff Λ Λ L sourceWord).obj :=
  sourceObject_nonzero
private theorem matrixVacuum_ne_zero :
    SupportedSectors.tensorMatrixVacuum D originalSc m cutoff Λ Λ L sourceWord ≠ 0 := by
  intro hz
  have hh := congrArg (fun x : SupportedSectors.tensorWordMatrixModule D originalSc m cutoff Λ Λ L sourceWord sourceWord =>
    x sourceSector ⟨(0,0),SupportedSectors.tensorWordVacuumEndpoint D Λ Λ sourceWord⟩
      (SupportedSectors.tensorSourcePath D Λ Λ sourceWord)) hz
  change (SupportedSectors.tensorMatrixVacuum D originalSc m cutoff Λ Λ L sourceWord)
    sourceSector ⟨(0,0),SupportedSectors.tensorWordVacuumEndpoint D Λ Λ sourceWord⟩
      (SupportedSectors.tensorSourcePath D Λ Λ sourceWord) = 0 at hh
  have hi : IsIso ((SupportedSectors.tensorMatrixVacuum D originalSc m cutoff Λ Λ L sourceWord)
    sourceSector ⟨(0,0),SupportedSectors.tensorWordVacuumEndpoint D Λ Λ sourceWord⟩
      (SupportedSectors.tensorSourcePath D Λ Λ sourceWord)) := by
    simp [SupportedSectors.tensorMatrixVacuum,SupportedSectors.tensorSourceFamily,
      SupportedSectors.tensorTargetFamily,sourceSector]
    infer_instance
  rw [hh] at hi
  have : Limits.HasZeroObject (SupportedSectors.H D Sc m cutoff N Λ Λ sourceSector) :=
    ⟨⟨SupportedSectors.supportedZero D Sc m cutoff N Λ Λ sourceSector,
      SupportedSectors.supportedZero_isZero D Sc m cutoff N Λ Λ sourceSector⟩⟩
  have hsrc := (Limits.isIsoZero_iff_source_target_isZero _ _).mp hi |>.1
  rw [SupportedSectors.tensorSourceFamily_source] at hsrc
  exact sourceObject_nonzero
    ((SupportedSectors.inclusion D Sc m cutoff N Λ Λ sourceSector).map_isZero hsrc)

example : SupportedSectors.tensorMatrixVacuum D originalSc m cutoff Λ Λ L sourceWord ≠ 0 :=
  matrixVacuum_ne_zero
private abbrev rowEquiv := SupportedSectors.tensorMatrixRowEquiv D originalSc m cutoff Λ Λ L
  probePairing reservoirPairing sourceWord (a := SKM.ob D (Λ - Λ) (upWord sourceWord))
  (SupportedSectors.tensorWordVacuumEndpoint D Λ Λ sourceWord)
  (SupportedSectors.tensorSourcePath D Λ Λ sourceWord)
  (SupportedSectors.tensorSourceLabels_up D Λ Λ sourceWord)
example (x : SupportedSectors.tensorWordMatrixModule D originalSc m cutoff Λ Λ L sourceWord sourceWord) :
    rowEquiv.symm (rowEquiv x) = x := rowEquiv.symm_apply_apply x
example : rowEquiv (SupportedSectors.tensorMatrixVacuum D originalSc m cutoff Λ Λ L sourceWord) ≠ 0 := by
  intro h
  apply matrixVacuum_ne_zero
  apply rowEquiv.injective
  exact h.trans (map_zero rowEquiv).symm

private abbrev originalEntry := SupportedSectors.tensorOriginalWordEntry D originalSc m cutoff Λ Λ L
  probePairing reservoirPairing sourceWord (a := SKM.ob D (Λ - Λ) (upWord sourceWord))
  (SupportedSectors.tensorWordVacuumEndpoint D Λ Λ sourceWord)
  (SupportedSectors.tensorSourcePath D Λ Λ sourceWord)
  (SupportedSectors.tensorSourceLabels_up D Λ Λ sourceWord)
example := SupportedSectors.tensorRowTargetIso D originalSc m cutoff Λ Λ L
  probePairing reservoirPairing sourceWord (a := SKM.ob D (Λ - Λ) (upWord sourceWord))
  (SupportedSectors.tensorSourcePath D Λ Λ sourceWord)
  (SupportedSectors.tensorSourceLabels_up D Λ Λ sourceWord)
example := SupportedSectors.tensorOriginalRowSourceIso D originalSc m cutoff Λ Λ L
  probePairing reservoirPairing sourceWord
example : originalEntry (SupportedSectors.tensorMatrixVacuum D originalSc m cutoff Λ Λ L sourceWord) ≠ 0 := by
  intro h
  apply matrixVacuum_ne_zero
  apply SupportedSectors.tensorOriginalWordEntry_injective D originalSc m cutoff Λ Λ L
    probePairing reservoirPairing sourceWord (a := SKM.ob D (Λ - Λ) (upWord sourceWord))
    (SupportedSectors.tensorWordVacuumEndpoint D Λ Λ sourceWord)
    (SupportedSectors.tensorSourcePath D Λ Λ sourceWord)
    (SupportedSectors.tensorSourceLabels_up D Λ Λ sourceWord)
  exact h.trans (map_zero originalEntry).symm
example := SupportedSectors.tensorSourceLabels_colors D Λ Λ sourceWord
example := SupportedSectors.tensorPathValueChart D originalSc m cutoff Λ Λ L
  (SupportedSectors.tensorSourcePath D Λ Λ sourceWord)
  (SupportedSectors.tensorSourceLabels_up D Λ Λ sourceWord)
example := SupportedSectors.tensorOriginalSourceUnit D originalSc m cutoff Λ Λ L
  probePairing reservoirPairing sourceWord
example := SupportedSectors.tensorMatrixQuotientObservation D originalSc m cutoff Λ Λ L
  probePairing reservoirPairing sourceWord (a := SKM.ob D (Λ - Λ) (upWord sourceWord))
  (SupportedSectors.tensorWordVacuumEndpoint D Λ Λ sourceWord)
  (SupportedSectors.tensorSourcePath D Λ Λ sourceWord)
  (SupportedSectors.tensorSourceLabels_up D Λ Λ sourceWord)
  (SupportedSectors.tensorMatrixVacuum D originalSc m cutoff Λ Λ L sourceWord)
example := SupportedSectors.tensorMatrixQuotientObservationLinear_apply D originalSc m cutoff Λ Λ L
  probePairing reservoirPairing sourceWord (a := SKM.ob D (Λ - Λ) (upWord sourceWord))
  (SupportedSectors.tensorWordVacuumEndpoint D Λ Λ sourceWord)
  (SupportedSectors.tensorSourcePath D Λ Λ sourceWord)
  (SupportedSectors.tensorSourceLabels_up D Λ Λ sourceWord)
  (SupportedSectors.tensorMatrixVacuum D originalSc m cutoff Λ Λ L sourceWord)
example := SupportedSectors.tensorWordQuotientObservation_apply D originalSc cutoff L m Λ Λ
  probePairing reservoirPairing sourceWord sourceWord (SupportedSectors.tensorSourcePath D Λ Λ sourceWord)
  (SupportedSectors.tensorMatrixVacuum D originalSc m cutoff Λ Λ L sourceWord)
example := SupportedSectors.tensorWordQuotientObservation_path_independent D originalSc cutoff L m Λ Λ
  probePairing reservoirPairing sourceWord sourceWord (SupportedSectors.tensorSourcePath D Λ Λ sourceWord)
  (SupportedSectors.tensorSourcePath D Λ Λ sourceWord)
private def observation := SupportedSectors.tensorWordQuotientObservation D originalSc cutoff L m Λ Λ
  probePairing reservoirPairing sourceWord sourceWord (SupportedSectors.tensorSourcePath D Λ Λ sourceWord)
example (x y : SupportedSectors.tensorWordMatrixModule D originalSc m cutoff Λ Λ L sourceWord sourceWord) := observation.map_add' x y
example (r : ℚ) (x : SupportedSectors.tensorWordMatrixModule D originalSc m cutoff Λ Λ L sourceWord sourceWord) := observation.map_smul' r x
end NonVacuity.SupportedTensorWordObservation
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.SwappedAssembly.SupportedTensorWordObservation
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owned module"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"
