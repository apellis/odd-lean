import OddMath.QuiverHecke.SwappedAssembly.SupportedTensorMatrixCoefficientObservation
import OddMath.QuiverHecke.SwappedAssembly.SupportedAction
import OddMath.QuiverHecke.SwappedAssembly.SupportedTensorEntryLayers
import OddMath.QuiverHecke.SwappedAssembly.SupportedTensorEntryLayerCharts
import OddMath.QuiverHecke.HalfTurn.PowerWordCoordinates
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath OddMath.SKM OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction OddMath.QuiverHecke.SwappedAssembly
namespace NonVacuity.SupportedTensorEntryLayerCharts
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


private theorem probePairing (i : Bool) : (probeCutoff D m i : ℤ) = D.h i Λ := by
  cases i <;> norm_num [probeCutoff, probeDotExponent, m, D, collisionDatum, SKM.Datum.h, Λ]
private theorem reservoirPairing (i : Bool) : (cutoff i : ℤ) = D.h i Λ := rfl
private def vacuum := SupportedSectors.tensorVacuum D originalSc m cutoff L Λ Λ
private def supportedPath :=
  (SupportedSectors.pathFunctor D Sc m cutoff N Λ Λ path).obj vacuum

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


private abbrev sourceWord : List Bool := [true,false]
private abbrev sourceSector : Sector Bool :=
  (0,SupportedSectors.tensorSourceContent D Λ Λ sourceWord)

private theorem sourceObject_nonzero :
    ¬ Limits.IsZero (SupportedSectors.tensorSourceObject D originalSc m cutoff Λ Λ L sourceWord).obj := by
  change ¬ Limits.IsZero supportedPath.obj
  exact supportedPath_nonzero

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

private def sy : Symmetrizer D where
  d := fun _ => 1
  pos := by intro _; norm_num
  symm := by intro i j; cases i <;> cases j <;> rfl

private theorem homogeneous : originalSc.Homogeneous := by
  intro _ _ _ _ _ _ _ _ h
  exact (h rfl).elim

private abbrev P := elvProbeReservoir D originalSc m cutoff N Λ Λ probePairing reservoirPairing
private abbrev coeff := elvProbeCrossCoeff D originalSc m cutoff N Λ Λ
  probePairing reservoirPairing sy homogeneous
private abbrev leftward := SupportedSectors.pointwiseLeftwardData D originalSc m cutoff N Λ Λ
  probePairing reservoirPairing sy homogeneous
private def Gs := SupportedSectors.tensorSourceFamily D originalSc m cutoff Λ Λ L sourceWord
private def Ys := SupportedSectors.tensorTargetFamily D originalSc m cutoff Λ Λ L

/-- The complete presentation obligations hold on the same source and
target families whose selected tensor matrix is proved nonzero. -/
example : SwappedObligations originalSc
    (P.layerRep (fun s => (Gs s).obj) (fun s => (Ys s).obj) (P.swappedGens coeff leftward)) :=
  SupportedSectors.pointwiseObligations D originalSc m cutoff N Λ Λ
    probePairing reservoirPairing sy homogeneous Gs Ys

private def nativeAction : UpwardModuleAction D originalSc (Λ - Λ) :=
  SupportedSectors.pointwiseUpwardModuleAction D originalSc m cutoff N Λ Λ
    probePairing reservoirPairing sy homogeneous Gs Ys (Λ - Λ)

/-- The proved occupied tensor matrix is a vector in the actual module
of the complete action, not an independent comparison module. -/
private def actionVacuum : nativeAction.V sourceWord :=
  SupportedSectors.tensorMatrixVacuum D originalSc m cutoff Λ Λ L sourceWord

private theorem actionVacuum_ne_zero : actionVacuum ≠ 0 := matrixVacuum_ne_zero

example : SupportedSectors.tensorMatrixVacuum D originalSc m cutoff Λ Λ L sourceWord ≠ 0 :=
  matrixVacuum_ne_zero
example : actionVacuum ≠ 0 := actionVacuum_ne_zero
example : Nontrivial (nativeAction.V sourceWord) := ⟨⟨actionVacuum, 0, actionVacuum_ne_zero⟩⟩

/-- The action of the identity diagram retains the actual nonzero tensor
matrix vacuum, with every action hypothesis supplied by the construction. -/
example : nativeAction.act sourceWord sourceWord (𝟙 _) actionVacuum ≠ 0 := by
  rw [nativeAction.act_id]
  exact actionVacuum_ne_zero

private def sourceDot := SKM.lay D (Λ - Λ) [] (.dot true) [up false]

/-- The complete native action's literal odd dot layer is seen by the
original-weight whole-Hom entry on the proved nonzero matrix vacuum. -/
example := SupportedSectors.tensorOriginalWordEntry_layer D originalSc m cutoff Λ Λ L
  probePairing reservoirPairing sourceWord (P.swappedGens coeff leftward)
  sourceDot (SKM.lay_valid D (Λ - Λ) [] (.dot true) [up false])
  (SupportedSectors.tensorWordVacuumEndpoint D Λ Λ sourceWord)
  (SupportedSectors.tensorSourcePath D Λ Λ sourceWord)
  (SupportedSectors.tensorSourcePath D Λ Λ sourceWord)
  (by simp [sourceDot, SKM.lay, SKM.sig, SKM.Shape.dom, wd])
  (by simp [sourceDot, SKM.lay, SKM.sig, SKM.Shape.cod, wd])
  (SupportedSectors.tensorMatrixVacuum D originalSc m cutoff Λ Λ L sourceWord)


private abbrev content := SupportedSectors.tensorSourceContent D Λ Λ sourceWord
private theorem content_eq : content = Finsupp.single false 1 + Finsupp.single true 1 := by
  simp only [content, sourceWord, SupportedSectors.tensorSourceContent,
    SupportedSectors.tensorSourceLabels, upWord, List.map_cons, List.map_nil, wd_cons, wd_nil,
    SPath.wordContent, add_zero]
  exact add_comm _ _
private theorem dotValid : StepValid (up true) false (0,content) := by
  simp [StepValid, content_eq]
private def dotLeft : SPath sourceDot.left (0,content) (0,content) := .nil _
private theorem dotLeft_up : ∀ a ∈ sourceDot.left, a.l.1 = true := by simp [sourceDot, SKM.lay, wd]
private theorem dotRight_up : ∀ a ∈ sourceDot.right, a.l.1 = true := by simp [sourceDot, SKM.lay, wd]
private def dotRight : SPath sourceDot.right (0,content - Finsupp.single true 1) (0,0) := by
  simpa [sourceDot, SKM.lay, content_eq, SPath.wordContent, wd] using
    SPath.reservoirPath sourceDot.right dotRight_up 0
private theorem dotUp : ∀ a ∈ sourceDot.dom.word, a.l.1 = true := by
  simp [sourceDot, SKM.lay, SKM.sig, SKM.Shape.dom, wd]
private def dotPath : SPath sourceDot.dom.word (0,content) (0,0) :=
  (dotLeft.append (.cons (Col.mk (up true) (SKM.wt D (Λ - Λ) [up false])) false
    (0,content) dotValid (.nil _))).append dotRight

example := SupportedSectors.tensorLayerDotRaw_arrow D originalSc m cutoff Λ Λ L
  probePairing reservoirPairing (Λ - Λ) [] [up false] true dotValid dotLeft dotLeft_up dotRight dotRight_up
  coeff leftward
example := SupportedSectors.tensorOriginalWordLayer_dot D originalSc m cutoff Λ Λ L
  probePairing reservoirPairing (Λ - Λ) [] [up false] true
  dotValid dotLeft dotLeft_up dotRight dotRight_up
  (TensorReservoirWords.pathHom D Sc m cutoff L Λ Λ dotPath dotUp)
  (SupportedSectors.tensorRowTargetIso D originalSc m cutoff Λ Λ L
    probePairing reservoirPairing sourceWord dotPath dotUp) coeff leftward
example := SupportedSectors.tensorLayerDotAt_eq D originalSc m cutoff L Λ Λ
  probePairing reservoirPairing (Λ - Λ) [] [up false] true dotValid dotLeft dotLeft_up dotRight dotRight_up coeff

private def sourceCross := SKM.lay D (Λ - Λ) [] (.cross true false) []
private theorem crossValid₁ : StepValid (up true) false (0,content) := dotValid
private theorem crossValid₂ : StepValid (up false) false (nextSector (up true) false (0,content)) := by
  simp [StepValid, nextSector, content_eq]
private theorem crossValid₃ : StepValid (up false) false (0,content) := by
  simp [StepValid, content_eq]
private theorem crossValid₄ : StepValid (up true) false (nextSector (up false) false (0,content)) := by
  simp [StepValid, nextSector, content_eq]
private theorem crossEnd : nextSector (up false) false (nextSector (up true) false (0,content)) =
    nextSector (up true) false (nextSector (up false) false (0,content)) := by
  apply Prod.ext
  · rfl
  · ext i
    cases i <;> simp [nextSector, content_eq]
private def crossLeft : SPath sourceCross.left (0,content) (0,content) := .nil _
private theorem crossLeft_up : ∀ a ∈ sourceCross.left, a.l.1 = true := by simp [sourceCross, SKM.lay, wd]
private theorem crossRight_up : ∀ a ∈ sourceCross.right, a.l.1 = true := by simp [sourceCross, SKM.lay, wd]
private def crossRight : SPath sourceCross.right
    (0,content - Finsupp.single false 1 - Finsupp.single true 1) (0,0) := by
  have hc : content - Finsupp.single false 1 - Finsupp.single true 1 = 0 := by
    ext i
    cases i <;> simp [content_eq]
  change SPath [] (0,content - Finsupp.single false 1 - Finsupp.single true 1) (0,0)
  rw [hc]
  exact .nil _
private theorem crossUp : ∀ a ∈ sourceCross.dom.word, a.l.1 = true := by
  simp [sourceCross, SKM.lay, SKM.sig, SKM.Shape.dom, wd]
private theorem crossUp' : ∀ a ∈ sourceCross.cod.word, a.l.1 = true := by
  simp [sourceCross, SKM.lay, SKM.sig, SKM.Shape.cod, wd]
private def crossSourcePath : SPath sourceCross.dom.word (0,content) (0,0) :=
  (crossLeft.append (SPath.two
    (c₁ := Col.mk (up true) (SKM.wt D (SKM.wt D (Λ - Λ) []) [up false]))
    (c₂ := Col.mk (up false) (SKM.wt D (Λ - Λ) []))
    false false crossValid₁ crossValid₂ crossEnd)).append crossRight
private def crossTargetPath : SPath sourceCross.cod.word (0,content) (0,0) :=
  (crossLeft.append (SPath.two
    (c₁ := Col.mk (up false) (SKM.wt D (SKM.wt D (Λ - Λ) []) [up true]))
    (c₂ := Col.mk (up true) (SKM.wt D (Λ - Λ) []))
    false false crossValid₃ crossValid₄ rfl)).append crossRight

example := SupportedSectors.tensorLayerCrossRaw_arrow D originalSc m cutoff Λ Λ L
  probePairing reservoirPairing (Λ - Λ) [] [] true false
  crossValid₁ crossValid₂ crossValid₃ crossValid₄ crossEnd crossLeft crossLeft_up crossRight crossRight_up
  coeff leftward
example := SupportedSectors.tensorOriginalWordLayer_cross D originalSc m cutoff Λ Λ L
  probePairing reservoirPairing (Λ - Λ) [] [] true false
  crossValid₁ crossValid₂ crossValid₃ crossValid₄ crossEnd crossLeft crossLeft_up crossRight crossRight_up
  (TensorReservoirWords.pathHom D Sc m cutoff L Λ Λ crossSourcePath crossUp)
  (TensorReservoirWords.pathHom D Sc m cutoff L Λ Λ crossTargetPath crossUp')
  (SupportedSectors.tensorRowTargetIso D originalSc m cutoff Λ Λ L
    probePairing reservoirPairing sourceWord crossSourcePath crossUp)
  (SupportedSectors.tensorRowTargetIso D originalSc m cutoff Λ Λ L
    probePairing reservoirPairing sourceWord crossTargetPath crossUp') coeff leftward
example := SupportedSectors.tensorLayerCrossAt_eq D originalSc m cutoff L Λ Λ
  probePairing reservoirPairing (Λ - Λ) [] [] true false
  crossValid₁ crossValid₂ crossValid₃ crossValid₄ crossEnd crossLeft crossLeft_up crossRight crossRight_up
  coeff (by decide : true ≠ false)

namespace Repeated
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
private def labels : List (Col Bool (Bool → ℤ)) := wd D (Λ - Λ) [up true,up true]
private theorem upward : ∀ a ∈ labels, a.l.1 = true := by simp [labels,wd]
private def path := SPath.reservoirPath labels upward 0
private abbrev ν : List Bool := [true,true]
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


private theorem probePairing (i : Bool) : (probeCutoff D m i : ℤ) = D.h i Λ := by
  cases i <;> norm_num [probeCutoff, probeDotExponent, m, D, collisionDatum, SKM.Datum.h, Λ]
private theorem reservoirPairing (i : Bool) : (cutoff i : ℤ) = D.h i Λ := rfl
private def vacuum := SupportedSectors.tensorVacuum D originalSc m cutoff L Λ Λ
private def supportedPath :=
  (SupportedSectors.pathFunctor D Sc m cutoff N Λ Λ path).obj vacuum

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
independent odd coefficients, for the repeated odd source word. -/
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


private abbrev sourceWord : List Bool := [true,true]
private abbrev sourceSector : Sector Bool :=
  (0,SupportedSectors.tensorSourceContent D Λ Λ sourceWord)

private theorem sourceObject_nonzero :
    ¬ Limits.IsZero (SupportedSectors.tensorSourceObject D originalSc m cutoff Λ Λ L sourceWord).obj := by
  change ¬ Limits.IsZero supportedPath.obj
  exact supportedPath_nonzero

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

private def sy : Symmetrizer D where
  d := fun _ => 1
  pos := by intro _; norm_num
  symm := by intro i j; cases i <;> cases j <;> rfl

private theorem homogeneous : originalSc.Homogeneous := by
  intro _ _ _ _ _ _ _ _ h
  exact (h rfl).elim

private abbrev P := elvProbeReservoir D originalSc m cutoff N Λ Λ probePairing reservoirPairing
private abbrev coeff := elvProbeCrossCoeff D originalSc m cutoff N Λ Λ
  probePairing reservoirPairing sy homogeneous
private abbrev leftward := SupportedSectors.pointwiseLeftwardData D originalSc m cutoff N Λ Λ
  probePairing reservoirPairing sy homogeneous
private def Gs := SupportedSectors.tensorSourceFamily D originalSc m cutoff Λ Λ L sourceWord
private def Ys := SupportedSectors.tensorTargetFamily D originalSc m cutoff Λ Λ L

/-- The complete presentation obligations hold on the same source and
target families whose selected tensor matrix is proved nonzero. -/
example : SwappedObligations originalSc
    (P.layerRep (fun s => (Gs s).obj) (fun s => (Ys s).obj) (P.swappedGens coeff leftward)) :=
  SupportedSectors.pointwiseObligations D originalSc m cutoff N Λ Λ
    probePairing reservoirPairing sy homogeneous Gs Ys

private def nativeAction : UpwardModuleAction D originalSc (Λ - Λ) :=
  SupportedSectors.pointwiseUpwardModuleAction D originalSc m cutoff N Λ Λ
    probePairing reservoirPairing sy homogeneous Gs Ys (Λ - Λ)

/-- The proved occupied tensor matrix is a vector in the actual module
of the complete action, not an independent comparison module. -/
private def actionVacuum : nativeAction.V sourceWord :=
  SupportedSectors.tensorMatrixVacuum D originalSc m cutoff Λ Λ L sourceWord

private theorem actionVacuum_ne_zero : actionVacuum ≠ 0 := matrixVacuum_ne_zero

example : SupportedSectors.tensorMatrixVacuum D originalSc m cutoff Λ Λ L sourceWord ≠ 0 :=
  matrixVacuum_ne_zero
example : actionVacuum ≠ 0 := actionVacuum_ne_zero
example : Nontrivial (nativeAction.V sourceWord) := ⟨⟨actionVacuum, 0, actionVacuum_ne_zero⟩⟩

/-- The action of the identity diagram retains the actual nonzero tensor
matrix vacuum, with every action hypothesis supplied by the construction. -/
example : nativeAction.act sourceWord sourceWord (𝟙 _) actionVacuum ≠ 0 := by
  rw [nativeAction.act_id]
  exact actionVacuum_ne_zero


private def sourceSame := SKM.lay D (Λ - Λ) [] (.cross true true) []
private abbrev content := SupportedSectors.tensorSourceContent D Λ Λ sourceWord
private theorem content_eq : content = Finsupp.single true 1 + Finsupp.single true 1 := by
  simp only [content, sourceWord, SupportedSectors.tensorSourceContent,
    SupportedSectors.tensorSourceLabels, upWord, List.map_cons, List.map_nil, wd_cons, wd_nil,
    SPath.wordContent, add_zero]
private theorem valid₁ : StepValid (up true) false (0,content) := by
  simp [StepValid, content_eq]
private theorem valid₂ : StepValid (up true) false (nextSector (up true) false (0,content)) := by
  simp [StepValid, nextSector, content_eq]
private def leftPath : SPath sourceSame.left (0,content) (0,content) := .nil _
private theorem left_up : ∀ a ∈ sourceSame.left, a.l.1 = true := by simp [sourceSame, SKM.lay, wd]
private theorem right_up : ∀ a ∈ sourceSame.right, a.l.1 = true := by simp [sourceSame, SKM.lay, wd]
private def rightPath : SPath sourceSame.right
    (0,content - Finsupp.single true 1 - Finsupp.single true 1) (0,0) := by
  have hc : content - Finsupp.single true 1 - Finsupp.single true 1 = 0 := by
    ext i
    cases i <;> simp [content_eq]
  change SPath [] (0,content - Finsupp.single true 1 - Finsupp.single true 1) (0,0)
  rw [hc]
  exact .nil _
private theorem layer_upward : ∀ a ∈ sourceSame.dom.word, a.l.1 = true := by
  simp [sourceSame, SKM.lay, SKM.sig, SKM.Shape.dom, wd]
private def layerPath : SPath sourceSame.dom.word (0,content) (0,0) :=
  (leftPath.append (.cons
    (Col.mk (up true) (SKM.wt D (SKM.wt D (Λ - Λ) []) [up true])) false (0,content) valid₁
    (.cons (Col.mk (up true) (SKM.wt D (Λ - Λ) [])) false _ valid₂ (.nil _)))).append rightPath

example := SupportedSectors.tensorLayerSameCrossRaw_arrow D originalSc m cutoff Λ Λ L
  probePairing reservoirPairing (Λ - Λ) [] [] true
  valid₁ valid₂ leftPath left_up rightPath right_up coeff leftward
example := SupportedSectors.tensorOriginalWordLayer_sameCross D originalSc m cutoff Λ Λ L
  probePairing reservoirPairing (Λ - Λ) [] [] true
  valid₁ valid₂ leftPath left_up rightPath right_up
  (TensorReservoirWords.pathHom D Sc m cutoff L Λ Λ layerPath layer_upward)
  (SupportedSectors.tensorRowTargetIso D originalSc m cutoff Λ Λ L
    probePairing reservoirPairing sourceWord layerPath layer_upward) coeff leftward
example := SupportedSectors.tensorLayerSameCrossAt_eq D originalSc m cutoff L Λ Λ
  probePairing reservoirPairing (Λ - Λ) [] [] true
  valid₁ valid₂ leftPath left_up rightPath right_up coeff
end Repeated

end NonVacuity.SupportedTensorEntryLayerCharts

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for owner in #[`OddMath.QuiverHecke.SwappedAssembly.SupportedTensorEntryLayerCharts,
      `OddMath.QuiverHecke.SwappedAssembly.SupportedTensorEntryLayers,
      `OddMath.QuiverHecke.SwappedAssembly.SupportedAction,
      `OddMath.QuiverHecke.SwappedAssembly.SupportedTensorMatrixCoefficientObservation] do
    let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
    let names := env.header.moduleData[idx]!.constNames
    if names.isEmpty then throwError "Empty owned module {owner}"
    for name in names do
      for ax in ← Lean.collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {name}"
    logInfo m!"Audited {names.size} owned declarations in {owner}: standard axioms"
  for name in #[``NonVacuity.SupportedTensorEntryLayerCharts.contentVector_ne_zero,
      ``NonVacuity.SupportedTensorEntryLayerCharts.supportedPath_nonzero,
      ``NonVacuity.SupportedTensorEntryLayerCharts.matrixVacuum_ne_zero,
      ``NonVacuity.SupportedTensorEntryLayerCharts.actionVacuum_ne_zero,
      ``NonVacuity.SupportedTensorEntryLayerCharts.Repeated.matrixVacuum_ne_zero,
      ``NonVacuity.SupportedTensorEntryLayerCharts.Repeated.actionVacuum_ne_zero] do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo "Audited the constructed nonzero-vector proofs in both word fixtures: standard axioms"

