import OddMath.QuiverHecke.SwappedAssembly.SupportedPointwiseLeftwardInverse
import OddMath.QuiverHecke.SwappedAssembly.SupportedTensorVacuum
import OddMath.QuiverHecke.HalfTurn.PowerWordCoordinates
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath OddMath.SKM OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction OddMath.QuiverHecke.SwappedAssembly
namespace NonVacuity.PointwiseLeftwardFixture
local instance tensorHomPi (A C : PiSCat.{0,0,1} ℚ) : PiSupercategory ℚ (A ⟶ C) :=
  PiTwoSupercategory.homPiLeft A C
def collisionDatum : SKM.Datum Bool (Bool → ℤ) where
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

def collisionScalars : SKM.Scalars collisionDatum ℚ where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := fun _ => isUnit_iff_ne_zero.mpr (by norm_num)


abbrev D := collisionDatum
abbrev originalSc := collisionScalars
abbrev Sc := parameterTwist D originalSc
def cutoff (_ : Bool) : ℕ := 20
def L (_ : Bool × ℕ) : ℕ := 20
def m (_ : Bool) : ℕ := 10
def Λ : Bool → ℤ := fun _ => 20
abbrev N := PowerWordContent.powerBound D cutoff L
def labels : List (Col Bool (Bool → ℤ)) := wd D 0 [up false]
theorem upward : ∀ a ∈ labels, a.l.1 = true := by simp [labels,wd]
def path := SPath.reservoirPath labels upward 0
abbrev ν : List Bool := [false]
abbrev σ : List Bool := ν.reverse
abbrev β := PowerWordWeight.wordBlock D Λ ν
def w : ContentCategory D Sc cutoff N β.1 := ⟨⟨ν⟩,rfl⟩
abbrev chosenEquiv := moduleIsoLinearEquiv
  (Pi.isoApp (TensorReservoirWords.valueChart D Sc m cutoff L Λ Λ path upward) β) w
theorem powers_high (q : Bool × ℕ) : 16 ≤ L q * SKM.SYM.elementaryWeight D q := by
  have hw : 0 < SKM.SYM.elementaryWeight D q := by
    unfold SKM.SYM.elementaryWeight
    split_ifs <;> omega
  change 16 ≤ 20 * SKM.SYM.elementaryWeight D q
  omega
theorem bounded_injective :
    Function.Injective (fun x : ExtendedAtMost D originalSc σ σ 2 =>
      powerWordHalfTurnCoordinate D originalSc cutoff L σ σ x.val) :=
  powerWordHalfTurnCoordinate_injective_on_extendedAtMost D originalSc cutoff L
    (fun _ => (by decide : 16 ≤ 20)) powers_high (by decide)
def identityNF : NFIdx σ σ := by
  have hc : Categorification.TypeA.canWord σ.length (1 : Equiv.Perm (Fin σ.length)) = [] := by
    apply List.length_eq_zero_iff.mp
    rw [Categorification.TypeA.length_canWord, Categorification.TypeA.length_one]
  refine ⟨([],1),by simp,by simp,?_⟩
  simp only [List.map_nil,hc,cw,List.reverse_nil,List.nil_append,pl,QuiverHecke.SChain]
def oddIndex : SKM.SYM.CoefficientIndex D := (0,{⟨false,rfl⟩})
def occupied : ExtendedAtMost D originalSc σ σ 2 :=
  ⟨extensionBasis D originalSc σ σ (oddIndex,identityNF),
    Submodule.subset_span ⟨(oddIndex,identityNF),by decide,rfl⟩⟩
def contentVector : (PowerWordWeight.wordAt D Sc cutoff L ν β.1).obj w :=
  powerWordHalfTurnCoordinate D originalSc cutoff L σ σ occupied.val
theorem contentVector_ne_zero : contentVector ≠ 0 := by
  intro hz
  have hh : occupied = (0 : ExtendedAtMost D originalSc σ σ 2) := by
    apply bounded_injective
    change powerWordHalfTurnCoordinate D originalSc cutoff L σ σ occupied.val =
      powerWordHalfTurnCoordinate D originalSc cutoff L σ σ 0
    exact hz.trans (map_zero _).symm
  exact (extensionBasis D originalSc σ σ).ne_zero (oddIndex,identityNF) (congrArg Subtype.val hh)
def chosenVector := chosenEquiv.symm contentVector
theorem chosenVector_ne_zero : chosenVector ≠ 0 := by
  intro hz
  apply contentVector_ne_zero
  have he := congrArg chosenEquiv hz
  simpa only [chosenVector,LinearEquiv.apply_symm_apply,map_zero] using he

theorem probePairing (i : Bool) : (probeCutoff D m i : ℤ) = D.h i Λ := by
  cases i <;> norm_num [probeCutoff, probeDotExponent, m, D, collisionDatum, SKM.Datum.h, Λ]
theorem reservoirPairing (i : Bool) : (cutoff i : ℤ) = D.h i Λ := rfl
def vacuum := SupportedSectors.tensorVacuum D originalSc m cutoff L Λ Λ
def supportedPath :=
  (SupportedSectors.pathFunctor D Sc m cutoff N Λ Λ path).obj vacuum
theorem source_transport_isZero {x y z : Bool → ℤ} (h : x = y)
    (F : probeOldWeightSpace D Sc m Λ x ⟶ elvWeightSpace D Sc cutoff N Λ z)
    (hz : Limits.IsZero (h ▸ F : probeOldWeightSpace D Sc m Λ y ⟶
      elvWeightSpace D Sc cutoff N Λ z)) : Limits.IsZero F := by
  subst y
  exact hz

theorem target_transport_isZero {x y : Bool → ℤ} (h : x = y)
    (F : probeOldWeightSpace D Sc m Λ (-Λ) ⟶ elvWeightSpace D Sc cutoff N Λ x)
    (hz : Limits.IsZero F) : Limits.IsZero (h ▸ F :
      probeOldWeightSpace D Sc m Λ (-Λ) ⟶ elvWeightSpace D Sc cutoff N Λ y) := by
  subst y
  exact hz

/-- The selected one-odd path has a nonzero supported Hom input. -/
theorem supportedPath_nonzero : ¬ Limits.IsZero supportedPath.obj := by
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

def sy : SKM.Symmetrizer D where
  d := fun _ => 1
  pos := fun _ => by decide
  symm := by intro i j; cases i <;> cases j <;> rfl
theorem homogeneous : originalSc.Homogeneous := by
  intro _ _ _ _ _ _ _ _ h
  exact (h rfl).elim
abbrev P := elvProbeReservoir D originalSc m cutoff N Λ Λ probePairing reservoirPairing

abbrev t : Sector Bool := (0,SPath.wordContent labels+0)
def chosen : P.CrossCoeff :=
  elvProbeCrossCoeff D originalSc m cutoff N Λ Λ probePairing reservoirPairing sy homogeneous
def leftward : P.LeftwardData :=
  SupportedSectors.pointwiseLeftwardData D originalSc m cutoff N Λ Λ
    probePairing reservoirPairing sy homogeneous


end NonVacuity.PointwiseLeftwardFixture
