import OddMath.QuiverHecke.SwappedAssembly.SupportedPresentation
import OddMath.QuiverHecke.SwappedAssembly.Zigzag
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeDenominatorUnits
import OddMath.QuiverHecke.SwappedAssembly.Sigma.SameColourBlocks
import OddMath.QuiverHecke.CyclotomicAction.ELVPowerWordHomCoordinates
import OddMath.QuiverHecke.HalfTurn.PowerWordCoordinates
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.SKM
open OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction
open CyclotomicCrossingTensor OddMath.QuiverHecke.SwappedAssembly
namespace NonVacuity.SupportedPresentation
local instance piSCatHomPi (A C : PiSCat.{0,0,1} ℚ) : PiSupercategory ℚ (A ⟶ C) :=
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
private def m (_ : Bool) : ℕ := 10
private def L (_ : Bool × ℕ) : ℕ := 10
private abbrev bound := PowerWordContent.powerBound D cutoff L
private def Λ : Bool → ℤ := fun _ => 20
private def sector : Sector Bool := (0, 0)
private def β : WeightBlocks D Λ (-Λ) := SupportedSectors.probeBlock D Λ sector
private def γ : WeightBlocks D Λ (-Λ) := SupportedSectors.reservoirBlock D Λ sector
private def extra : WeightBlocks D Λ (-Λ) := ⟨[false, true], by
  ext b
  cases b <;> norm_num [blockWeight, collisionDatum, SKM.Datum.α]⟩
private theorem extra_ne : extra ≠ γ := by
  intro he
  have hh := congrArg (fun δ => δ.1.card) he
  change (2 : ℕ) = 0 at hh
  omega
private def W := ReservoirWordValue.initialValue D Λ Sc cutoff L
private def forgetFunctor (ν : List Bool) (h : ν = []) :
    ProbeEvaluatedModules D Sc m ν ⥤
      Superfunctor ℚ (OldContentCategory D Sc (probeCutoff D m) []) (SVec ℚ) := by
  subst ν
  exact ObjectProperty.ι _
private instance (ν : List Bool) (h : ν = []) : (forgetFunctor ν h).Additive := by
  subst ν
  exact ⟨by intros; rfl⟩
private instance (ν : List Bool) (h : ν = []) : (forgetFunctor ν h).Linear ℚ := by
  subst ν
  exact ⟨fun _ _ => rfl⟩
private instance (ν : List Bool) (h : ν = []) : IsSuperfunctor ℚ (forgetFunctor ν h) := by
  subst ν
  exact ⟨fun hf => hf⟩
private def forget : Superfunctor ℚ (ProbeCanonicalModules D Sc m β.1)
    (Superfunctor ℚ (OldContentCategory D Sc (probeCutoff D m) []) (SVec ℚ)) :=
  ⟨forgetFunctor _ Multiset.toList_zero⟩
private def G : ContentHomSupport.Hom D Sc m cutoff bound β γ :=
  forget.comp (VacuumTensor.superfunctor (W γ) (probeOldVacuumObject D Sc m))
private def M := WeightTensorVacuum.regularProbe D Sc m Λ
private theorem hUp (i : Bool) : (-Λ) + D.α i = (-Λ) + D.α i := rfl
private theorem hDown (i : Bool) : (-Λ - D.α i) + D.α i = -Λ := sub_add_cancel _ _

example : extra ≠ γ := extra_ne
/-- The collision block has a predecessor even though the selected formal
content is empty; the exact Hom realization still vanishes there. -/
example (i : Bool) : ∃ δ, blockSucc D Λ i (hDown i) δ = extra := by
  apply (exists_blockSucc_iff D Λ i (hDown i) extra).mpr
  cases i <;> simp [extra]
example := ContentHomSupport.obj_off_isZero D Sc m cutoff bound β γ G M extra extra_ne
example := ContentHomSupport.obj_selected D Sc m cutoff bound β γ G M
example := ContentHomSupport.map_selected D Sc m cutoff bound β γ G (𝟙 M)
example (i : Bool) := ContentHomSupport.postE_component D Sc m cutoff bound β γ i (hUp i) G
example (i : Bool) := ContentHomSupport.preF_component D Sc m cutoff bound β γ i (hUp i) G
example (i : Bool) := ContentHomSupport.postE_selected D Sc m cutoff bound β γ i (hUp i) G M
example (i : Bool) (δ : WeightBlocks D Λ (-Λ-D.α i)) :=
  ContentHomSupport.postF_absent_isZero D Sc m cutoff bound β γ i (hDown i) G
    (by simp [γ, sector, SupportedSectors.reservoirBlock]) M δ
example (i : Bool) (N : ProbeOldWeightProduct D Sc m Λ (-Λ-D.α i)) :=
  ContentHomSupport.preE_absent_isZero D Sc m cutoff bound β γ i (hDown i) G
    (by simp [β, sector, SupportedSectors.probeBlock]) N extra
example (p : ZMod 2) :=
  ContentHomSupport.shift_off_isZero D Sc m cutoff bound β γ p G M extra extra_ne

private def postG (i : Bool) : ContentHomSupport.Hom D Sc m cutoff bound β
    (blockSucc D Λ i (hUp i) γ) :=
  G.comp (elvBlockInd D Sc cutoff bound i Λ (hUp i) γ)
example (i : Bool) := ContentHomSupport.postF_component D Sc m cutoff bound β γ i (hUp i) (postG i)
example (i : Bool) := ContentHomSupport.postF_selected D Sc m cutoff bound β γ i (hUp i) (postG i) M
example (i : Bool) := ContentHomSupport.postF_off_isZero D Sc m cutoff bound β γ i (hUp i)
  (postG i) M extra extra_ne
private def preG (i : Bool) : ContentHomSupport.Hom D Sc m cutoff bound
    (blockSucc D Λ i (hUp i) β) γ :=
  (probeOldBlockRes D Sc m i Λ (hUp i) β).comp G
example (i : Bool) := ContentHomSupport.preE_component D Sc m cutoff bound γ i (hUp i) β (preG i)
example (i : Bool) := ContentHomSupport.preE_selected D Sc m cutoff bound γ i (hUp i) β (preG i) M

/-- At the selected component the realization is literally the existing
whole-weight tensor-vacuum functor on every input. -/
private theorem selected_eq (N : ProbeOldWeightProduct D Sc m Λ (-Λ)) :
    ((ContentHomSupport.realization D Sc m cutoff bound β γ G).obj N) γ =
      ((WeightTensorVacuum.selectedHom D Sc m cutoff Λ Λ L).obj N) γ := by
  rw [ContentHomSupport.obj_selected]
  rfl

private abbrev ν : List Bool := []
private abbrev σ : List Bool := ν.reverse
private abbrev C := OldCategory D Sc cutoff
private abbrev wordTarget := powerWordModule D Sc cutoff L ν
private theorem powers_high (j : Bool × ℕ) : 16 ≤ L j * SKM.SYM.elementaryWeight D j := by
  change 16 ≤ 10 * (2 * (j.2 + 1))
  omega
private theorem bounded_injective :
    Function.Injective (fun x : ExtendedAtMost D originalSc σ σ 2 =>
      powerWordHalfTurnCoordinate D originalSc cutoff L σ σ x.val) :=
  powerWordHalfTurnCoordinate_injective_on_extendedAtMost D originalSc cutoff L
    (fun _ => (by decide : 16 ≤ 20)) powers_high (by decide)
private def identityNF : NFIdx σ σ := by
  change NFIdx ([] : List Bool) []
  have hc : Categorification.TypeA.canWord 0 (1 : Equiv.Perm (Fin 0)) = [] := by
    apply List.length_eq_zero_iff.mp
    rw [Categorification.TypeA.length_canWord, Categorification.TypeA.length_one]
  refine ⟨([], 1), by simp, by simp, ?_⟩
  simp only [List.map_nil, List.length_nil, hc, cw, List.reverse_nil,
    List.nil_append, QuiverHecke.pl, QuiverHecke.SChain]
private def oddIndex : SKM.SYM.CoefficientIndex D := (0, {⟨false, rfl⟩, ⟨true, rfl⟩})
private def occupied : ExtendedAtMost D originalSc σ σ 2 :=
  ⟨extensionBasis D originalSc σ σ (oddIndex, identityNF),
    Submodule.subset_span ⟨(oddIndex, identityNF), by decide, rfl⟩⟩
private theorem coordinate_ne_zero : (show wordTarget.obj (⟨ν⟩ : C) from
    powerWordHalfTurnCoordinate D originalSc cutoff L σ σ occupied.val) ≠ 0 := by
  intro hz
  have hh : occupied = (0 : ExtendedAtMost D originalSc σ σ 2) := by
    apply bounded_injective
    change powerWordHalfTurnCoordinate D originalSc cutoff L σ σ occupied.val =
      powerWordHalfTurnCoordinate D originalSc cutoff L σ σ 0
    exact hz.trans (map_zero _).symm
  exact (extensionBasis D originalSc σ σ).ne_zero (oddIndex, identityNF) (congrArg Subtype.val hh)


private def wordObject : ContentCategory D Sc cutoff bound (0 : Multiset Bool) := ⟨⟨[]⟩, rfl⟩
private def vector : (W γ).obj wordObject :=
  powerWordHalfTurnCoordinate D originalSc cutoff L σ σ occupied.val
example : vector ≠ 0 := coordinate_ne_zero

/-- The exact-content realization is occupied at the regular input, not
merely a construction using zero functors. -/
private theorem occupied_output : ¬ Limits.IsZero (((ContentHomSupport.realization D Sc m cutoff bound β γ G).obj M) γ) := by
  intro hz
  let e : ((ContentHomSupport.realization D Sc m cutoff bound β γ G).obj M) γ ≅ W γ :=
    eqToIso (selected_eq M) ≪≫ Pi.isoApp (WeightTensorVacuum.selectedIso D Sc m cutoff Λ Λ L) γ
  have hw : Limits.IsZero (W γ) := hz.of_iso e.symm
  have he := (Limits.IsZero.iff_id_eq_zero (W γ)).mp hw
  have hv := congrArg (fun f : End (W γ) => f.app 0 wordObject vector) he
  apply coordinate_ne_zero
  change vector = 0 at hv
  exact hv

private def supportedObject : SupportedSectors.H D Sc m cutoff bound Λ Λ sector :=
  ⟨ContentHomSupport.realization D Sc m cutoff bound β γ G,
    ContentHomSupport.realization_supported D Sc m cutoff bound β γ G⟩

private theorem probePairing (i : Bool) : (probeCutoff D m i : ℤ) = D.h i Λ := by
  cases i <;> norm_num [probeCutoff, probeDotExponent, m, D, collisionDatum, SKM.Datum.h, Λ]
private theorem reservoirPairing (i : Bool) : (cutoff i : ℤ) = D.h i Λ := rfl
private abbrev P := elvProbeReservoir D originalSc m cutoff bound Λ Λ probePairing reservoirPairing
private def sy : SKM.Symmetrizer D where
  d := fun _ => 1
  pos := by intro _; norm_num
  symm := by intro i j; cases i <;> cases j <;> rfl
private theorem homogeneous : originalSc.Homogeneous := by
  intro _ _ _ _ _ _ _ _ h
  exact (h rfl).elim
private def coefficient :=
  elvProbeCrossCoeff D originalSc m cutoff bound Λ Λ probePairing reservoirPairing sy homogeneous
private theorem coefficient_supernatural : coefficient.IsSupernatural :=
  elvProbeCrossCoeff_isSupernatural D originalSc m cutoff bound Λ Λ probePairing reservoirPairing sy homogeneous

private def probeSector (i : Bool) := nextSector (true, i) true sector
private theorem probeStep_valid (i : Bool) : StepValid (false, i) true (probeSector i) := by
  simp [probeSector, StepValid, nextSector]
private theorem probeStep_return (i : Bool) : nextSector (false, i) true (probeSector i) = sector :=
  SPath.next_upDn_true_true sector
private def probeRaised (i : Bool) : SupportedSectors.H D Sc m cutoff bound Λ Λ (probeSector i) :=
  (SupportedSectors.step D Sc m cutoff bound Λ Λ (false, i) true (probeSector i)
    (probeStep_valid i)).obj ((probeStep_return i).symm ▸ supportedObject)

private def reservoirSector (i : Bool) := nextSector (false, i) false sector
private theorem reservoirStep_valid (i : Bool) : StepValid (true, i) false (reservoirSector i) := by
  simp [reservoirSector, StepValid, nextSector]
private theorem reservoirStep_return (i : Bool) :
    nextSector (true, i) false (reservoirSector i) = sector :=
  SPath.next_dnUp_false_false sector
private def reservoirDotPath (i : Bool) : SPath (wd D 0 [up i]) (reservoirSector i) sector :=
  SPath.one false (reservoirStep_valid i) (reservoirStep_return i)
private def probeCapPath (i : Bool) : SPath (wd D 0 [up i, dn i]) sector sector :=
  SPath.two true true (by trivial) (by simp [StepValid, nextSector])
    (SPath.next_upDn_true_true sector)
private def reservoirCupPath (i : Bool) : SPath (wd D 0 [dn i, up i]) sector sector :=
  SPath.two false false (by trivial) (by simp [StepValid, nextSector])
    (SPath.next_dnUp_false_false sector)
private def mixedCrossPath (i : Bool) :
    SPath (wd D 0 [up i, up i]) (reservoirSector i) (probeSector i) :=
  SPath.two false true (reservoirStep_valid i) (by trivial)
    (by simp [probeSector, reservoirSector, sector, nextSector])
private def shiftedSector (i : Bool) := nextSector (false, i) false (probeSector false)
private def shiftedDotPath (i : Bool) : SPath (wd D 0 [up i]) (shiftedSector i) (probeSector false) :=
  SPath.one false (by simp [StepValid, shiftedSector, nextSector])
    (SPath.next_dnUp_false_false (probeSector false))

/-- The chosen factor's post-E step has its nonzero content shift at this endpoint. -/
example (i : Bool) : homContentShift D i (shiftedSector i).1 = 1 := by
  cases i <;> simp [homContentShift, contentParity, shiftedSector, probeSector, sector,
    nextSector, Finsupp.weight_single, D, collisionDatum]
example (i : Bool) := SupportedSectors.restrictGenImage D originalSc m cutoff bound Λ Λ
  probePairing reservoirPairing (P.dotImage i 0) (shiftedDotPath i) (shiftedDotPath i) (probeRaised false)

example (l : Letter Bool) (side : Bool) (t : Sector Bool) (hv : StepValid l side t) :=
  SupportedSectors.factor_step D originalSc m cutoff bound Λ Λ probePairing reservoirPairing l side t hv
example (i : Bool) := SupportedSectors.factor_pathFunctor D originalSc m cutoff bound Λ Λ
  probePairing reservoirPairing (probeCapPath i)
example (i : Bool) := SupportedSectors.factor_pathFunctor_inclusion D originalSc m cutoff bound Λ Λ
  probePairing reservoirPairing (reservoirCupPath i)
example (i : Bool) := SupportedSectors.factor_path_obj D originalSc m cutoff bound Λ Λ
  probePairing reservoirPairing (reservoirDotPath i) supportedObject
example (i : Bool) := SupportedSectors.restrictGenImage D originalSc m cutoff bound Λ Λ
  probePairing reservoirPairing (P.dotImage i 0) (reservoirDotPath i) (reservoirDotPath i) supportedObject
example (i : Bool) := SupportedSectors.restrictGenImage_hom D originalSc m cutoff bound Λ Λ
  probePairing reservoirPairing (P.dotImage i 0) (reservoirDotPath i) (reservoirDotPath i) supportedObject
example (i : Bool) := SupportedSectors.restrictGenImage_mem D originalSc m cutoff bound Λ Λ
  probePairing reservoirPairing (P.dotImage i 0) (reservoirDotPath i) (reservoirDotPath i) supportedObject
  ((P.dotImage_supernatural i 0 (reservoirDotPath i) (reservoirDotPath i)).mem supportedObject.obj)
example (i : Bool) := SupportedSectors.generatorTransformation D originalSc m cutoff bound Λ Λ
  probePairing reservoirPairing (P.dotImage i 0) (reservoirDotPath i) (reservoirDotPath i)
  (P.dotImage_supernatural i 0 (reservoirDotPath i) (reservoirDotPath i))
example (i : Bool) := SupportedSectors.generatorTransformation_app D originalSc m cutoff bound Λ Λ
  probePairing reservoirPairing (P.dotImage i 0) (reservoirDotPath i) (reservoirDotPath i)
  (P.dotImage_supernatural i 0 (reservoirDotPath i) (reservoirDotPath i)) supportedObject
example (i : Bool) := SupportedSectors.generatorTransformation_mem D originalSc m cutoff bound Λ Λ
  probePairing reservoirPairing (P.dotImage i 0) (reservoirDotPath i) (reservoirDotPath i)
  (P.dotImage_supernatural i 0 (reservoirDotPath i) (reservoirDotPath i))
example (i : Bool) := SupportedSectors.restrictGenImage D originalSc m cutoff bound Λ Λ
  probePairing reservoirPairing (P.capImage i 0) (probeCapPath i) (.nil sector) supportedObject
example (i : Bool) := SupportedSectors.restrictGenImage D originalSc m cutoff bound Λ Λ
  probePairing reservoirPairing (P.cupImage i 0) (.nil sector) (reservoirCupPath i) supportedObject

/-- The mixed equal-colour crossing uses the constructed inverse coefficient;
its naturality input follows from the proved denominator units. -/
example (i : Bool) := SupportedSectors.upwardImage D originalSc m cutoff bound Λ Λ
  probePairing reservoirPairing coefficient (.cross i i, 0) (mixedCrossPath i) (mixedCrossPath i) (probeRaised i)
example (i : Bool) := SupportedSectors.upwardImage_supernatural D originalSc m cutoff bound Λ Λ
  probePairing reservoirPairing coefficient coefficient_supernatural (.cross i i, 0)
  (mixedCrossPath i) (mixedCrossPath i)
example (i : Bool) := SupportedSectors.generatorTransformation D originalSc m cutoff bound Λ Λ
  probePairing reservoirPairing ((P.upwardGens coefficient).image (.cross i i, 0))
  (mixedCrossPath i) (mixedCrossPath i)
  (P.upwardGens_supernatural coefficient coefficient_supernatural (.cross i i, 0) (mixedCrossPath i) (mixedCrossPath i))

open scoped Classical
private def zeroExact (s : Sector Bool) : ContentHomSupport.Hom D Sc m cutoff bound
    (SupportedSectors.probeBlock D Λ s) (SupportedSectors.reservoirBlock D Λ s) :=
  ⟨elvZeroFunctor D Sc cutoff bound (SupportedSectors.reservoirBlock D Λ s).1⟩
private def zeroSupported (s : Sector Bool) : SupportedSectors.H D Sc m cutoff bound Λ Λ s :=
  ⟨ContentHomSupport.realization D Sc m cutoff bound _ _ (zeroExact s),
    ContentHomSupport.realization_supported D Sc m cutoff bound _ _ (zeroExact s)⟩
private def family (s : Sector Bool) : SupportedSectors.H D Sc m cutoff bound Λ Λ s :=
  if h : s = sector then h.symm ▸ supportedObject else zeroSupported s
private theorem family_sector : family sector = supportedObject := by simp [family]
private theorem wt_sector : P.wt sector = 0 := by
  change (Λ - contentWeight D sector.1) + (-Λ + contentWeight D sector.2) = 0
  simp [sector]
private abbrev emptyObject := SKM.ob D (0 : Bool → ℤ) []
private def identityMatrix : SupportedSectors.matrixModule D originalSc m cutoff bound Λ Λ
    family family emptyObject := fun _ _ p => by
  cases p
  exact 𝟙 _
private theorem identityMatrix_ne_zero : identityMatrix ≠ 0 := by
  intro h
  have he := congrArg (fun x => x sector ⟨sector, wt_sector⟩ (.nil sector)) h
  change 𝟙 (family sector) = 0 at he
  rw [family_sector] at he
  have ha := congrArg (fun f : End supportedObject => f.hom) he
  have hv := congrArg (fun f : End supportedObject.obj => (f.app 0 M) γ) ha
  apply occupied_output
  apply (Limits.IsZero.iff_id_eq_zero _).mpr
  exact hv

example : identityMatrix ≠ 0 := identityMatrix_ne_zero
example := SupportedSectors.matrixEquiv D originalSc m cutoff bound Λ Λ
  probePairing reservoirPairing family family emptyObject
example : SupportedSectors.matrixEquiv D originalSc m cutoff bound Λ Λ
    probePairing reservoirPairing family family emptyObject identityMatrix ≠ 0 := by
  intro h
  apply identityMatrix_ne_zero
  apply (SupportedSectors.matrixEquiv D originalSc m cutoff bound Λ Λ
    probePairing reservoirPairing family family emptyObject).injective
  simpa only [map_zero] using h
example (i : Bool) := SupportedSectors.pathHomEquiv_upwardImage D originalSc m cutoff bound Λ Λ
  probePairing reservoirPairing coefficient (.cross i i, 0)
  (mixedCrossPath i) (mixedCrossPath i) (probeRaised i)

private abbrev generators := P.upwardGens coefficient
private theorem native_zigzag : ZigzagRelations originalSc
    (P.layerRep (fun s => (family s).obj) (fun s => (family s).obj) generators) :=
  P.zigzagRelations (P.cupCapZigzag_of generators rfl rfl)

/-- The full contextual zigzag equation transfers on the occupied supported module;
no inversion relation is supplied to this check. -/
example (i : Bool) : SupportedSectors.relationHolds D originalSc m cutoff bound Λ Λ
    probePairing reservoirPairing family family generators (.zigE i 0) :=
  (SupportedSectors.relationHolds_iff D originalSc m cutoff bound Λ Λ
    probePairing reservoirPairing family family generators (.zigE i 0)).2
      (native_zigzag (.zigE i 0) rfl)
example (i : Bool) : SupportedSectors.relationHolds D originalSc m cutoff bound Λ Λ
    probePairing reservoirPairing family family generators (.zigF i 0) :=
  (SupportedSectors.relationHolds_iff D originalSc m cutoff bound Λ Λ
    probePairing reservoirPairing family family generators (.zigF i 0)).2
      (native_zigzag (.zigF i 0) rfl)

example : SupportedSectors.interchangeHolds D originalSc m cutoff bound Λ Λ
    probePairing reservoirPairing family family generators :=
  (SupportedSectors.interchangeHolds_iff D originalSc m cutoff bound Λ Λ
    probePairing reservoirPairing family family generators).2
      (P.interchangeLaw (fun s => (family s).obj) (fun s => (family s).obj)
        (P.upwardGens_supernatural coefficient coefficient_supernatural))

end NonVacuity.SupportedPresentation
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for owner in #[`OddMath.QuiverHecke.SwappedAssembly.SupportedMatrixModules,
      `OddMath.QuiverHecke.SwappedAssembly.SupportedPresentation] do
    let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owned module {owner}"
    let names := env.header.moduleData[idx]!.constNames
    if names.isEmpty then throwError "Empty owned module {owner}"
    for name in names do
      for ax in ← Lean.collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {name}"
    logInfo m!"Audited all {names.size} owned declarations in {owner}"
