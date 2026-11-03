import OddMath.QuiverHecke.SwappedAssembly.SupportedSteps
import OddMath.QuiverHecke.SwappedAssembly.Sigma.SameColourBlocks
import OddMath.QuiverHecke.CyclotomicAction.ELVPowerWordHomCoordinates
import OddMath.QuiverHecke.HalfTurn.PowerWordCoordinates
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.SKM
open OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction
open CyclotomicCrossingTensor OddMath.QuiverHecke.SwappedAssembly
namespace NonVacuity.SupportedSteps
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
example : ¬ Limits.IsZero (((ContentHomSupport.realization D Sc m cutoff bound β γ G).obj M) γ) := by
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
example := (SupportedSectors.inclusion D Sc m cutoff bound Λ Λ sector).obj supportedObject
example := (SupportedSectors.inclusion D Sc m cutoff bound Λ Λ sector).map (𝟙 supportedObject)
example := SupportedSectors.target D Sc m cutoff bound Λ Λ sector
example (i : Bool) := SupportedSectors.probe_valid_iff D Λ i sector
example (i : Bool) := SupportedSectors.reservoir_valid_iff D Λ i sector
example (i : Bool) := SupportedSectors.probeBlock_up D Λ i sector
example (i : Bool) := SupportedSectors.reservoirBlock_down D Λ i sector

private def content : Bool →₀ ℕ := Finsupp.single false 1 + Finsupp.single true 1
private def occupiedSector : Sector Bool := (content, content)
private theorem probe_valid (i : Bool) : StepValid (false, i) true occupiedSector := by
  cases i <;> simp [StepValid, occupiedSector, content]
private theorem reservoir_valid (i : Bool) : StepValid (true, i) false occupiedSector := by
  cases i <;> simp [StepValid, occupiedSector, content]
example (i : Bool) := SupportedSectors.probeBlock_down D Λ i (probe_valid i)
example (i : Bool) := SupportedSectors.reservoirBlock_up D Λ i (reservoir_valid i)

/-- The ambient original weights coincide but the chosen formal blocks
remain different, on each factor. -/
example : SupportedSectors.probeWeight D Λ occupiedSector = SupportedSectors.probeWeight D Λ sector := by
  have hc : contentWeight D content = 0 := by
    rw [content, map_add]
    simp only [contentWeight, Finsupp.weight_single, one_nsmul]
    ext i
    cases i <;> norm_num [D, collisionDatum, SKM.Datum.α]
  simp [SupportedSectors.probeWeight, occupiedSector, sector, hc]
example : (SupportedSectors.probeBlock D Λ occupiedSector).1 ≠
    (SupportedSectors.probeBlock D Λ sector).1 := by
  intro he
  have hc := congrArg (fun b => b.count false) he
  simp [SupportedSectors.probeBlock, occupiedSector, sector, content] at hc


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
private def reservoirRaised (i : Bool) : SupportedSectors.H D Sc m cutoff bound Λ Λ (reservoirSector i) :=
  (SupportedSectors.step D Sc m cutoff bound Λ Λ (true, i) false (reservoirSector i)
    (reservoirStep_valid i)).obj ((reservoirStep_return i).symm ▸ supportedObject)

/-- All four supported steps act on constructed objects from the same
occupied tensor input, with their actual formal endpoint transports. -/
example (i : Bool) := probeRaised i
example (i : Bool) := reservoirRaised i
example (i : Bool) := (SupportedSectors.step D Sc m cutoff bound Λ Λ
  (true, i) true sector (by trivial)).obj (probeRaised i)
example (i : Bool) := (SupportedSectors.step D Sc m cutoff bound Λ Λ
  (false, i) false sector (by trivial)).obj (reservoirRaised i)
example (i : Bool) := SupportedSectors.step_inclusion D Sc m cutoff bound Λ Λ
  (false, i) true (probeSector i) (probeStep_valid i)
example (i : Bool) := SupportedSectors.step_inclusion D Sc m cutoff bound Λ Λ
  (true, i) false (reservoirSector i) (reservoirStep_valid i)
example (i : Bool) := SupportedSectors.step_inclusion D Sc m cutoff bound Λ Λ
  (true, i) true sector (by trivial)
example (i : Bool) := SupportedSectors.step_inclusion D Sc m cutoff bound Λ Λ
  (false, i) false sector (by trivial)

private def shiftedSector (i : Bool) := nextSector (false, i) false (probeSector false)
private theorem shifted_valid (i : Bool) : StepValid (true, i) false (shiftedSector i) := by
  simp [shiftedSector, StepValid, nextSector]
private theorem shifted_return (i : Bool) :
    nextSector (true, i) false (shiftedSector i) = probeSector false :=
  SPath.next_dnUp_false_false (probeSector false)
example (i : Bool) := (SupportedSectors.step D Sc m cutoff bound Λ Λ
  (true, i) false (shiftedSector i) (shifted_valid i)).obj
    ((shifted_return i).symm ▸ probeRaised false)
/-- Nonempty odd probe content makes the reservoir content shift nontrivial. -/
example (i : Bool) : homContentShift D i (shiftedSector i).1 = 1 := by
  cases i <;> simp [homContentShift, contentParity, shiftedSector, probeSector, sector,
    nextSector, Finsupp.weight_single, D, collisionDatum]


end NonVacuity.SupportedSteps
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.SwappedAssembly.SupportedSteps
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owned module"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"
