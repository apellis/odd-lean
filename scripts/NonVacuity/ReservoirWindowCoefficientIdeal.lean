import OddMath.QuiverHecke.SwappedAssembly.Sigma.ReservoirWindowCoefficientIdeal
import OddMath.SKM.AugmentedInverseEvaluation
import Mathlib.Algebra.Category.ModuleCat.Ulift
import OddMath.QuiverHecke.SwappedAssembly.Sigma.SameColourBlocks
import OddMath.QuiverHecke.CyclotomicAction.ELVPowerWordHomCoordinates
import OddMath.QuiverHecke.HalfTurn.PowerWordCoordinates
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.SKM
open OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction
open CyclotomicCrossingTensor OddMath.QuiverHecke.SwappedAssembly
namespace NonVacuity.ReservoirWindowCoefficientIdeal
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
private theorem selected_nonzero : ¬ Limits.IsZero (((ContentHomSupport.realization D Sc m cutoff bound β γ G).obj M) γ) := by
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

local instance homPi (A B : PiSCat.{0, 0, 1} ℚ) : PiSupercategory ℚ (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B
private theorem hP : ∀ i, (probeCutoff D m i : ℤ) = D.h i Λ := by
  intro i
  rfl
private theorem hR : ∀ i, (cutoff i : ℤ) = D.h i Λ := by
  intro i
  rfl
private abbrev P := elvProbeReservoir D originalSc m cutoff bound Λ Λ hP hR
private theorem hProbeDown (i : Bool) : -(P.muP sector + D.α i) + D.α i = -P.muP sector := by abel
private def coeff : P.CrossCoeff where
  a _ _ _ _ := 0

private def forgetSuperspace : SVec ℚ ⥤ ModuleCat ℚ where
  obj V := ModuleCat.of ℚ V
  map f := ModuleCat.ofHom f
  map_id _ := rfl
  map_comp _ _ := rfl
private instance : forgetSuperspace.Additive where
  map_add := by intros; rfl
private def evaluation (t : Sector Bool) (N : P.T.obj (-P.muP t))
    (δ : WeightBlocks D Λ (P.muM t)) (a : ContentCategory D Sc cutoff bound δ.1) :
    P.H t ⥤ ModuleCat.{1} ℚ :=
  superfunctorTotalEvaluation (k := ℚ) N ⋙
    CategoryTheory.Pi.eval (fun β : WeightBlocks D Λ (P.muM t) =>
      ContentModules D Sc cutoff bound β.1) δ ⋙
    superfunctorTotalEvaluation (k := ℚ) a ⋙ forgetSuperspace ⋙ ModuleCat.uliftFunctor.{1} ℚ
private instance evaluation_additive (t : Sector Bool) (N : P.T.obj (-P.muP t))
    (δ : WeightBlocks D Λ (P.muM t)) (a : ContentCategory D Sc cutoff bound δ.1) :
    (evaluation t N δ a).Additive := by
  let : (CategoryTheory.Pi.eval (fun β : WeightBlocks D Λ (P.muM t) =>
      ContentModules D Sc cutoff bound β.1) δ).Additive := ⟨by intros; rfl⟩
  have h0 : (superfunctorTotalEvaluation (k := ℚ) (D := P.W.obj (P.muM t)) N).Additive := inferInstance
  have h2 : (superfunctorTotalEvaluation (k := ℚ) (D := SVec ℚ) a).Additive := inferInstance
  have h3 : forgetSuperspace.Additive := inferInstance
  have h4 : (ModuleCat.uliftFunctor.{1, 0} ℚ).Additive := inferInstance
  unfold evaluation
  infer_instance

private def positiveSector (i : Bool) : Sector Bool := (0, Finsupp.single i 20)
private def negativeSector (i : Bool) : Sector Bool := (Finsupp.single i 20, 0)
private def zeroSector (i : Bool) : Sector Bool := (Finsupp.single i 10, Finsupp.single i 10)
private theorem reservoir_positive (i : Bool) : 0 ≤ D.h i (P.muM (positiveSector i)) := by
  change 0 ≤ (-Λ + contentWeight D (Finsupp.single i 20)) i
  rw [contentWeight, Finsupp.weight_single]
  cases i <;> norm_num [D, collisionDatum, Datum.α, Λ]
private theorem probe_negative (i : Bool) : 0 ≤ D.h i (-P.muP (negativeSector i)) := by
  change 0 ≤ (-(Λ - contentWeight D (Finsupp.single i 20))) i
  rw [contentWeight, Finsupp.weight_single]
  cases i <;> norm_num [D, collisionDatum, Datum.α, Λ]
private theorem reservoir_zero (i : Bool) : D.h i (P.muM (zeroSector i)) = 0 := by
  change (-Λ + contentWeight D (Finsupp.single i 10)) i = 0
  rw [contentWeight, Finsupp.weight_single]
  cases i <;> norm_num [D, collisionDatum, Datum.α, Λ]
private theorem probe_zero (i : Bool) : D.h i (-P.muP (zeroSector i)) = 0 := by
  change (-(Λ - contentWeight D (Finsupp.single i 10))) i = 0
  rw [contentWeight, Finsupp.weight_single]
  cases i <;> norm_num [D, collisionDatum, Datum.α, Λ]

/-- The named unit inverse acts on the proved nonzero supported tensor Hom. -/
example (i : Bool) :=
  (SupportedSectors.reservoirCupInverseData D originalSc m cutoff bound Λ Λ hP hR i
    sector supportedObject (evaluation sector M γ wordObject) coeff
    (by change (-20 : ℤ) ≤ 0; omega)).isInverse
example (i : Bool) :=
  (SupportedSectors.reservoirCupInverseData D originalSc m cutoff bound Λ Λ hP hR i
    sector supportedObject (evaluation sector M γ wordObject) coeff
    (by change (-20 : ℤ) ≤ 0; omega)).negPrincipal.isInverse
example (i : Bool) := SupportedSectors.reservoirCupInverseData_principal_of_absent D originalSc m
  cutoff bound Λ Λ hP hR i sector supportedObject (evaluation sector M γ wordObject) coeff
  (by change (-20 : ℤ) ≤ 0; omega) (by simp [StepValid, sector])
example (i : Bool) (r : Fin 20) :=
  SupportedSectors.reservoirCupInverseData_window_of_absent D originalSc m cutoff bound Λ Λ hP hR i
    sector supportedObject (evaluation sector M γ wordObject) coeff
    (by change (-20 : ℤ) ≤ 0; omega) (by simp [StepValid, sector]) r

/-- The opposite local height retains the chosen principal and cap columns. -/
example (i : Bool) (Z : SupportedSectors.H D Sc m cutoff bound Λ Λ (positiveSector i))
    (N : P.T.obj (-P.muP (positiveSector i))) (δ : WeightBlocks D Λ (P.muM (positiveSector i)))
    (a : ContentCategory D Sc cutoff bound δ.1) :=
  (SupportedSectors.reservoirCapInverseData D originalSc m cutoff bound Λ Λ hP hR i
    (positiveSector i) Z (evaluation _ N δ a) coeff (reservoir_positive i)).isInverse
example (i : Bool) (Z : SupportedSectors.H D Sc m cutoff bound Λ Λ (positiveSector i))
    (N : P.T.obj (-P.muP (positiveSector i))) (δ : WeightBlocks D Λ (P.muM (positiveSector i)))
    (a : ContentCategory D Sc cutoff bound δ.1) :=
  SupportedSectors.reservoirCapInverseData_principal D originalSc m cutoff bound Λ Λ hP hR i
    (positiveSector i) Z (evaluation _ N δ a) coeff (reservoir_positive i)
    (by simp [StepValid, positiveSector])
example (i : Bool) (Z : SupportedSectors.H D Sc m cutoff bound Λ Λ (positiveSector i))
    (N : P.T.obj (-P.muP (positiveSector i))) (δ : WeightBlocks D Λ (P.muM (positiveSector i)))
    (a : ContentCategory D Sc cutoff bound δ.1)
    (r : Fin (D.h i (P.muM (positiveSector i))).toNat) :=
  SupportedSectors.reservoirCapInverseData_window D originalSc m cutoff bound Λ Λ hP hR i
    (positiveSector i) Z (evaluation _ N δ a) coeff (reservoir_positive i)
    (by simp [StepValid, positiveSector]) r

/-- Both named records include the common height-zero, empty-window boundary. -/
example (i : Bool) (Z : SupportedSectors.H D Sc m cutoff bound Λ Λ (zeroSector i))
    (N : P.T.obj (-P.muP (zeroSector i))) (δ : WeightBlocks D Λ (P.muM (zeroSector i)))
    (a : ContentCategory D Sc cutoff bound δ.1) :=
  (SupportedSectors.reservoirCapInverseData D originalSc m cutoff bound Λ Λ hP hR i
    (zeroSector i) Z (evaluation _ N δ a) coeff
    (by simpa only [reservoir_zero] using le_refl (0 : ℤ))).negPrincipal.isInverse
example (i : Bool) (Z : SupportedSectors.H D Sc m cutoff bound Λ Λ (zeroSector i))
    (N : P.T.obj (-P.muP (zeroSector i))) (δ : WeightBlocks D Λ (P.muM (zeroSector i)))
    (a : ContentCategory D Sc cutoff bound δ.1) :=
  (SupportedSectors.reservoirCupInverseData D originalSc m cutoff bound Λ Λ hP hR i
    (zeroSector i) Z (evaluation _ N δ a) coeff
    (by simpa only [reservoir_zero] using le_refl (0 : ℤ))).isInverse

private def sy : Symmetrizer D where
  d := fun _ => 1
  pos := fun _ => by norm_num
  symm := by intro i j; cases i <;> cases j <;> rfl
private theorem hc : originalSc.Homogeneous := by
  intro _ _ _ _ _ _ _ _ h
  exact (h rfl).elim
private abbrev outEval := SupportedSectors.reservoirOutputEval D originalSc m cutoff bound Λ Λ hP hR
private abbrev outputIdeal (t : Sector Bool) (δ : WeightBlocks D Λ (P.muM t)) :=
  contentModuleCoefficientIdeal D Sc cutoff bound δ.1 sy
    (parameterTwist_homogeneous D originalSc hc) (P.T.obj (-P.muP t))
private theorem negativeHeight (i : Bool) : D.h i (P.muM sector) ≤ 0 := by
  change (-20 : ℤ) ≤ 0
  omega

example := SupportedSectors.reservoirOutputEval_obj D originalSc m cutoff bound Λ Λ hP hR
  sector γ supportedObject.obj
example := SupportedSectors.reservoirOutputEval_map D originalSc m cutoff bound Λ Λ hP hR
  sector γ (𝟙 supportedObject.obj)
example := SupportedSectors.reservoirOutput_mem_zero D originalSc m cutoff bound Λ Λ hP hR
  sy hc sector γ (𝟙 ((outEval sector γ).obj supportedObject.obj))
example {A B : P.T.obj (-P.muP sector) ⟶ contentModuleTarget D Sc cutoff bound γ.1}
    (f : A ⟶ B) := SupportedSectors.reservoirOutput_mem_zero D originalSc m cutoff bound Λ Λ hP hR
  sy hc sector γ f
example (i : Bool) (r s : ℕ) := SupportedSectors.reservoirCupInverseData_closure_mem
  D originalSc m cutoff bound Λ Λ hP hR sy hc i sector supportedObject γ coeff (negativeHeight i) r s
example (i : Bool) (r s : ℕ) := SupportedSectors.reservoirCupInverseData_negPrincipal_closure_mem
  D originalSc m cutoff bound Λ Λ hP hR sy hc i sector supportedObject γ coeff (negativeHeight i) r s
example (i : Bool) (j : Fin 20) (r : ℕ) (hjr : (j : ℕ) < r) :=
  SupportedSectors.reservoirCupInverseData_boundary_mem D originalSc m cutoff bound Λ Λ hP hR
    sy hc i sector supportedObject γ coeff (negativeHeight i) j r hjr
example (i : Bool) (j : Fin 20) (r : ℕ) :=
  SupportedSectors.reservoirCupInverseData_contraction_mem D originalSc m cutoff bound Λ Λ hP hR
    sy hc i sector supportedObject γ coeff (negativeHeight i) r j

/-- Negating the principal leaves these finite unit rows and their contractions intact. -/
example (i : Bool) (j : Fin 20) (r : ℕ) (hjr : (j : ℕ) < r) :
    (outputIdeal sector γ).mem 1 (P.centralPaddedUnit i sector supportedObject.obj (outEval sector γ) false r ≫
      (SupportedSectors.reservoirCupInverseData D originalSc m cutoff bound Λ Λ hP hR i sector
        supportedObject (outEval sector γ) coeff (negativeHeight i)).negPrincipal.window j) :=
  SupportedSectors.reservoirCupInverseData_boundary_mem D originalSc m cutoff bound Λ Λ hP hR
    sy hc i sector supportedObject γ coeff (negativeHeight i) j r hjr
example (i : Bool) (j : Fin 20) (r : ℕ) :
    (outputIdeal sector γ).mem 1 (P.centralPaddedUnit i sector supportedObject.obj (outEval sector γ) false r ≫
      (SupportedSectors.reservoirCupInverseData D originalSc m cutoff bound Λ Λ hP hR i sector
        supportedObject (outEval sector γ) coeff (negativeHeight i)).negPrincipal.window j -
          if r = (j : ℕ) then 𝟙 _ else 0) :=
  SupportedSectors.reservoirCupInverseData_contraction_mem D originalSc m cutoff bound Λ Λ hP hR
    sy hc i sector supportedObject γ coeff (negativeHeight i) r j

/-- An absent unit inverse row is nonzero at the concrete nonzero collision-supported Hom. -/
example (i : Bool) (j : Fin 20) :
    (SupportedSectors.reservoirCupInverseData D originalSc m cutoff bound Λ Λ hP hR i sector
      supportedObject (outEval sector γ) coeff (negativeHeight i)).window j ≠ 0 := by
  intro hz
  have hδ := (SupportedSectors.reservoirCupInverseData D originalSc m cutoff bound Λ Λ hP hR i sector
    supportedObject (outEval sector γ) coeff (negativeHeight i)).isInverse.2.2.2.1 j j
  rw [hz, Limits.comp_zero, ite_eq_left rfl] at hδ
  have ho : Limits.IsZero ((outEval sector γ).obj supportedObject.obj) :=
    (Limits.IsZero.iff_id_eq_zero _).mpr hδ.symm
  exact selected_nonzero ((superfunctorTotalEvaluation (k := ℚ) M).map_isZero ho)

example (i : Bool) (Z : SupportedSectors.H D Sc m cutoff bound Λ Λ (positiveSector i))
    (δ : WeightBlocks D Λ (P.muM (positiveSector i))) (r s : ℕ) :=
  SupportedSectors.reservoirCapInverseData_closure_mem D originalSc m cutoff bound Λ Λ hP hR sy hc
    i (positiveSector i) Z δ coeff (reservoir_positive i) r s
example (i : Bool) (Z : SupportedSectors.H D Sc m cutoff bound Λ Λ (positiveSector i))
    (δ : WeightBlocks D Λ (P.muM (positiveSector i))) (r s : ℕ) :=
  SupportedSectors.reservoirCapInverseData_negPrincipal_closure_mem D originalSc m cutoff bound Λ Λ hP hR sy hc
    i (positiveSector i) Z δ coeff (reservoir_positive i) r s
example (i : Bool) (Z : SupportedSectors.H D Sc m cutoff bound Λ Λ (positiveSector i))
    (δ : WeightBlocks D Λ (P.muM (positiveSector i)))
    (j : Fin (D.h i (P.muM (positiveSector i))).toNat) (r : ℕ) (hjr : (j : ℕ) < r) :=
  SupportedSectors.reservoirCapInverseData_boundary_mem D originalSc m cutoff bound Λ Λ hP hR sy hc
    i (positiveSector i) Z δ coeff (reservoir_positive i) j r hjr
example (i : Bool) (Z : SupportedSectors.H D Sc m cutoff bound Λ Λ (positiveSector i))
    (δ : WeightBlocks D Λ (P.muM (positiveSector i)))
    (j : Fin (D.h i (P.muM (positiveSector i))).toNat) (r : ℕ) :=
  SupportedSectors.reservoirCapInverseData_contraction_mem D originalSc m cutoff bound Λ Λ hP hR sy hc
    i (positiveSector i) Z δ coeff (reservoir_positive i) j r

private def occupiedNegative (i : Bool) : Sector Bool := (0, Finsupp.single i 1)
private theorem occupiedNegative_height (i : Bool) : D.h i (P.muM (occupiedNegative i)) ≤ 0 := by
  change (-Λ + contentWeight D (Finsupp.single i 1)) i ≤ 0
  rw [contentWeight, Finsupp.weight_single]
  cases i <;> norm_num [D, collisionDatum, Datum.α, Λ]
example (i : Bool) (Z : SupportedSectors.H D Sc m cutoff bound Λ Λ (occupiedNegative i))
    (δ : WeightBlocks D Λ (P.muM (occupiedNegative i))) (r s : ℕ) :=
  SupportedSectors.reservoirCupInverseData_closure_mem D originalSc m cutoff bound Λ Λ hP hR sy hc
    i (occupiedNegative i) Z δ coeff (occupiedNegative_height i) r s
example (i : Bool) (Z : SupportedSectors.H D Sc m cutoff bound Λ Λ (occupiedNegative i))
    (δ : WeightBlocks D Λ (P.muM (occupiedNegative i)))
    (j : Fin (-D.h i (P.muM (occupiedNegative i))).toNat) (r : ℕ) (hjr : (j : ℕ) < r) :=
  SupportedSectors.reservoirCupInverseData_boundary_mem D originalSc m cutoff bound Λ Λ hP hR sy hc
    i (occupiedNegative i) Z δ coeff (occupiedNegative_height i) j r hjr

example (i : Bool) (Z : SupportedSectors.H D Sc m cutoff bound Λ Λ (occupiedNegative i))
    (δ : WeightBlocks D Λ (P.muM (occupiedNegative i)))
    (j : Fin (-D.h i (P.muM (occupiedNegative i))).toNat) :=
  SupportedSectors.reservoirCupInverseData_window D originalSc m cutoff bound Λ Λ hP hR i
    (occupiedNegative i) Z (outEval (occupiedNegative i) δ) coeff (occupiedNegative_height i)
    (by simp [StepValid, occupiedNegative]) j

end NonVacuity.ReservoirWindowCoefficientIdeal
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for owner in #[`OddMath.QuiverHecke.SwappedAssembly.Sigma.ReservoirWindowCoefficientIdeal,
      `OddMath.QuiverHecke.CyclotomicAction.ELVContentHomZero,
      `OddMath.QuiverHecke.CyclotomicAction.ELVReservoirClosureIdeal,
      `OddMath.QuiverHecke.CyclotomicAction.ELVReservoirBoundaryIdeal] do
    let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
    let names := env.header.moduleData[idx]!.constNames
    if names.isEmpty then throwError "Empty owner {owner}"
    for name in names do
      for ax in ← Lean.collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {name}"
    logInfo m!"Audited all {names.size} owned declarations in {owner}"
