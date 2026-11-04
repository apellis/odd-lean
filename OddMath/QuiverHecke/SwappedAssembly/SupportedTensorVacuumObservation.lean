import OddMath.QuiverHecke.SwappedAssembly.SupportedTensorUnitObservation

/-! # Canonical observation of the supported tensor vacuum

SwappedVacuumCoordinates §§3–7: the cyclic matrix vacuum has precisely
the prescribed original-weight source chart. The cyclic observation
therefore reads its source identity quotient class.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath.SKM
namespace OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
open CyclotomicAction ELVOld
universe u v w r
local instance tensorVacuumObservationHomPi {k : Type u} [CommRing k] (A C : PiSCat.{u,u,u + 1} k) :
    PiSupercategory k (A ⟶ C) := PiTwoSupercategory.homPiLeft A C
private theorem fullSubcategory_eqToHom {C : Type v} [Category.{w} C]
    (P : ObjectProperty C) {X Y : P.FullSubcategory} (h : X = Y) :
    (eqToHom h).hom = eqToHom (congrArg ObjectProperty.FullSubcategory.obj h) := by
  cases h
  rfl

variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : Datum I X) (Sc : Scalars D k) (m cutoff : I → ℕ) (ΛP ΛR : X) (L : I × ℕ → ℕ)
local notation "Tw" => parameterTwist D Sc
local notation "N" => PowerWordContent.powerBound D cutoff L
variable (hP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hR : ∀ i, (cutoff i : ℤ) = D.h i ΛR) (s : List I)
local notation "p" => tensorSourcePath D ΛP ΛR s
local notation "up" => tensorSourceLabels_up D ΛP ΛR s
local notation "endpt" => tensorWordVacuumEndpoint D ΛP ΛR s
local notation "cS" => tensorSourceContent D ΛP ΛR s
local notation "P" => elvProbeReservoir D Sc m cutoff N ΛP ΛR hP hR

private theorem matrixVacuum_entry :
    tensorMatrixVacuum D Sc m cutoff ΛP ΛR L s (0,cS) ⟨(0,0),endpt⟩ p =
      eqToHom (tensorSourceFamily_source D Sc m cutoff ΛP ΛR L s) ≫
        eqToHom (congrArg (pathFunctor D Tw m cutoff N ΛP ΛR p).obj
          (tensorTargetFamily_zero D Sc m cutoff ΛP ΛR L)).symm := by
  classical
  simp [tensorMatrixVacuum,tensorSourceFamily,tensorTargetFamily]

/-- The canonical row projection reads the identity of the specified
source word, through the actual factor path chart. -/
theorem tensorVacuumRowProjection_vacuum :
    tensorVacuumRowProjection D Sc m cutoff ΛP ΛR L hP hR s endpt p
      (tensorMatrixVacuum D Sc m cutoff ΛP ΛR L s) =
      eqToHom (congrArg (fun Z : H D Tw m cutoff N ΛP ΛR (0,cS) => Z.obj)
        (tensorSourceFamily_source D Sc m cutoff ΛP ΛR L s)) ≫
        eqToHom (factor_path_obj D Sc m cutoff N ΛP ΛR hP hR p
          (tensorVacuum D Sc m cutoff L ΛP ΛR)) := by
  dsimp only [tensorVacuumRowProjection, MatrixSourceRow.projectionAt,
    LinearMap.comp_apply, MatrixSourceRow.projection, LinearMap.coe_mk, AddHom.coe_mk]
  rw [matrixVacuum_entry]
  simp only [entryEquiv,LinearEquiv.trans_apply,LinearEquiv.coe_toLinearMap,Linear.homCongr_apply,
    Iso.refl_inv,Category.id_comp,eqToIso.hom]
  change ((eqToHom (tensorSourceFamily_source D Sc m cutoff ΛP ΛR L s)).hom ≫ eqToHom _) ≫ eqToHom _ = _
  simp only [fullSubcategory_eqToHom,eqToHom_trans]

/-- The vacuum's original-weight row is its prescribed source chart. -/
theorem tensorOriginalWordEntry_vacuum :
    tensorOriginalWordEntry D Sc m cutoff ΛP ΛR L hP hR s endpt p up
      (tensorMatrixVacuum D Sc m cutoff ΛP ΛR L s) =
      (tensorOriginalRowSourceIso D Sc m cutoff ΛP ΛR L hP hR s).hom := by
  dsimp only [tensorOriginalWordEntry,tensorOriginalRowEntry,LinearMap.comp_apply,
    TensorEntryPullback.linear,LinearMap.coe_mk,AddHom.coe_mk]
  rw [tensorVacuumRowProjection_vacuum]
  simp only [TensorEntryPullback.map,tensorOriginalRowSourceIso,Iso.trans_hom,Functor.mapIso_hom,
    Iso.symm_hom,eqToIso.hom,Category.assoc]
  rfl

local notation "R₀" => WeightTensorVacuum.regularProbe D Tw m ΛP
local notation "β" => tensorSourceWordBlock D ΛP ΛR s
local notation "w" => PowerWordContentCyclicity.wordObject D Tw cutoff L s.reverse (s.reverse : Multiset I) rfl

/-- The canonical value of an original-input source-word row through its
normalized global source path chart, evaluated on its prescribed unit. -/
def tensorSourceWordValue
    (f : tensorOriginalRowSource D Sc m cutoff ΛP ΛR L s ⟶
      TensorReservoirWords.pathHom D Tw m cutoff L ΛP ΛR p up) :=
  (((tensorSourcePathValueChart D Sc m cutoff ΛP ΛR L s).hom β).total w)
    ((((f.total R₀) β).total w) (tensorOriginalSourceUnit D Sc m cutoff ΛP ΛR L hP hR s))

attribute [local irreducible] tensorOriginalRowSourceIso tensorSourcePathValueChart tensorOriginalSourceUnit
  tensorOriginalWordEntry tensorMatrixVacuum tensorSourceWordValue

/-- The prescribed source unit is sent to the literal old-word unit by
its unchanged whole source chart and global path value chart. -/
theorem tensorOriginalSourceUnit_apply :
    tensorSourceWordValue D Sc m cutoff ΛP ΛR L hP hR s
      (tensorOriginalRowSourceIso D Sc m cutoff ΛP ΛR L hP hR s).hom =
      PowerWordYoneda.unitVector D Tw cutoff L s.reverse := by
  let e := tensorOriginalRowSourceIso D Sc m cutoff ΛP ΛR L hP hR s
  let C := moduleIsoLinearEquiv (Pi.isoApp (tensorSourcePathValueChart D Sc m cutoff ΛP ΛR L s) β) w
  have hR₀ := congrArg (fun f : End (TensorReservoirWords.pathHom D Tw m cutoff L ΛP ΛR p up) => f.total R₀) e.inv_hom_id
  rw [Superfunctor.comp_total] at hR₀
  rw [show (𝟙 _ : End (TensorReservoirWords.pathHom D Tw m cutoff L ΛP ΛR p up)).total R₀ = 𝟙 _ from
    SuperNatTrans.id_total _ R₀] at hR₀
  have hβ := congrFun hR₀ β
  have hw := congrArg (fun f : End (((TensorReservoirWords.pathHom D Tw m cutoff L ΛP ΛR p up).obj R₀) β) => f.total w) hβ
  change ((e.inv.total R₀) β ≫ (e.hom.total R₀) β).total w =
    (𝟙 _ : End (((TensorReservoirWords.pathHom D Tw m cutoff L ΛP ΛR p up).obj R₀) β)).total w at hw
  rw [Superfunctor.comp_total,show (𝟙 _ : End (((TensorReservoirWords.pathHom D Tw m cutoff L ΛP ΛR p up).obj R₀) β)).total w = 𝟙 _ from
    SuperNatTrans.id_total _ w] at hw
  have hz := congrArg (fun f => f (C.symm (PowerWordYoneda.unitVector D Tw cutoff L s.reverse))) hw
  change ((e.hom.total R₀) β).total w
    (((e.inv.total R₀) β).total w (C.symm (PowerWordYoneda.unitVector D Tw cutoff L s.reverse))) =
      C.symm (PowerWordYoneda.unitVector D Tw cutoff L s.reverse) at hz
  unfold tensorSourceWordValue tensorOriginalSourceUnit
  change C (((e.hom.total R₀) β).total w
    (((e.inv.total R₀) β).total w (C.symm (PowerWordYoneda.unitVector D Tw cutoff L s.reverse)))) = _
  rw [hz,C.apply_symm_apply]

/-- The cyclic matrix vacuum has the literal old-word unit as its
canonical source-chart value. -/
theorem tensorMatrixVacuum_unit :
    tensorSourceWordValue D Sc m cutoff ΛP ΛR L hP hR s
      (tensorOriginalWordEntry D Sc m cutoff ΛP ΛR L hP hR s endpt p up
        (tensorMatrixVacuum D Sc m cutoff ΛP ΛR L s)) =
      PowerWordYoneda.unitVector D Tw cutoff L s.reverse := by
  exact (congrArg (tensorSourceWordValue D Sc m cutoff ΛP ΛR L hP hR s)
    (tensorOriginalWordEntry_vacuum D Sc m cutoff ΛP ΛR L hP hR s)).trans
      (tensorOriginalSourceUnit_apply D Sc m cutoff ΛP ΛR L hP hR s)

/-- The literal word unit has the source coefficient-one identity class. -/
theorem tensorSourceUnit_class :
    PowerWordQuotientCoordinates.coordinate D Sc cutoff L s s
      (PowerWordYoneda.unitVector D Tw cutoff L s.reverse) =
      (PowerWordQuotientCoordinates.kernel D Sc cutoff L s s).mkQ
        (sourceCoefficientHom D Sc 1 (𝟙 _)) := by
  have h := PowerWordQuotientCoordinates.coefficient_unit_class D Sc cutoff L s (1 : SKM.SYM D k)
  simp only [map_one,End.one_def] at h
  rw [show (𝟙 (powerWordModule D Tw cutoff L s.reverse)).total (OldCategory.mk s.reverse) = 𝟙 _ from
    SuperNatTrans.id_total _ _] at h
  exact h

/-- The literal cyclic matrix vacuum has its source coefficient-one
identity class through its prescribed normalized source-word chart. -/
theorem tensorMatrixVacuum_class :
    PowerWordQuotientCoordinates.coordinate D Sc cutoff L s s
      (tensorSourceWordValue D Sc m cutoff ΛP ΛR L hP hR s
        (tensorOriginalWordEntry D Sc m cutoff ΛP ΛR L hP hR s endpt p up
          (tensorMatrixVacuum D Sc m cutoff ΛP ΛR L s))) =
      (PowerWordQuotientCoordinates.kernel D Sc cutoff L s s).mkQ
        (sourceCoefficientHom D Sc 1 (𝟙 _)) := by
  rw [tensorMatrixVacuum_unit]
  exact tensorSourceUnit_class D Sc cutoff L s

end OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
