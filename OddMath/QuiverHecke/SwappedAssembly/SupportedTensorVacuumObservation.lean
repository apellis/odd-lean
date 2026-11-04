import OddMath.QuiverHecke.SwappedAssembly.SupportedTensorWordObservation

/-! # Canonical observation of the supported tensor vacuum

SwappedVacuumCoordinates §§3–7: the cyclic matrix vacuum has precisely
the prescribed original-weight source chart. Its literal ambient row
and unchanged-input whole-Hom entry are identified before evaluation.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath.SKM
namespace OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
open CyclotomicAction ELVOld
universe u v w
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

private theorem rowProjection_apply
    (x : tensorWordMatrixModule D Sc m cutoff ΛP ΛR L s s) :
    tensorVacuumRowProjection D Sc m cutoff ΛP ΛR L hP hR s endpt p x =
      (x (0,cS) ⟨(0,0),endpt⟩ p).hom ≫
        eqToHom (factor_path_obj D Sc m cutoff N ΛP ΛR hP hR p
          (tensorTargetFamily D Sc m cutoff ΛP ΛR L (0,0))) ≫
        eqToHom (congrArg ((P).pathFunctor p).obj
          (congrArg (fun Z : H D Tw m cutoff N ΛP ΛR (0,0) => Z.obj)
            (tensorTargetFamily_zero D Sc m cutoff ΛP ΛR L))) := by
  simp only [tensorVacuumRowProjection,MatrixSourceRow.projectionAt,
    LinearMap.comp_apply,LinearEquiv.coe_toLinearMap,Linear.homCongr_apply,
    MatrixSourceRow.projection,entryEquiv,LinearEquiv.trans_apply,
    Iso.refl_inv,Category.id_comp]
  exact Category.assoc _ _ _

/-- The canonical row projection reads the identity of the specified
source word, through the actual factor path chart. -/
theorem tensorVacuumRowProjection_vacuum :
    tensorVacuumRowProjection D Sc m cutoff ΛP ΛR L hP hR s endpt p
      (tensorMatrixVacuum D Sc m cutoff ΛP ΛR L s) =
      eqToHom (congrArg (fun Z : H D Tw m cutoff N ΛP ΛR (0,cS) => Z.obj)
        (tensorSourceFamily_source D Sc m cutoff ΛP ΛR L s)) ≫
        eqToHom (factor_path_obj D Sc m cutoff N ΛP ΛR hP hR p
          (tensorVacuum D Sc m cutoff L ΛP ΛR)) := by
  rw [rowProjection_apply,matrixVacuum_entry,InducedCategory.comp_hom]
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

end OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
