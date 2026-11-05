import OddMath.QuiverHecke.CyclotomicAction.ELVContentMissingColourMatrix
import OddMath.QuiverHecke.CyclotomicAction.ELVContentUpperCharts
import OddMath.QuiverHecke.CyclotomicAction.ELVUnitColumnMatrices

/-! # The old missing-colour unit inverse in content coordinates

Brundan–Ellis (1.13) at the empty boundary: the proved-zero principal
coordinate is removed from the prescribed global inverse, and the chosen
following F/E and shifted value charts transport its remaining columns.
The input module retains the full old coefficient algebra.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open BalancedInduction CyclotomicCrossingTensor
universe u

private def givenUnitIsoLinearEquiv {k : Type u} [CommRing k] {V W : SVec k}
    (e : V ≅ W) : V ≃ₗ[k] W where
  toLinearMap := e.hom
  invFun := e.inv
  left_inv x := congrArg (fun f : V ⟶ V => f x) e.hom_inv_id
  right_inv x := congrArg (fun f : W ⟶ W => f x) e.inv_hom_id

private def conjugateUnitIso {k : Type u} [CommRing k] {V W V' W' : SVec k}
    (v : V ≃ₗ[k] V') (w : W ≃ₗ[k] W') (e : V' ≅ W') : V ≅ W :=
  SVec.isoOfLinearEquiv (v.trans ((givenUnitIsoLinearEquiv e).trans w.symm))

private theorem conjugateUnitIso_hom {k : Type u} [CommRing k] {V W V' W' : SVec k}
    (v : V ≃ₗ[k] V') (w : W ≃ₗ[k] W') (e : V' ≅ W') (f : V ⟶ W)
    (h : w.toLinearMap.comp f = e.hom.comp v.toLinearMap) :
    (conjugateUnitIso v w e).hom = f := by
  apply SVec.hom_ext
  intro x
  apply w.injective
  change w (w.symm (e.hom (v x))) = w (f x)
  rw [LinearEquiv.apply_symm_apply]
  exact (LinearMap.congr_fun h x).symm

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (γ : List I) (i : I) (hi : i ∉ γ)
  (N : Superfunctor k (OldContentCategory D Sc cutoff γ) (SVec k))
  (w : OldContentCategory D Sc cutoff γ)
local notation "Q" => oldContentInclusion D Sc cutoff γ
local notation "G" => induced Q N
local notation "K" => oldContentAppend D Sc cutoff γ i
local notation "J" => append D Sc cutoff i
local notation "dK" => oldContentAppendDot_supernatural D Sc cutoff γ i
local notation "dJ" => oldAppendDot_supernatural D Sc cutoff i
local notation "count" => contentUnitCount D cutoff i (γ : Multiset I)

private theorem content_unitColumn_square (n : ℕ) :
    (oldContentFEChart D Sc cutoff γ i N w).toLinearMap.comp (unitDotLinear K dK N n w) =
      (unitDotLinear J dJ G n w.obj).comp (oldContentValueChart D Sc cutoff γ N w).toLinearMap := by
  apply LinearMap.ext
  intro b
  exact oldContentFEChart_unitDot D Sc cutoff γ i N w n b

private theorem globalUnitIso_hom :
    (missingColourUnitMatrixIso D Sc cutoff γ i hi N w).hom =
      unitColumnMatrix J dJ G count w.obj := by
  rw [missingColourUnitMatrixIso_hom]
  rfl

/-- The prescribed old inverse transported to native content module values,
with its actual finite shifted unit columns. No scalar-evaluation premise. -/
def contentMissingUnitMatrixIso :
    unitColumnSourceSpace (D.parity i) N count w ≅
      ((restriction K).obj ((induction K).obj N)).obj w :=
  conjugateUnitIso
    (V := unitColumnSourceSpace (D.parity i) N count w)
    (W := ((restriction K).obj ((induction K).obj N)).obj w)
    (V' := unitColumnSourceSpace (D.parity i) G count w.obj)
    (W' := ((restriction J).obj ((induction J).obj G)).obj w.obj)
    (unitColumnFamilyEquiv N G w w.obj (oldContentValueChart D Sc cutoff γ N w) (D.parity i) count)
    (oldContentFEChart D Sc cutoff γ i N w)
    (missingColourUnitMatrixIso D Sc cutoff γ i hi N w)

/-- Its forward field is the prescribed matrix of shifted ordinary unit/dot columns. -/
theorem contentMissingUnitMatrixIso_hom :
    (contentMissingUnitMatrixIso D Sc cutoff γ i hi N w).hom =
      unitColumnMatrix K dK N count w := by
  apply conjugateUnitIso_hom
  rw [globalUnitIso_hom]
  exact unitColumnMatrix_square K J dK dJ N G w w.obj
    (oldContentValueChart D Sc cutoff γ N w)
    (oldContentFEChart D Sc cutoff γ i N w).toLinearMap
    (content_unitColumn_square D Sc cutoff γ i N w) count

end OddMath.QuiverHecke.ELVOld
