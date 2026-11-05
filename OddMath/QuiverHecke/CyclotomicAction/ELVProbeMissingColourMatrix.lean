import OddMath.QuiverHecke.CyclotomicAction.ELVContentMissingColourMatrix
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeUpperCharts
import OddMath.QuiverHecke.CyclotomicAction.ELVUnitColumnMatrices

/-! # The prescribed scalar unit matrix at a missing-colour output

Brundan--Ellis (1.13), DeformedMatrixComparison (4). The lower E/F coordinate
is proved zero. The given global old inverse is transported through the
selected following F/E and canonical shifted value charts. The forward map
is identified with the prescribed finite shifted unit/dot columns.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.ELVOld OddMath.QuiverHecke.ELVOld.BalancedInduction
open OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
namespace OddMath.QuiverHecke
universe u
private theorem missingUnitDot_congr
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    {p : ZMod 2} {α β : ∀ s, J.obj s ⟶ J.obj s}
    (hα : IsSupernatural k p α) (hβ : IsSupernatural k p β) (he : α = β)
    (M : Superfunctor k C (SVec k)) (n : ℕ) (w : C) :
    unitDotLinear J hα M n w = unitDotLinear J hβ M n w := by
  cases he
  rfl

private def missingGivenIsoLinearEquiv {k : Type u} [CommRing k] {V W : SVec k}
    (e : V ≅ W) : V ≃ₗ[k] W where
  toLinearMap := e.hom
  invFun := e.inv
  left_inv x := congrArg (fun f : V ⟶ V => f x) e.hom_inv_id
  right_inv x := congrArg (fun f : W ⟶ W => f x) e.inv_hom_id

private def missingConjugateGivenIso
    {k : Type u} [CommRing k] {A B V W V' W' : SVec k}
    (s : A ≃ₗ[k] V') (a : A ≃ₗ[k] V) (e : V ≅ W)
    (b : B ≃ₗ[k] W) (t : B ≃ₗ[k] W') : V' ≅ W' :=
  SVec.isoOfLinearEquiv
    ((s.symm.trans a).trans ((missingGivenIsoLinearEquiv e).trans (b.symm.trans t)))

private theorem missingConjugateGivenIso_hom_apply
    {k : Type u} [CommRing k] {A B V W V' W' : SVec k}
    (s : A ≃ₗ[k] V') (a : A ≃ₗ[k] V) (e : V ≅ W)
    (b : B ≃ₗ[k] W) (t : B ≃ₗ[k] W') (x : V') :
    (missingConjugateGivenIso s a e b t).hom x = t (b.symm (e.hom (a (s.symm x)))) := rfl

private theorem missingConjugateGivenIso_hom_identify
    {k : Type u} [CommRing k] {A B V W V' W' : SVec k}
    (s : A ≃ₗ[k] V') (a : A ≃ₗ[k] V) (e : V ≅ W)
    (b : B ≃ₗ[k] W) (t : B ≃ₗ[k] W') (r : A →ₗ[k] B) (f : V' ⟶ W')
    (hContent : b.toLinearMap ∘ₗ r = SVec.toLinearMap e.hom ∘ₗ a.toLinearMap)
    (hScalar : t.toLinearMap ∘ₗ r = SVec.toLinearMap f ∘ₗ s.toLinearMap) :
    (missingConjugateGivenIso s a e b t).hom = f := by
  apply LinearMap.ext
  intro x
  have hc := congrArg (fun y => t (b.symm y))
    (LinearMap.congr_fun hContent (s.symm x)).symm
  have hb := congrArg t (b.symm_apply_apply (r (s.symm x)))
  have hs := LinearMap.congr_fun hScalar (s.symm x)
  have hv := congrArg f (s.apply_symm_apply x)
  exact (missingConjugateGivenIso_hom_apply s a e b t x).trans (hc.trans (hb.trans (hs.trans hv)))

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ) (γ : List I)
  (N : Superfunctor k (OldContentCategory D Sc (probeCutoff D m) γ) (SVec k))
  (hN : ProbeEvaluatesCoefficients D m Sc γ N) (i : I) (hi : i ∉ γ)
  (w : OldContentCategory D Sc (probeCutoff D m) γ)
local notation "cut" => probeCutoff D m
local notation "Q" => oldContentInclusion D Sc cut γ
local notation "G" => induced Q N
local notation "K" => oldContentAppend D Sc cut γ i
local notation "J" => append D Sc cut i
local notation "S" => probeOrdinaryAppend D Sc m γ i
local notation "U" => probeOldOrdinaryFunctor D Sc m γ
local notation "O" => probeOrdinaryModuleSuperfunctor D Sc m γ N hN
local notation "dK" => probeOldContentAppendDot_supernatural D Sc m γ i
local notation "dJ" => oldAppendDot_supernatural D Sc cut i
local notation "dS" => probeOrdinaryAppendDot_supernatural D Sc m γ i
local notation "count" => contentUnitCount D cut i (γ : Multiset I)

private theorem missingGlobalUnitIso_hom :
    (missingColourUnitMatrixIso D Sc cut γ i hi N w).hom =
      unitColumnMatrix J dJ G count w.obj := by
  rw [missingColourUnitMatrixIso_hom]
  rfl

private theorem missingContent_unitColumn_square (n : ℕ) :
    (oldContentFEChart D Sc cut γ i N w).toLinearMap ∘ₗ unitDotLinear K dK N n w =
      unitDotLinear J dJ G n w.obj ∘ₗ (oldContentValueChart D Sc cut γ N w).toLinearMap := by
  have he := missingUnitDot_congr K dK (oldContentAppendDot_supernatural D Sc cut γ i) rfl N n w
  rw [he]
  apply LinearMap.ext
  intro b
  exact oldContentFEChart_unitDot D Sc cut γ i N w n b

/-- The selected ordinary missing-colour unit matrix is invertible using the
GIVEN old inverse. Its forward-field identification is proved below. -/
def probeMissingColourUnitMatrixIso :
    unitColumnSourceSpace (D.parity i) O count ((U).obj w) ≅
      ((restriction S).obj ((induction S).obj O)).obj ((U).obj w) :=
  missingConjugateGivenIso
    (A := unitColumnSourceSpace (D.parity i) N count w)
    (B := ((restriction K).obj ((induction K).obj N)).obj w)
    (V := unitColumnSourceSpace (D.parity i) G count w.obj)
    (W := ((restriction J).obj ((induction J).obj G)).obj w.obj)
    (unitColumnFamilyEquiv N O w ((U).obj w)
      (probeOutputValueLinearEquiv D Sc m γ N hN w) (D.parity i) count)
    (unitColumnFamilyEquiv N G w w.obj
      (oldContentValueChart D Sc cut γ N w) (D.parity i) count)
    (missingColourUnitMatrixIso D Sc cut γ i hi N w)
    (oldContentFEChart D Sc cut γ i N w)
    (probeOutputFELinearEquiv D Sc m γ N hN i w)

/-- The forward field is precisely the prescribed finite unit/dot columns
with their canonical source shifts, including genuine empty output. -/
theorem probeMissingColourUnitMatrixIso_hom :
    (probeMissingColourUnitMatrixIso D Sc m γ N hN i hi w).hom =
      unitColumnMatrix S dS O count ((U).obj w) := by
  have hContent := unitColumnMatrix_square K J dK dJ N G w w.obj
    (oldContentValueChart D Sc cut γ N w)
    (oldContentFEChart D Sc cut γ i N w).toLinearMap
    (missingContent_unitColumn_square D Sc m γ N i w) count
  have hg := congrArg SVec.toLinearMap (missingGlobalUnitIso_hom D Sc m γ N i hi w)
  have hOld := linearSquare_reencode _ _ _ _ _ _ _ _ rfl rfl hg rfl hContent
  have hScalar := unitColumnMatrix_square K S dK dS N O w ((U).obj w)
    (probeOutputValueLinearEquiv D Sc m γ N hN w)
    (probeOutputFELinearEquiv D Sc m γ N hN i w).toLinearMap
    (probeOutputFELinearEquiv_unitDot D Sc m γ N hN i w) count
  have hfinal := missingConjugateGivenIso_hom_identify
    (A := unitColumnSourceSpace (D.parity i) N count w)
    (B := ((restriction K).obj ((induction K).obj N)).obj w)
    (V := unitColumnSourceSpace (D.parity i) G count w.obj)
    (W := ((restriction J).obj ((induction J).obj G)).obj w.obj)
    (V' := unitColumnSourceSpace (D.parity i) O count ((U).obj w))
    (W' := ((restriction S).obj ((induction S).obj O)).obj ((U).obj w))
    (unitColumnFamilyEquiv N O w ((U).obj w)
      (probeOutputValueLinearEquiv D Sc m γ N hN w) (D.parity i) count)
    (unitColumnFamilyEquiv N G w w.obj
      (oldContentValueChart D Sc cut γ N w) (D.parity i) count)
    (missingColourUnitMatrixIso D Sc cut γ i hi N w)
    (oldContentFEChart D Sc cut γ i N w)
    (probeOutputFELinearEquiv D Sc m γ N hN i w)
    (SVec.toLinearMap (unitColumnMatrix K dK N count w))
    (unitColumnMatrix S dS O count ((U).obj w))
    hOld hScalar
  exact hfinal

end OddMath.QuiverHecke
