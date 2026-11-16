import OddMath.QuiverHecke.CyclotomicAction.ContentMatrix
import OddMath.QuiverHecke.CyclotomicAction.ProbeVacuumCharts
import OddMath.QuiverHecke.CyclotomicAction.ContentBlockExtension
import OddMath.QuiverHecke.HnBasis
import OddMath.QuiverHecke.CyclotomicAction.FullyFaithfulInduction
import OddMath.QuiverHecke.CyclotomicAction.ProbeMixed
import OddMath.QuiverHecke.CyclotomicAction.CapInputMatrices
import OddMath.QuiverHecke.CyclotomicAction.ContentModule
import OddMath.Algebra.FiniteSupermoduleFunctor
import OddMath.SKM.RouquierHomContent
import OddMath.QuiverHecke.CyclotomicAction.GlobalWeightRouquier

/-!
# Probe cap

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # The prescribed scalar unit matrix at a missing-colour output

Brundan--Ellis (1.13), DeformedMatrixComparison (4). The lower E/F coordinate
is proved zero. The given global old inverse is transported through the
selected following F/E and canonical shifted value charts. The forward map
is identified with the prescribed finite shifted unit/dot columns.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.ELV OddMath.QuiverHecke.ELV.BalancedInduction
open OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
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
end

end

section

/-! # Scalar comparison of the prescribed inverse unit coefficients

The missing-colour, including empty-output, left-cap field comes from a
specified actual unit-matrix inverse coordinate and its canonical source
unshift. Both forward matrix squares are proved by the selected content
and scalar charts, so the original inverse row is preserved as well.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.ELV OddMath.QuiverHecke.ELV.BalancedInduction
open OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
namespace OddMath.QuiverHecke
universe u
private theorem inverseRowUnitDot_congr
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

private theorem inverseRowOldMatrix_hom :
    (missingColourUnitMatrixIso D Sc cut γ i hi N w).hom =
      unitColumnMatrix J dJ G count w.obj := by
  rw [missingColourUnitMatrixIso_hom]
  rfl

private theorem inverseRowContent_unitColumn_square (n : ℕ) :
    (oldContentFEChart D Sc cut γ i N w).toLinearMap ∘ₗ unitDotLinear K dK N n w =
      unitDotLinear J dJ G n w.obj ∘ₗ (oldContentValueChart D Sc cut γ N w).toLinearMap := by
  have he := inverseRowUnitDot_congr K dK (oldContentAppendDot_supernatural D Sc cut γ i) rfl N n w
  rw [he]
  apply LinearMap.ext
  intro b
  exact oldContentFEChart_unitDot D Sc cut γ i N w n b

/-- The actual ordinary inverse coefficient, with its original canonical
source unshift. The last such row is the normalized left cap candidate. -/
def probeMissingColourUnitCoefficient (r : Fin count) :
    ((restriction S).obj ((induction S).obj O)).obj ((U).obj w) ⟶ (O).obj ((U).obj w) :=
  unitColumnInverseRow O ((U).obj w) (D.parity i) count
    (probeMissingColourUnitMatrixIso D Sc m γ N hN i hi w) r

/-- The selected content/scalar charts preserve the exact inverse row and
its canonical unshift, for every coefficient (hence also the top row). -/
theorem probeMissingColourUnitCoefficient_compare (r : Fin count) :
    ((oldContentValueChart D Sc cut γ N w).symm.trans
      (probeOutputValueLinearEquiv D Sc m γ N hN w)).toLinearMap ∘ₗ
        SVec.toLinearMap (unitColumnInverseRow G w.obj (D.parity i) count
          (missingColourUnitMatrixIso D Sc cut γ i hi N w) r) =
      SVec.toLinearMap (probeMissingColourUnitCoefficient D Sc m γ N hN i hi w r) ∘ₗ
        ((oldContentFEChart D Sc cut γ i N w).symm.trans
          (probeOutputFELinearEquiv D Sc m γ N hN i w)).toLinearMap := by
  have hOld₀ := unitColumnMatrix_square K J dK dJ N G w w.obj
    (oldContentValueChart D Sc cut γ N w)
    (oldContentFEChart D Sc cut γ i N w).toLinearMap
    (inverseRowContent_unitColumn_square D Sc m γ N i w) count
  have hgOld := congrArg SVec.toLinearMap (inverseRowOldMatrix_hom D Sc m γ N i hi w)
  have hOld := linearSquare_reencode _ _ _ _ _ _ _ _ rfl rfl hgOld rfl hOld₀
  have hNew₀ := unitColumnMatrix_square K S dK dS N O w ((U).obj w)
    (probeOutputValueLinearEquiv D Sc m γ N hN w)
    (probeOutputFELinearEquiv D Sc m γ N hN i w).toLinearMap
    (probeOutputFELinearEquiv_unitDot D Sc m γ N hN i w) count
  have hgNew := congrArg SVec.toLinearMap
    (probeMissingColourUnitMatrixIso_hom D Sc m γ N hN i hi w)
  have hNew := linearSquare_reencode _ _ _ _ _ _ _ _ rfl rfl hgNew rfl hNew₀
  have h := unitColumnInverseRow_compare_common
    (B := ((restriction K).obj ((induction K).obj N)).obj w)
    (W := ((restriction J).obj ((induction J).obj G)).obj w.obj)
    (W' := ((restriction S).obj ((induction S).obj O)).obj ((U).obj w))
    N G O w w.obj ((U).obj w)
    (oldContentValueChart D Sc cut γ N w)
    (probeOutputValueLinearEquiv D Sc m γ N hN w) (D.parity i) count
    (oldContentFEChart D Sc cut γ i N w)
    (probeOutputFELinearEquiv D Sc m γ N hN i w)
    (missingColourUnitMatrixIso D Sc cut γ i hi N w)
    (probeMissingColourUnitMatrixIso D Sc m γ N hN i hi w)
    (SVec.toLinearMap (unitColumnMatrix K dK N count w)) hOld hNew r
  exact h
end OddMath.QuiverHecke
end

end

section

/-! # Prescribed left inverse-coefficient fields under scalar charts

The normalized left cap in DeformedMatrixComparison comes from the given
inverse unit matrix and its source unshift. This identifies the old side
of the scalar inverse-row comparison with the prescribed coefficient module
map; at genuine empty output it is the original moduleUnitCoefficient.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
open BalancedInduction TensorMatrixCoordinates
universe u

private theorem dropInverse_coordinate {k : Type u} [CommRing k] {ι : Type}
    (V : Option ι → SVec k) (h₀ : Subsingleton (V none)) {W : SVec k}
    (e : OddMath.FiniteSuperspace.product V ≅ W) (x : W) (r : ι) :
    (((SVec.isoOfLinearEquiv
      (OddMath.FiniteSuperspace.dropZeroPrincipalEquiv V h₀)).symm ≪≫ e).inv x) r =
      (e.inv x) (some r) := rfl

section GlobalModule
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
  (i : I) (γ : List I) (hh : 0 ≤ contentCrossingHeight D cutoff i (γ : Multiset I))
  (w : OldContentCategory D Sc cutoff γ)
local instance leftCapBindingPi : PiSupercategory k (Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :=
  supermodulePiSupercategory
local notation "count" => contentUnitCount D cutoff i (γ : Multiset I)

private def coefficientDropIso
    (h₀ : Subsingleton ((unitMatrixFamily D Sc cutoff i M count none).obj w.obj)) :
    unitColumnSourceSpace (D.parity i) M count w.obj ≅ mateTargetSpace D Sc cutoff i M w.obj :=
  (SVec.isoOfLinearEquiv (OddMath.FiniteSuperspace.dropZeroPrincipalEquiv
    (fun a => (unitMatrixFamily D Sc cutoff i M count a).obj w.obj) h₀)).symm ≪≫
  contentUnitMatrixComponentIso D Sc cutoff M i γ hh w

private theorem coefficientDropIso_row
    (h₀ : Subsingleton ((unitMatrixFamily D Sc cutoff i M count none).obj w.obj)) (r : Fin count) :
    SVec.toLinearMap (unitColumnInverseRow M w.obj (D.parity i) count
      (coefficientDropIso D Sc cutoff M i γ hh w h₀) r) =
    SVec.toLinearMap ((contentUnitCoefficientMap D Sc cutoff M i γ hh r).total w) := by
  apply LinearMap.ext
  intro x
  have hRow := unitColumnInverseRow_apply M w.obj (D.parity i) count
    (coefficientDropIso D Sc cutoff M i γ hh w h₀) r x
  have hDrop := dropInverse_coordinate
    (fun a => (unitMatrixFamily D Sc cutoff i M count a).obj w.obj) h₀
    (contentUnitMatrixComponentIso D Sc cutoff M i γ hh w) x r
  have hField := contentUnitCoefficientMap_total D Sc cutoff M i γ hh r w x
  exact hRow.trans ((congrArg
    (fun z => ((SKM.homParityShiftDatum (k := k) (r.val • D.parity i)).iso M).hom.total w.obj z)
    hDrop).trans hField.symm)

end GlobalModule

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (γ : List I) (i : I) (hi : i ∉ γ)
  (N : Superfunctor k (OldContentCategory D Sc cutoff γ) (SVec k))
  (w : OldContentCategory D Sc cutoff γ)
local notation "G" => induced (oldContentInclusion D Sc cutoff γ) N
local notation "count" => contentUnitCount D cutoff i (γ : Multiset I)

/-- Dropping the proved-zero principal coordinate leaves exactly the
prescribed old inverse coefficient module map, including its source unshift. -/
theorem missingColourUnitInverseRow_eq_coefficientMap (r : Fin count) :
    SVec.toLinearMap (unitColumnInverseRow G w.obj (D.parity i) count
      (missingColourUnitMatrixIso D Sc cutoff γ i hi N w) r) =
    SVec.toLinearMap ((contentUnitCoefficientMap D Sc cutoff G i γ
      (contentCrossingHeight_nonneg_of_not_mem D cutoff γ i hi) r).total w) := by
  have h := coefficientDropIso_row D Sc cutoff G i γ
    (contentCrossingHeight_nonneg_of_not_mem D cutoff γ i hi) w
    (oldContentUnitPrincipal_subsingleton_of_not_mem D Sc cutoff γ i hi N count w.obj) r
  exact h
end OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor

namespace OddMath.QuiverHecke
universe u
private theorem leftCap_relative_square
    {k A V V' B W W' : Type u} [CommRing k]
    [AddCommMonoid A] [Module k A] [AddCommMonoid V] [Module k V]
    [AddCommMonoid V'] [Module k V'] [AddCommMonoid B] [Module k B]
    [AddCommMonoid W] [Module k W] [AddCommMonoid W'] [Module k W']
    (a : A ≃ₗ[k] V) (s : A ≃ₗ[k] V') (b : B ≃ₗ[k] W) (t : B ≃ₗ[k] W')
    (f : W →ₗ[k] V) (g : W' →ₗ[k] V')
    (h : (a.symm.trans s).toLinearMap ∘ₗ f = g ∘ₗ (b.symm.trans t).toLinearMap) :
    s.toLinearMap ∘ₗ (a.symm.toLinearMap ∘ₗ f ∘ₗ b.toLinearMap) = g ∘ₗ t.toLinearMap := by
  apply LinearMap.ext
  intro x
  have h₀ := LinearMap.congr_fun h (b x)
  exact h₀.trans (congrArg (fun z => g (t z)) (b.symm_apply_apply x))
end OddMath.QuiverHecke

namespace OddMath.QuiverHecke
open ELV ELV.BalancedInduction ELV.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ) (γ : List I)
  (N : Superfunctor k (OldContentCategory D Sc (probeCutoff D m) γ) (SVec k))
  (hN : ProbeEvaluatesCoefficients D m Sc γ N) (i : I) (hi : i ∉ γ)
  (w : OldContentCategory D Sc (probeCutoff D m) γ)
local notation "cut" => probeCutoff D m
local notation "G" => induced (oldContentInclusion D Sc cut γ) N
local notation "count" => contentUnitCount D cut i (γ : Multiset I)

/-- The scalar inverse coefficient comparison uses the literal prescribed old
coefficient module map, rather than a separately normalized cap. -/
theorem probeMissingColourUnitCoefficient_contentMap (r : Fin count) :
    ((oldContentValueChart D Sc cut γ N w).symm.trans
      (probeOutputValueLinearEquiv D Sc m γ N hN w)).toLinearMap ∘ₗ
      SVec.toLinearMap ((contentUnitCoefficientMap D Sc cut G i γ
        (contentCrossingHeight_nonneg_of_not_mem D cut γ i hi) r).total w) =
    SVec.toLinearMap (probeMissingColourUnitCoefficient D Sc m γ N hN i hi w r) ∘ₗ
      ((oldContentFEChart D Sc cut γ i N w).symm.trans
        (probeOutputFELinearEquiv D Sc m γ N hN i w)).toLinearMap := by
  have hCompare := probeMissingColourUnitCoefficient_compare D Sc m γ N hN i hi w r
  have hField := missingColourUnitInverseRow_eq_coefficientMap D Sc cut γ i hi N w r
  have h := linearSquare_reencode _ _ _ _ _ _ _ _ rfl hField.symm rfl rfl hCompare
  exact h
/-- In original relative values, the comparison removes the fully faithful
inclusion unit after the prescribed old coefficient map and selected F/E chart. -/
theorem probeMissingColourUnitCoefficient_relative (r : Fin count) :
    (probeOutputValueLinearEquiv D Sc m γ N hN w).toLinearMap ∘ₗ
      ((oldContentValueChart D Sc cut γ N w).symm.toLinearMap ∘ₗ
        SVec.toLinearMap ((contentUnitCoefficientMap D Sc cut G i γ
          (contentCrossingHeight_nonneg_of_not_mem D cut γ i hi) r).total w) ∘ₗ
        (oldContentFEChart D Sc cut γ i N w).toLinearMap) =
    SVec.toLinearMap (probeMissingColourUnitCoefficient D Sc m γ N hN i hi w r) ∘ₗ
      (probeOutputFELinearEquiv D Sc m γ N hN i w).toLinearMap := by
  have h := leftCap_relative_square
    (oldContentValueChart D Sc cut γ N w) (probeOutputValueLinearEquiv D Sc m γ N hN w)
    (oldContentFEChart D Sc cut γ i N w) (probeOutputFELinearEquiv D Sc m γ N hN i w)
    (SVec.toLinearMap ((contentUnitCoefficientMap D Sc cut G i γ
      (contentCrossingHeight_nonneg_of_not_mem D cut γ i hi) r).total w))
    (SVec.toLinearMap (probeMissingColourUnitCoefficient D Sc m γ N hN i hi w r))
    (probeMissingColourUnitCoefficient_contentMap D Sc m γ N hN i hi w r)
  exact h

end OddMath.QuiverHecke

namespace OddMath.QuiverHecke
open ELV ELV.BalancedInduction ELV.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (N : Superfunctor k (OldContentCategory D Sc (probeCutoff D m) []) (SVec k))
  (hN : ProbeEvaluatesCoefficients D m Sc [] N) (i : I)
local notation "cut" => probeCutoff D m
local notation "v" => (OldContentCategory.mk (OldCategory.mk []) (List.Perm.refl []) : OldContentCategory D Sc cut [])
local notation "G₀" => induced (oldContentInclusion D Sc cut []) N
local notation "hi₀" => (by simp : i ∉ ([] : List I))
local notation "hh₀" => contentCrossingHeight_nonneg_of_not_mem D cut [] i hi₀

end OddMath.QuiverHecke
end

end

section

/-! # The native prescribed left cap under the selected scalar chart

The inverse-defined left cap of DeformedMatrixComparison is the selected
F/E chart, prescribed inverse unit coefficient and inverse inclusion unit.
Its actual native module-map field is preserved by the original scalar
value and append charts, with the canonical row normalization unchanged.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
open ELV ELV.BalancedInduction ELV.CyclotomicCrossingTensor
universe u

private theorem leftCap_field_total
    {I X k : Type u} [AddCommGroup X] [CommRing k]
    (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
    (γ : List I) (i : I) (N : Superfunctor k (OldContentCategory D Sc cutoff γ) (SVec k))
    (hh : 0 ≤ contentCrossingHeight D cutoff i (γ : Multiset I))
    (r : Fin (contentUnitCount D cutoff i (γ : Multiset I)))
    (w : OldContentCategory D Sc cutoff γ) :
    SVec.toLinearMap ((contentCoefficientCap D Sc cutoff γ i N hh r).total w) =
      (oldContentValueChart D Sc cutoff γ N w).symm.toLinearMap ∘ₗ
        SVec.toLinearMap ((contentUnitCoefficientMap D Sc cutoff
          (induced (oldContentInclusion D Sc cutoff γ) N) i γ hh r).total w) ∘ₗ
        (oldContentFEChart D Sc cutoff γ i N w).toLinearMap := by
  exact contentCoefficientCap_total D Sc cutoff γ i N hh r w

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ) (γ : List I)
  (N : Superfunctor k (OldContentCategory D Sc (probeCutoff D m) γ) (SVec k))
  (hN : ProbeEvaluatesCoefficients D m Sc γ N) (i : I) (hi : i ∉ γ)
  (w : OldContentCategory D Sc (probeCutoff D m) γ)
local notation "cut" => probeCutoff D m
local notation "count" => contentUnitCount D cut i (γ : Multiset I)

/-- The actual native prescribed inverse-defined left-cap field is carried
to the actual ordinary inverse coefficient by the selected scalar charts.
The ordinary right counit is not substituted for this field. -/
theorem probeMissingColourUnitCoefficient_cap (r : Fin count) :
    (probeOutputValueLinearEquiv D Sc m γ N hN w).toLinearMap ∘ₗ
      SVec.toLinearMap ((contentCoefficientCap D Sc cut γ i N
        (contentCrossingHeight_nonneg_of_not_mem D cut γ i hi) r).total w) =
    SVec.toLinearMap (probeMissingColourUnitCoefficient D Sc m γ N hN i hi w r) ∘ₗ
      (probeOutputFELinearEquiv D Sc m γ N hN i w).toLinearMap := by
  have hCompare := probeMissingColourUnitCoefficient_relative D Sc m γ N hN i hi w r
  have hField := leftCap_field_total D Sc cut γ i N
    (contentCrossingHeight_nonneg_of_not_mem D cut γ i hi) r w
  have h := linearSquare_reencode _ _ _ _ _ _ _ _ rfl hField rfl rfl hCompare
  exact h

end OddMath.QuiverHecke
end

end

section

/-! # Normalization window of the actual ordinary inverse unit coefficient

The prescribed inverse row extracts its own unit/dot column and kills all
other columns in the finite window. Its canonical source unshift is kept
throughout. This is the ordinary left-cap normalization needed for the
native cap and ground probe functional.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped BigOperators
namespace OddMath.QuiverHecke.ELV.BalancedInduction
universe u
section GenericWindow
variable {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive A] [Linear k A] [Supercategory k A]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
  (M : Superfunctor k C (SVec k)) (m : ℕ) (w : C)
local instance unitCoefficientWindowPi : PiSupercategory k (Superfunctor k C (SVec k)) :=
  supermodulePiSupercategory
variable (e : unitColumnSourceSpace p M m w ≅ ((restriction J).obj ((induction J).obj M)).obj w)

private theorem inverseWindow_assembled_single {ι : Type} [Fintype ι] [DecidableEq ι]
    (V : ι → SVec k) (X : SVec k) (f : ∀ a, V a ⟶ X) (a : ι) (b : V a) :
    OddMath.FiniteSuperspace.assembleColumns V X f (Pi.single a b) = f a b := by
  change (∑ s, f s ((Pi.single a b : (s : ι) → V s) s)) = _
  rw [Finset.sum_eq_single a]
  · simp
  · intro s _ hs
    rw [Pi.single_eq_of_ne hs]
    exact map_zero _
  · simp

private theorem inverseWindow_matrix_single (a : Fin m)
    (b : ((SKM.homParityShift (k := k) (a.val • p)).obj M).obj w) :
    unitColumnMatrix J hα M m w (Pi.single a b) =
      (shiftedUnitDotColumn J hα M a.val).total w b := by
  classical
  exact inverseWindow_assembled_single
    (fun a : Fin m => ((SKM.homParityShift (k := k) (a.val • p)).obj M).obj w)
    (((restriction J).obj ((induction J).obj M)).obj w)
    (fun a => (shiftedUnitDotColumn J hα M a.val).total w) a b

private theorem inverseWindow_component
    (he : e.hom = unitColumnMatrix J hα M m w) (r : Fin m) (x : unitColumnSourceSpace p M m w) :
    unitColumnInverseRow M w p m e r (unitColumnMatrix J hα M m w x) =
      unitColumnUnshift M w p m r x := by
  have hx := (OddMath.FiniteSuperspace.isoLinearEquiv e).symm_apply_apply x
  change e.inv (e.hom x) = x at hx
  rw [he] at hx
  change ((SKM.homParityShiftDatum (k := k) (r.val • p)).iso M).hom.total w
    ((e.inv (unitColumnMatrix J hα M m w x)) r) =
      ((SKM.homParityShiftDatum (k := k) (r.val • p)).iso M).hom.total w (x r)
  exact congrArg (fun y => ((SKM.homParityShiftDatum (k := k) (r.val • p)).iso M).hom.total w (y r)) hx

private theorem inverseWindow_shifted_unit (n : ℕ) (b : M.obj w) :
    (shiftedUnitDotColumn J hα M n).total w
      ((moduleIsoLinearEquiv ((SKM.homParityShiftDatum (k := k) (n • p)).iso M) w).symm b) =
      unitDotLinear J hα M n w b := by
  have h := LinearMap.congr_fun (shiftedUnitDotColumn_total J hα M n w)
    ((moduleIsoLinearEquiv ((SKM.homParityShiftDatum (k := k) (n • p)).iso M) w).symm b)
  have hz := (moduleIsoLinearEquiv ((SKM.homParityShiftDatum (k := k) (n • p)).iso M) w).apply_symm_apply b
  change (shiftedUnitDotColumn J hα M n).total w _ =
    unitDotLinear J hα M n w
      ((moduleIsoLinearEquiv ((SKM.homParityShiftDatum (k := k) (n • p)).iso M) w)
        ((moduleIsoLinearEquiv ((SKM.homParityShiftDatum (k := k) (n • p)).iso M) w).symm b)) at h
  exact h.trans (congrArg (unitDotLinear J hα M n w) hz)

private theorem inverseWindow_same (he : e.hom = unitColumnMatrix J hα M m w)
    (r : Fin m) (b : M.obj w) :
    unitColumnInverseRow M w p m e r (unitDotLinear J hα M r.val w b) = b := by
  let es := moduleIsoLinearEquiv ((SKM.homParityShiftDatum (k := k) (r.val • p)).iso M) w
  have h := inverseWindow_component J hα M m w e he r (Pi.single r (es.symm b))
  rw [inverseWindow_matrix_single, unitColumnUnshift_apply, Pi.single_eq_same] at h
  dsimp only [es] at h
  rw [inverseWindow_shifted_unit] at h
  exact h.trans (es.apply_symm_apply b)

private theorem inverseWindow_other (he : e.hom = unitColumnMatrix J hα M m w)
    (r s : Fin m) (hrs : r ≠ s) (b : M.obj w) :
    unitColumnInverseRow M w p m e r (unitDotLinear J hα M s.val w b) = 0 := by
  let es := moduleIsoLinearEquiv ((SKM.homParityShiftDatum (k := k) (s.val • p)).iso M) w
  have h := inverseWindow_component J hα M m w e he r (Pi.single s (es.symm b))
  rw [inverseWindow_matrix_single, unitColumnUnshift_apply, Pi.single_eq_of_ne hrs, map_zero] at h
  dsimp only [es] at h
  rw [inverseWindow_shifted_unit] at h
  exact h

/-- A GIVEN inverse with the prescribed forward unit columns has the exact
Kronecker extraction window. The concrete ordinary inverse below supplies
this intermediate forward-field premise from its proved identification. -/
theorem unitColumnInverseRow_unitDot_window
    (he : e.hom = unitColumnMatrix J hα M m w) (r : Fin m) (a : ℕ) (ha : a < m) :
    SVec.toLinearMap (unitColumnInverseRow M w p m e r) ∘ₗ unitDotLinear J hα M a w =
      if a = r.val then LinearMap.id else 0 := by
  by_cases har : a = r.val
  · rw [ite_eq_left har, har]
    apply LinearMap.ext
    intro b
    exact inverseWindow_same J hα M m w e he r b
  · rw [ite_eq_right har]
    apply LinearMap.ext
    intro b
    exact inverseWindow_other J hα M m w e he r ⟨a, ha⟩ (fun h => har (congrArg Fin.val h).symm) b
end GenericWindow
end OddMath.QuiverHecke.ELV.BalancedInduction

namespace OddMath.QuiverHecke
open ELV ELV.BalancedInduction ELV.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ) (γ : List I)
  (N : Superfunctor k (OldContentCategory D Sc (probeCutoff D m) γ) (SVec k))
  (hN : ProbeEvaluatesCoefficients D m Sc γ N) (i : I) (hi : i ∉ γ)
  (w : OldContentCategory D Sc (probeCutoff D m) γ)
local notation "count" => contentUnitCount D (probeCutoff D m) i (γ : Multiset I)
local notation "S" => probeOrdinaryAppend D Sc m γ i
local notation "U" => probeOldOrdinaryFunctor D Sc m γ
local notation "O" => probeOrdinaryModuleSuperfunctor D Sc m γ N hN

/-- The actual ordinary inverse coefficient extracts its prescribed dot
power and kills every other power in the finite unit window. -/
theorem probeMissingColourUnitCoefficient_unitDot (r : Fin count) (a : ℕ) (ha : a < count) :
    SVec.toLinearMap (probeMissingColourUnitCoefficient D Sc m γ N hN i hi w r) ∘ₗ
      unitDotLinear S (probeOrdinaryAppendDot_supernatural D Sc m γ i) O a ((U).obj w) =
    if a = r.val then LinearMap.id else 0 := by
  have h := unitColumnInverseRow_unitDot_window S (probeOrdinaryAppendDot_supernatural D Sc m γ i)
    O count ((U).obj w) (probeMissingColourUnitMatrixIso D Sc m γ N hN i hi w)
    (probeMissingColourUnitMatrixIso_hom D Sc m γ N hN i hi w) r a ha
  exact h
end OddMath.QuiverHecke
end

end

section

/-! # Scalar coordinates of the regular probe vacuum

The height-zero regular probe in `SwappedActionAssembly.md`, F2, has a
canonical ground-ring coordinate. We derive it from the empty-word PBW
basis (BE2, (11.1)), retaining the prescribed empty idempotent vector.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k)

private theorem zeroWord_eq (s : Word I 0) : s = vacuumWord := by
  apply Subtype.ext
  exact List.length_eq_zero_iff.mp s.property

private def zeroNF : NFIdx ([] : List I) [] := by
  have hc : Categorification.TypeA.canWord 0 (1 : Equiv.Perm (Fin 0)) = [] := by
    apply List.length_eq_zero_iff.mp
    rw [Categorification.TypeA.length_canWord, Categorification.TypeA.length_one]
  refine ⟨([], 1), by simp, by simp, ?_⟩
  simp only [List.map_nil, List.length_nil, hc, cw, List.reverse_nil, List.nil_append, pl, SChain]

private theorem zeroNF_eq (j : NFIdx ([] : List I) []) : j = zeroNF := by
  apply Subtype.ext
  apply Prod.ext
  · apply List.eq_nil_iff_forall_not_mem.mpr
    intro x hx
    exact Nat.not_lt_zero x (j.property.2.1 x hx)
  · ext a
    exact Fin.elim0 a

private def zeroIndex : HnIdx I 0 := ⟨(vacuumWord, vacuumWord), zeroNF⟩

private theorem zeroIndex_eq (j : HnIdx I 0) : j = zeroIndex := by
  rcases j with ⟨⟨a,b⟩, j⟩
  obtain rfl := zeroWord_eq a
  obtain rfl := zeroWord_eq b
  exact congrArg (fun h => (⟨(vacuumWord, vacuumWord), h⟩ : HnIdx I 0)) (zeroNF_eq j)

@[instance_reducible] private def zeroIndexUnique : Unique (HnIdx I 0) where
  default := zeroIndex
  uniq := zeroIndex_eq

private def heightZeroLinearEquiv : k ≃ₗ[k] Hn D Sc 0 := by
  letI := zeroIndexUnique (I := I)
  exact (Module.Basis.singleton (HnIdx I 0) k).equiv (Hn.basis D Sc 0) (Equiv.refl _)

private theorem heightZeroLinearEquiv_one :
    heightZeroLinearEquiv D Sc 1 = Hn.wordIdempotent (vacuumWord (I := I)) := by
  let := zeroIndexUnique (I := I)
  have h := Module.Basis.equiv_apply (b := Module.Basis.singleton (HnIdx I 0) k)
    (b' := Hn.basis D Sc 0) (e := Equiv.refl _) (zeroIndex (I := I))
  rw [Module.Basis.singleton_apply, Equiv.refl_apply] at h
  change heightZeroLinearEquiv D Sc 1 = _ at h
  rw [h, Hn.basis_apply, ELV.vacuum_nf D Sc]
  rfl

variable [Fintype I]

private theorem heightZeroIdempotent_one :
    Hn.wordIdempotent (vacuumWord (I := I)) = (1 : Hn D Sc 0) := by
  classical
  have hu : (Finset.univ : Finset (Word I 0)) = {vacuumWord} := by
    ext s
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    exact zeroWord_eq s
  change OddMath.FiniteHomMatrix.idem vacuumWord = OddMath.FiniteHomMatrix.localUnit Finset.univ
  rw [hu]
  simp [OddMath.FiniteHomMatrix.localUnit]

private theorem heightZeroLinearEquiv_scalar (c : k) :
    heightZeroLinearEquiv D Sc c = algebraMap k (Hn D Sc 0) c := by
  have h := (heightZeroLinearEquiv D Sc).map_smul c (1 : k)
  simpa only [smul_eq_mul, mul_one, heightZeroLinearEquiv_one,
    heightZeroIdempotent_one, Algebra.algebraMap_eq_smul_one] using h

/-- The scalar coordinate of the height-zero algebra, with no cyclotomic
relation or scalar specialization imposed on its empty-word component. -/
def heightZeroScalarEquiv : k ≃ₐ[k] Hn D Sc 0 :=
  AlgEquiv.ofLinearEquiv (heightZeroLinearEquiv D Sc)
    (by rw [heightZeroLinearEquiv_one, heightZeroIdempotent_one])
    (by intro x y; simp only [heightZeroLinearEquiv_scalar, map_mul])

variable (m : I → ℕ)

private theorem probeVacuumVector_val :
    (probeOldVacuumVector D Sc m).val = (1 : Hn D Sc 0) := by
  change Hn.wordIdempotent (vacuumWord (I := I)) = _
  exact heightZeroIdempotent_one D Sc

/-- The scalar parametrization of the literal empty word value of the regular
probe. Its value at one is the original empty idempotent vector. -/
def probeVacuumScalarEquiv :
    k ≃ₗ[k] (probeOldVacuumRegular D Sc m).obj (probeOldVacuumObject D Sc m) where
  toFun c := c • probeOldVacuumVector D Sc m
  invFun v := (heightZeroScalarEquiv D Sc).symm v.val
  left_inv c := by
    change (heightZeroScalarEquiv D Sc).symm (c • (probeOldVacuumVector D Sc m).val) = c
    rw [probeVacuumVector_val]
    change (heightZeroScalarEquiv D Sc).symm (algebraMap k (Hn D Sc 0) c) = c
    rw [← heightZeroLinearEquiv_scalar]
    exact (heightZeroScalarEquiv D Sc).symm_apply_apply c
  right_inv v := by
    apply Subtype.ext
    change (heightZeroScalarEquiv D Sc).symm v.val • (probeOldVacuumVector D Sc m).val = v.val
    rw [probeVacuumVector_val]
    change algebraMap k (Hn D Sc 0) ((heightZeroScalarEquiv D Sc).symm v.val) = v.val
    rw [← heightZeroLinearEquiv_scalar]
    exact (heightZeroScalarEquiv D Sc).apply_symm_apply v.val
  map_add' c d := add_smul c d _
  map_smul' c d := by simp only [RingHom.id_apply, mul_smul, smul_eq_mul]

/-- This coordinate uses the unrescaled prescribed vacuum vector. -/
theorem probeVacuumScalarEquiv_one :
    probeVacuumScalarEquiv D Sc m 1 = probeOldVacuumVector D Sc m := one_smul k _

/-- Every vector of the empty regular probe is even. -/
theorem probeVacuum_even
    (v : (probeOldVacuumRegular D Sc m).obj (probeOldVacuumObject D Sc m)) :
    v ∈ ((probeOldVacuumRegular D Sc m).obj (probeOldVacuumObject D Sc m)).part 0 := by
  obtain ⟨c, rfl⟩ := (probeVacuumScalarEquiv D Sc m).surjective v
  apply Submodule.smul_mem
  change probeOldVacuumVector D Sc m ∈ (probeOldWordSVec D m Sc []
    (SuperBimodule.regular (heightParity D Sc
      (probePolynomial (k := k) (probeDotExponent D) m)
      (probePolynomial_parity D m) 0)) (probeOldVacuumObject D Sc m)).part 0
  dsimp only [probeOldVacuumRegular, probeOldModule, probeOldModuleFunctor,
    probeOldWordSVec, probeOldVacuumVector]
  apply (SVec.mem_sub_part_iff _ _ _).mpr
  change (probeOldWordIdempotent D m Sc [] (probeOldVacuumObject D Sc m) :
    heightAlgebra D Sc (probePolynomial (k := k) (probeDotExponent D) m) 0) ∈
      (SuperBimodule.regularSVec (heightParity D Sc
        (probePolynomial (k := k) (probeDotExponent D) m)
        (probePolynomial_parity D m) 0)).part 0
  apply (SuperBimodule.mem_regularSVec_part_iff _).mpr
  exact probeOldWordIdempotent_parity D m Sc [] (probeOldVacuumObject D Sc m)

end OddMath.QuiverHecke
end

end

section

/-! # Inverse-defined caps on the regular vacuum probe

The normalized probe cap needed in `SwappedVacuumNonpositiveBubbles.md`,
§2, must be a module morphism with target the original regular T₀.
We use the selected native F/E chart, the prescribed last inverse row,
and the inverse fully faithful inclusion unit. No final mixed slide or
identification with a separate action's left counit is asserted here.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.ProbeVacuumCap
open BalancedInduction CyclotomicCrossingTensor
universe u

private theorem total_mem
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {F G : Superfunctor k C (SVec k)} {f : F ⟶ G} {p : ZMod 2}
    (hf : f ∈ parity (R := k) _ _ p) (t : C) :
    f.total t ∈ parity (R := k) (F.obj t) (G.obj t) p := by
  rcases parity_eq_zero_or_one p with rfl | rfl
  · rw [SuperNatTrans.total, Superfunctor.app_eq_zero_of_mem hf (by decide : (1 : ZMod 2) ≠ 0) t,
      add_zero]
    exact f.app_mem 0 t
  · rw [SuperNatTrans.total, Superfunctor.app_eq_zero_of_mem hf (by decide : (0 : ZMod 2) ≠ 1) t,
      zero_add]
    exact f.app_mem 1 t

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) [Fintype I] (m : I → ℕ)
local notation "cut" => probeCutoff D m
local notation "N" => probeOldVacuumRegular D Sc m
local notation "K" => oldContentAppend D Sc cut []
local notation "s" => probeOldVacuumObject D Sc m

omit [Fintype I] in
private theorem height (i : I) :
    0 ≤ contentCrossingHeight D cut i (([] : List I) : Multiset I) := by
  simp [contentCrossingHeight]

private def topIndex (i : I) (hP : 0 < cut i) :
    Fin (contentUnitCount D cut i (([] : List I) : Multiset I)) :=
  ⟨cut i - 1, by rw [VacuumCoefficient.count]; omega⟩

/-- The native F/E module of the original regular probe T₀. -/
abbrev source (i : I) : Superfunctor k (OldContentCategory D Sc cut []) (SVec k) :=
  (restriction (K i)).obj ((induction (K i)).obj N)

/-- The inverse-defined last coefficient cap, now with the original regular
probe as target rather than its full-old extension. -/
def cap (i : I) (hP : 0 < cut i) : source D Sc m i ⟶ N :=
  contentCoefficientCap D Sc cut [] i N (height D m i) (topIndex D m i hP)

/-- The probe cap has the prescribed last-row degree (P-1)*p. -/
theorem cap_mem (i : I) (hP : 0 < cut i) :
    cap D Sc m i hP ∈ parity (R := k) _ _ ((cut i - 1) • D.parity i) :=
  contentCoefficientCap_mem D Sc cut [] i N (height D m i) (topIndex D m i hP)

end OddMath.QuiverHecke.ELV.ProbeVacuumCap
end

end

section

/-! # The signed vacuum probe polynomial on the old coend

The scalar comparison is the prescribed append isomorphism, and its proved
dot square retains the given signed dot. This attaches the vacuum probe
annihilator of `SwappedVacuumBubbles.md`, (5), to the old module itself.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.ELV OddMath.QuiverHecke.ELV.BalancedInduction
namespace OddMath.QuiverHecke
universe u v

private theorem iso_total_injective
    {k C : Type u} [CommRing k] [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
    {F G : Superfunctor k C (SVec k)} (e : F ≅ G) (w : C) :
    Function.Injective (e.hom.total w) :=
  (moduleIsoLinearEquiv e w).injective

private theorem intertwine_probe_polynomial
    {k V W : Type u} [CommRing k] [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W]
    (C : V →ₗ[k] W) (hC : Function.Injective C)
    (x : Module.End k V) (y : Module.End k W) (h : C.comp x = y.comp C)
    (m : ℕ) (hy : (y ^ 2 + 1) ^ m = 0) : (x ^ 2 + 1) ^ m = 0 := by
  have h2 := intertwine_pow C x y h 2
  have hs : C.comp (x ^ 2 + 1) = (y ^ 2 + 1).comp C := by
    rw [LinearMap.comp_add, LinearMap.add_comp, h2]
    rfl
  have hm := intertwine_pow C (x ^ 2 + 1) (y ^ 2 + 1) hs m
  apply LinearMap.ext
  intro z
  apply hC
  have hh := LinearMap.congr_fun hm z
  simpa only [LinearMap.comp_apply, hy, LinearMap.zero_apply, map_zero] using hh

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) [Fintype I] (m : I → ℕ)
  (N : Superfunctor k (ELV.OldContentCategory D Sc (probeCutoff D m) []) (SVec k))
  (hN : ProbeEvaluatesCoefficients D m Sc [] N)
include hN

/-- The given signed dot on the unchanged old vacuum coend has the plus-one
probe annihilator. Scalar evaluation and the chosen append comparison are proved inputs. -/
theorem probeOldVacuumInductionDot_odd (i : I) (hi : D.parity i = 1)
    (w : ELV.OldContentCategory D Sc (probeCutoff D m) [i]) :
    (probeOldContentInductionDot D Sc m [] i N w ^ 2 + 1) ^ m i = 0 := by
  rcases w with ⟨⟨word⟩, hw⟩
  let w : ELV.OldContentCategory D Sc (probeCutoff D m) [i] := ⟨⟨word⟩, hw⟩
  let O := probeOrdinaryModuleSuperfunctor D Sc m [] N hN
  let U := probeOldOrdinaryFunctor D Sc m [i]
  let L := ELV.BalancedInduction.induced
    (ELV.oldContentAppend D Sc (probeCutoff D m) [] i) N
  let hL := probeOldInduced_evaluatesCoefficients D m Sc [] i N hN
  let S := probeOrdinaryModuleSuperfunctor D Sc m [i] L hL
  let T := ELV.BalancedInduction.induced (probeOrdinaryAppend D Sc m [] i) O
  let e : S ≅ T := probeAppendOrdinaryModuleIso D Sc m [] N hN i
  let C := probeAppendComparisonLinear D Sc m [] N hN i w
  let x := probeOldContentInductionDot D Sc m [] i N w
  let y := transformLinear (probeOrdinaryAppendDot_supernatural D Sc m [] i) O (U.obj w)
  have hC : Function.Injective C := by
    dsimp only [C, probeAppendComparisonLinear]
    have hh : Function.Injective (e.hom.total (U.obj w)) :=
      iso_total_injective (F := S) (G := T) e (U.obj w)
    dsimp only [e, S, T, L, O, U, w, probeOrdinaryModuleSuperfunctor,
      probeOrdinaryModuleFunctor, probeOrdinaryOldObject, probeOldOrdinaryFunctor] at hh ⊢
    exact hh
  have hd : C.comp x = y.comp C := probeAppendOrdinaryModuleIso_hom_dot D Sc m [] N hN i w
  exact intertwine_probe_polynomial C hC x y hd (m i)
    (probeOrdinaryVacuumInductionDot_odd D Sc m i hi O (U.obj w))

/-- The literal old vacuum probe satisfies its polynomial as an endomorphism
of the entire old induced supermodule, before scalar descent. -/
theorem probeOldVacuumModuleDot_odd (i : I) (hi : D.parity i = 1) :
    let x : End (ELV.BalancedInduction.induced
        (ELV.oldContentAppend D Sc (probeCutoff D m) [] i) N) :=
      ELV.BalancedInduction.transformComponent
        (probeOldContentAppendDot_supernatural D Sc m [] i) N
    (x ^ 2 + 1) ^ m i = 0 := by
  dsimp only
  apply ELV.BalancedInduction.end_eq_zero_of_total
  intro w
  let P := ELV.BalancedInduction.induced
    (ELV.oldContentAppend D Sc (probeCutoff D m) [] i) N
  let x : End P := ELV.BalancedInduction.transformComponent
    (probeOldContentAppendDot_supernatural D Sc m [] i) N
  have hx : x.total w = probeOldContentInductionDot D Sc m [] i N w := by
    dsimp only [probeOldContentInductionDot]
    simp only [x, SuperNatTrans.total, ELV.BalancedInduction.transformComponent_app,
      hi, zero_ne_one, ↓reduceIte, zero_add]
  change ((x ^ 2 + 1) ^ m i).total w = 0
  rw [ELV.BalancedInduction.end_total_pow]
  have hs : (x ^ 2 + 1).total w = (x ^ 2).total w + (1 : End P).total w := by
    change ((x ^ 2).app 0 w + (1 : End P).app 0 w) +
      ((x ^ 2).app 1 w + (1 : End P).app 1 w) =
      ((x ^ 2).app 0 w + (x ^ 2).app 1 w) +
        ((1 : End P).app 0 w + (1 : End P).app 1 w)
    abel
  have h1 : (1 : End P).total w = (1 : End (P.obj w)) := SuperNatTrans.id_total _ _
  rw [hs, ELV.BalancedInduction.end_total_pow, h1, hx]
  exact probeOldVacuumInductionDot_odd D Sc m N hN i hi w

end OddMath.QuiverHecke
end

end

section

/-! # Native probe cap normalization

The last inverse-unit row in `SwappedVacuumNonpositiveBubbles.md`, §2,
extracts the prescribed native unit/dot column. The selected scalar charts
are cancelled, retaining the actual module unit, dot and coefficient cap.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
open ELV ELV.BalancedInduction ELV.CyclotomicCrossingTensor
universe u

private theorem inverseRow_window_cancel
    {k V W S T : Type u} [CommRing k]
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    [AddCommGroup S] [Module k S] [AddCommGroup T] [Module k T]
    (v : V ≃ₗ[k] W) (c : S →ₗ[k] T)
    (f : S →ₗ[k] V) (g : T →ₗ[k] W) (a : V →ₗ[k] S) (b : W →ₗ[k] T)
    (hf : v.toLinearMap ∘ₗ f = g ∘ₗ c)
    (ha : c ∘ₗ a = b ∘ₗ v.toLinearMap)
    (q : Prop) [Decidable q] (hg : g ∘ₗ b = if q then LinearMap.id else 0) :
    f ∘ₗ a = if q then LinearMap.id else 0 := by
  apply LinearMap.ext
  intro x
  apply v.injective
  have h : v (f (a x)) = (g ∘ₗ b) (v x) := by
    calc
      _ = g (c (a x)) := LinearMap.congr_fun hf (a x)
      _ = g (b (v x)) := congrArg g (LinearMap.congr_fun ha x)
      _ = _ := rfl
  rw [hg] at h
  by_cases hq : q
  · simpa only [hq, ↓reduceIte, LinearMap.id_apply, LinearMap.comp_apply] using h
  · simpa only [hq, ↓reduceIte, LinearMap.zero_apply, map_zero, LinearMap.comp_apply] using h

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ) (γ : List I)
  (N : Superfunctor k (OldContentCategory D Sc (probeCutoff D m) γ) (SVec k))
  (hN : ProbeEvaluatesCoefficients D m Sc γ N) (i : I) (hi : i ∉ γ)
  (w : OldContentCategory D Sc (probeCutoff D m) γ)
local notation "cut" => probeCutoff D m
local notation "count" => contentUnitCount D cut i (γ : Multiset I)
local notation "K" => oldContentAppend D Sc cut γ i
include hN

/-- The actual native prescribed cap extracts its own given dotted-unit
column, with the canonical inverse-row unshift and no additional scalar. -/
theorem probeContentCoefficientCap_unitDot (r : Fin count) (a : ℕ) (ha : a < count) :
    SVec.toLinearMap ((contentCoefficientCap D Sc cut γ i N
      (contentCrossingHeight_nonneg_of_not_mem D cut γ i hi) r).total w) ∘ₗ
      unitDotLinear K (probeOldContentAppendDot_supernatural D Sc m γ i) N a w =
    if a = r.val then LinearMap.id else 0 := by
  classical
  exact inverseRow_window_cancel
    (probeOutputValueLinearEquiv D Sc m γ N hN w)
    (probeOutputFELinearEquiv D Sc m γ N hN i w).toLinearMap _ _ _ _
    (probeMissingColourUnitCoefficient_cap D Sc m γ N hN i hi w r)
    (probeOutputFELinearEquiv_unitDot D Sc m γ N hN i w a) _
    (probeMissingColourUnitCoefficient_unitDot D Sc m γ N hN i hi w r a ha)

/-- The same native window on the component of the actual module
unit/dot column, rather than a separately specified coend operator. -/
theorem probeContentCoefficientCap_unitDotColumn
    (r : Fin count) (a : ℕ) (ha : a < count) :
    SVec.toLinearMap ((contentCoefficientCap D Sc cut γ i N
      (contentCrossingHeight_nonneg_of_not_mem D cut γ i hi) r).total w) ∘ₗ
      SVec.toLinearMap ((unitDotColumn K
        (probeOldContentAppendDot_supernatural D Sc m γ i) N a).total w) =
    if a = r.val then LinearMap.id else 0 := by
  rw [unitDotColumn_total]
  exact probeContentCoefficientCap_unitDot D Sc m γ N hN i hi w r a ha

end OddMath.QuiverHecke

namespace OddMath.QuiverHecke.ELV.ProbeVacuumCap
open BalancedInduction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) [Fintype I] (m : I → ℕ)
local notation "cut" => probeCutoff D m
local notation "N" => probeOldVacuumRegular D Sc m
local notation "K" => oldContentAppend D Sc cut []
local notation "s" => probeOldVacuumObject D Sc m

/-- The actual native dot on the same F/E probe superspace as the cap. -/
abbrev dot (i : I) : End ((source D Sc m i).obj s) :=
  restrictedDotComponent (K i) (probeOldContentAppendDot_supernatural D Sc m [] i) N s

/-- The given ordinary unit applied to the literal ground coordinate. -/
def unitVector (i : I) (c : k) : (source D Sc m i).obj s :=
  ((adjunction (K i)).unit.app N).total s ((probeVacuumScalarEquiv D Sc m) c)

end OddMath.QuiverHecke.ELV.ProbeVacuumCap
end

end

section

/-! # Module-map normalization of the regular probe cap

The normalized cap of `SwappedActionAssembly.md`, §5 (A14), must retain
its module maps before Hom precomposition. We promote the given inverse-row
window and signed dot polynomial to that level, without a left adjunction.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.ProbeVacuumCap
open BalancedInduction CyclotomicCrossingTensor
universe u

private theorem module_window
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {M S : Superfunctor k C (SVec k)} (a : M ⟶ S) (b : S ⟶ M)
    (q : Prop) [Decidable q]
    (h : ∀ w, SVec.toLinearMap (b.total w) ∘ₗ SVec.toLinearMap (a.total w) =
      if q then LinearMap.id else 0) :
    a ≫ b = if q then 𝟙 M else 0 := by
  apply FiniteSupermodule.hom_ext_total
  intro w
  rw [Superfunctor.comp_total]
  have hw := h w
  by_cases hq : q
  · rw [ite_eq_left hq] at hw ⊢
    apply LinearMap.ext
    intro x
    rw [SVec.comp_apply]
    have hid : (𝟙 M : M ⟶ M).total w = 𝟙 (M.obj w) := SuperNatTrans.id_total M.toFunctor w
    rw [hid, SVec.id_apply]
    simpa only [LinearMap.comp_apply, SVec.coe_toLinearMap, LinearMap.id_apply]
      using LinearMap.congr_fun hw x
  · rw [ite_eq_right hq] at hw ⊢
    apply LinearMap.ext
    intro x
    rw [SVec.comp_apply]
    simpa only [SuperNatTrans.total, Superfunctor.zero_app, zero_add, SVec.zero_apply, LinearMap.comp_apply, SVec.coe_toLinearMap, LinearMap.zero_apply]
      using LinearMap.congr_fun hw x

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) [Fintype I] (m : I → ℕ)
local notation "cut" => probeCutoff D m
local notation "N" => probeOldVacuumRegular D Sc m
local notation "K" => oldContentAppend D Sc cut []

/-- The same dot used in the normalized ground window, retained as a
module endomorphism before evaluation or Hom precomposition. -/
abbrev moduleDot (i : I) : End (source D Sc m i) :=
  restrictedDotEnd (K i) (probeOldContentAppendDot_supernatural D Sc m [] i) N

/-- The given dotted-unit column followed by the prescribed last inverse
row is the Kronecker identity as a module map, at every empty-content object. -/
theorem unitDotColumn_cap (i : I) (hP : 0 < cut i) (a : ℕ) (ha : a < cut i) :
    unitDotColumn (K i) (probeOldContentAppendDot_supernatural D Sc m [] i) N a ≫
      cap D Sc m i hP = if a + 1 = cut i then 𝟙 N else 0 := by
  classical
  let r : Fin (contentUnitCount D cut i (([] : List I) : Multiset I)) :=
    ⟨cut i - 1, by rw [VacuumCoefficient.count]; omega⟩
  have hac : a < contentUnitCount D cut i (([] : List I) : Multiset I) := by
    rw [VacuumCoefficient.count]
    exact ha
  have h := module_window
    (unitDotColumn (K i) (probeOldContentAppendDot_supernatural D Sc m [] i) N a)
    (cap D Sc m i hP) (a = r.val) (fun w =>
      probeContentCoefficientCap_unitDotColumn D Sc m [] N
        (probeOldModule_evaluatesCoefficients D m Sc [] _) i (by simp) w r a hac)
  have har : a = r.val ↔ a + 1 = cut i := by dsimp only [r]; omega
  simpa only [har] using h

/-- The signed probe polynomial holds on the same module endomorphism
whose components were used for the normalized cap window. -/
theorem moduleDot_odd_polynomial (i : I) (hi : D.parity i = 1) :
    (moduleDot D Sc m i ^ 2 + 1) ^ m i = 0 := by
  exact additiveFunctor_odd_probe_polynomial (restriction (K i))
    (dotEnd (K i) (probeOldContentAppendDot_supernatural D Sc m [] i) N) (m i)
    (probeOldVacuumModuleDot_odd D Sc m N
      (probeOldModule_evaluatesCoefficients D m Sc [] _) i hi)

end OddMath.QuiverHecke.ELV.ProbeVacuumCap
end

end

section

/-! # Precomposition by the prescribed probe cap

`SwappedActionAssembly.md`, §5 (A14) and §6, uses the homogeneous native
cap on a Hom sector. We retain the actual inverse-defined cap and the same
module dot. The lower Hom construction does not require a Rouquier family;
identification with its normalized left adjunction still requires its unit
and triangles.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELV.ProbeVacuumCap
open BalancedInduction CyclotomicCrossingTensor
universe u

private theorem homPreTransform_total
    {k : Type u} [CommRing k] {A B R : PiSCat.{u,u,u+1} k}
    {F G : A ⟶ B} {p : ZMod 2} (η : F ⟶ G)
    (hη : η ∈ parity (R := k) _ _ p) (H : B ⟶ R) :
    (SKM.homPreTransform (c := R) η hη).total H = η ▷ H := by
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    simp [SuperNatTrans.total, SKM.homPreTransform]

private theorem whiskerRight_total
    {k : Type u} [CommRing k] {A B R : PiSCat.{u,u,u+1} k}
    {F G : A ⟶ B} (η : F ⟶ G) (H : B ⟶ R) (M : A) :
    (η ▷ H).total M = H.map (η.total M) := by
  change H.map (η.app 0 M) + H.map (η.app 1 M) = H.map (η.app 0 M + η.app 1 M)
  exact (Functor.map_add H.toFunctor).symm

private theorem restrictedDot_supernatural
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α) :
    IsSupernatural k p (F := induction J ⋙ restriction J) (G := induction J ⋙ restriction J)
      (fun M => restrictedDotEnd J hα M) :=
  (transformComponent_supernatural hα).whiskerRight (restriction J)

private theorem family_total
    {k : Type u} [CommRing k] {C A : Type*} [Category C] [Category A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    {F G : C ⥤ A} {p : ZMod 2} {α : ∀ M, F.obj M ⟶ G.obj M}
    (hα : IsSupernatural k p α) (M : C) : hα.toSuperNatTrans.total M = α M := by
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    simp [SuperNatTrans.total, IsSupernatural.toSuperNatTrans]

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) [Fintype I] (m : I → ℕ)
local notation "cut" => probeCutoff D m
local notation "N" => probeOldVacuumRegular D Sc m
local notation "K" => oldContentAppend D Sc cut []

/-- The native module category of the original empty-content probe, with
its given vector-parity shift. -/
def modulePiCategory : PiSCat.{u,u,u+1} k where
  toSCat := SCat.of k (Superfunctor k (OldContentCategory D Sc cut []) (SVec k))
  pi := supermodulePiSupercategory

/-- The actual F/E endofunctor on the probe input category. -/
def appendRestrict (i : I) : modulePiCategory D Sc m ⟶ modulePiCategory D Sc m :=
  show Superfunctor k
    (Superfunctor k (OldContentCategory D Sc cut []) (SVec k))
    (Superfunctor k (OldContentCategory D Sc cut []) (SVec k)) from
      ⟨induction (K i) ⋙ restriction (K i)⟩

private def lastSlot (i : I) (hP : 0 < cut i) :
    Fin (contentUnitCount D cut i (([] : List I) : Multiset I)) :=
  ⟨cut i - 1, by rw [VacuumCoefficient.count]; omega⟩

omit [Fintype I] in
private theorem height_2 (i : I) : 0 ≤ contentCrossingHeight D cut i (([] : List I) : Multiset I) := by
  simp [contentCrossingHeight]

/-- The input-supernatural last inverse row, as a genuine 2-cell in the
native Π-supercategory of module categories. -/
def capCell (i : I) (hP : 0 < cut i) :
    appendRestrict D Sc m i ⟶ 𝟙 (modulePiCategory D Sc m) :=
  contentCoefficientCapFamily D Sc cut [] i (height_2 D m i) (lastSlot D m i hP)

omit [Fintype I] in
/-- The cap 2-cell retains the prescribed last-row degree. -/
theorem capCell_mem (i : I) (hP : 0 < cut i) :
    capCell D Sc m i hP ∈ parity (R := k) _ _ ((cut i - 1) • D.parity i) :=
  Superfunctor.mem_parity_iff_isHomogeneous.mpr
    (contentCoefficientCapFamily_isHomogeneous D Sc cut [] i
      (height_2 D m i) (lastSlot D m i hP))

/-- Its component at the regular probe is the already normalized cap. -/
theorem capCell_total (i : I) (hP : 0 < cut i) :
    (capCell D Sc m i hP).total N = cap D Sc m i hP :=
  contentCoefficientCapFamily_total D Sc cut [] i
    (height_2 D m i) (lastSlot D m i hP) N

/-- Precomposition by the actual cap, with signed naturality on every
reservoir functor and arbitrary homogeneous maps between such functors. -/
def preCap (R : PiSCat.{u,u,u+1} k) (i : I) (hP : 0 < cut i) :
    SuperNatTrans k (SKM.homPre (k := k) (c := R) (appendRestrict D Sc m i))
      (SKM.homPre (k := k) (c := R) (𝟙 (modulePiCategory D Sc m))) :=
  SKM.homPreTransform (k := k) (B := PiSCat.{u,u,u+1} k) (capCell D Sc m i hP) (capCell_mem D Sc m i hP)

/-- The actual restricted induction dot as an input-supernatural 2-cell. -/
def dotCell (i : I) : End (appendRestrict D Sc m i) :=
  (restrictedDot_supernatural (K i)
    (probeOldContentAppendDot_supernatural D Sc m [] i)).toSuperNatTrans

omit [Fintype I] in
/-- The dot 2-cell has precisely the moving-colour degree. -/
theorem dotCell_mem (i : I) : dotCell D Sc m i ∈ parity (R := k) _ _ (D.parity i) :=
  Superfunctor.mem_parity_iff_isHomogeneous.mpr
    ((restrictedDot_supernatural (K i)
      (probeOldContentAppendDot_supernatural D Sc m [] i)).toSuperNatTrans_isHomogeneous)

/-- Its regular-probe component is the same module dot as the cap window. -/
theorem dotCell_total (i : I) : (dotCell D Sc m i).total N = moduleDot D Sc m i := by
  exact family_total (restrictedDot_supernatural (K i)
    (probeOldContentAppendDot_supernatural D Sc m [] i)) N

/-- The genuine precomposition dot transformation on the chosen Hom carrier. -/
def preDot (R : PiSCat.{u,u,u+1} k) (i : I) :
    SuperNatTrans k (SKM.homPre (k := k) (c := R) (appendRestrict D Sc m i))
      (SKM.homPre (k := k) (c := R) (appendRestrict D Sc m i)) :=
  SKM.homPreTransform (k := k) (B := PiSCat.{u,u,u+1} k)
    (dotCell D Sc m i) (dotCell_mem D Sc m i)

/-- Evaluating the precomposition dot gives the reservoir image of the
same signed module dot, with no transpose substitution. -/
theorem preDot_total (R : PiSCat.{u,u,u+1} k) (i : I)
    (H : modulePiCategory D Sc m ⟶ R) :
    ((preDot D Sc m R i).total H).total N = H.map (moduleDot D Sc m i) := by
  rw [preDot, homPreTransform_total, whiskerRight_total, dotCell_total]

/-- Evaluation of the given Hom dot, with its endomorphism object explicit. -/
def preDotEnd (R : PiSCat.{u,u,u+1} k) (i : I)
    (H : modulePiCategory D Sc m ⟶ R) : End (H.obj (source D Sc m i)) :=
  ((preDot D Sc m R i).total H).total N

/-- This evaluated endomorphism is the image of the same module dot. -/
theorem preDotEnd_eq (R : PiSCat.{u,u,u+1} k) (i : I)
    (H : modulePiCategory D Sc m ⟶ R) :
    preDotEnd D Sc m R i H = H.map (moduleDot D Sc m i) :=
  preDot_total D Sc m R i H

/-- The polynomial is preserved on the evaluated, actual precomposition
dot in the same Hom carrier as the prescribed cap. -/
theorem preDot_odd_polynomial (R : PiSCat.{u,u,u+1} k) (i : I) (hi : D.parity i = 1)
    (H : modulePiCategory D Sc m ⟶ R) :
    (preDotEnd D Sc m R i H ^ 2 + 1) ^ m i = 0 := by
  rw [preDotEnd_eq]
  exact additiveFunctor_odd_probe_polynomial H.toFunctor (moduleDot D Sc m i) (m i)
    (moduleDot_odd_polynomial D Sc m i hi)

end OddMath.QuiverHecke.ELV.ProbeVacuumCap
end

end

section

/-! # Supported and absent two-step OLD probe induction

`SwappedActionAssembly` F2: identify the actual two global OLD probe
induction coordinates with their stored-target block inductions. An absent
double predecessor contributes the actual zero evaluated module, including
when the first predecessor alone is absent. No weight-fibre finiteness or
coefficient-power quotient is used.
-/
noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.CyclotomicAction
universe u
namespace OddMath.QuiverHecke
open ELV
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)

section Pair
variable (i j : I) (Λ : X) {x₀ x₁ x₃ : X}
  (h₁ : x₀ + D.α j = x₁) (h₂ : x₁ + D.α i = x₃)

/-- Both actual block inductions, retaining their chosen intermediate content. -/
abbrev probeOldBlockPairInd (β : WeightBlocks D Λ x₀) :=
  (probeOldBlockInd D Sc m j Λ h₁ β).comp
    (probeOldBlockInd D Sc m i Λ h₂ (blockSucc D Λ j h₁ β))

/-- Literal coordinate of the composed product induction at a double successor. -/
theorem probeOldEFunctor_comp₂_blockSucc (β : WeightBlocks D Λ x₀) :
    probeOldEFunctor D Sc m j Λ h₁ ⋙
        (probeOldInductionComponent D Sc m i Λ h₂
          (blockSucc₂ D i j Λ h₁ h₂ β)).toFunctor =
      (probeOldBlockEval D Sc m Λ β).toFunctor ⋙
        (probeOldBlockPairInd D Sc m i j Λ h₁ h₂ β).toFunctor := by
  rw [probeOldInductionComponent_blockSucc]
  change (probeOldInductionComponent D Sc m j Λ h₁
      (blockSucc D Λ j h₁ β)).toFunctor ⋙
    (probeOldBlockInd D Sc m i Λ h₂ (blockSucc D Λ j h₁ β)).toFunctor = _
  rw [probeOldInductionComponent_blockSucc]
  rfl

/-- An absent double predecessor gives the actual zero coordinate, including
when only the inner predecessor is absent. -/
theorem probeOldEFunctor_comp₂_isZero (ε : WeightBlocks D Λ x₃)
    (hε : ¬ ∃ β, blockSucc₂ D i j Λ h₁ h₂ β = ε)
    (M : ProbeOldWeightProduct D Sc m Λ x₀) :
    Limits.IsZero ((probeOldEFunctor D Sc m j Λ h₁ ⋙
      (probeOldInductionComponent D Sc m i Λ h₂ ε).toFunctor).obj M) := by
  by_cases hγ : ∃ γ, blockSucc D Λ i h₂ γ = ε
  · obtain ⟨γ, rfl⟩ := hγ
    have hz : Limits.IsZero ((probeOldEFunctor D Sc m j Λ h₁).obj M γ) :=
      probeOldInductionComponent_isZero D Sc m j Λ h₁ γ
        (fun ⟨β, hβ⟩ => hε ⟨β, by rw [blockSucc₂, hβ]⟩) M
    exact Limits.IsZero.of_iso
      ((probeOldBlockInd D Sc m i Λ h₂ γ).toFunctor.map_isZero hz)
      (eqToIso (probeOldInductionComponent_obj_blockSucc D Sc m i Λ h₂ γ _))
  · exact probeOldInductionComponent_isZero D Sc m i Λ h₂ ε hγ _

end Pair
end OddMath.QuiverHecke
end

end

section

/-! # Three-step OLD probe induction on original weights

Brundan–Ellis (1.9): retain all actual intermediate content blocks in
three successive OLD probe inductions. The literal product coordinate
is the selected block triple; absent triple predecessors have the actual
zero evaluated module, including missing inner predecessors.
-/
noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
open ELV CyclotomicAction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (i j l : I) (Λ : X) {x₀ x₁ x₂ x₃ : X}
  (h₁ : x₀ + D.α l = x₁) (h₂ : x₁ + D.α j = x₂) (h₃ : x₂ + D.α i = x₃)

/-- The actual block reached by the three successive inductions. -/
abbrev probeOldBlockSucc₃ (β : WeightBlocks D Λ x₀) : WeightBlocks D Λ x₃ :=
  blockSucc D Λ i h₃ (blockSucc₂ D j l Λ h₁ h₂ β)

/-- All three chosen block inductions, retaining both stored intermediate targets. -/
abbrev probeOldBlockTripleInd (β : WeightBlocks D Λ x₀) :=
  (probeOldBlockPairInd D Sc m j l Λ h₁ h₂ β).comp
    (probeOldBlockInd D Sc m i Λ h₃ (blockSucc₂ D j l Λ h₁ h₂ β))

/-- The literal global triple coordinate is the selected actual block triple. -/
theorem probeOldEFunctor_comp₃_blockSucc (β : WeightBlocks D Λ x₀) :
    (probeOldEFunctor D Sc m l Λ h₁ ⋙ probeOldEFunctor D Sc m j Λ h₂) ⋙
      (probeOldInductionComponent D Sc m i Λ h₃
        (probeOldBlockSucc₃ D i j l Λ h₁ h₂ h₃ β)).toFunctor =
    (probeOldBlockEval D Sc m Λ β).toFunctor ⋙
      (probeOldBlockTripleInd D Sc m i j l Λ h₁ h₂ h₃ β).toFunctor := by
  rw [probeOldInductionComponent_blockSucc]
  change (probeOldEFunctor D Sc m l Λ h₁ ⋙
      (probeOldEFunctor D Sc m j Λ h₂ ⋙
        (probeOldBlockEval D Sc m Λ (blockSucc₂ D j l Λ h₁ h₂ β)).toFunctor)) ⋙
      (probeOldBlockInd D Sc m i Λ h₃ (blockSucc₂ D j l Λ h₁ h₂ β)).toFunctor = _
  change (probeOldEFunctor D Sc m l Λ h₁ ⋙
      (probeOldInductionComponent D Sc m j Λ h₂ (blockSucc₂ D j l Λ h₁ h₂ β)).toFunctor) ⋙
      (probeOldBlockInd D Sc m i Λ h₃ (blockSucc₂ D j l Λ h₁ h₂ β)).toFunctor = _
  rw [probeOldEFunctor_comp₂_blockSucc]
  rfl

/-- The selected equality on the entire supported output object. -/
theorem probeOldWeightTriple_obj_eq (β : WeightBlocks D Λ x₀)
    (M : ProbeOldWeightProduct D Sc m Λ x₀) :
    ((probeOldEFunctor D Sc m l Λ h₁ ⋙ probeOldEFunctor D Sc m j Λ h₂) ⋙
      (probeOldInductionComponent D Sc m i Λ h₃
        (probeOldBlockSucc₃ D i j l Λ h₁ h₂ h₃ β)).toFunctor).obj M =
      (probeOldBlockTripleInd D Sc m i j l Λ h₁ h₂ h₃ β).obj (M β) :=
  congrArg (fun H => H.obj M) (probeOldEFunctor_comp₃_blockSucc D Sc m i j l Λ h₁ h₂ h₃ β)

/-- An absent triple predecessor gives the actual zero coordinate, at every input. -/
theorem probeOldEFunctor_comp₃_isZero (ε : WeightBlocks D Λ x₃)
    (hε : ¬ ∃ β, probeOldBlockSucc₃ D i j l Λ h₁ h₂ h₃ β = ε)
    (M : ProbeOldWeightProduct D Sc m Λ x₀) :
    Limits.IsZero (((probeOldEFunctor D Sc m l Λ h₁ ⋙ probeOldEFunctor D Sc m j Λ h₂) ⋙
      (probeOldInductionComponent D Sc m i Λ h₃ ε).toFunctor).obj M) := by
  by_cases hγ : ∃ γ, blockSucc D Λ i h₃ γ = ε
  · obtain ⟨γ, rfl⟩ := hγ
    have hz : Limits.IsZero ((probeOldEFunctor D Sc m l Λ h₁ ⋙
        (probeOldInductionComponent D Sc m j Λ h₂ γ).toFunctor).obj M) :=
      probeOldEFunctor_comp₂_isZero D Sc m j l Λ h₁ h₂ γ
        (fun ⟨β, hβ⟩ => hε ⟨β, by rw [probeOldBlockSucc₃, hβ]⟩) M
    exact Limits.IsZero.of_iso
      ((probeOldBlockInd D Sc m i Λ h₃ γ).toFunctor.map_isZero hz)
      (eqToIso (probeOldInductionComponent_obj_blockSucc D Sc m i Λ h₃ γ _))
  · exact probeOldInductionComponent_isZero D Sc m i Λ h₃ ε hγ _

end OddMath.QuiverHecke
end

end
