import OddMath.QuiverHecke.CyclotomicAction.ELVProbeMissingColourMatrix
import OddMath.QuiverHecke.CyclotomicAction.ELVUnitColumnInverseRows

/-! # Scalar comparison of the prescribed inverse unit coefficients

The missing-colour, including empty-output, left-cap field comes from a
specified actual unit-matrix inverse coordinate and its canonical source
unshift. Both forward matrix squares are proved by the selected content
and scalar charts, so the original inverse row is preserved as well.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.ELVOld OddMath.QuiverHecke.ELVOld.BalancedInduction
open OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
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
