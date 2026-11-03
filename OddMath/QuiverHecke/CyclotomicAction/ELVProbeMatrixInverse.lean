import OddMath.QuiverHecke.CyclotomicAction.ELVProbeMatrixInverseCandidates
import OddMath.QuiverHecke.CyclotomicAction.ELVContentFiniteMatrixComparison
import OddMath.QuiverHecke.CyclotomicAction.ELVParityMatrixSquares

/-! # Prescribed scalar finite matrix inverses

Brundan--Ellis (1.13)--(1.14), DeformedMatrixComparison (4), (5).
Both candidate conjugates of the GIVEN global old matrix inverses have
exactly the independently prescribed ordinary scalar forward fields.
The content and scalar finite matrix squares supply this identification;
no compatibility or inverse hypothesis is added.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.ELVOld OddMath.QuiverHecke.ELVOld.BalancedInduction
open OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
namespace OddMath.QuiverHecke
universe u
private def attachedGivenIsoLinearEquiv {k : Type u} [CommRing k] {V W : SVec k}
    (e : V ≅ W) : V ≃ₗ[k] W where
  toLinearMap := e.hom
  invFun := e.inv
  left_inv x := congrArg (fun f : V ⟶ V => f x) e.hom_inv_id
  right_inv x := congrArg (fun f : W ⟶ W => f x) e.inv_hom_id

private def attachedConjugateGivenIso
    {k : Type u} [CommRing k] {A B V W V' W' : SVec k}
    (s : A ≃ₗ[k] V') (a : A ≃ₗ[k] V) (e : V ≅ W)
    (b : B ≃ₗ[k] W) (t : B ≃ₗ[k] W') : V' ≅ W' :=
  SVec.isoOfLinearEquiv
    ((s.symm.trans a).trans ((attachedGivenIsoLinearEquiv e).trans (b.symm.trans t)))

private theorem attachedConjugateGivenIso_hom_apply
    {k : Type u} [CommRing k] {A B V W V' W' : SVec k}
    (s : A ≃ₗ[k] V') (a : A ≃ₗ[k] V) (e : V ≅ W)
    (b : B ≃ₗ[k] W) (t : B ≃ₗ[k] W') (x : V') :
    (attachedConjugateGivenIso s a e b t).hom x = t (b.symm (e.hom (a (s.symm x)))) := rfl

private theorem attachedConjugateGivenIso_inv_apply
    {k : Type u} [CommRing k] {A B V W V' W' : SVec k}
    (s : A ≃ₗ[k] V') (a : A ≃ₗ[k] V) (e : V ≅ W)
    (b : B ≃ₗ[k] W) (t : B ≃ₗ[k] W') (x : W') :
    (attachedConjugateGivenIso s a e b t).inv x = s (a.symm (e.inv (b (t.symm x)))) := rfl

private theorem attachedConjugateGivenIso_hom_identify
    {k : Type u} [CommRing k] {A B V W V' W' : SVec k}
    (s : A ≃ₗ[k] V') (a : A ≃ₗ[k] V) (e : V ≅ W)
    (b : B ≃ₗ[k] W) (t : B ≃ₗ[k] W') (r : A →ₗ[k] B) (f : V' ⟶ W')
    (hContent : b.toLinearMap ∘ₗ r = SVec.toLinearMap e.hom ∘ₗ a.toLinearMap)
    (hScalar : t.toLinearMap ∘ₗ r = SVec.toLinearMap f ∘ₗ s.toLinearMap) :
    (attachedConjugateGivenIso s a e b t).hom = f := by
  apply LinearMap.ext
  intro x
  have hc := congrArg (fun y => t (b.symm y))
    (LinearMap.congr_fun hContent (s.symm x)).symm
  have hb := congrArg t (b.symm_apply_apply (r (s.symm x)))
  have hs := LinearMap.congr_fun hScalar (s.symm x)
  have hv := congrArg f (s.apply_symm_apply x)
  exact (attachedConjugateGivenIso_hom_apply s a e b t x).trans (hc.trans (hb.trans (hs.trans hv)))

section GenericFields
variable {k C A B : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (K : A ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
  {p : ZMod 2} {γ δ : ∀ s, (J ⋙ K).obj s ⟶ (J ⋙ K).obj s}
  (hγ : IsSupernatural k p γ) (hδ : IsSupernatural k p δ) (he : γ = δ)
include he
private theorem attachedUnitComponent_congr
    {α β : ∀ s, K.obj s ⟶ K.obj s}
    (hα : IsSupernatural k p α) (hβ : IsSupernatural k p β) (hd : α = β)
    (M : Superfunctor k A (SVec k)) (m : ℕ) (w : A) :
    gridUnitMatrixComponent J K hγ hα M m w = gridUnitMatrixComponent J K hδ hβ M m w := by
  cases he
  cases hd
  rfl
private theorem attachedCapComponent_congr
    {α β : ∀ s, J.obj s ⟶ J.obj s}
    (hα : IsSupernatural k p α) (hβ : IsSupernatural k p β) (hd : α = β)
    (M : Superfunctor k A (SVec k)) (m : ℕ) (w : A) :
    gridCapMatrixComponent J K hγ hα M m w = gridCapMatrixComponent J K hδ hβ M m w := by
  cases he
  cases hd
  rfl
end GenericFields

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ) (ν : List I) (i : I)
  (N : Superfunctor k (OldContentCategory D Sc (probeCutoff D m) (i :: ν)) (SVec k))
  (hN : ProbeEvaluatesCoefficients D m Sc (i :: ν) N)
  (w : OldContentCategory D Sc (probeCutoff D m) (i :: ν))
local notation "cut" => probeCutoff D m
local notation "J" => oldContentAppend D Sc cut ν i
local notation "K" => oldContentAppend D Sc cut (i :: ν) i
local notation "Q" => oldContentInclusion D Sc cut (i :: ν)
local notation "G" => induced Q N
local notation "T" => probeOrdinaryAppend D Sc m ν i
local notation "S" => probeOrdinaryAppend D Sc m (i :: ν) i
local notation "U" => probeOldOrdinaryFunctor D Sc m (i :: ν)
local notation "O" => probeOrdinaryModuleSuperfunctor D Sc m (i :: ν) N hN
local notation "uCount" => contentUnitCount D cut i (w.obj.word : Multiset I)
local notation "cCount" => contentCapCount D cut i (w.obj.word : Multiset I)
local notation "hProbe" => probeMatrixOldCross_supernatural D Sc m ν i
local notation "hContent" => oldContentMatrixCross_supernatural D Sc cut ν i
local notation "hOrd" => probeMatrixOrdinaryCross_supernatural D Sc m ν i
local notation "duProbe" => probeOldContentAppendDot_supernatural D Sc m (i :: ν) i
local notation "duContent" => oldContentAppendDot_supernatural D Sc cut (i :: ν) i
local notation "duOrd" => probeOrdinaryAppendDot_supernatural D Sc m (i :: ν) i
local notation "dcProbe" => probeOldContentAppendDot_supernatural D Sc m ν i
local notation "dcContent" => oldContentAppendDot_supernatural D Sc cut ν i
local notation "dcOrd" => probeOrdinaryAppendDot_supernatural D Sc m ν i

/-- The positive-height candidate's forward map is the independently given
ordinary finite unit matrix, with its prescribed mate and unscaled columns. -/
theorem probeTransportedUnitMatrixIso_hom
    (hh : 0 ≤ contentCrossingHeight D cut i (w.obj.word : Multiset I)) :
    (probeTransportedUnitMatrixIso D Sc m ν i N hN w hh).hom =
      gridUnitMatrixComponent T S hOrd duOrd O uCount ((U).obj w) := by
  have hFields := attachedUnitComponent_congr J K hProbe hContent rfl duProbe duContent rfl N uCount w
  have hContent₀ := oldContentMatrixCharts_unitMatrix D Sc cut ν i N uCount w
  have hContent₁ := linearSquare_reencode _ _ _ _ _ _ _ _ rfl
    (congrArg SVec.toLinearMap hFields) rfl rfl hContent₀
  have hGiven := congrArg SVec.toLinearMap
    (TensorMatrixCoordinates.moduleUnitMatrixIso_hom D Sc cut G i w.obj hh)
  have hOld := linearSquare_reencode _ _ _ _ _ _ _ _ rfl rfl hGiven rfl hContent₁
  have hScalar := probeMatrixCharts_unitMatrix D Sc m ν i N hN uCount w
  have hfinal := attachedConjugateGivenIso_hom_identify
    (A := gridUnitMatrixSourceSpace J (D.parity i) N uCount w)
    (B := ((restriction K).obj (induced K N)).obj w)
    (V := unitMatrixSourceSpace D Sc cut i G uCount w.obj)
    (W := mateTargetSpace D Sc cut i G w.obj)
    (V' := gridUnitMatrixSourceSpace T (D.parity i) O uCount ((U).obj w))
    (W' := ((restriction S).obj (induced S O)).obj ((U).obj w))
    (probeUnitMatrixFamilyLinearEquiv D Sc m ν i N hN uCount w)
    (oldContentUnitFamilyEquiv D Sc cut ν i N uCount w)
    (TensorMatrixCoordinates.moduleUnitMatrixIso D Sc cut G i w.obj hh)
    (oldContentFELinearEquiv D Sc cut ν i N w)
    (probeMatrixTargetLinearEquiv D Sc m ν i N hN w)
    (SVec.toLinearMap (gridUnitMatrixComponent J K hProbe duProbe N uCount w))
    (gridUnitMatrixComponent T S hOrd duOrd O uCount ((U).obj w)) hOld hScalar
  exact hfinal

/-- The negative-height candidate's forward map is the independently given
ordinary finite cap matrix, with its prescribed mate and normalized rows. -/
theorem probeTransportedCapMatrixIso_hom
    (hh : contentCrossingHeight D cut i (w.obj.word : Multiset I) ≤ 0) :
    (probeTransportedCapMatrixIso D Sc m ν i N hN w hh).hom =
      gridCapMatrixComponent T S hOrd dcOrd O cCount ((U).obj w) := by
  have hFields := attachedCapComponent_congr J K hProbe hContent rfl dcProbe dcContent rfl N cCount w
  have hContent₀ := oldContentMatrixCharts_capMatrix D Sc cut ν i N cCount w
  have hContent₁ := linearSquare_reencode _ _ _ _ _ _ _ _ rfl
    (congrArg SVec.toLinearMap hFields) rfl rfl hContent₀
  have hGiven := congrArg SVec.toLinearMap
    (TensorMatrixCoordinates.moduleCapMatrixIso_hom D Sc cut G i w.obj hh)
  have hOld := linearSquare_reencode _ _ _ _ _ _ _ _ rfl rfl hGiven rfl hContent₁
  have hScalar := probeMatrixCharts_capMatrix D Sc m ν i N hN cCount w
  have hfinal := attachedConjugateGivenIso_hom_identify
    (A := (induced J ((restriction J).obj N)).obj w)
    (B := gridCapMatrixTargetSpace K (D.parity i) N cCount w)
    (V := mateSourceSpace D Sc cut i G w.obj)
    (W := capMatrixTargetSpace D Sc cut i G cCount w.obj)
    (V' := (induced T ((restriction T).obj O)).obj ((U).obj w))
    (W' := gridCapMatrixTargetSpace S (D.parity i) O cCount ((U).obj w))
    (probeMatrixSourceLinearEquiv D Sc m ν i N hN w)
    (oldContentEFLinearEquiv D Sc cut ν i N w)
    (TensorMatrixCoordinates.moduleCapMatrixIso D Sc cut G i w.obj hh)
    (oldContentCapFamilyEquiv D Sc cut ν i N cCount w)
    (probeCapMatrixFamilyLinearEquiv D Sc m ν i N hN cCount w)
    (SVec.toLinearMap (gridCapMatrixComponent J K hProbe dcProbe N cCount w))
    (gridCapMatrixComponent T S hOrd dcOrd O cCount ((U).obj w)) hOld hScalar
  exact hfinal

/-- The identified unit field preserves the given finite-family grading. -/
theorem probeTransportedUnitMatrixIso_hom_mem
    (hh : 0 ≤ contentCrossingHeight D cut i (w.obj.word : Multiset I)) :
    (probeTransportedUnitMatrixIso D Sc m ν i N hN w hh).hom ∈ parity (R := k) _ _ 0 := by
  rw [probeTransportedUnitMatrixIso_hom]
  exact gridUnitMatrixComponent_mem T S hOrd duOrd O uCount ((U).obj w)
theorem probeTransportedUnitMatrixIso_inv_mem
    (hh : 0 ≤ contentCrossingHeight D cut i (w.obj.word : Multiset I)) :
    (probeTransportedUnitMatrixIso D Sc m ν i N hN w hh).inv ∈ parity (R := k) _ _ 0 :=
  inv_mem _ (probeTransportedUnitMatrixIso_hom_mem D Sc m ν i N hN w hh)
/-- The identified cap field preserves its given normalized finite grading. -/
theorem probeTransportedCapMatrixIso_hom_mem
    (hh : contentCrossingHeight D cut i (w.obj.word : Multiset I) ≤ 0) :
    (probeTransportedCapMatrixIso D Sc m ν i N hN w hh).hom ∈ parity (R := k) _ _ 0 := by
  rw [probeTransportedCapMatrixIso_hom]
  exact gridCapMatrixComponent_mem T S hOrd dcOrd O cCount ((U).obj w)
theorem probeTransportedCapMatrixIso_inv_mem
    (hh : contentCrossingHeight D cut i (w.obj.word : Multiset I) ≤ 0) :
    (probeTransportedCapMatrixIso D Sc m ν i N hN w hh).inv ∈ parity (R := k) _ _ 0 :=
  inv_mem _ (probeTransportedCapMatrixIso_hom_mem D Sc m ν i N hN w hh)
end OddMath.QuiverHecke
