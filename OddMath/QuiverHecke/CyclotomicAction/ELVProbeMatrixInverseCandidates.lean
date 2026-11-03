import OddMath.QuiverHecke.CyclotomicAction.ELVProbeFiniteMatrixComparison
import OddMath.QuiverHecke.CyclotomicAction.ELVContentGridMatrixCoordinates
import OddMath.QuiverHecke.CyclotomicAction.ELVModuleMatrixInverse

/-! # Concrete scalar conjugates of the given old matrix inverses

DeformedMatrixComparison (4), (5): take the actual global old prescribed
matrix inverse on the selected full-content extension, then use the genuine
content and scalar charts. The positive/negative height hypotheses are the
ones of that given old inverse. These constructions do NOT yet identify
their forward maps with the prescribed scalar matrix components: the
relative-content-to-global field square is still the explicit attachment
obligation. Output content here is i::ν; empty-output and absent-i branches
are separate.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.ELVOld OddMath.QuiverHecke.ELVOld.BalancedInduction
open OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
namespace OddMath.QuiverHecke
universe u

private def probeGivenIsoLinearEquiv {k : Type u} [CommRing k] {V W : SVec k}
    (e : V ≅ W) : V ≃ₗ[k] W where
  toLinearMap := e.hom
  invFun := e.inv
  left_inv x := congrArg (fun f : V ⟶ V => f x) e.hom_inv_id
  right_inv x := congrArg (fun f : W ⟶ W => f x) e.inv_hom_id

private def probeConjugateGivenIso
    {k : Type u} [CommRing k] {A B V W V' W' : SVec k}
    (s : A ≃ₗ[k] V') (a : A ≃ₗ[k] V) (e : V ≅ W)
    (b : B ≃ₗ[k] W) (t : B ≃ₗ[k] W') : V' ≅ W' :=
  SVec.isoOfLinearEquiv
    ((s.symm.trans a).trans ((probeGivenIsoLinearEquiv e).trans (b.symm.trans t)))

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ) (ν : List I) (i : I)
  (N : Superfunctor k (ELVOld.OldContentCategory D Sc (probeCutoff D m) (i :: ν)) (SVec k))
  (hN : ProbeEvaluatesCoefficients D m Sc (i :: ν) N)
  (w : ELVOld.OldContentCategory D Sc (probeCutoff D m) (i :: ν))
local notation "cut" => probeCutoff D m
local notation "J" => ELVOld.oldContentAppend D Sc cut ν i
local notation "K" => ELVOld.oldContentAppend D Sc cut (i :: ν) i
local notation "A" => CyclotomicCrossingTensor.append D Sc cut i
local notation "Q" => oldContentInclusion D Sc cut (i :: ν)
local notation "G" => induced Q N
local notation "T" => probeOrdinaryAppend D Sc m ν i
local notation "S" => probeOrdinaryAppend D Sc m (i :: ν) i
local notation "U" => probeOldOrdinaryFunctor D Sc m (i :: ν)
local notation "O" => probeOrdinaryModuleSuperfunctor D Sc m (i :: ν) N hN
local notation "uCount" => contentUnitCount D cut i (w.obj.word : Multiset I)
local notation "cCount" => contentCapCount D cut i (w.obj.word : Multiset I)

/-- Conjugate the GIVEN positive-height global old inverse, through the
selected content extension and scalar charts. Forward field attachment is open. -/
def probeTransportedUnitMatrixIso
    (hh : 0 ≤ contentCrossingHeight D cut i (w.obj.word : Multiset I)) :
    gridUnitMatrixSourceSpace T (D.parity i) O uCount ((U).obj w) ≅
      ((restriction S).obj (induced S O)).obj ((U).obj w) :=
  probeConjugateGivenIso
    (A := gridUnitMatrixSourceSpace J (D.parity i) N uCount w)
    (B := ((restriction K).obj (induced K N)).obj w)
    (V := unitMatrixSourceSpace D Sc cut i G uCount w.obj)
    (W := mateTargetSpace D Sc cut i G w.obj)
    (probeUnitMatrixFamilyLinearEquiv D Sc m ν i N hN uCount w)
    (oldContentUnitFamilyEquiv D Sc cut ν i N uCount w)
    (TensorMatrixCoordinates.moduleUnitMatrixIso D Sc cut G i w.obj hh)
    (oldContentFELinearEquiv D Sc cut ν i N w)
    (probeMatrixTargetLinearEquiv D Sc m ν i N hN w)

/-- Conjugate the GIVEN negative-height global old inverse, through exactly
the same selected charts. Forward field attachment is open. -/
def probeTransportedCapMatrixIso
    (hh : contentCrossingHeight D cut i (w.obj.word : Multiset I) ≤ 0) :
    (induced T ((restriction T).obj O)).obj ((U).obj w) ≅
      gridCapMatrixTargetSpace S (D.parity i) O cCount ((U).obj w) :=
  probeConjugateGivenIso
    (A := (induced J ((restriction J).obj N)).obj w)
    (B := gridCapMatrixTargetSpace K (D.parity i) N cCount w)
    (V := mateSourceSpace D Sc cut i G w.obj)
    (W := capMatrixTargetSpace D Sc cut i G cCount w.obj)
    (probeMatrixSourceLinearEquiv D Sc m ν i N hN w)
    (oldContentEFLinearEquiv D Sc cut ν i N w)
    (TensorMatrixCoordinates.moduleCapMatrixIso D Sc cut G i w.obj hh)
    (oldContentCapFamilyEquiv D Sc cut ν i N cCount w)
    (probeCapMatrixFamilyLinearEquiv D Sc m ν i N hN cCount w)

/-- The positive-height candidate uses the original old prescribed forward map. -/
theorem probeTransportedUnitMatrixIso_hom_apply
    (hh : 0 ≤ contentCrossingHeight D cut i (w.obj.word : Multiset I))
    (x : gridUnitMatrixSourceSpace T (D.parity i) O uCount ((U).obj w)) :
    (probeTransportedUnitMatrixIso D Sc m ν i N hN w hh).hom x =
      probeMatrixTargetLinearEquiv D Sc m ν i N hN w
        ((oldContentFELinearEquiv D Sc cut ν i N w).symm
          ((TensorMatrixCoordinates.moduleUnitMatrixIso D Sc cut G i w.obj hh).hom
            (oldContentUnitFamilyEquiv D Sc cut ν i N uCount w
              ((probeUnitMatrixFamilyLinearEquiv D Sc m ν i N hN uCount w).symm x)))) := rfl

/-- Its inverse is the original given old inverse, with the same charts reversed. -/
theorem probeTransportedUnitMatrixIso_inv_apply
    (hh : 0 ≤ contentCrossingHeight D cut i (w.obj.word : Multiset I))
    (x : ((restriction S).obj (induced S O)).obj ((U).obj w)) :
    (probeTransportedUnitMatrixIso D Sc m ν i N hN w hh).inv x =
      probeUnitMatrixFamilyLinearEquiv D Sc m ν i N hN uCount w
        ((oldContentUnitFamilyEquiv D Sc cut ν i N uCount w).symm
          ((TensorMatrixCoordinates.moduleUnitMatrixIso D Sc cut G i w.obj hh).inv
            (oldContentFELinearEquiv D Sc cut ν i N w
              ((probeMatrixTargetLinearEquiv D Sc m ν i N hN w).symm x)))) := rfl

/-- The negative-height candidate uses the original old prescribed forward map. -/
theorem probeTransportedCapMatrixIso_hom_apply
    (hh : contentCrossingHeight D cut i (w.obj.word : Multiset I) ≤ 0)
    (x : (induced T ((restriction T).obj O)).obj ((U).obj w)) :
    (probeTransportedCapMatrixIso D Sc m ν i N hN w hh).hom x =
      probeCapMatrixFamilyLinearEquiv D Sc m ν i N hN cCount w
        ((oldContentCapFamilyEquiv D Sc cut ν i N cCount w).symm
          ((TensorMatrixCoordinates.moduleCapMatrixIso D Sc cut G i w.obj hh).hom
            (oldContentEFLinearEquiv D Sc cut ν i N w
              ((probeMatrixSourceLinearEquiv D Sc m ν i N hN w).symm x)))) := rfl

/-- Its inverse uses the given old negative-height inverse and reversed charts. -/
theorem probeTransportedCapMatrixIso_inv_apply
    (hh : contentCrossingHeight D cut i (w.obj.word : Multiset I) ≤ 0)
    (x : gridCapMatrixTargetSpace S (D.parity i) O cCount ((U).obj w)) :
    (probeTransportedCapMatrixIso D Sc m ν i N hN w hh).inv x =
      probeMatrixSourceLinearEquiv D Sc m ν i N hN w
        ((oldContentEFLinearEquiv D Sc cut ν i N w).symm
          ((TensorMatrixCoordinates.moduleCapMatrixIso D Sc cut G i w.obj hh).inv
            (oldContentCapFamilyEquiv D Sc cut ν i N cCount w
              ((probeCapMatrixFamilyLinearEquiv D Sc m ν i N hN cCount w).symm x)))) := rfl

end OddMath.QuiverHecke
