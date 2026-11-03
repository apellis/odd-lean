import OddMath.QuiverHecke.CyclotomicAction.ELVProbeMatrixEntryComparison

/-! # Both prescribed finite scalar matrix squares

DeformedMatrixComparison (4), (5): the independently specified finite unit
and cap matrices commute with the genuine selected E/F/F/E and canonical
parity-family charts. The entry equations are proved, not assumed. Matrix
inversion is kept as a subsequent step using the prescribed old inverse.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped BigOperators
open OddMath.QuiverHecke.ELVOld OddMath.QuiverHecke.ELVOld.BalancedInduction
namespace OddMath.QuiverHecke
universe u

private theorem scalarColumns_square
    {k : Type u} [CommRing k] {ι : Type} [Fintype ι]
    (V W : ι → SVec k) (X Y : SVec k) (e : ∀ a, V a ≃ₗ[k] W a)
    (c : X →ₗ[k] Y) (f : ∀ a, V a ⟶ X) (g : ∀ a, W a ⟶ Y)
    (h : ∀ a, c ∘ₗ SVec.toLinearMap (f a) = SVec.toLinearMap (g a) ∘ₗ (e a).toLinearMap) :
    c ∘ₗ SVec.toLinearMap (OddMath.FiniteSuperspace.assembleColumns V X f) =
      SVec.toLinearMap (OddMath.FiniteSuperspace.assembleColumns W Y g) ∘ₗ
        (LinearEquiv.piCongrRight e).toLinearMap := by
  apply LinearMap.ext
  intro x
  change c (∑ a, f a (x a)) = ∑ a, g a (e a (x a))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro a _
  exact LinearMap.congr_fun (h a) (x a)

private theorem scalarRows_square
    {k : Type u} [CommRing k] {ι : Type}
    (V W : ι → SVec k) (X Y : SVec k) (e : ∀ a, V a ≃ₗ[k] W a)
    (c : X →ₗ[k] Y) (f : ∀ a, X ⟶ V a) (g : ∀ a, Y ⟶ W a)
    (h : ∀ a, (e a).toLinearMap ∘ₗ SVec.toLinearMap (f a) = SVec.toLinearMap (g a) ∘ₗ c) :
    (LinearEquiv.piCongrRight e).toLinearMap ∘ₗ
        SVec.toLinearMap (OddMath.FiniteSuperspace.assembleRows X V f) =
      SVec.toLinearMap (OddMath.FiniteSuperspace.assembleRows Y W g) ∘ₗ c := by
  apply LinearMap.ext
  intro x
  funext a
  change e a (f a x) = g a (c x)
  exact LinearMap.congr_fun (h a) x

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ) (ν : List I) (i : I)
  (N : Superfunctor k (ELVOld.OldContentCategory D Sc (probeCutoff D m) (i :: ν)) (SVec k))
  (hN : ProbeEvaluatesCoefficients D m Sc (i :: ν) N)
local notation "J" => ELVOld.oldContentAppend D Sc (probeCutoff D m) ν i
local notation "K" => ELVOld.oldContentAppend D Sc (probeCutoff D m) (i :: ν) i
local notation "T" => probeOrdinaryAppend D Sc m ν i
local notation "S" => probeOrdinaryAppend D Sc m (i :: ν) i
local notation "U" => probeOldOrdinaryFunctor D Sc m (i :: ν)
local notation "O" => probeOrdinaryModuleSuperfunctor D Sc m (i :: ν) N hN

/-- The entire prescribed finite unit matrix commutes with its genuine
canonical source-family chart and selected F/E target chart. -/
theorem probeMatrixCharts_unitMatrix
    (b : ℕ) (w : ELVOld.OldContentCategory D Sc (probeCutoff D m) (i :: ν)) :
    (probeMatrixTargetLinearEquiv D Sc m ν i N hN w).toLinearMap ∘ₗ
        SVec.toLinearMap (gridUnitMatrixComponent J K (probeMatrixOldCross_supernatural D Sc m ν i)
          (probeOldContentAppendDot_supernatural D Sc m (i :: ν) i) N b w) =
      SVec.toLinearMap (gridUnitMatrixComponent T S (probeMatrixOrdinaryCross_supernatural D Sc m ν i)
          (probeOrdinaryAppendDot_supernatural D Sc m (i :: ν) i) O b ((U).obj w)) ∘ₗ
        (probeUnitMatrixFamilyLinearEquiv D Sc m ν i N hN b w).toLinearMap := by
  exact scalarColumns_square
    (fun a => (gridUnitMatrixFamily J (D.parity i) N b a).obj w)
    (fun a => (gridUnitMatrixFamily T (D.parity i) O b a).obj ((U).obj w))
    (((restriction K).obj (induced K N)).obj w)
    (((restriction S).obj (induced S O)).obj ((U).obj w))
    (probeUnitMatrixSlotLinearEquiv D Sc m ν i N hN b w)
    (probeMatrixTargetLinearEquiv D Sc m ν i N hN w).toLinearMap
    (fun a => (gridUnitMatrixEntry J K (probeMatrixOldCross_supernatural D Sc m ν i)
      (probeOldContentAppendDot_supernatural D Sc m (i :: ν) i) N b a).total w)
    (fun a => (gridUnitMatrixEntry T S (probeMatrixOrdinaryCross_supernatural D Sc m ν i)
      (probeOrdinaryAppendDot_supernatural D Sc m (i :: ν) i) O b a).total ((U).obj w))
    (probeMatrixCharts_unitEntry D Sc m ν i N hN b w)

/-- The entire prescribed finite cap matrix commutes with its genuine
selected E/F source chart and canonical target-family chart. -/
theorem probeMatrixCharts_capMatrix
    (b : ℕ) (w : ELVOld.OldContentCategory D Sc (probeCutoff D m) (i :: ν)) :
    (probeCapMatrixFamilyLinearEquiv D Sc m ν i N hN b w).toLinearMap ∘ₗ
        SVec.toLinearMap (gridCapMatrixComponent J K (probeMatrixOldCross_supernatural D Sc m ν i)
          (probeOldContentAppendDot_supernatural D Sc m ν i) N b w) =
      SVec.toLinearMap (gridCapMatrixComponent T S (probeMatrixOrdinaryCross_supernatural D Sc m ν i)
          (probeOrdinaryAppendDot_supernatural D Sc m ν i) O b ((U).obj w)) ∘ₗ
        (probeMatrixSourceLinearEquiv D Sc m ν i N hN w).toLinearMap := by
  exact scalarRows_square
    (fun a => (gridCapMatrixFamily K (D.parity i) N b a).obj w)
    (fun a => (gridCapMatrixFamily S (D.parity i) O b a).obj ((U).obj w))
    ((induced J ((restriction J).obj N)).obj w)
    ((induced T ((restriction T).obj O)).obj ((U).obj w))
    (probeCapMatrixSlotLinearEquiv D Sc m ν i N hN b w)
    (probeMatrixSourceLinearEquiv D Sc m ν i N hN w).toLinearMap
    (fun a => (gridCapMatrixEntry J K (probeMatrixOldCross_supernatural D Sc m ν i)
      (probeOldContentAppendDot_supernatural D Sc m ν i) N b a).total w)
    (fun a => (gridCapMatrixEntry T S (probeMatrixOrdinaryCross_supernatural D Sc m ν i)
      (probeOrdinaryAppendDot_supernatural D Sc m ν i) O b a).total ((U).obj w))
    (probeMatrixCharts_capEntry D Sc m ν i N hN b w)

end OddMath.QuiverHecke
