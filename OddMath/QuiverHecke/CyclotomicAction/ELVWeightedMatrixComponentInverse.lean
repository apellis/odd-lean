import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedFiniteMatrixComparison
import Mathlib.CategoryTheory.Comma.Arrow

/-! # Inverses of the prescribed weighted matrix components

DeformedMatrixComparison (2), (4): the given old matrix inverse and the
selected genuine chart squares make the prescribed weighted forward maps
bijective. The resulting isomorphisms use those exact forward maps.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open CyclotomicCrossingTensor BalancedInduction
universe u

private def svecIsoEquiv {k : Type u} [CommRing k] {V W : SVec k} (e : V ≅ W) : V ≃ₗ[k] W where
  toLinearMap := e.hom
  invFun := e.inv
  left_inv x := congrArg (fun f : V ⟶ V => f x) e.hom_inv_id
  right_inv x := congrArg (fun f : W ⟶ W => f x) e.inv_hom_id
private theorem iso_hom_bijective {k : Type u} [CommRing k] {V W : SVec k} (e : V ≅ W) :
    Function.Bijective e.hom := (svecIsoEquiv e).bijective
private theorem equiv_hom_bijective {k V W : Type u} [CommRing k]
    [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W] (e : V ≃ₗ[k] W) :
    Function.Bijective e.toLinearMap := e.bijective

private theorem bijective_square {k V W X Y : Type u} [CommRing k]
    [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]
    [AddCommMonoid X] [Module k X] [AddCommMonoid Y] [Module k Y]
    (c : W →ₗ[k] Y) (f : V →ₗ[k] W) (g : X →ₗ[k] Y) (d : V →ₗ[k] X)
    (hc : Function.Bijective c) (hf : Function.Bijective f) (hd : Function.Bijective d)
    (h : c ∘ₗ f = g ∘ₗ d) : Function.Bijective g := by
  constructor
  · intro x y hxy
    obtain ⟨v, hv⟩ := hd.surjective x
    obtain ⟨w, hw⟩ := hd.surjective y
    have hmid : g (d v) = g (d w) := by
      simpa only [hv, hw] using hxy
    have hh : c (f v) = c (f w) :=
      (LinearMap.congr_fun h v).trans (hmid.trans (LinearMap.congr_fun h w).symm)
    exact hv.symm.trans ((congrArg d (hf.injective (hc.injective hh))).trans hw)
  · intro y
    obtain ⟨w, hw⟩ := hc.surjective y
    obtain ⟨v, hv⟩ := hf.surjective w
    exact ⟨d v, (LinearMap.congr_fun h v).symm.trans ((congrArg c hv).trans hw)⟩

private def isoOfBijectiveMap {k : Type u} [CommRing k] {V W : SVec k} (f : V ⟶ W)
    (hf : Function.Bijective f) : V ≅ W := SVec.isoOfLinearEquiv (LinearEquiv.ofBijective f hf)

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ) (i : I)
local notation "Q" => oldTruncateFunctor D Sc cutoff N

private theorem oldUnit_bijective (P : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (w : OldCategory D Sc cutoff) (hh : 0 ≤ contentCrossingHeight D cutoff i (w.word : Multiset I)) :
    Function.Bijective (unitMatrixComponent D Sc cutoff i P
      (contentUnitCount D cutoff i (w.word : Multiset I)) w) := by
  rw [← TensorMatrixCoordinates.moduleUnitMatrixIso_hom D Sc cutoff P i w hh]
  exact iso_hom_bijective (TensorMatrixCoordinates.moduleUnitMatrixIso D Sc cutoff P i w hh)
private theorem oldCap_bijective (P : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (w : OldCategory D Sc cutoff) (hh : contentCrossingHeight D cutoff i (w.word : Multiset I) ≤ 0) :
    Function.Bijective (capMatrixComponent D Sc cutoff i P
      (contentCapCount D cutoff i (w.word : Multiset I)) w) := by
  rw [← TensorMatrixCoordinates.moduleCapMatrixIso_hom D Sc cutoff P i w hh]
  exact iso_hom_bijective (TensorMatrixCoordinates.moduleCapMatrixIso D Sc cutoff P i w hh)

variable (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))
local notation "RM" => weightedRestriction D Sc cutoff N M

/-- The actual weighted unit matrix is bijective at its prescribed nonnegative-height size. -/
theorem weightedUnitMatrixComponent_bijective (w : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (w.word : Multiset I)) :
    Function.Bijective (weightedUnitMatrixComponent D Sc cutoff N i M
      (contentUnitCount D cutoff i (w.word : Multiset I)) ((Q).obj w)) := by
  exact bijective_square _ _ _ _
    (equiv_hom_bijective (weightedMateTargetLinearEquiv D Sc cutoff N i M w))
    (oldUnit_bijective D Sc cutoff i RM w hh)
    (equiv_hom_bijective (weightedUnitMatrixValueEquiv D Sc cutoff N i M _ w))
    (weightedMatrixCharts_unitMatrix D Sc cutoff N i M _ w)

/-- The actual weighted cap matrix is bijective at its prescribed nonpositive-height size. -/
theorem weightedCapMatrixComponent_bijective (w : OldCategory D Sc cutoff)
    (hh : contentCrossingHeight D cutoff i (w.word : Multiset I) ≤ 0) :
    Function.Bijective (weightedCapMatrixComponent D Sc cutoff N i M
      (contentCapCount D cutoff i (w.word : Multiset I)) ((Q).obj w)) := by
  exact bijective_square _ _ _ _
    (equiv_hom_bijective (weightedCapMatrixValueEquiv D Sc cutoff N i M _ w))
    (oldCap_bijective D Sc cutoff i RM w hh)
    (equiv_hom_bijective (weightedMateSourceLinearEquiv D Sc cutoff N i M w))
    (weightedMatrixCharts_capMatrix D Sc cutoff N i M _ w)

/-- The given unit forward map, with its actual domain and codomain retained. -/
def weightedUnitMatrixArrow (m : ℕ) (w : TruncatedCategory D Sc cutoff N) : Arrow (SVec k) :=
  Arrow.mk (weightedUnitMatrixComponent D Sc cutoff N i M m w)
/-- The given cap forward map, with its actual domain and codomain retained. -/
def weightedCapMatrixArrow (m : ℕ) (w : TruncatedCategory D Sc cutoff N) : Arrow (SVec k) :=
  Arrow.mk (weightedCapMatrixComponent D Sc cutoff N i M m w)

/-- An inverse for the exact prescribed weighted unit forward matrix. -/
def weightedUnitMatrixComponentIso (w : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (w.word : Multiset I)) :
    (weightedUnitMatrixArrow D Sc cutoff N i M (contentUnitCount D cutoff i (w.word : Multiset I)) ((Q).obj w)).left ≅
      (weightedUnitMatrixArrow D Sc cutoff N i M (contentUnitCount D cutoff i (w.word : Multiset I)) ((Q).obj w)).right :=
  isoOfBijectiveMap (weightedUnitMatrixComponent D Sc cutoff N i M
    (contentUnitCount D cutoff i (w.word : Multiset I)) ((Q).obj w))
      (weightedUnitMatrixComponent_bijective D Sc cutoff N i M w hh)

/-- An inverse for the exact prescribed weighted cap forward matrix. -/
def weightedCapMatrixComponentIso (w : OldCategory D Sc cutoff)
    (hh : contentCrossingHeight D cutoff i (w.word : Multiset I) ≤ 0) :
    (weightedCapMatrixArrow D Sc cutoff N i M (contentCapCount D cutoff i (w.word : Multiset I)) ((Q).obj w)).left ≅
      (weightedCapMatrixArrow D Sc cutoff N i M (contentCapCount D cutoff i (w.word : Multiset I)) ((Q).obj w)).right :=
  isoOfBijectiveMap (weightedCapMatrixComponent D Sc cutoff N i M
    (contentCapCount D cutoff i (w.word : Multiset I)) ((Q).obj w))
      (weightedCapMatrixComponent_bijective D Sc cutoff N i M w hh)

theorem weightedUnitMatrixComponentIso_hom (w : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (w.word : Multiset I)) :
    (weightedUnitMatrixComponentIso D Sc cutoff N i M w hh).hom =
      weightedUnitMatrixComponent D Sc cutoff N i M
        (contentUnitCount D cutoff i (w.word : Multiset I)) ((Q).obj w) := rfl

theorem weightedCapMatrixComponentIso_hom (w : OldCategory D Sc cutoff)
    (hh : contentCrossingHeight D cutoff i (w.word : Multiset I) ≤ 0) :
    (weightedCapMatrixComponentIso D Sc cutoff N i M w hh).hom =
      weightedCapMatrixComponent D Sc cutoff N i M
        (contentCapCount D cutoff i (w.word : Multiset I)) ((Q).obj w) := rfl

end OddMath.QuiverHecke.ELVOld
