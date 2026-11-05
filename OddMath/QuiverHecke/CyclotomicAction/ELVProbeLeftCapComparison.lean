import OddMath.QuiverHecke.CyclotomicAction.ELVProbeUnitInverseRows
import OddMath.QuiverHecke.CyclotomicAction.ELVContentCoefficientMaps

/-! # Prescribed left inverse-coefficient fields under scalar charts

The normalized left cap in DeformedMatrixComparison comes from the given
inverse unit matrix and its source unshift. This identifies the old side
of the scalar inverse-row comparison with the prescribed coefficient module
map; at genuine empty output it is the original moduleUnitCoefficient.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
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
end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor

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
open ELVOld ELVOld.BalancedInduction ELVOld.CyclotomicCrossingTensor
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
open ELVOld ELVOld.BalancedInduction ELVOld.CyclotomicCrossingTensor
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
