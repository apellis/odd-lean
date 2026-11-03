import OddMath.QuiverHecke.CyclotomicAction.ELVProbeCapUniqueness
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeRestrictionComparison

/-! # Uniqueness of native coefficient caps on scalar-evaluating probes

The same local inverse row comparison is required at F(E(T₀)), not only
at T₀, when the prescribed transpose in `SwappedActionAssembly.md` (A14)
is evaluated. The given unit-column inverse forces the coefficient cap
on every scalar-evaluating module at an output with absent moving colour.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction ELVOld.CyclotomicCrossingTensor
universe u

private theorem inverse_column
    {k V V' W W' : Type u} [CommRing k]
    [AddCommGroup V] [Module k V] [AddCommGroup V'] [Module k V']
    [AddCommGroup W] [Module k W] [AddCommGroup W'] [Module k W']
    (v : V ≃ₗ[k] V') (w : W ≃ₗ[k] W') (a : V →ₗ[k] W) (b : V' →ₗ[k] W')
    (h : w.toLinearMap ∘ₗ a = b ∘ₗ v.toLinearMap) :
    w.symm.toLinearMap ∘ₗ b = a ∘ₗ v.symm.toLinearMap := by
  apply LinearMap.ext
  intro x
  apply w.injective
  have hh := LinearMap.congr_fun h (v.symm x)
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using hh.symm

private theorem pullback_row_ext
    {k V V' W W' Z : Type u} [CommRing k]
    [AddCommGroup V] [Module k V] [AddCommGroup V'] [Module k V']
    [AddCommGroup W] [Module k W] [AddCommGroup W'] [Module k W']
    [AddCommGroup Z] [Module k Z]
    (v : V ≃ₗ[k] V') (w : W ≃ₗ[k] W') (a : ℕ → V →ₗ[k] W) (b : ℕ → V' →ₗ[k] W')
    (m : ℕ) (hcol : ∀ n, w.toLinearMap ∘ₗ a n = b n ∘ₗ v.toLinearMap)
    (hspan : ∀ f g : W' →ₗ[k] Z,
      (∀ n, n < m → f ∘ₗ b n = g ∘ₗ b n) → f = g)
    (f g : W →ₗ[k] Z) (h : ∀ n, n < m → f ∘ₗ a n = g ∘ₗ a n) : f = g := by
  have hfg := hspan (f ∘ₗ w.symm.toLinearMap) (g ∘ₗ w.symm.toLinearMap) (fun n hn => by
    rw [LinearMap.comp_assoc, LinearMap.comp_assoc, inverse_column v w (a n) (b n) (hcol n)]
    rw [← LinearMap.comp_assoc, ← LinearMap.comp_assoc, h n hn])
  apply LinearMap.ext
  intro x
  have hx := LinearMap.congr_fun hfg (w x)
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] using hx

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ) (γ : List I)
  (N : Superfunctor k (OldContentCategory D Sc (probeCutoff D m) γ) (SVec k))
  (hN : ProbeEvaluatesCoefficients D m Sc γ N) (i : I) (hi : i ∉ γ)
local notation "cut" => probeCutoff D m
local notation "K" => oldContentAppend D Sc cut γ i
local notation "T" => probeOrdinaryAppend D Sc m γ i
local notation "U" => probeOldOrdinaryFunctor D Sc m γ
local notation "O" => probeOrdinaryModuleSuperfunctor D Sc m γ N hN
local notation "count" => contentUnitCount D cut i (γ : Multiset I)
include hN

/-- The window on the actual given unit/dot columns uniquely determines
any native coefficient row in the scalar-evaluating class. This criterion
is intermediate: the local inverse equations supply its window premise. -/
theorem probeContentCoefficientCap_eq_of_window (r : Fin count)
    (f : (restriction K).obj ((induction K).obj N) ⟶ N)
    (hf : ∀ w a, a < count →
      SVec.toLinearMap (f.total w) ∘ₗ
        unitDotLinear K (probeOldContentAppendDot_supernatural D Sc m γ i) N a w =
      if a = r.val then LinearMap.id else 0) :
    f = contentCoefficientCap D Sc cut γ i N
      (contentCrossingHeight_nonneg_of_not_mem D cut γ i hi) r := by
  apply OddMath.FiniteSupermodule.hom_ext_total
  intro w
  suffices he : SVec.toLinearMap (f.total w) =
      SVec.toLinearMap ((contentCoefficientCap D Sc cut γ i N
        (contentCrossingHeight_nonneg_of_not_mem D cut γ i hi) r).total w) by
    exact congrArg SVec.ofHom he
  apply pullback_row_ext
    (probeOutputValueLinearEquiv D Sc m γ N hN w)
    (probeOutputFELinearEquiv D Sc m γ N hN i w)
    (fun a => unitDotLinear K (probeOldContentAppendDot_supernatural D Sc m γ i) N a w)
    (fun a => unitDotLinear T (probeOrdinaryAppendDot_supernatural D Sc m γ i) O a ((U).obj w))
    count
  · intro a
    exact probeOutputFELinearEquiv_unitDot D Sc m γ N hN i w a
  · intro g h hgh
    exact unitColumnMatrix_row_ext T (probeOrdinaryAppendDot_supernatural D Sc m γ i) O
      count ((U).obj w) (probeMissingColourUnitMatrixIso D Sc m γ N hN i hi w)
      (probeMissingColourUnitMatrixIso_hom D Sc m γ N hN i hi w) g h hgh
  · intro a ha
    exact (hf w a ha).trans (probeContentCoefficientCap_unitDot D Sc m γ N hN i hi w r a ha).symm

end OddMath.QuiverHecke
