import OddMath.QuiverHecke.CyclotomicAction.ELVContentUpperCharts
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeMatrixCharts

/-! # Scalar following E/F and value charts on arbitrary output content

The missing-colour case of DeformedMatrixComparison (4) has no predecessor
content. These are the selected invertible following E/F and value charts
for any output content, with every prescribed unscaled unit/dot column.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.ELVOld OddMath.QuiverHecke.ELVOld.BalancedInduction
namespace OddMath.QuiverHecke
universe u
section Generic
variable {k C A B : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
  (K : A ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
private theorem matrixUnit_endpoint_refl {p : ZMod 2}
    {β : ∀ s, K.obj s ⟶ K.obj s} (hβ : IsSupernatural k p β)
    (N : Superfunctor k A (SVec k)) (n : ℕ) (w : A) :
    endpointUnitDotLinear K hβ N n w (K.obj w) rfl = unitDotLinear K hβ N n w := by
  apply LinearMap.ext
  intro b
  exact (endpointUnitDotLinear_refl_apply K hβ N n w b).trans
    (unitDotLinear_apply K hβ N n w b).symm

end Generic
private theorem matrixUnit_plain_reencode
    {k V W Y : Type u} [CommRing k]
    [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]
    [AddCommMonoid Y] [Module k Y]
    (c c₀ : W →ₗ[k] Y) (f : V →ₗ[k] W) (g g₀ : V →ₗ[k] Y) (v : V →ₗ[k] V)
    (hc : c = c₀) (hg : g₀ = g) (hv : ∀ b, v b = b) (h : c₀ ∘ₗ f = g₀) :
    c ∘ₗ f = g ∘ₗ v := by
  rw [hc]
  apply LinearMap.ext
  intro b
  exact (LinearMap.congr_fun h b).trans
    ((LinearMap.congr_fun hg b).trans (congrArg g (hv b)).symm)

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ) (γ : List I)
  (N : Superfunctor k (OldContentCategory D Sc (probeCutoff D m) γ) (SVec k))
  (hN : ProbeEvaluatesCoefficients D m Sc γ N)
local notation "U" => probeOldOrdinaryFunctor D Sc m γ
local notation "O" => probeOrdinaryModuleSuperfunctor D Sc m γ N hN
local notation "e" => eqToIso (probeOrdinaryModuleSuperfunctor_restrict D Sc m γ N hN)

/-- The scalar value chart on arbitrary output content. -/
def probeOutputValueLinearEquiv (w : OldContentCategory D Sc (probeCutoff D m) γ) :
    N.obj w ≃ₗ[k] (O).obj ((U).obj w) := (moduleIsoLinearEquiv e w).symm

theorem probeOutputValueLinearEquiv_symm_apply
    (w : OldContentCategory D Sc (probeCutoff D m) γ) (b : (O).obj ((U).obj w)) :
    (probeOutputValueLinearEquiv D Sc m γ N hN w).symm b = b := by
  change SVec.toLinearMap ((e).hom.total w) b = b
  simp only [SuperNatTrans.total, probeRestrictionEqToIso_hom_app,
    ↓reduceIte, one_ne_zero, add_zero, SVec.toLinearMap]
  rfl

theorem probeOutputValueLinearEquiv_apply
    (w : OldContentCategory D Sc (probeCutoff D m) γ) (b : N.obj w) :
    probeOutputValueLinearEquiv D Sc m γ N hN w b = b := by
  have h := (probeOutputValueLinearEquiv D Sc m γ N hN w).apply_symm_apply b
  have hv := probeOutputValueLinearEquiv_symm_apply D Sc m γ N hN w b
  exact (congrArg (probeOutputValueLinearEquiv D Sc m γ N hN w) hv).symm.trans h

variable (i : I)
local notation "K" => oldContentAppend D Sc (probeCutoff D m) γ i
local notation "S" => probeOrdinaryAppend D Sc m γ i

/-- The following F/E chart uses the same selected append isomorphism. -/
abbrev probeOutputFELinearEquiv (w : OldContentCategory D Sc (probeCutoff D m) γ) :=
  probeAppendLinearEquiv D Sc m γ N hN i ((K).obj w)

theorem probeOutputFELinearEquiv_hom (w : OldContentCategory D Sc (probeCutoff D m) γ) :
    (probeOutputFELinearEquiv D Sc m γ N hN i w).toLinearMap =
      probeAppendComparisonLinear D Sc m γ N hN i ((K).obj w) := rfl

/-- Every unit/dot column uses the selected scalar following and value charts,
without requiring any occurrence of i in the output content. -/
theorem probeOutputFELinearEquiv_unitDot
    (w : OldContentCategory D Sc (probeCutoff D m) γ) (n : ℕ) :
    (probeOutputFELinearEquiv D Sc m γ N hN i w).toLinearMap ∘ₗ
        unitDotLinear K (probeOldContentAppendDot_supernatural D Sc m γ i) N n w =
      unitDotLinear S (probeOrdinaryAppendDot_supernatural D Sc m γ i) O n ((U).obj w) ∘ₗ
        (probeOutputValueLinearEquiv D Sc m γ N hN w).toLinearMap := by
  have h := probeAppendComparisonLinear_unitDotColumn D Sc m γ N hN i w n
  have hEnd := matrixUnit_endpoint_refl S (probeOrdinaryAppendDot_supernatural D Sc m γ i)
    O n ((U).obj w)
  exact matrixUnit_plain_reencode _ _ _ _ _ _
    (probeOutputFELinearEquiv_hom D Sc m γ N hN i w) hEnd
    (probeOutputValueLinearEquiv_apply D Sc m γ N hN w) h

end OddMath.QuiverHecke
