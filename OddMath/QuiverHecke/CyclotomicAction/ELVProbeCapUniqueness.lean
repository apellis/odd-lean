import OddMath.QuiverHecke.CyclotomicAction.ELVProbeCapModuleWindow
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeMissingColourMatrix

/-! # Uniqueness of the prescribed probe cap from its unit window

The local inverse row defining the left cap in `RouquierLeftCupCap`
extracts the right dotted unit columns. At the regular vacuum probe these
columns span, by the given unit matrix inverse. This is the uniqueness
input for comparing that local inverse row with the specified native cap;
it does not assume a left adjunction or a cap-identification premise.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped BigOperators
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u

private theorem assembled_row_ext {k : Type u} [CommRing k]
    {ι : Type} [Fintype ι] (V : ι → SVec k) (W : SVec k)
    {Z : Type u} [AddCommGroup Z] [Module k Z]
    (col : ∀ a, V a ⟶ W) (e : OddMath.FiniteSuperspace.product V ≅ W)
    (he : e.hom = OddMath.FiniteSuperspace.assembleColumns V W col)
    (f g : W →ₗ[k] Z) (h : ∀ a x, f (col a x) = g (col a x)) : f = g := by
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := (OddMath.FiniteSuperspace.isoLinearEquiv e).surjective x
  change f (e.hom y) = g (e.hom y)
  rw [he]
  change f (∑ a, col a (y a)) = g (∑ a, col a (y a))
  rw [map_sum, map_sum]
  exact Finset.sum_congr rfl (fun a _ => h a (y a))

section Generic
variable {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive A] [Linear k A] [Supercategory k A]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
  (M : Superfunctor k C (SVec k)) (m : ℕ) (w : C)
local instance capUniquenessPi : PiSupercategory k (Superfunctor k C (SVec k)) :=
  supermodulePiSupercategory

/-- A prescribed finite unit matrix forces uniqueness of every linear row
from its values on the unshifted dotted-unit columns. The matrix premise
is supplied by the existing concrete inverse in applications. -/
theorem unitColumnMatrix_row_ext
    (e : unitColumnSourceSpace p M m w ≅ ((restriction J).obj ((induction J).obj M)).obj w)
    (he : e.hom = unitColumnMatrix J hα M m w)
    {Z : Type u} [AddCommGroup Z] [Module k Z]
    (f g : ((restriction J).obj ((induction J).obj M)).obj w →ₗ[k] Z)
    (h : ∀ a, a < m → f ∘ₗ unitDotLinear J hα M a w =
      g ∘ₗ unitDotLinear J hα M a w) : f = g := by
  apply assembled_row_ext
    (fun r : Fin m => ((SKM.homParityShift (k := k) (r.val • p)).obj M).obj w)
    (((restriction J).obj ((induction J).obj M)).obj w)
    (fun r => (shiftedUnitDotColumn J hα M r.val).total w) e he
  intro r x
  have hr := LinearMap.congr_fun (h r.val r.isLt)
    (((SKM.homParityShiftDatum (k := k) (r.val • p)).iso M).hom.total w x)
  have hc := LinearMap.congr_fun (shiftedUnitDotColumn_total J hα M r.val w) x
  set_option backward.dsimp.instances true in
    dsimp only [shiftedUnitDotLinear, LinearMap.comp_apply, SVec.toLinearMap] at hc
  exact (congrArg f hc).trans (hr.trans (congrArg g hc).symm)
end Generic

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

private theorem module_column_equality
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
    (M : Superfunctor k C (SVec k)) (w : C) (a : ℕ)
    (f g : (restriction J).obj ((induction J).obj M) ⟶ M)
    (h : unitDotColumn J hα M a ≫ f = unitDotColumn J hα M a ≫ g) :
    SVec.toLinearMap (f.total w) ∘ₗ unitDotLinear J hα M a w =
      SVec.toLinearMap (g.total w) ∘ₗ unitDotLinear J hα M a w := by
  rw [← unitDotColumn_total]
  rw [← SVec.toLinearMap_comp, ← SVec.toLinearMap_comp,
    ← Superfunctor.comp_total, ← Superfunctor.comp_total, h]

end OddMath.QuiverHecke.ELVOld.BalancedInduction

namespace OddMath.QuiverHecke.ELVOld.ProbeVacuumCap
open BalancedInduction CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) [Fintype I] (m : I → ℕ)
local notation "cut" => probeCutoff D m
local notation "N" => probeOldVacuumRegular D Sc m
local notation "K" => oldContentAppend D Sc cut []
local notation "T" => probeOrdinaryAppend D Sc m []
local notation "U" => probeOldOrdinaryFunctor D Sc m []
local notation "M" => probeOrdinaryModuleSuperfunctor D Sc m [] N (probeOldModule_evaluatesCoefficients D m Sc [] _)

/-- On the original regular probe, any module row with the prescribed
finite unit/dot window is the given native cap. This intermediate criterion
will be supplied by the actual local augmented inverse's `gg` equations. -/
theorem cap_eq_of_unitDot_window (i : I) (hP : 0 < cut i)
    (f : source D Sc m i ⟶ N)
    (hf : ∀ a, a < cut i →
      unitDotColumn (K i) (probeOldContentAppendDot_supernatural D Sc m [] i) N a ≫ f =
        if a + 1 = cut i then 𝟙 N else 0) : f = cap D Sc m i hP := by
  apply OddMath.FiniteSupermodule.hom_ext_total
  intro w
  suffices he : SVec.toLinearMap (f.total w) = SVec.toLinearMap ((cap D Sc m i hP).total w) by
    exact congrArg SVec.ofHom he
  apply pullback_row_ext
    (probeOutputValueLinearEquiv D Sc m [] N (probeOldModule_evaluatesCoefficients D m Sc [] _) w)
    (probeOutputFELinearEquiv D Sc m [] N (probeOldModule_evaluatesCoefficients D m Sc [] _) i w)
    (fun a => unitDotLinear (K i) (probeOldContentAppendDot_supernatural D Sc m [] i) N a w)
    (fun a => unitDotLinear (T i) (probeOrdinaryAppendDot_supernatural D Sc m [] i) M a ((U).obj w))
    (cut i)
  · intro a
    exact probeOutputFELinearEquiv_unitDot D Sc m [] N
      (probeOldModule_evaluatesCoefficients D m Sc [] _) i w a
  · intro g h hgh
    apply unitColumnMatrix_row_ext (T i) (probeOrdinaryAppendDot_supernatural D Sc m [] i) M
      (contentUnitCount D cut i (([] : List I) : Multiset I)) ((U).obj w)
      (probeMissingColourUnitMatrixIso D Sc m [] N
        (probeOldModule_evaluatesCoefficients D m Sc [] _) i (by simp) w)
      (probeMissingColourUnitMatrixIso_hom D Sc m [] N
        (probeOldModule_evaluatesCoefficients D m Sc [] _) i (by simp) w) g h
    intro a ha
    rw [VacuumCoefficient.count] at ha
    exact hgh a ha
  · intro a ha
    exact module_column_equality (K i) (probeOldContentAppendDot_supernatural D Sc m [] i) N w a
      f (cap D Sc m i hP) ((hf a ha).trans (unitDotColumn_cap D Sc m i hP a ha).symm)

end OddMath.QuiverHecke.ELVOld.ProbeVacuumCap
