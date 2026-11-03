import OddMath.QuiverHecke.CyclotomicAction.ELVContentVacuumCapWindow
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeCapUniqueness

/-! # The finite unit decomposition on the old empty-content category

The empty boundary of the existing local-inverse construction is the
finite decomposition by prescribed unit columns and coefficient caps.
The given old global inverse supplies spanning over all old coefficients.
No scalar-evaluation condition or new Frobenius pairing is used.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped BigOperators
namespace OddMath.QuiverHecke.ELVOld
open BalancedInduction CyclotomicCrossingTensor
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

private theorem module_window
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {M S : Superfunctor k C (SVec k)} (a : M ⟶ S) (b : S ⟶ M)
    (q : Prop) [Decidable q]
    (h : ∀ w x, b.total w (a.total w x) = if q then x else 0) :
    a ≫ b = if q then 𝟙 M else 0 := by
  apply OddMath.FiniteSupermodule.hom_ext_total
  intro w
  rw [Superfunctor.comp_total]
  apply SVec.hom_ext
  intro x
  rw [SVec.comp_apply]
  by_cases hq : q
  · rw [ite_eq_left hq]
    have hi : (𝟙 M : M ⟶ M).total w = 𝟙 (M.obj w) := SuperNatTrans.id_total M.toFunctor w
    rw [hi, SVec.id_apply]
    simpa only [hq, ↓reduceIte] using h w x
  · rw [ite_eq_right hq]
    simpa only [hq, ↓reduceIte, SuperNatTrans.total, Superfunctor.zero_app, zero_add,
      SVec.zero_apply] using h w x

private theorem unit_component
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
    (M : Superfunctor k C (SVec k)) (n : ℕ) (w : C) (b : M.obj w) :
    (unitDotColumn J hα M n).total w b = unitDotLinear J hα M n w b :=
  LinearMap.congr_fun (unitDotColumn_total J hα M n w) b

private theorem column_point_equality
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
    (M T : Superfunctor k C (SVec k)) (w : C) (a : ℕ)
    (f g : (restriction J).obj ((induction J).obj M) ⟶ T)
    (h : unitDotColumn J hα M a ≫ f = unitDotColumn J hα M a ≫ g) :
    SVec.toLinearMap (f.total w) ∘ₗ unitDotLinear J hα M a w =
      SVec.toLinearMap (g.total w) ∘ₗ unitDotLinear J hα M a w := by
  rw [← unitDotColumn_total]
  rw [← SVec.toLinearMap_comp, ← SVec.toLinearMap_comp,
    ← Superfunctor.comp_total, ← Superfunctor.comp_total, h]

private theorem finite_total_on_column {C : Type*} [Category C] [Preadditive C]
    {M S : C} {n : ℕ} (u : Fin n → (M ⟶ S)) (v : Fin n → (S ⟶ M))
    (h : ∀ a r, u a ≫ v r = if a.val = r.val then 𝟙 M else 0) (a : Fin n) :
    u a ≫ (∑ r, v r ≫ u r) = u a := by
  classical
  rw [Preadditive.comp_sum, Finset.sum_eq_single a]
  · rw [← Category.assoc, h a a, ite_eq_left rfl, Category.id_comp]
  · intro r _ hra
    have hne : a.val ≠ r.val := fun hval => hra (Fin.ext hval).symm
    rw [← Category.assoc, h a r, ite_eq_right hne, Limits.zero_comp]
  · intro ha
    exact False.elim (ha (Finset.mem_univ a))

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (N : Superfunctor k (OldContentCategory D Sc cutoff []) (SVec k)) (i : I)
local notation "K" => oldContentAppend D Sc cutoff [] i
local notation "Q" => oldContentInclusion D Sc cutoff []
local notation "J" => append D Sc cutoff i
local notation "G" => induced Q N
local notation "count" => contentUnitCount D cutoff i (([] : List I) : Multiset I)

private theorem height : 0 ≤ contentCrossingHeight D cutoff i (([] : List I) : Multiset I) := by
  simp [contentCrossingHeight]

/-- The given old coefficient cap and unit columns have their Kronecker
window as module maps on every empty-content input module. -/
theorem contentVacuumCoefficientCap_unitDotColumn (r : Fin count) (a : ℕ) (ha : a < count) :
    unitDotColumn K (oldContentAppendDot_supernatural D Sc cutoff [] i) N a ≫
      contentCoefficientCap D Sc cutoff [] i N (height D cutoff i) r =
      if a = r.val then 𝟙 N else 0 := by
  classical
  apply module_window
  intro w b
  have hu := unit_component K (oldContentAppendDot_supernatural D Sc cutoff [] i) N a w b
  exact (congrArg ((contentCoefficientCap D Sc cutoff [] i N (height D cutoff i) r).total w) hu).trans
    (contentVacuumCoefficientCap_unitDot D Sc cutoff N i w r a ha b)

/-- The given old global unit inverse proves that native unit columns
jointly detect maps, without requiring scalar coefficient evaluation. -/
theorem contentVacuumUnitColumn_hom_ext
    (T : Superfunctor k (OldContentCategory D Sc cutoff []) (SVec k))
    (f g : (restriction K).obj ((induction K).obj N) ⟶ T)
    (h : ∀ a, a < count →
      unitDotColumn K (oldContentAppendDot_supernatural D Sc cutoff [] i) N a ≫ f =
      unitDotColumn K (oldContentAppendDot_supernatural D Sc cutoff [] i) N a ≫ g) : f = g := by
  apply OddMath.FiniteSupermodule.hom_ext_total
  intro w
  suffices he : SVec.toLinearMap (f.total w) = SVec.toLinearMap (g.total w) by
    exact congrArg SVec.ofHom he
  apply pullback_row_ext (oldContentValueChart D Sc cutoff [] N w)
    (oldContentFEChart D Sc cutoff [] i N w)
    (fun a => unitDotLinear K (oldContentAppendDot_supernatural D Sc cutoff [] i) N a w)
    (fun a => unitDotLinear J (oldAppendDot_supernatural D Sc cutoff i) G a w.obj) count
  · intro a
    apply LinearMap.ext
    intro b
    exact oldContentFEChart_unitDot D Sc cutoff [] i N w a b
  · intro g h hgh
    have he : (missingColourUnitMatrixIso D Sc cutoff [] i (by simp) N w).hom =
        unitColumnMatrix J (oldAppendDot_supernatural D Sc cutoff i) G count w.obj := by
      rw [missingColourUnitMatrixIso_hom]
      rfl
    exact unitColumnMatrix_row_ext J (oldAppendDot_supernatural D Sc cutoff i) G count w.obj
      (missingColourUnitMatrixIso D Sc cutoff [] i (by simp) N w) he g h hgh
  · intro a ha
    exact column_point_equality K (oldContentAppendDot_supernatural D Sc cutoff [] i) N T w a
      f g (h a ha)

/-- The prescribed caps and unit columns give the finite decomposition of
native F/E over the full old coefficient algebra, including count zero. -/
theorem contentVacuumCoefficientCap_total :
    (∑ r : Fin count, contentCoefficientCap D Sc cutoff [] i N (height D cutoff i) r ≫
      unitDotColumn K (oldContentAppendDot_supernatural D Sc cutoff [] i) N r.val) =
      𝟙 ((restriction K).obj ((induction K).obj N)) := by
  apply contentVacuumUnitColumn_hom_ext D Sc cutoff N i
  intro a ha
  rw [Category.comp_id]
  exact finite_total_on_column
    (fun r : Fin count => unitDotColumn K (oldContentAppendDot_supernatural D Sc cutoff [] i) N r.val)
    (fun r => contentCoefficientCap D Sc cutoff [] i N (height D cutoff i) r)
    (fun a r => contentVacuumCoefficientCap_unitDotColumn D Sc cutoff N i r a.val a.isLt) ⟨a, ha⟩

end OddMath.QuiverHecke.ELVOld
