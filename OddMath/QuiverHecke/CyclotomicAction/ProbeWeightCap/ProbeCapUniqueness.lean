import Mathlib.CategoryTheory.Conj
import OddMath.QuiverHecke.CyclotomicAction.ProbeReindexWeight.ProbeWeightUnitCoordinates
import OddMath.QuiverHecke.CyclotomicAction.ProbeWeightBraid.ProbeWeightCrossCoordinates
import OddMath.QuiverHecke.SwappedAssembly.Sigma.DistinctPureEntries
import OddMath.QuiverHecke.SwappedAssembly.Sigma.DistinctPureReservoirEntry
import OddMath.QuiverHecke.SwappedAssembly.Sigma.MixedEntryPureNilpotent
import OddMath.QuiverHecke.SwappedAssembly.Sigma.PaddedBendWindowEquations
import OddMath.QuiverHecke.SwappedAssembly.Sigma.Permutation
import OddMath.QuiverHecke.SwappedAssembly.Sigma.SwappingReservoir
import OddMath.SKM.RouquierCanonicalDistinctLeftMate

/-!
# Probe weight cap

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

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
namespace OddMath.QuiverHecke.ELV.BalancedInduction
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

end OddMath.QuiverHecke.ELV.BalancedInduction

namespace OddMath.QuiverHecke.ELV.ProbeVacuumCap
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

end OddMath.QuiverHecke.ELV.ProbeVacuumCap
end

end

section

/-! # The stored probe cap in the full OLD coefficient coordinates

SwappedActionAssembly F2: the missing-colour inverse cap is the
prescribed boundary coefficient, transported through the even upper-loop
chart. All module components and full OLD coefficients are retained.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELV ELV.BalancedInduction ELV.CyclotomicCrossingTensor CyclotomicAction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (γ : List I) (i : I) {μ : List I} (h : (i :: γ).Perm μ) (hi : i ∉ γ)
local notation "count" => contentUnitCount D (probeCutoff D m) i (γ : Multiset I)
local notation "L" => probeMissingStoredLoc D Sc m γ i h hi
local notation "V" => probeMissingStoredCoefficients D Sc m γ i h hi

/-- The raw stored local cap is the top boundary coefficient, with no
normalization scalar inserted. -/
theorem probeMissingStoredLoc_cap_eq (hn : 0 < count) : (L).capL = (V).cap := by
  have hcount : (count : ℤ) = contentCrossingHeight D (probeCutoff D m) i (γ : Multiset I) :=
    contentUnitCount_cast D (probeCutoff D m) i (γ : Multiset I)
      (contentCrossingHeight_nonneg_of_not_mem D (probeCutoff D m) γ i hi)
  apply (V).hom_ext
  intro n hnc
  have hh : -contentCrossingHeight D (probeCutoff D m) i (γ : Multiset I) < 0 := by omega
  have hw := (L).cupD_capL hh (n := n) (by omega)
  have he : (- -contentCrossingHeight D (probeCutoff D m) i (γ : Multiset I) - 1).toNat = count - 1 := by omega
  calc
    _ = if n = count - 1 then 𝟙 _ else 0 := by
      simpa only [he, SKM.SuperRouquierLoc.cupD, SKM.RouquierBoundary.cup] using hw
    _ = _ := ((V).cup_cap hn hnc).symm

/-- The explicit selected upper-loop chart transports the stored cap to
the un-reindexed evaluated OLD boundary cap. -/
theorem probeMissingStoredLoc_cap_chart (hn : 0 < count) :
    (L).capL = (probeAppendUpperLoopSuperIso D Sc m γ i h).inv ≫
      (probeEvaluatedMissingCoefficients D Sc m γ i hi).cap := by
  rw [probeMissingStoredLoc_cap_eq D Sc m γ i h hi hn]
  simp only [SKM.RouquierBoundary.Coefficients.cap, hn, ite_true]
  rfl

/-- On the original regular probe, the full OLD boundary cap is precisely
its prescribed native vacuum cap. The finite moments are proved from the
constructed boundary inverse. -/
theorem probeMissingBoundary_regular_cap [Fintype I]
    (hP : 0 < probeCutoff D m i) :
    (contentMissingBoundaryCoefficients D Sc (probeCutoff D m) [] i (by simp)).cap.total
      (probeOldVacuumRegular D Sc m) = ProbeVacuumCap.cap D Sc m i hP := by
  apply ProbeVacuumCap.cap_eq_of_unitDot_window D Sc m i hP
  intro a ha
  let W := contentMissingBoundaryCoefficients D Sc (probeCutoff D m) [] i (by simp)
  have hp : 0 < contentUnitCount D (probeCutoff D m) i (([] : List I) : Multiset I) := by
    simpa only [VacuumCoefficient.count] using hP
  have hw := W.cup_cap hp (j := a) (by simpa only [VacuumCoefficient.count] using ha)
  have ht := congrArg (fun η => η.total (probeOldVacuumRegular D Sc m)) hw
  rw [Superfunctor.comp_total] at ht
  have hu : (SKM.RouquierBoundary.cup
      (inductionModuleAdjunction (k := k) (oldContentAppend D Sc (probeCutoff D m) [] i))
      (inductionModuleDot (oldContentAppend D Sc (probeCutoff D m) [] i)
        (oldContentAppendDot_supernatural D Sc (probeCutoff D m) [] i)) a).total
          (probeOldVacuumRegular D Sc m) =
      unitDotColumn (oldContentAppend D Sc (probeCutoff D m) [] i)
        (probeOldContentAppendDot_supernatural D Sc m [] i) (probeOldVacuumRegular D Sc m) a := by
    rw [inductionModuleUnitPower_eq, gridUnitColumnTransformation_total]
  rw [hu] at ht
  by_cases he : a + 1 = probeCutoff D m i
  · have he' : a = contentUnitCount D (probeCutoff D m) i (([] : List I) : Multiset I) - 1 := by
      rw [VacuumCoefficient.count]; omega
    rw [ite_eq_left he'] at ht
    exact (ht.trans (SuperNatTrans.id_total
      (𝟭 (Superfunctor k (OldContentCategory D Sc (probeCutoff D m) []) (SVec k)))
      (probeOldVacuumRegular D Sc m))).trans (ite_eq_left he).symm
  · have he' : a ≠ contentUnitCount D (probeCutoff D m) i (([] : List I) : Multiset I) - 1 := by
      rw [VacuumCoefficient.count]; omega
    rw [ite_eq_right he'] at ht
    simpa only [SuperNatTrans.total, Superfunctor.zero_app, zero_add, ite_eq_right he] using ht

end OddMath.QuiverHecke
end

end

section

/-! # The raw restricted probe dot in the successor source chart

SwappedActionAssembly F2 and SwappedVacuumNonpositiveBubbles §1 (2):
the raw probe dot on the upper loop follows the same selected successor
chart as the whole-weight left cap, at every input weight module.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELV CyclotomicAction
universe u

private theorem rightWhisker_total
    {k : Type u} [CommRing k] {A B C : PiSCat.{u,u,u+1} k}
    {F G : A ⟶ B} (f : F ⟶ G) (Z : B ⟶ C) (N : A) :
    (f ▷ Z).total N = Z.map (f.total N) := by
  change Z.map (f.app 0 N) + Z.map (f.app 1 N) = Z.map (f.app 0 N + f.app 1 N)
  exact (Functor.map_add Z.toFunctor).symm

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (i : I) (Λ : X) {x y : X} (h : x + D.α i = y)
  (δ : WeightBlocks D Λ x) (M : ProbeOldWeightProduct D Sc m Λ x)
local notation "ε" => blockSucc D Λ i h δ
local notation "perm" => probeOldBlockTarget_perm D i Λ h δ ε rfl
local notation "R" => probeOldBlockRes D Sc m i Λ h δ

/-- The raw upper-loop dot commutes with the selected successor source
chart, without a moment hypothesis or a choice of inverse dot. -/
theorem probeOldWeightFollowing_dot :
    ((probeOldActionDot D Sc m i Λ h ▷ probeOldF D Sc m i Λ h).total M) δ ≫
      eqToHom (probeOldWeightFollowing_obj D Sc m i Λ h δ M) =
    eqToHom (probeOldWeightFollowing_obj D Sc m i Λ h δ M) ≫
      (R).map (probeAppendToDotComponent D Sc m δ.1.toList i ε.1.toList perm (M δ)) := by
  rw [rightWhisker_total, probeOldWeightFollowing_eqToHom]
  change (R).map ((probeOldActionDot D Sc m i Λ h).total M ε) ≫ _ = _
  rw [probeOldActionDot_via_total D Sc m i Λ h δ ε rfl M]
  simp only [Category.assoc, ← Functor.map_comp,
    eqToHom_trans, eqToHom_refl, Category.comp_id]

end OddMath.QuiverHecke
end

end

section

/-! # Restricted probe dots through the upper-loop chart

SwappedActionAssembly F2 and SwappedVacuumNonpositiveBubbles §1 (2):
the same OLD append comparison used for the cap source preserves the
raw restricted induction dot at every input module.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
open ELV ELV.BalancedInduction ELV.CyclotomicCrossingTensor
universe u
attribute [local irreducible] oldAppendReindexIso
private theorem restriction_total
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (Q : C ⥤ A) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q]
    {M N : Superfunctor k A (SVec k)} (f : M ⟶ N) (w : C) :
    ((restriction Q).map f).total w = f.total (Q.obj w) := rfl

private theorem transform_total
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    {J : C ⥤ A} [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    {p : ZMod 2} {α : ∀ v, J.obj v ⟶ J.obj v} (hα : IsSupernatural k p α)
    (N : Superfunctor k C (SVec k)) (w : A) :
    (transformComponent hα N).total w = transformLinear hα N w := by
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    simp only [SuperNatTrans.total, transformComponent_app,
      ite_true, ite_false, zero_ne_one, one_ne_zero, add_zero, zero_add]

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (γ : List I) (i : I) {μ : List I} (h : (i :: γ).Perm μ)
local notation "cut" => probeCutoff D m
local notation "K₀" => oldContentAppendTo D Sc cut γ i (i :: γ) (List.Perm.refl _)
local notation "K" => oldContentAppendTo D Sc cut γ i μ h
local notation "e" => oldAppendReindexIso D Sc cut (List.Perm.refl γ) i
  (List.Perm.refl (i :: γ)) h h

/-- The actual restricted signed dots commute with the selected even
upper-loop comparison before choosing the original regular probe. -/
theorem oldAppendUpperLoop_dot
    (N : Superfunctor k (OldContentCategory D Sc cut γ) (SVec k)) :
    restrictedDotEnd K₀
      (probeAppendToDot_supernatural D Sc m γ i (i :: γ) (List.Perm.refl _)) N ≫
        (restriction K).map ((e).hom.app N) =
      (restriction K).map ((e).hom.app N) ≫
        restrictedDotEnd K (probeAppendToDot_supernatural D Sc m γ i μ h) N := by
  have hd := oldAppendReindexIso_dot D Sc m (List.Perm.refl γ) i
    (List.Perm.refl (i :: γ)) h h N
  have hm := congrArg (restriction K).map hd
  apply HomogeneousSuperfunctorIso.total_ext
  intro w
  have hw := congrArg (fun f => f.total w) hm
  simp only [restrictedDotEnd, Functor.mapEnd_apply, dotEnd, Functor.map_comp,
    Superfunctor.comp_total, restriction_total, transform_total] at hw ⊢
  convert hw using 1 <;> rfl

end OddMath.QuiverHecke
end

end
