import OddMath.QuiverHecke.CyclotomicAction.ELVFullInductionSquareRows
import OddMath.Algebra.HomogeneousSuperfunctorIso

/-! # The ordinary counit through a full-inclusion source chart

Brundan–Ellis (1.13)–(1.14): retain the specified ordinary counit and
chosen restriction chart. The input module is independent until the
zeroth-component transpose is specialized to the identity map.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
private theorem coend_ext
    {k C A V : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive A] [Linear k A] [AddCommMonoid V] [Module k V]
    (J : C ⥤ A) (R : C ⥤ SVec k) {w : A}
    {f g : Obj J R w →ₗ[k] V}
    (h : ∀ s (a : J.obj s ⟶ w) (b : R.obj s), f (tensor J R s a b) = g (tensor J R s a b)) : f = g := by
  classical
  apply LinearMap.cancel_right (Submodule.mkQ_surjective (relations J R w)) |>.mp
  apply DirectSum.linearMap_ext
  intro s
  apply TensorProduct.ext
  ext a b
  exact h s a b

section Transpose
variable {k C A : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (R : Superfunctor k C (SVec k)) (M : Superfunctor k A (SVec k))

/-- Transpose of the zeroth component, with independent input module. -/
def evenTransposeLinear (c : R ⟶ (restriction J).obj M) (w : A) :
    Obj J R.toFunctor w →ₗ[k] M.obj w :=
  restrictionCounitLinear J M w ∘ₗ mapComponent J c 0 w

theorem evenTransposeLinear_tensor (c : R ⟶ (restriction J).obj M)
    (s : C) (w : A) (g : J.obj s ⟶ w) (b : R.obj s) :
    evenTransposeLinear J R M c w (tensor J R.toFunctor s g b) = M.map g (c.app 0 s b) := by
  rw [evenTransposeLinear, LinearMap.comp_apply, mapComponent_tensor, twist_zero]
  exact restrictionCounitLinear_tensor J M s w g (c.app 0 s b)

/-- Specializing the independent input map to the identity recovers the given counit. -/
theorem evenTransposeLinear_id (w : A) :
    evenTransposeLinear J ((restriction J).obj M) M (𝟙 _) w = restrictionCounitLinear J M w := by
  apply coend_ext _ _
  intro s g b
  have h := evenTransposeLinear_tensor J ((restriction J).obj M) M (𝟙 _) s w g b
  have hi : (𝟙 ((restriction J).obj M) : _ ⟶ _).app 0 s b = b := rfl
  exact (h.trans (congrArg (M.map g) hi)).trans (restrictionCounitLinear_tensor J M s w g b).symm

end Transpose

private theorem evenMap_value_naturality
    {k A B : Type u} [CommRing k]
    [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
    [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
    (U : A ⥤ B) [U.Additive] [U.Linear k] [IsSuperfunctor k U]
    (M : Superfunctor k A (SVec k)) (P : Superfunctor k B (SVec k))
    (a : M ⟶ (restriction U).obj P) (ha : a ∈ parity (R := k) _ _ 0)
    (s w : A) (g : s ⟶ w) (b : M.obj s) :
    a.total w (M.map g b) = P.map (U.map g) (a.total s b) := by
  rw [HomogeneousSuperfunctorIso.total_eq_app a ha w, HomogeneousSuperfunctorIso.total_eq_app a ha s]
  exact congrArg (fun f : M.obj s ⟶ ((restriction U).obj P).obj w => f b)
    (a.toNatTrans.naturality g)

private theorem module_map_comp_value
    {k B : Type u} [CommRing k] [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
    (P : Superfunctor k B (SVec k)) {s w z : B} (g : s ⟶ w) (h : w ⟶ z) (b : P.obj s) :
    P.map h (P.map g b) = P.map (g ≫ h) b :=
  (congrArg (fun f : P.obj s ⟶ P.obj z => f b) (P.toFunctor.map_comp g h)).symm

variable {k C A B : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (U : A ⥤ B) [U.Additive] [U.Linear k] [IsSuperfunctor k U] [U.Full] [U.Faithful]
  (Q : C ⥤ B) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q]
  (T : B ⥤ B) [T.Additive] [T.Linear k] [IsSuperfunctor k T]
  (h : J ⋙ U = Q ⋙ T)
  (R : Superfunctor k C (SVec k)) (M : Superfunctor k A (SVec k)) (P : Superfunctor k B (SVec k))
  (c : R ⟶ (restriction J).obj M)
  (a : M ⟶ (restriction U).obj P) (ha : a ∈ parity (R := k) _ _ 0)
  (e : induced Q R ≅ (restriction T).obj P) (he : e.hom ∈ parity (R := k) _ _ 0)

include ha he in
/-- The selected source chart transports the prescribed ordinary counit.
Its unit condition is verified for the canonical full-content restriction chart. -/
theorem fullSquareOrdinarySourceLinear_counit
    (hUnit : ∀ s (b : R.obj s), e.hom.total (Q.obj s) (unit Q R.toFunctor s b) =
      P.map (eqToHom (congrArg (fun F : C ⥤ B => F.obj s) h)) (a.total (J.obj s) (c.app 0 s b))) (w : A) :
    a.total w ∘ₗ evenTransposeLinear J R M c w =
      counit T P.toFunctor (U.obj w) ∘ₗ fullSquareOrdinarySourceLinear J U Q T h R T P e w := by
  apply coend_ext _ _
  intro s g b
  have hL := congrArg (a.total w) (evenTransposeLinear_tensor J R M c s w g b)
  have hN := evenMap_value_naturality U M P a ha (J.obj s) w g (c.app 0 s b)
  have hS := fullSquareOrdinarySourceLinear_tensor_of_image J U Q T h R T P e he s w g b
    (P.map (eqToHom (congrArg (fun F : C ⥤ B => F.obj s) h)) (a.total (J.obj s) (c.app 0 s b))) (hUnit s b)
  have hR := congrArg (counit T P.toFunctor (U.obj w)) hS
  have hEval := counit_tensor T P.toFunctor (U.obj w) (Q.obj s)
    (eqToHom (congrArg (fun F : C ⥤ B => F.obj s) h).symm ≫ U.map g)
    (P.map (eqToHom (congrArg (fun F : C ⥤ B => F.obj s) h)) (a.total (J.obj s) (c.app 0 s b)))
  have hComp := module_map_comp_value P (eqToHom (congrArg (fun F : C ⥤ B => F.obj s) h))
    (eqToHom (congrArg (fun F : C ⥤ B => F.obj s) h).symm ≫ U.map g) (a.total (J.obj s) (c.app 0 s b))
  have hCoef : eqToHom (congrArg (fun F : C ⥤ B => F.obj s) h) ≫
      (eqToHom (congrArg (fun F : C ⥤ B => F.obj s) h).symm ≫ U.map g) = U.map g := by simp
  have hCancel := congrArg (fun v => P.map v (a.total (J.obj s) (c.app 0 s b))) hCoef
  exact (hL.trans hN).trans (hR.trans (hEval.trans (hComp.trans hCancel))).symm

/-- The selected ordinary source chart commutes with the literal local and
ambient counits after the canonical input inclusion unit. -/
theorem fullSquareOrdinarySourceLinear_counit_unit
    (a : induced Q ((restriction J).obj M) ≅ (restriction T).obj (induced U M))
    (ha : a.hom ∈ parity (R := k) _ _ 0)
    (hUnit : ∀ s (b : M.obj (J.obj s)),
      a.hom.total (Q.obj s) (unit Q ((restriction J).obj M).toFunctor s b) =
        (induced U M).map (eqToHom (congrArg (fun F : C ⥤ B => F.obj s) h))
          (unit U M.toFunctor (J.obj s) b))
    (w : A) (x : Obj J ((restriction J).obj M).toFunctor w) :
    unit U M.toFunctor w (restrictionCounitLinear J M w x) =
      counit T (induced U M).toFunctor (U.obj w)
        (fullSquareOrdinarySourceLinear J U Q T h ((restriction J).obj M) T (induced U M) a w x) := by
  have hCompat : ∀ s (b : ((restriction J).obj M).obj s),
      a.hom.total (Q.obj s) (unit Q ((restriction J).obj M).toFunctor s b) =
        (induced U M).map (eqToHom (congrArg (fun F : C ⥤ B => F.obj s) h))
          (((adjunctionUnit U).app M).total (J.obj s) ((𝟙 ((restriction J).obj M) : _ ⟶ _).app 0 s b)) := by
    intro s b
    have hU := unit_total_apply U M (J.obj s) b
    have hi : (𝟙 ((restriction J).obj M) : _ ⟶ _).app 0 s b = b := rfl
    have hI := congrArg (((adjunctionUnit U).app M).total (J.obj s)) hi
    exact (hUnit s b).trans (congrArg ((induced U M).map
      (eqToHom (congrArg (fun F : C ⥤ B => F.obj s) h))) (hU.symm.trans hI.symm))
  have hMap := fullSquareOrdinarySourceLinear_counit J U Q T h
    ((restriction J).obj M) M (induced U M) (𝟙 _) ((adjunctionUnit U).app M)
    (adjunctionUnit_mem U M) a ha hCompat w
  have hPoint := LinearMap.congr_fun hMap x
  simp only [LinearMap.comp_apply] at hPoint
  have hTrans := LinearMap.congr_fun (evenTransposeLinear_id J M w) x
  have hI := congrArg (((adjunctionUnit U).app M).total w) hTrans
  have hU := unit_total_apply U M w (restrictionCounitLinear J M w x)
  exact hU.symm.trans (hI.symm.trans hPoint)

end OddMath.QuiverHecke.ELVOld.BalancedInduction
