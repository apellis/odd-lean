import OddMath.QuiverHecke.CyclotomicAction.ELVFullInductionSquareSource
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedMatrixRows

/-! # Ordinary unit and dot fields through a full-inclusion square

The unit/dot part of Brundan–Ellis (1.13)–(1.14) is compared before
specializing the canonical content inclusion. The selected chart, the
ordinary unit, and all dot powers retain their literal coend formulas.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
private theorem coend_ext
    {k C A V : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive A] [Linear k A] [AddCommMonoid V] [Module k V]
    (J : C ⥤ A) (M : C ⥤ SVec k) {w : A}
    {f g : Obj J M w →ₗ[k] V}
    (h : ∀ s (a : J.obj s ⟶ w) (b : M.obj s),
      f (tensor J M s a b) = g (tensor J M s a b)) : f = g := by
  classical
  apply LinearMap.cancel_right (Submodule.mkQ_surjective (relations J M w)) |>.mp
  apply DirectSum.linearMap_ext
  intro s
  apply TensorProduct.ext
  ext a b
  exact h s a b

private theorem unitDot_apply
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
    (P : Superfunctor k C (SVec k)) (n : ℕ) (s : C) (b : P.obj s) :
    unitDotLinear J hα P n s b = ((transformLinear hα P (J.obj s)) ^ n) (unit J P.toFunctor s b) := rfl

variable {k C A B E : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
  [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (U : A ⥤ E) [U.Additive] [U.Linear k] [IsSuperfunctor k U] [U.Full] [U.Faithful]
  (Q : C ⥤ B) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q]
  (T : B ⥤ E) [T.Additive] [T.Linear k] [IsSuperfunctor k T]
  (h : J ⋙ U = Q ⋙ T) (M : Superfunctor k C (SVec k))

/-- The selected target chart carries the ordinary unit to the ordinary unit. -/
theorem fullSquareTargetLinear_unit (s : C) (b : M.obj s) :
    fullSquareTargetLinear J U Q T h M (J.obj s) (T.obj (Q.obj s))
      (congrArg (fun F : C ⥤ E => F.obj s) h) (unit J M.toFunctor s b) =
      unit T (induced Q M).toFunctor (Q.obj s) (unit Q M.toFunctor s b) := by
  have hC := fullSquareTargetLinear_tensor J U Q T h M s (J.obj s) (T.obj (Q.obj s))
    (congrArg (fun F : C ⥤ E => F.obj s) h) (𝟙 (J.obj s)) b
  have he : ((eqToHom (congrArg (fun F : C ⥤ E => F.obj s) h).symm ≫ U.map (𝟙 (J.obj s))) ≫
      eqToHom (congrArg (fun F : C ⥤ E => F.obj s) h)) = 𝟙 (T.obj (Q.obj s)) := by
    simp
  have hL := congrArg (fullSquareTargetLinear J U Q T h M (J.obj s) (T.obj (Q.obj s))
    (congrArg (fun F : C ⥤ E => F.obj s) h)) (unit_apply J M.toFunctor s b)
  have hE := congrArg (fun a => tensor T (induced Q M).toFunctor (Q.obj s) a
    (unit Q M.toFunctor s b)) he
  have hR := unit_apply T (induced Q M).toFunctor (Q.obj s) (unit Q M.toFunctor s b)
  have hh := hL.trans (hC.trans (hE.trans hR.symm))
  exact hh

variable {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
  {β : ∀ s, T.obj s ⟶ T.obj s} (hβ : IsSupernatural k p β)

/-- The whole selected chart intertwines homogeneous dot operators when their
coefficient square commutes. Canonical content supplies that coefficient equality. -/
theorem fullSquareTargetLinear_transform (w : A) (z : E) (hz : U.obj w = z)
    (hCoeff : ∀ s (g : J.obj s ⟶ w),
      ((eqToHom (congrArg (fun F : C ⥤ E => F.obj s) h).symm ≫ U.map (α s ≫ twist k p g)) ≫ eqToHom hz) =
        β (Q.obj s) ≫ twist k p ((eqToHom (congrArg (fun F : C ⥤ E => F.obj s) h).symm ≫ U.map g) ≫ eqToHom hz)) :
    fullSquareTargetLinear J U Q T h M w z hz ∘ₗ transformLinear hα M w =
      transformLinear hβ (induced Q M) z ∘ₗ fullSquareTargetLinear J U Q T h M w z hz := by
  apply coend_ext _ _
  intro s g b
  have hL := congrArg (fullSquareTargetLinear J U Q T h M w z hz)
    (transformLinear_tensor hα M w s g b)
  have hC := fullSquareTargetLinear_tensor J U Q T h M s w z hz (α s ≫ twist k p g) b
  have hR := congrArg (transformLinear hβ (induced Q M) z)
    (fullSquareTargetLinear_tensor J U Q T h M s w z hz g b)
  have hT := transformLinear_tensor hβ (induced Q M) z (Q.obj s)
    ((eqToHom (congrArg (fun F : C ⥤ E => F.obj s) h).symm ≫ U.map g) ≫ eqToHom hz)
    (unit Q M.toFunctor s b)
  have hCo := congrArg (fun a => tensor T (induced Q M).toFunctor (Q.obj s) a
    (unit Q M.toFunctor s b)) (hCoeff s g)
  exact (hL.trans (hC.trans hCo)).trans (hR.trans hT).symm

/-- The selected target chart transports every ordinary unit/dot column.
The coefficient condition is discharged for the prescribed content dot. -/
theorem fullSquareTargetLinear_unitDot (s : C) (n : ℕ) (b : M.obj s)
    (hCoeff : ∀ v (g : J.obj v ⟶ J.obj s),
      ((eqToHom (congrArg (fun F : C ⥤ E => F.obj v) h).symm ≫ U.map (α v ≫ twist k p g)) ≫
        eqToHom (congrArg (fun F : C ⥤ E => F.obj s) h)) =
      β (Q.obj v) ≫ twist k p ((eqToHom (congrArg (fun F : C ⥤ E => F.obj v) h).symm ≫ U.map g) ≫
        eqToHom (congrArg (fun F : C ⥤ E => F.obj s) h))) :
    fullSquareTargetLinear J U Q T h M (J.obj s) (T.obj (Q.obj s))
      (congrArg (fun F : C ⥤ E => F.obj s) h) (unitDotLinear J hα M n s b) =
      unitDotLinear T hβ (induced Q M) n (Q.obj s) (unit Q M.toFunctor s b) := by
  have hD := fullSquareTargetLinear_transform J U Q T h M hα hβ (J.obj s) (T.obj (Q.obj s))
    (congrArg (fun F : C ⥤ E => F.obj s) h) hCoeff
  have hP := intertwine_pow
    (fullSquareTargetLinear J U Q T h M (J.obj s) (T.obj (Q.obj s))
      (congrArg (fun F : C ⥤ E => F.obj s) h))
    (transformLinear hα M (J.obj s)) (transformLinear hβ (induced Q M) (T.obj (Q.obj s)))
    hD n
  have hP' := LinearMap.congr_fun hP (unit J M.toFunctor s b)
  have hR := congrArg ((transformLinear hβ (induced Q M) (T.obj (Q.obj s))) ^ n)
    (fullSquareTargetLinear_unit J U Q T h M s b)
  have hL := congrArg (fullSquareTargetLinear J U Q T h M (J.obj s) (T.obj (Q.obj s))
    (congrArg (fun F : C ⥤ E => F.obj s) h)) (unitDot_apply J hα M n s b)
  have hO := unitDot_apply T hβ (induced Q M) n (Q.obj s) (unit Q M.toFunctor s b)
  have hFinal := hL.trans (hP'.trans (hR.trans hO.symm))
  exact hFinal

end OddMath.QuiverHecke.ELVOld.BalancedInduction
